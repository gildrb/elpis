# Strided absolute-tile split/combine partition of the target verify-attention kernels as shipped by
# ext patch 3006 (exllamav3_ext/attn_verify.cuh + attn_verify.cu: attn_verify_split_k3v3 / _k4v4
# and attn_verify_combine), transcribed from the CUDA integer expressions over Nat. H =
# attn_verify.cuh, C = attn_verify.cu. C `int` arithmetic on the non-negative values used here is
# Nat arithmetic while nothing overflows (L <= 2^18 + 8, gridDim.x = S <= 82). This supersedes
# bend/attn_chunk.bend, which models 3003's fixed 512-token chunks (one partial per chunk, removed
# from the kernel by 3006); that module and its laws are left unchanged. Independent reference:
# attn_stride_spec.bend; laws: attn_stride_laws.bend; buffer bounds: attn_stride_bounds.bend.
import Base

# H: ceil division (a + b - 1) / b as written in av_live_tiles and av_cta_tiles
def cdiv(a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

def bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# Work guarded by a kernel condition: none unless the condition holds
def gate(b: Bool, n: Nat) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      n

# H av_live_tiles(L) = (L + AV_T - 1) / AV_T, AV_T = 64: `n_tiles` of the split kernel and of the
# combine, L = cache_seqlens[b] + q_len
def live_tiles(+L: Nat) -> Nat:
  cdiv(L, 64n)

# H av_cta_tiles(n_tiles, x, S) = (n_tiles - x + S - 1) / S: `ntiles` of split CTA x (reached only
# when x < n_tiles, so n_tiles - x does not wrap)
def cta_tiles(+n: Nat, +x: Nat, +S: Nat) -> Nat:
  cdiv(Nat.sub(n, x), S)

# H av_live_slots(n_tiles, S) = n_tiles < S ? n_tiles : S: `live` of the combine
def live_slots(+n: Nat, +S: Nat) -> Nat:
  Nat.min(n, S)

# C issue / tile loop: n0 = (cta + it * S) * AV_T, cta = blockIdx.x, S = gridDim.x
def tile_n0(+x: Nat, +it: Nat, +S: Nat) -> Nat:
  Nat.mul(Nat.add(x, Nat.mul(it, S)), 64n)

# C: q_abs = L - q_len + gid, the causal bound of the thread row with q_pos = gid
def q_abs(L: Nat, +q_len: Nat, qpos: Nat) -> Nat:
  Nat.add(Nat.sub(L, q_len), qpos)

# C split CTA x: `if (cta >= n_tiles) return;`, then `for (it = 0; it < ntiles; ++it)`: the tile
# stages the tokens n0 + j, j < AV_T (one per (warp, t, e) lane, law lanes_once), and token `tok`
# enters the softmax of the row with q_pos = gid (row_ok: gid < q_len, the laws' hypothesis) iff
# `tok <= q_abs`. True when kv position p is one of them.
def tile_visits(+x: Nat, +it: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Bool:
  Bool.and(Nat.is_lt(x, live_tiles(L)),
    Bool.and(Nat.is_lt(it, cta_tiles(live_tiles(L), x, S)),
      Bool.and(Nat.is_le(tile_n0(x, it, S), p),
        Bool.and(Nat.is_lt(p, Nat.add(tile_n0(x, it, S), 64n)), Nat.is_le(p, q_abs(L, q_len, qpos))))))

def tile_hits(+x: Nat, +it: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  bit(tile_visits(x, it, p, L, S, q_len, qpos))

# Tiles it < k of CTA x
def tiles(+k: Nat, +x: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+it:
      Nat.add(tiles(it, x, p, L, S, q_len, qpos), tile_hits(x, it, p, L, S, q_len, qpos))

# Times position p enters row qpos's running state in CTA x (its partial slot x)
def cta_hits(+x: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  tiles(cta_tiles(live_tiles(L), x, S), x, p, L, S, q_len, qpos)

# Summed over the CTAs x < k of the grid (k = S = gridDim.x)
def ctas_hits(+k: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+x:
      Nat.add(ctas_hits(x, p, L, S, q_len, qpos), cta_hits(x, p, L, S, q_len, qpos))

# C: tok0 = n0 + warp * 8 + 2 * t; tok = tok0 + e: the tile-local token of lane (warp, t, e)
def lane_tok(w: Nat, t: Nat, e: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(w, 8n), Nat.mul(2n, t)), e)

# The tile-local tokens of the lanes, warp < AV_NW = 8, t = lane & 3 < 4, e < 2, in loop order
def lanes.e(k: Nat, +w: Nat, +t: Nat, +e: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      lane_tok(w, t, e) <> lanes.e(r, w, t, 1n+e)

def lanes.t(k: Nat, +w: Nat, +t: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      List.append(&2, Nat, lanes.e(2n, w, t, 0n), lanes.t(r, w, 1n+t))

def lanes.w(k: Nat, +w: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+r:
      List.append(&2, Nat, lanes.t(4n, w, 0n), lanes.w(r, 1n+w))

def lanes() -> List<&2, Nat>:
  lanes.w(8n, 0n)

# C split epilogue: CTA x stores partial slot `cta` = x (pbase uses cta) once, after its tile loop,
# unless it returned early (x >= n_tiles). Stores of slot s by CTA x:
def cta_store(+x: Nat, +s: Nat, +L: Nat) -> Nat:
  gate(Nat.is_lt(x, live_tiles(L)), bit(Nat.is_eq(x, s)))

# Stores of slot s by the CTAs x < k
def writes(+k: Nat, +s: Nat, +L: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+x:
      Nat.add(writes(x, s, L), cta_store(x, s, L))

# C attn_verify_combine: both loops visit s = 0 .. live - 1 in this fixed increasing order;
# `left` = live - s
def combine.go(left: Nat, +s: Nat) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+r:
      s <> combine.go(r, 1n+s)

# C: live = av_live_slots(av_live_tiles(L), splits), splits = S (attn_verify_gr passes the split
# grid's x to the combine)
def combine_order(+L: Nat, +S: Nat) -> List<&2, Nat>:
  combine.go(live_slots(live_tiles(L), S), 0n)

# The combine's skip test `if (ml.x == NEG_INF) continue;`: slot s keeps m = -inf exactly when no
# token of its tiles passes the row's mask, i.e. when its first tile start 64 s is past the row
# (laws skip_witness / skip_sound tie this predicate to cta_hits).
def row_nonempty(+s: Nat, +qa: Nat) -> Bool:
  Nat.is_le(Nat.mul(s, 64n), qa)

def keep(b: Bool, s: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case False{}:
      xs
    case True{}:
      s <> xs

def row_filter(+xs: List<&2, Nat>, +qa: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case s <> rest:
      keep(row_nonempty(s, qa), s, row_filter(rest, qa))

# The slots the weighted-sum loop merges into row qpos, in merge order (the non-skipped ones)
def merged(+L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> List<&2, Nat>:
  row_filter(combine_order(L, S), q_abs(L, q_len, qpos))
