# Fixed-absolute-chunk split/combine partition of the target verify-attention kernels as shipped by
# ext patch 3003 (exllamav3_ext/attn_verify.cuh + attn_verify.cu: attn_verify_split_k3v3 / _k4v4
# and attn_verify_combine), transcribed from the CUDA integer expressions over Nat. H =
# attn_verify.cuh, C = attn_verify.cu. C `int` arithmetic on the non-negative values used here is
# Nat arithmetic while nothing overflows (L <= 2^18 + 8, chunk <= 2^12, gridDim.x <= 82). This
# supersedes bend/attn_split.bend, which models 3003's earlier round-relative split (av_split_len,
# removed from the kernel); that module and its laws are left unchanged. Independent reference:
# attn_chunk_spec.bend; laws: attn_chunk_laws.bend; buffer bounds: attn_chunk_bounds.bend.
import Base

# H: ceil division (a + b - 1) / b as written in av_live_chunks and the ntiles line of C
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

# H av_live_chunks(L, chunk) = (L + chunk - 1) / chunk: `n_chunks` of the split kernel and `live`
# of the combine, L = cache_seqlens[b] + q_len
def live(+L: Nat, +chunk: Nat) -> Nat:
  cdiv(L, chunk)

# C: n_start = c * chunk
def n_start(c: Nat, +chunk: Nat) -> Nat:
  Nat.mul(c, chunk)

# C: n_end = min(n_start + chunk, L)
def n_end(+c: Nat, +L: Nat, +chunk: Nat) -> Nat:
  Nat.min(Nat.add(n_start(c, chunk), chunk), L)

# C: ntiles = (n_end - n_start + AV_T - 1) / AV_T, AV_T = 64
def ntiles(+c: Nat, +L: Nat, +chunk: Nat) -> Nat:
  cdiv(Nat.sub(n_end(c, L, chunk), n_start(c, chunk)), 64n)

# C issue / tile loop: n0 = n_start + it * AV_T
def tile_n0(+c: Nat, it: Nat, +chunk: Nat) -> Nat:
  Nat.add(n_start(c, chunk), Nat.mul(it, 64n))

# C: q_abs = L - q_len + gid, the causal bound of the thread row with q_pos = gid
def q_abs(L: Nat, +q_len: Nat, qpos: Nat) -> Nat:
  Nat.add(Nat.sub(L, q_len), qpos)

# C tile loop `for (it = 0; it < ntiles; ++it)` of chunk c: the tile stages the tokens n0 + j,
# j < AV_T (one per (warp, t, e) lane, law lanes_once), and token `tok` enters the softmax of the
# row with q_pos = gid (row_ok: gid < q_len, the laws' hypothesis) iff `tok < n_end && tok <= q_abs`.
# True when kv position p is one of them.
def tile_visits(+c: Nat, +it: Nat, +p: Nat, +L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> Bool:
  Bool.and(Nat.is_lt(it, ntiles(c, L, chunk)),
    Bool.and(Nat.is_le(tile_n0(c, it, chunk), p),
      Bool.and(Nat.is_lt(p, Nat.add(tile_n0(c, it, chunk), 64n)),
        Bool.and(Nat.is_lt(p, n_end(c, L, chunk)), Nat.is_le(p, q_abs(L, q_len, qpos))))))

def tile_hits(+c: Nat, +it: Nat, +p: Nat, +L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  bit(tile_visits(c, it, p, L, chunk, q_len, qpos))

# Tiles it < k of chunk c
def tiles(+k: Nat, +c: Nat, +p: Nat, +L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+it:
      Nat.add(tiles(it, c, p, L, chunk, q_len, qpos), tile_hits(c, it, p, L, chunk, q_len, qpos))

# Times position p enters row qpos's softmax while a CTA processes chunk c (its partial)
def chunk_hits(+c: Nat, +p: Nat, +L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  tiles(ntiles(c, L, chunk), c, p, L, chunk, q_len, qpos)

# Summed over the chunks c < k (the live chunks, k = n_chunks, each processed once: law cta_once)
def chunks_hits(+k: Nat, +p: Nat, +L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+c:
      Nat.add(chunks_hits(c, p, L, chunk, q_len, qpos), chunk_hits(c, p, L, chunk, q_len, qpos))

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

# C chunk loop of CTA x = blockIdx.x: `c = blockIdx.x; if (c >= n_chunks) return;` then process c,
# `c += gridDim.x; if (c >= n_chunks) break;`, S = gridDim.x. Counts the iterations that process
# (and store the partial block of) chunk s. The loop runs at most n_chunks times (c grows by
# S >= 1 from c >= 0), so f = n_chunks is enough fuel.
def cta(+f: Nat, +c: Nat, +S: Nat, +s: Nat, +L: Nat, +chunk: Nat) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+g:
      gate(Nat.is_lt(c, live(L, chunk)),
        Nat.add(bit(Nat.is_eq(c, s)), cta(g, Nat.add(c, S), S, s, L, chunk)))

# Stores of chunk s's partial block by the CTAs x < k
def writes(+k: Nat, +S: Nat, +s: Nat, +L: Nat, +chunk: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+x:
      Nat.add(writes(x, S, s, L, chunk), cta(live(L, chunk), x, S, s, L, chunk))

# C attn_verify_combine: both loops visit s = 0 .. live - 1 in this fixed increasing order;
# `left` = live - s
def combine.go(left: Nat, +s: Nat) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+r:
      s <> combine.go(r, 1n+s)

def combine_order(+L: Nat, +chunk: Nat) -> List<&2, Nat>:
  combine.go(live(L, chunk), 0n)

# The combine's skip test `if (ml.x == NEG_INF) continue;`: the partial of chunk s keeps m = -inf
# exactly when no token of the chunk passes the row's mask, i.e. when its first position n_start is
# past the row (laws skip_witness / skip_sound tie this predicate to chunk_hits).
def row_nonempty(+s: Nat, +chunk: Nat, +qa: Nat) -> Bool:
  Nat.is_le(n_start(s, chunk), qa)

def keep(b: Bool, s: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case False{}:
      xs
    case True{}:
      s <> xs

def row_filter(+xs: List<&2, Nat>, +chunk: Nat, +qa: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case s <> rest:
      keep(row_nonempty(s, chunk, qa), s, row_filter(rest, chunk, qa))

# The chunks the weighted-sum loop merges into row qpos, in merge order (the non-skipped ones)
def merged(+L: Nat, +chunk: Nat, +q_len: Nat, +qpos: Nat) -> List<&2, Nat>:
  row_filter(combine_order(L, chunk), chunk, q_abs(L, q_len, qpos))
