# Tile schedule of the ext 3010 CUDA prefill attention kernel (exllamav3_ext/pattn_kernel.cuh,
# pattn_kernel<F16>), transcribed from its integer expressions over Nat. C `int` arithmetic on the
# non-negative values used here is Nat arithmetic while nothing overflows (keys <= 2^18 + 2^11, head
# indices < 2^8). K = pattn_kernel.cuh. Independent reference: pattn_sched_spec.bend; laws:
# pattn_sched_laws.bend; finite link to the CUDA source: pattn_sched_diff.py (PATTN_SCHED_TABLE.bend).
# Names: L = total = cache_seqlens[b] + kv_append_len (keys the chunk sees), q = q_len, qb = the CTA's
# query block (K: qb = gridDim.x - 1 - blockIdx.x), r = a thread row of the block (gid or gid + 8,
# r < PA_BQ = 16), it = the kv tile iteration, p = a kv position (key).
import Base
import ./attn_stride.bend as Stride

# K: p0 = qb * PA_BQ; q_abs0 = total - q_len + p0 (absolute position of the CTA's first row)
def q_abs0(+L: Nat, +q: Nat, +qb: Nat) -> Nat:
  Nat.add(Nat.sub(L, q), Nat.mul(qb, 16n))

# K: q_abs_r0 = q_abs0 + gid, q_abs_r1 = q_abs0 + gid + 8: row r's causal bound
def row_abs(+L: Nat, +q: Nat, +qb: Nat, +r: Nat) -> Nat:
  Nat.add(q_abs0(L, q, qb), r)

# K: n_hi = min(q_abs0 + PA_BQ, total)
def n_hi(+L: Nat, +q: Nat, +qb: Nat) -> Nat:
  Nat.min(Nat.add(q_abs0(L, q, qb), 16n), L)

# K: ntiles = (n_hi + PA_BN - 1) / PA_BN (the tile loop runs it = 0 .. ntiles - 1)
def ntiles(+L: Nat, +q: Nat, +qb: Nat) -> Nat:
  Stride.cdiv(n_hi(L, q, qb), 32n)

# K: n0 = it * PA_BN (issue and loop)
def n0(+it: Nat) -> Nat:
  Nat.mul(it, 32n)

# K: the causal / length mask runs only when n0 + PA_BN - 1 > q_abs0
def masked(+L: Nat, +q: Nat, +qb: Nat, +it: Nat) -> Bool:
  Nat.is_lt(q_abs0(L, q, qb), Nat.add(n0(it), 31n))

# K: under the mask, key is dropped iff key > qa || key >= total
def mask_ok(m: Bool, +L: Nat, +q: Nat, +qb: Nat, +r: Nat, +p: Nat) -> Bool:
  match m:
    case False{}:
      True{}
    case True{}:
      Bool.and(Nat.is_le(p, row_abs(L, q, qb, r)), Nat.is_lt(p, L))

# K: tile it stages keys n0 + c, c < PA_BN (one lane each, law lanes_once); key p enters row r's
# softmax in iteration it iff it is one of them, the iteration runs, and the mask keeps it
def visits(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +it: Nat, +p: Nat) -> Bool:
  Bool.and(Nat.is_le(n0(it), p),
    Bool.and(Nat.is_lt(p, Nat.add(n0(it), 32n)),
      Bool.and(Nat.is_lt(it, ntiles(L, q, qb)), mask_ok(masked(L, q, qb, it), L, q, qb, r, p))))

# K: key = n0 + 8 * nt + 2 * t + (e & 1), nt < 4, t < 4, e < 4: the tile-local columns of the lanes
def lane_cols.e(+e: Nat, +nt: Nat, +t: Nat) -> List<&2, Nat>:
  match e:
    case 0n:
      []
    case 1n+k:
      Nat.add(Nat.add(Nat.mul(8n, nt), Nat.mul(2n, t)), Nat.mod(k, 2n)) <> lane_cols.e(k, nt, t)

def lane_cols.t(+t: Nat, +nt: Nat) -> List<&2, Nat>:
  match t:
    case 0n:
      []
    case 1n+k:
      List.append(&2, Nat, lane_cols.e(2n, nt, k), lane_cols.t(k, nt))

def lane_cols(+nt: Nat) -> List<&2, Nat>:
  match nt:
    case 0n:
      []
    case 1n+k:
      List.append(&2, Nat, lane_cols.t(4n, k), lane_cols(k))

# K issue: row0 = bt[n0 / PA_PAGE] * PA_PAGE + (n0 % PA_PAGE); the tile reads the page slots
# n0 % 256 .. n0 % 256 + 31 of that page
def page_off(+it: Nat) -> Nat:
  Nat.mod(n0(it), 256n)

# K: warp w of the CTA of kv head kvh computes q head kvh * PA_G + w (PA_G = 6); the q prologue maps
# smem row = hl * PA_BQ + pos to head kvh * 6 + hl, position p0 + pos
def q_head(+kvh: Nat, +w: Nat) -> Nat:
  Nat.add(Nat.mul(kvh, 6n), w)

def q_pos(+qb: Nat, +r: Nat) -> Nat:
  Nat.add(Nat.mul(qb, 16n), r)

# K: QK^T span = the 32-dim scale group g (two k16 MMA steps on dims 32 g + 16 s + k, s < 2, k < 16),
# flushed into fp32 after it; PV span = the 32-key tile (flushed per tile). A dim / key belongs to span
# d / 32
def span(+d: Nat) -> Nat:
  Nat.div(d, 32n)
