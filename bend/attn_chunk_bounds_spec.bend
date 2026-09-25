# Independent reference for the 3003 partial / output buffers (attn_chunk_bounds.bend): the
# partials are one row-major array [bsz][n_kv][max_chunks][48 rows][W] (W = 256 floats of o, or
# the 2 floats (m, l)), the output and q one row-major array [bsz][q_len][n_q][256]; the cell of a
# coordinate is its row-major offset and the array holds the product of its extents.
import Base

# Row-major offset of (b, h, c, r, w) in [.][n_kv][mc][48][W]
def pcell(+b: Nat, +h: Nat, +c: Nat, +r: Nat, +w: Nat, +n_kv: Nat, +mc: Nat, +W: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), h), mc), c), 48n), r), W), w)

def psize(+bsz: Nat, +n_kv: Nat, +mc: Nat, +W: Nat) -> Nat:
  Nat.mul(bsz, Nat.mul(n_kv, Nat.mul(mc, Nat.mul(48n, W))))

# Row-major offset of (b, q_pos, head, d) in [.][q_len][n_q][256]; the q head of kv head kvh's
# local head hl is kvh * group + hl
def ocell(+b: Nat, +q_pos: Nat, +head: Nat, +d: Nat, +q_len: Nat, +n_q: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, q_len), q_pos), n_q), head), 256n), d)

def osize(+bsz: Nat, +q_len: Nat, +n_q: Nat) -> Nat:
  Nat.mul(bsz, Nat.mul(q_len, Nat.mul(n_q, 256n)))
