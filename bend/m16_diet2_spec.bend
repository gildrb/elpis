# Reference (EXL3_M16_DIET = 0 / 1) m16 tile step of ext 2107's three decode m16 kernels, and the shared
# vocabulary. Transcribed from the patched tree (patch 2107-m16-decode-diet-on2106.patch, sha256
# 0584196d...; D: = exl3_dq.cuh, T: = exl3_tail_m16_kernel.cuh, M: = exl3_mlp_m16_kernel.cuh, G: =
# exl3_gemm_m16g_kernel.cuh, P: = ptx.cuh, all under exllamav3_ext/, line numbers of the patched tree):
# - mma_tile(sa, st) (M:531, T:402, G:315): ldmatrix of the activation piece at sa, then for
#   each of the 4 weight tiles t of the ring slot at st: dq8_aligned_4bits(st + t * 128, lane * 8)
#   (D:164-184) reads words i0 = (i1 + 31) & 31 and i1 = (lane * 8) >> 3 of the 128-byte tile, extracts
#   the eight 16-bit trellis windows with one funnel shift (FSHF_IMM, P:314) and bit-field extracts
#   (BFE16_IMM, P:315) and decodes them pairwise with decode_3inst_2; the fragment {f0[0], f1[0], f0[1],
#   f1[1]} is the MMA A operand for each of the MT activation tiles.
# Bit-level values are modelled at nibble granularity: a 32-bit word is its 8 nibbles, least significant
# first. Every shift, extract offset and byte select of both extractions is a multiple of 4 bits, so this
# is exact: a funnel shift right by 4k bits drops k nibbles of {hi:lo}, `& 0xffff` keeps nibbles 0-3,
# bfe.u32 (pos 4k, len 16) keeps nibbles k .. k + 3 with zero fill past bit 31, and a prmt byte is two
# nibbles. The codebook decode_3inst_2 is the same function in both modes and is kept abstract: a decode
# is its argument pair (Dec). Addresses are shared-window byte addresses (the generic ring / xbuf
# pointers enter as rs = cvta(ring); cvta of p + d is cvta(p) + d inside the window).
import Base

# ---- nibble words ----

def ntake(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case x <> rest:
          x <> ntake(m, rest)

def ndrop(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      xs
    case 1n+m:
      match xs:
        case Nil{}:
          Nil{}
        case x <> rest:
          ndrop(m, rest)

def zero4() -> List<&2, Nat>:
  [0n, 0n, 0n, 0n]

# The zero word.
def zw() -> List<&2, Nat>:
  [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]

def cat(+x: List<&2, Nat>, +y: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, x, y)

# shf.r.wrap / __funnelshift_r(lo, hi, 4k), k < 8: bits 4k .. 4k + 31 of {hi:lo}.
def shf(+lo: List<&2, Nat>, +hi: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  ntake(8n, ndrop(k, cat(lo, hi)))

# x & 0xffff
def lo16(+x: List<&2, Nat>) -> List<&2, Nat>:
  cat(ntake(4n, x), zero4())

# bfe.u32 x, 4k, 16 (BFE16_IMM): bits 4k .. 4k + 15, zero past bit 31.
def bfe16(+x: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  cat(ntake(4n, ndrop(k, cat(x, zero4()))), zero4())

# The 16-bit window at bit 4k of the 64-bit {a:b} (a = word i0 above b = word i1), zero-extended.
def window(+a: List<&2, Nat>, +b: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  cat(ntake(4n, ndrop(k, cat(b, a))), zero4())

# The eight windows w0 .. w7 of a lane (w_i at bit 4 (7 - i)).
type Win8 is Data:
  Win8{w0: List<&2, Nat>, w1: List<&2, Nat>, w2: List<&2, Nat>, w3: List<&2, Nat>, w4: List<&2, Nat>,
    w5: List<&2, Nat>, w6: List<&2, Nat>, w7: List<&2, Nat>}

def windows(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Win8:
  Win8{window(a, b, 7n), window(a, b, 6n), window(a, b, 5n), window(a, b, 4n), window(a, b, 3n), window(a, b, 2n),
    window(a, b, 1n), window(a, b, 0n)}

# ---- the reference extraction (dq8_aligned_4bits, D:171-179) ----

# FSHF_IMM(s, b, a, 20); w7 = b & 0xffff; BFE16_IMM(w6, b, 4) .. (w3, b, 16); w2 = s & 0xffff;
# BFE16_IMM(w1, s, 4); BFE16_IMM(w0, s, 8)
def ref_windows(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Win8:
  +s = shf(b, a, 5n)
  Win8{bfe16(s, 2n), bfe16(s, 1n), lo16(s), bfe16(b, 4n), bfe16(b, 3n), bfe16(b, 2n), bfe16(b, 1n), lo16(b)}

# ---- tile step ----

# decode_3inst_2<cb>(lo, hi): kept abstract (the same codebook in every mode).
type Dec is Data:
  Dec{lo: List<&2, Nat>, hi: List<&2, Nat>}

# One MMA of the tile loop: weight tile t, activation tile mt, A fragment {f0[0], f1[0], f0[1], f1[1]}.
type TE is Data:
  Ldsm{sa: Nat}
  Mma{t: Nat, mt: Nat, a0: Dec, a1: Dec, a2: Dec, a3: Dec}

def mmas(n: Nat, +mt: Nat, +t: Nat, +w: Win8, rest: List<&2, TE>) -> List<&2, TE>:
  match n:
    case 0n:
      rest
    case 1n+m:
      match w:
        case Win8{+w0, +w1, +w2, +w3, +w4, +w5, +w6, +w7}:
          Mma{t, mt, Dec{w0, w1}, Dec{w4, w5}, Dec{w2, w3}, Dec{w6, w7}} <> mmas(m, 1n+mt, t, Win8{w0, w1, w2, w3, w4, w5, w6, w7}, rest)

# Shared memory: a list of (byte address, word) cells, the word given by its nibbles; a read sees the
# first cell at that address (none: the zero word) as a 32-bit word, i.e. its nibbles 0 .. 7 (missing ones
# 0). Any shared-memory content is such a list.
type Cell is Data:
  Cell{addr: Nat, w: List<&2, Nat>}

def nth(n: Nat, xs: List<&2, Nat>) -> Nat:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          0n
        case x <> rest:
          x
    case 1n+m:
      match xs:
        case Nil{}:
          0n
        case x <> rest:
          nth(m, rest)

def w8(+w: List<&2, Nat>) -> List<&2, Nat>:
  [nth(0n, w), nth(1n, w), nth(2n, w), nth(3n, w), nth(4n, w), nth(5n, w), nth(6n, w), nth(7n, w)]

def rd_pick(c: Bool, +w: List<&2, Nat>, +other: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      w
    case False{}:
      other

def raw(mem: List<&2, Cell>, +x: Nat) -> List<&2, Nat>:
  match mem:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cell{+ad, +w}:
          rd_pick(Nat.is_eq(ad, x), w, raw(rest, x))

def rd(+mem: List<&2, Cell>, +x: Nat) -> List<&2, Nat>:
  w8(raw(mem, x))

# The word index of a lane's two words in a 128-byte tile: i1 = (lane * 8) >> 3, i0 = (i1 + 31) & 31.
def ref_i1(+lane: Nat) -> Nat:
  Nat.div(Nat.mul(lane, 8n), 8n)

def ref_i0(+lane: Nat) -> Nat:
  Nat.mod(Nat.add(ref_i1(lane), 31n), 32n)

# ptr = (const uint32_t*) (st + t * 128), ptr[i]: the shared address of word i of tile t of the ring slot
# at byte offset co (st = ring + cur_off).
def ref_addr(+rs: Nat, +co: Nat, +t: Nat, +i: Nat) -> Nat:
  Nat.add(rs, Nat.add(Nat.add(co, Nat.mul(t, 128n)), Nat.mul(4n, i)))

# The 4 tiles t = tl0 .. 3 of mma_tile (MT activation tiles each), mem = the shared words.
def ref_tiles(n: Nat, +t: Nat, +mem: List<&2, Cell>, +rs: Nat, +co: Nat, +lane: Nat, +MT: Nat) -> List<&2, TE>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      mmas(MT, 0n, t, ref_windows(rd(mem, ref_addr(rs, co, t, ref_i0(lane))), rd(mem, ref_addr(rs, co, t, ref_i1(lane)))),
        ref_tiles(m, 1n+t, mem, rs, co, lane, MT))

# mma_tile(xbuf_sa + x_off, ring + cur_off) of one loop iteration.
def ref_iter(+mem: List<&2, Cell>, +rs: Nat, +lane: Nat, +xsa: Nat, +co: Nat, +xo: Nat, +MT: Nat) -> List<&2, TE>:
  Ldsm{Nat.add(xsa, xo)} <> ref_tiles(4n, 0n, mem, rs, co, lane, MT)

# ---- mode dispatch (the ext 2106 two-mode switch, for the comparison) ----

# A kernel instance DIET = d runs 2106's loop bookkeeping iff d != 0 (`if constexpr (DIET)`, T:458,
# M:591; `if constexpr (!DIET)`, G:347) and 2107's tile step iff d >= 2 (`if constexpr (DIET >= 2)`, T:491,
# M:624, G:431).
type Feat is Data:
  Feat{bookkeeping: Bool, decode: Bool}

def feat(+d: Nat) -> Feat:
  Feat{Bool.not(Nat.is_eq(d, 0n)), Nat.is_le(2n, d)}
