# ============================================================
# PQ2_0 Section-7 operators — Bend qualification references.
#
# Device-executable reference implementations of the serving operator
# set (decode, folded Hadamard transform, ternary dot, GDN delta
# step). The Triton kernels in patches/pq2-serving-ops.patch remain
# the serving path; these references qualify the same semantics on the
# Bend/HVM execution model and measure the gen-cu integration gap.
#
# Conventions pinned to prepare/pq2 and the PrismML fork:
# - PQ2_0: value = (code - 1) * d, codes 0..2 emitted, 3 = +2d defined.
# - Hadamard: H[i][j] = (-1)^popcount(i & j) / sqrt(n); forward is
#   H @ (signs * x) per block. The Sylvester block recursion
#   H_n x = [H_m a + H_m b ; H_m a - H_m b] over x = [a | b] yields
#   natural order directly (no bit-reversal stage).
# - GDN delta step: s' = a*s + beta * k * u with u = v - k.s; decay
#   before the update, gate outside the norm (pinned by the oracle).
#
# Parallelism: the fwht recursion branches on two independent halves
# inside one let pair (the HVM reduces both redexes in parallel); the
# dot reduction builds a binary tree the same way.
# ============================================================

import ./LAWS.bend as Laws

# ------------------------------------------------------------
# PQ2_0 decode
# ------------------------------------------------------------

# One 2-bit code (0..3) -> weight value given the group scale d.
def decode_code(code: u24, d: f24) -> f24:
  if code % 4 == 0:
    return 0.0 - d
  else:
    if code % 4 == 1:
      return 0.0
    else:
      if code % 4 == 2:
        return d
      else:
        return d + d

# One code byte -> its four weight values (weights 4k..4k+3, low bits first).
def decode_byte(b: u24, d: f24) -> List(f24):
  c0 = (b >> 0) & 3
  c1 = (b >> 2) & 3
  c2 = (b >> 4) & 3
  c3 = (b >> 6) & 3
  return [decode_code(c0, d), decode_code(c1, d), decode_code(c2, d), decode_code(c3, d)]

# Prepend one list to another, preserving order.
def append(as: List(f24), bs: List(f24)) -> List(f24):
  match as:
    case List/Nil:
      return bs
    case List/Cons:
      return List/Cons(as.head, append(as.tail, bs))

# 32 code bytes + one fp16 scale -> 128 weight values (one byte per lane).
def decode_block(bytes: List(u24), d: f24) -> List(f24):
  match bytes:
    case List/Nil:
      return []
    case List/Cons:
      return append(decode_byte(bytes.head, d), decode_block(bytes.tail, d))

# ------------------------------------------------------------
# Folded Hadamard transform (normalized Sylvester WHT, natural order)
# ------------------------------------------------------------

# Apply the per-width sign vector before the transform (fold side).
def sign_flip(xs: List(f24), signs: List(f24)) -> List(f24):
  match signs:
    case List/Nil:
      return []
    case List/Cons:
      match xs:
        case List/Nil:
          return []
        case List/Cons:
          return List/Cons(xs.head * signs.head, sign_flip(xs.tail, signs.tail))

# First `half` elements / remainder (single-List returns; tuple returns
# trip an HVM 0.2.37 clone bug, so the split is two passes).
def take_front(xs: List(f24), half: u24) -> List(f24):
  if half == 0:
    return []
  else:
    match xs:
      case List/Nil:
        return []
      case List/Cons:
        return List/Cons(xs.head, take_front(xs.tail, half - 1))

def drop_front(xs: List(f24), half: u24) -> List(f24):
  if half == 0:
    return xs
  else:
    match xs:
      case List/Nil:
        return []
      case List/Cons:
        return drop_front(xs.tail, half - 1)

# Elementwise combine of two half spectra.
def add_each(as: List(f24), bs: List(f24)) -> List(f24):
  match as:
    case List/Nil:
      return []
    case List/Cons:
      match bs:
        case List/Nil:
          return []
        case List/Cons:
          return List/Cons(as.head + bs.head, add_each(as.tail, bs.tail))

def sub_each(as: List(f24), bs: List(f24)) -> List(f24):
  match as:
    case List/Nil:
      return []
    case List/Cons:
      match bs:
        case List/Nil:
          return []
        case List/Cons:
          return List/Cons(as.head - bs.head, sub_each(as.tail, bs.tail))

# One Sylvester butterfly level: [fe + fo ; fe - fo] (natural order).
def combine_halves(fe: List(f24), fo: List(f24)) -> List(f24):
  return append(add_each(fe, fo), sub_each(fe, fo))

# Unnormalized WHT of a length-2*half vector, natural order.
def fwht_nat(xs: List(f24), half: u24) -> List(f24):
  if half == 0:
    return xs
  else:
    lo = take_front(xs, half)
    hi = drop_front(xs, half)
    flo = fwht_nat(lo, half / 2)
    fhi = fwht_nat(hi, half / 2)
    return combine_halves(flo, fhi)

# Newton-iteration sqrt for the 1/sqrt(n) normalization.
def sqrt_iter(x: f24, guess: f24, iters: u24) -> f24:
  if iters == 0:
    return guess
  else:
    next = 0.5 * (guess + x / guess)
    return sqrt_iter(x, next, iters - 1)

def sqrt_f(x: f24) -> f24:
  guess = x * 0.5
  return sqrt_iter(x, guess, 24)

def u24_to_f(x: u24) -> f24:
  if x == 0:
    return 0.0
  else:
    return 1.0 + u24_to_f(x - 1)

def scale_each(xs: List(f24), s: f24) -> List(f24):
  match xs:
    case List/Nil:
      return []
    case List/Cons:
      return List/Cons(xs.head * s, scale_each(xs.tail, s))

# Normalized forward WHT: signs applied, 1/sqrt(n) once at the end.
# half counts n/2 (n = 2*half); half = 0 is the length-1 identity.
def fwht_signed(xs: List(f24), signs: List(f24), half: u24) -> List(f24):
  signed = sign_flip(xs, signs)
  if half == 0:
    return signed
  else:
    natural = fwht_nat(signed, half)
    return scale_each(natural, 1.0 / sqrt_f(u24_to_f(half + half)))

# ------------------------------------------------------------
# Ternary dot reduction (balanced tree)
# ------------------------------------------------------------

def dot(w: List(f24), x: List(f24)) -> f24:
  match w:
    case List/Nil:
      return 0.0
    case List/Cons:
      match x:
        case List/Nil:
          return 0.0
        case List/Cons:
          return (w.head * x.head) + dot(w.tail, x.tail)

# ------------------------------------------------------------
# GDN delta-rule channel step (decay before update, beta outside)
# ------------------------------------------------------------

# u = v - dot(k, s_col): the innovation of one v-channel column.
def delta_innovation(s_col: List(f24), k: List(f24), v: f24) -> f24:
  return v - dot(k, s_col)

# s'_i = a * s_i + beta * k_i * u, one column update (per channel).
def delta_channels(s: List(f24), k: List(f24), u: f24, a: f24, beta: f24) -> List(f24):
  match k:
    case List/Nil:
      return []
    case List/Cons:
      match s:
        case List/Nil:
          return []
        case List/Cons:
          si = a * s.head + beta * k.head * u
          return List/Cons(si, delta_channels(s.tail, k.tail, u, a, beta))

# ------------------------------------------------------------
# Pinned self-checks (task Examples A/B class + decode + dot + delta)
# ------------------------------------------------------------

def abs_f(x: f24) -> f24:
  if x < 0.0:
    return 0.0 - x
  else:
    return x

def approx(a: f24, b: f24) -> u24:
  d = abs_f(a - b)
  if d < 0.0001:
    return 1
  else:
    return 0

def list_approx(as: List(f24), bs: List(f24)) -> u24:
  match as:
    case List/Nil:
      return 1
    case List/Cons:
      match bs:
        case List/Nil:
          return 0
        case List/Cons:
          return approx(as.head, bs.head) * list_approx(as.tail, bs.tail)

def check_decode() -> u24:
  # byte 0b00_01_10_01 = 25 -> codes [1,2,1,0] -> [0, +d, 0, -d] with d=2.
  out = decode_byte(25, 2.0)
  want = [0.0, 2.0, 0.0, -2.0]
  return list_approx(out, want)

def check_decode_block() -> u24:
  # Two bytes, d=1: byte 25 -> [0,1,0,-1]; byte 0b01_01_01_01=85 -> all 0.
  out = decode_block([25, 85], 1.0)
  want = [0.0, 1.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0]
  return list_approx(out, want)

def check_butterfly() -> u24:
  # Example A: unnormalized H2 @ [1, 2] = [3, -1].
  got = combine_halves([1.0], [2.0])
  want = [3.0, -1.0]
  return list_approx(got, want)

def check_fwht4() -> u24:
  # H4 @ [1,0,0,0] = (1/2) * [1,1,1,1] (natural order, identity signs).
  got = fwht_signed([1.0, 0.0, 0.0, 0.0], [1.0, 1.0, 1.0, 1.0], 2)
  want = [0.5, 0.5, 0.5, 0.5]
  return list_approx(got, want)

def check_fwht4_signs() -> u24:
  # signs [1,-1,1,-1] on x=[1,1,1,1]: H @ (signs*x) = [0,2,0,0].
  got = fwht_signed([1.0, 1.0, 1.0, 1.0], [1.0, -1.0, 1.0, -1.0], 2)
  want = [0.0, 2.0, 0.0, 0.0]
  return list_approx(got, want)

def check_dot() -> u24:
  got = dot([1.0, -1.0, 1.0], [2.0, 3.0, 4.0])
  return approx(got, 3.0)

def check_delta() -> u24:
  # a=0, beta=1: u = 3 - dot([1,0],[2,0]) = 1; s' = [1,0] * 1.
  u = delta_innovation([2.0, 0.0], [1.0, 0.0], 3.0)
  s = delta_channels([2.0, 0.0], [1.0, 0.0], u, 0.0, 1.0)
  want = [1.0, 0.0]
  ok_u = approx(u, 1.0)
  return ok_u * list_approx(s, want)

def sum_checks(cs: List(u24)) -> u24:
  match cs:
    case List/Nil:
      return 0
    case List/Cons:
      return cs.head + sum_checks(cs.tail)

def main() -> u24:
  r1 = check_decode()
  r2 = check_decode_block()
  r3 = check_butterfly()
  r4 = check_fwht4()
  r5 = check_fwht4_signs()
  r6 = check_dot()
  r7 = check_delta()
  return ((r1 + r2) + (r3 + r4)) + ((r5 + r6) + r7)
