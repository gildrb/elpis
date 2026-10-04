# Rounding-error bound vocabulary of the error-bound laws (bend/err_*_laws.bend).
#
# A Path counts, by class, the rounding steps on the way from one input term to one output
# element. Standard model (IEEE 754; Higham, Accuracy and Stability of Numerical Algorithms,
# 2nd ed., 2002, section 2.2 and Lemma 3.1): a step of class c multiplies the term by (1 + d)
# with |d| <= u_c; if sigma = sum of the u_c on the path is < 1, the path's relative error
# factor satisfies |prod(1 + d) - 1| <= sigma / (1 - sigma), which increases with sigma. So a
# kernel whose every output path has a sigma no larger than the worst path of another kernel
# computing the same sum has a worst-case error bound no larger than that kernel's.
#
# The laws never fix the class bounds: sigma(w, p) takes any weights w (one unit for all), and
# every law holds for EVERY w in the class order (order below), so it holds for the true
# hardware bounds whatever their exact values, as long as that order holds:
#   w.r32 <= w.t32,   x * w.t32 <= w.r16,   w.r16 <= w.t16,   x * w.t16 <= w.q8
# (x = the exchange rate of a law; x = 128 needs u_t32 <= 2^-18 when u_r16 = 2^-11, and
# u_t16 <= 2^-7 when u_q8 = 1.)
# Classes, finest first:
#   r32  fp32 result rounded to nearest (FADD / FFMA / FMUL, cvt.rn.f32.*)
#   t32  fp32 tensor-core accumulate (mma.sync .f32 accumulator; alignment and truncation)
#   r16  fp16 result rounded to nearest (HADD2 / HFMA2 / HMUL2, cvt.rn.f16.f32)
#   t16  fp16 tensor-core accumulate (mma.sync .f16 accumulator)
#   q8   an activation rounded to an int8 grid of step max|x| / 127 (per-row scale) before a
#        dot product: an element below half a step becomes 0, so |d| <= 1 (u_q8 = 1)
#   ex2, rcp, rsq  special-function steps (ex2.approx, rcp.approx or div, rsqrt.approx),
#        compared kind by kind (no exchange)
# Exact, so no step: fp16 x fp16 products inside an MMA, fp16 -> fp32 conversions, moves.
import Base

type Path is Data:
  Path{r32: Nat, t32: Nat, r16: Nat, t16: Nat, q8: Nat, ex2: Nat, rcp: Nat, rsq: Nat}

type W is Data:
  W{r32: Nat, t32: Nat, r16: Nat, t16: Nat, q8: Nat, ex2: Nat, rcp: Nat, rsq: Nat}

def zero() -> Path:
  Path{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# The concatenation of two path segments.
def add(p: Path, q: Path) -> Path:
  match p:
    case Path{a1, b1, c1, d1, h1, e1, f1, g1}:
      match q:
        case Path{a2, b2, c2, d2, h2, e2, f2, g2}:
          Path{Nat.add(a1, a2), Nat.add(b1, b2), Nat.add(c1, c2), Nat.add(d1, d2),
            Nat.add(h1, h2), Nat.add(e1, e2), Nat.add(f1, f2), Nat.add(g1, g2)}

# Sum of the class bounds along the path, in the unit of w.
def sigma(w: W, p: Path) -> Nat:
  match w:
    case W{+wa, +wb, +wc, +wd, +wh, +we, +wf, +wg}:
      match p:
        case Path{a, b, c, d, h, e, f, g}:
          Nat.add(Nat.mul(a, wa), Nat.add(Nat.mul(b, wb), Nat.add(Nat.mul(c, wc),
            Nat.add(Nat.mul(d, wd), Nat.add(Nat.mul(h, wh), Nat.add(Nat.mul(e, we),
              Nat.add(Nat.mul(f, wf), Nat.mul(g, wg))))))))

# The class order every law assumes of w, with exchange rate x.
def order(+x: Nat, w: W) -> Bool:
  match w:
    case W{+wa, +wb, +wc, +wd, +wh, we, wf, wg}:
      Bool.and(Nat.is_le(wa, wb), Bool.and(Nat.is_le(Nat.mul(x, wb), wc),
        Bool.and(Nat.is_le(wc, wd), Nat.is_le(Nat.mul(x, wd), wh))))

# e is dominated by s at exchange rate x: e's steps can be matched one to one to s's steps of
# the same or a coarser class, tier by tier from the coarsest: q8; then r16 < t16 (suffix
# sums), where every q8 step of s left unmatched may absorb up to x of e's r16 / t16 steps;
# then r32 < t32 (suffix sums), where every r16 / t16 step of s left unmatched (including the
# capacity a spare q8 step lends) may absorb up to x of e's r32 / t32 steps. Special-function
# steps are matched kind by kind.
def dom(+x: Nat, e: Path, s: Path) -> Bool:
  match e:
    case Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          +capc = Nat.mul(x, Nat.sub(sh, eh))
          +spare = Nat.sub(Nat.add(Nat.add(sd, sc), capc), Nat.add(ed, ec))
          Bool.and(Nat.is_le(eh, sh),
            Bool.and(Nat.is_le(ed, Nat.add(sd, capc)),
              Bool.and(Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), capc)),
                Bool.and(Nat.is_le(eb, Nat.add(sb, Nat.mul(x, spare))),
                  Bool.and(Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), Nat.mul(x, spare))),
                    Bool.and(Nat.is_le(ee, se), Bool.and(Nat.is_le(ef, sf), Nat.is_le(eg, sg))))))))
