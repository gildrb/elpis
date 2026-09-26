# Emits the parameters ext 2106's laws are instantiated with (bend/m16_diet.bend, bend/m16_diet_laws.bend)
# for the served decode m16 kernels, one line per activation tile count MT = 1, 2 (the instances
# exl3_gemm_m16g.cu / exl3_mlp_m16.cu build) plus the tail / 8201 phase k-tile counts:
#   cfg mt MT: pf PF fold FOLD xr XR tiles_w TW w_stage W_STAGE x_iter X_ITER ring_mask M xbuf_mask M
#     xchunk_mask M fold_mask M iss_off0 O pow2 R X C F cadence D
# The masks are P - 1 for the moduli the model uses (dring: PF W_STAGE, dxnext: 2 XR X_ITER, dchunk:
# XR X_ITER, dfold: FOLD X_ITER); iss_off0 = (PF - 1) W_STAGE is m16g's first loop issue offset; pow2
# flags that each modulus is a power of two (so `x & (P - 1)` is `x mod P`); cadence = FOLD | 2 XR.
#   kt tail KT0 KT1 KT2 mlp KT1 KT2
# bend/m16_diet_diff.py compares every value with the patched sources.
import Base
import ./gemm_m16_partition.bend as Part
import ./mlp_m16_sched.bend as Mlp
import ./tail_m16_sched.bend as Tail
import ./m16_diet.bend as Impl

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# n is a power of two (fuel >= n suffices: each step halves n).
def pow2(fuel: Nat, +n: Nat) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      Bool.or(Nat.is_eq(n, 1n), Bool.and(Bool.and(Nat.is_lt(1n, n), Nat.is_eq(Nat.mod(n, 2n), 0n)), pow2(f, Nat.div(n, 2n))))

def is_p2(+n: Nat) -> String:
  bit(pow2(n, n))

def cfg(+mt: Nat) -> String:
  +pf = Impl.cfg_pf()
  +fo = Impl.cfg_fold()
  +xr = Impl.cfg_xr()
  +ws = Impl.cfg_ws()
  +xi = Impl.cfg_xi(mt)
  +RING = Nat.mul(pf, ws)
  +XBUF = Nat.mul(Nat.mul(2n, xr), xi)
  +XCH = Nat.mul(xr, xi)
  +FOLDP = Nat.mul(fo, xi)
  "cfg mt " ++ Nat.show(mt) ++ ": pf " ++ Nat.show(pf) ++ " fold " ++ Nat.show(fo) ++ " xr " ++ Nat.show(xr) ++
    " tiles_w " ++ Nat.show(Impl.cfg_tiles_w()) ++ " w_stage " ++ Nat.show(ws) ++ " x_iter " ++ Nat.show(xi) ++
    " ring_mask " ++ Nat.show(Nat.sub(RING, 1n)) ++ " xbuf_mask " ++ Nat.show(Nat.sub(XBUF, 1n)) ++
    " xchunk_mask " ++ Nat.show(Nat.sub(XCH, 1n)) ++ " fold_mask " ++ Nat.show(Nat.sub(FOLDP, 1n)) ++
    " iss_off0 " ++ Nat.show(Nat.mul(Nat.sub(pf, 1n), ws)) ++ " pow2 " ++ is_p2(RING) ++ " " ++ is_p2(XBUF) ++ " " ++
    is_p2(XCH) ++ " " ++ is_p2(FOLDP) ++ " cadence " ++ bit(Nat.is_eq(Nat.mod(Nat.mul(2n, xr), fo), 0n)) ++ "\n"

def kts() -> String:
  "kt tail " ++ Nat.show(Tail.kt0(Tail.kin())) ++ " " ++ Nat.show(Part.kt(Tail.hidden())) ++ " " ++
    Nat.show(Part.kt(Tail.inter())) ++ " mlp " ++ Nat.show(Part.kt(Mlp.hidden())) ++ " " ++ Nat.show(Part.kt(Mlp.inter())) ++ "\n"

def main() -> IO(Unit):
  IO.print(cfg(1n) ++ cfg(2n) ++ kts())
