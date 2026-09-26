# Emits ext 8205's slot-weighted schedule tables from the Nat model bend/m16_wsched.bend, in the flat
# uint16 layout the host builder exllamav3_ext/quant/exl3_m16_wsched.h uploads (and gen_sched.py's
# flat()):
#   header[8] = mc0, mc1, mc2, nwait, kind, 0, 0, 0 (kind 0 = standalone 8201 MLP: mc0 = 0)
#   8201 block[G * 11] | pair[NP * 5] | wait list | fc1[2 NG1] nc1[2 NG1] fc2[NG2] nc2[NG2]
#   kind 1 (tail) only: tail block[G * 4] | fc0[NG0] nc0[NG0]
# One line per table: "kind K weights a0,b0,a1,b1,a2,b2: v,v,...". Printed for the served shapes
# (G = 164, 82 SMs, o_proj 6144 x 5120, MLP 5120 x 17408) at uniform weights and at ext 8205's
# defaults (exl3_mlp_m16.cuh: tail (1000, 845) (1000, 966) (1000, 927); MLP p1 (1000, 950), p2
# (1000, 927)). bend/m16_wsched_diff.py compares every line with gen_sched.py and the C++ builder.
import Base
import ./gemm_m16_partition.bend as Part
import ./mlp_m16_sched.bend as Mlp
import ./tail_m16_sched.bend as Tail
import ./m16_wsched.bend as W

def g() -> Nat:
  Mlp.grid()

def nsm() -> Nat:
  82n

def a() -> Nat:
  Tail.kin()

def h() -> Nat:
  Mlp.hidden()

def i() -> Nat:
  Mlp.inter()

def cells(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      "," ++ Nat.show(x) ++ cells(rest)

def block_rows(left: Nat, +b: Nat, +off: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      cells([W.s1(g(), nsm(), h(), i(), a1, b1, b), W.n1(g(), nsm(), h(), i(), a1, b1, b), Mlp.slice(b),
        W.s2(g(), nsm(), h(), i(), a2, b2, b), W.n2(g(), nsm(), h(), i(), a2, b2, b),
        W.ring2(g(), nsm(), h(), i(), a1, b1, b), W.fin_pair(g(), nsm(), h(), i(), a2, b2, b),
        W.fin_rank(g(), nsm(), h(), i(), a2, b2, b), W.fin_cnt(g(), nsm(), h(), i(), a2, b2, b), off,
        W.wait_cnt(g(), nsm(), h(), i(), a2, b2, b)]) ++
        block_rows(rest, 1n+b, Nat.add(off, W.wait_cnt(g(), nsm(), h(), i(), a2, b2, b)), a1, b1, a2, b2)

def pair_rows(left: Nat, +p: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      cells([W.exp_gate(g(), nsm(), h(), i(), a1, b1, p), W.exp_up(g(), nsm(), h(), i(), a1, b1, p),
        W.fin_warps(g(), nsm(), h(), i(), a2, b2, p), W.fin_warps(g(), nsm(), h(), i(), a2, b2, p),
        W.wait2(g(), nsm(), h(), i(), a2, b2, p)]) ++ pair_rows(rest, 1n+p, a1, b1, a2, b2)

def wait_rows(left: Nat, +b: Nat, +a2: Nat, +b2: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      cells(W.waits(g(), nsm(), h(), i(), a2, b2, b)) ++ wait_rows(rest, 1n+b, a2, b2)

def fc1_rows(left: Nat, +x: Nat, +a1: Nat, +b1: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.fc1(g(), nsm(), h(), i(), a1, b1, x)) ++ fc1_rows(rest, 1n+x, a1, b1)

def nc1_rows(left: Nat, +x: Nat, +a1: Nat, +b1: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.nc1(g(), nsm(), h(), i(), a1, b1, x)) ++ nc1_rows(rest, 1n+x, a1, b1)

def fc2_rows(left: Nat, +x: Nat, +a2: Nat, +b2: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.fc2(g(), nsm(), h(), i(), a2, b2, x)) ++ fc2_rows(rest, 1n+x, a2, b2)

def nc2_rows(left: Nat, +x: Nat, +a2: Nat, +b2: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.nc2(g(), nsm(), h(), i(), a2, b2, x)) ++ nc2_rows(rest, 1n+x, a2, b2)

def fc0_rows(left: Nat, +x: Nat, +a0: Nat, +b0: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.fc0(g(), nsm(), a(), h(), a0, b0, x)) ++ fc0_rows(rest, 1n+x, a0, b0)

def nc0_rows(left: Nat, +x: Nat, +a0: Nat, +b0: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      "," ++ Nat.show(W.nc0(g(), nsm(), a(), h(), a0, b0, x)) ++ nc0_rows(rest, 1n+x, a0, b0)

def tail_rows(left: Nat, +b: Nat, +a0: Nat, +b0: Nat, +a1: Nat, +b1: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+rest:
      cells([W.s0(g(), nsm(), a(), h(), a0, b0, b), W.n0(g(), nsm(), a(), h(), a0, b0, b),
        W.ring1(g(), nsm(), a(), h(), a0, b0, b), W.tring2(g(), nsm(), a(), h(), i(), a0, b0, a1, b1, b)]) ++
        tail_rows(rest, 1n+b, a0, b0, a1, b1)

def kind_tail(kind: Nat, +a0: Nat, +b0: Nat, +a1: Nat, +b1: Nat) -> String:
  match kind:
    case 0n:
      ""
    case 1n+k:
      tail_rows(g(), 0n, a0, b0, a1, b1) ++ fc0_rows(Tail.ng0(h()), 0n, a0, b0) ++
        nc0_rows(Tail.ng0(h()), 0n, a0, b0)

def mc0_of(kind: Nat, +a0: Nat, +b0: Nat) -> Nat:
  match kind:
    case 0n:
      0n
    case 1n+k:
      W.mc0(g(), nsm(), a(), h(), a0, b0)

def table(+kind: Nat, +a0: Nat, +b0: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat) -> String:
  +NG1 = Part.groups(2n, i())
  +NG2 = Part.groups(1n, h())
  "kind " ++ Nat.show(kind) ++ " weights " ++ Nat.show(a0) ++ "," ++ Nat.show(b0) ++ "," ++ Nat.show(a1) ++
    "," ++ Nat.show(b1) ++ "," ++ Nat.show(a2) ++ "," ++ Nat.show(b2) ++ ":" ++
    Nat.show(mc0_of(kind, a0, b0)) ++ "," ++ Nat.show(W.mc1(g(), nsm(), h(), i(), a1, b1)) ++ "," ++
    Nat.show(W.mc2(g(), nsm(), h(), i(), a2, b2)) ++ "," ++ Nat.show(W.wait_off(g(), nsm(), h(), i(), a2, b2, g())) ++
    "," ++ Nat.show(kind) ++ ",0,0,0" ++
    block_rows(g(), 0n, 0n, a1, b1, a2, b2) ++ pair_rows(Mlp.pairs(i()), 0n, a1, b1, a2, b2) ++
    wait_rows(g(), 0n, a2, b2) ++ fc1_rows(NG1, 0n, a1, b1) ++ nc1_rows(NG1, 0n, a1, b1) ++
    fc2_rows(NG2, 0n, a2, b2) ++ nc2_rows(NG2, 0n, a2, b2) ++ kind_tail(kind, a0, b0, a1, b1) ++ "\n"

def main() -> IO(Unit):
  IO.print(table(0n, 1n, 1n, 1n, 1n, 1n, 1n) ++ table(1n, 1n, 1n, 1n, 1n, 1n, 1n) ++
    table(0n, 1n, 1n, 1000n, 950n, 1000n, 927n) ++ table(1n, 1000n, 845n, 1000n, 966n, 1000n, 927n))
