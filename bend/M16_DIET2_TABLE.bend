# Emits ext 2107's modelled decode instances (bend/m16_diet2.bend against bend/m16_diet2_spec.bend) for
# bend/m16_diet2_diff.py, which evaluates the patched C sources on the same inputs:
#   extract A B: ref W0 .. W7 | diet W0 .. W7 | spec W0 .. W7
#     the eight windows w0 .. w7 (32-bit hex) of dq8_aligned_4bits / dq8_m16_regs / the bit-offset spec
#     for word i0 = A, word i1 = B, over marker word pairs whose nibbles are pairwise distinct (so any
#     other shift, extract offset, byte selector or mask changes some printed window);
#   lds lane L: diet D0 .. D7 | ref R0 .. R7
#     the byte offsets from the ring base of the 8 words a lane reads in ring slot 0 (tiles t = 0 .. 3,
#     word dw0 / i0 then word dw1 / i1 of each), lanes 0 .. 31;
#   mode E: M       EXL3_M16_DIET = E (unset, "", "0", "1", "2", "3", "00", "a") gives mode M (bad = refused)
#   set X: M        torch.ops.exl3_m16.diet(X) from mode 1 (q = query)
#   inst D: I B K   the launchers' instance DIET = I for mode D, 2106 bookkeeping B, 2107 tile step K
import Base
import ./m16_diet2_spec.bend as Spec
import ./m16_diet2.bend as Impl

def pick(n: Nat, ds: List<&2, String>) -> String:
  match n:
    case 0n:
      match ds:
        case Nil{}:
          "?"
        case d <> rest:
          d
    case 1n+m:
      match ds:
        case Nil{}:
          "?"
        case d <> rest:
          pick(m, rest)

def hexd(+n: Nat) -> String:
  pick(n, ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "A", "B", "C", "D", "E", "F"])

# A word's hex, most significant nibble first.
def hexw(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      hexw(rest) ++ hexd(x)

def win8(w: Spec.Win8) -> String:
  match w:
    case Spec.Win8{w0, w1, w2, w3, w4, w5, w6, w7}:
      hexw(w0) ++ " " ++ hexw(w1) ++ " " ++ hexw(w2) ++ " " ++ hexw(w3) ++ " " ++ hexw(w4) ++ " " ++ hexw(w5) ++ " " ++
        hexw(w6) ++ " " ++ hexw(w7)

def extract(+a: List<&2, Nat>, +b: List<&2, Nat>) -> String:
  "extract " ++ hexw(a) ++ " " ++ hexw(b) ++ ": ref " ++ win8(Spec.ref_windows(a, b)) ++ " | diet " ++
    win8(Impl.diet_windows(a, b)) ++ " | spec " ++ win8(Spec.windows(a, b)) ++ "\n"

def lds_d(n: Nat, +t: Nat, +lane: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(Impl.lds_addr(Nat.add(Impl.dw0(0n, lane), 0n), t)) ++ " " ++
        Nat.show(Impl.lds_addr(Nat.add(Impl.dw1(0n, lane), 0n), t)) ++ lds_d(m, 1n+t, lane)

def lds_r(n: Nat, +t: Nat, +lane: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(Spec.ref_addr(0n, 0n, t, Spec.ref_i0(lane))) ++ " " ++ Nat.show(Spec.ref_addr(0n, 0n, t, Spec.ref_i1(lane))) ++
        lds_r(m, 1n+t, lane)

def lanes(n: Nat, +lane: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      "lds lane " ++ Nat.show(lane) ++ ": diet" ++ lds_d(4n, 0n, lane) ++ " | ref" ++ lds_r(4n, 0n, lane) ++ "\n" ++ lanes(m, 1n+lane)

def mode_s(m: Impl.Mode) -> String:
  match m:
    case Impl.Ok{x}:
      Nat.show(x)
    case Impl.Bad{}:
      "bad"

def mode(+name: String, env: Impl.Env) -> String:
  "mode " ++ name ++ ": " ++ mode_s(Impl.parse(env)) ++ "\n"

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def feat(f: Spec.Feat) -> String:
  match f:
    case Spec.Feat{b, k}:
      bit(b) ++ " " ++ bit(k)

def inst(+d: Nat) -> String:
  "inst " ++ Nat.show(d) ++ ": " ++ Nat.show(Impl.inst(d)) ++ " " ++ feat(Spec.feat(Impl.inst(d))) ++ "\n"

def main() -> IO(Unit):
  +m1 = {[8n, 9n, 10n, 11n, 12n, 13n, 14n, 15n] : List<&2, Nat>}
  +m0 = {[0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n] : List<&2, Nat>}
  +m3 = {[7n, 6n, 5n, 4n, 3n, 2n, 1n, 0n] : List<&2, Nat>}
  +m2 = {[15n, 14n, 13n, 12n, 11n, 10n, 9n, 8n] : List<&2, Nat>}
  IO.print(extract(m1, m0) ++ extract(m0, m1) ++ extract(m2, m3) ++ extract(m3, m2) ++ lanes(32n, 0n) ++
    mode("unset", Impl.Unset{}) ++ mode("\"\"", Impl.Str{Nil{}}) ++ mode("\"0\"", Impl.Str{[48n]}) ++
    mode("\"1\"", Impl.Str{[49n]}) ++ mode("\"2\"", Impl.Str{[50n]}) ++ mode("\"3\"", Impl.Str{[51n]}) ++
    mode("\"00\"", Impl.Str{[48n, 48n]}) ++ mode("\"a\"", Impl.Str{[97n]}) ++
    "set q: " ++ Nat.show(Impl.set_mode(1n, Impl.Query{})) ++ "\n" ++ "set 0: " ++ Nat.show(Impl.set_mode(1n, Impl.Put{0n})) ++ "\n" ++
    "set 1: " ++ Nat.show(Impl.set_mode(1n, Impl.Put{1n})) ++ "\n" ++ "set 2: " ++ Nat.show(Impl.set_mode(1n, Impl.Put{2n})) ++ "\n" ++
    "set 3: " ++ Nat.show(Impl.set_mode(1n, Impl.Put{3n})) ++ "\n" ++ "set 7: " ++ Nat.show(Impl.set_mode(1n, Impl.Put{7n})) ++ "\n" ++
    inst(0n) ++ inst(1n) ++ inst(2n))
