# Finite differential table of the ext 5106 b/a GEMV model (bend/gdn_ba_ksplit.bend), compared byte for
# byte by bend/gdn_ba_ksplit_diff.py against the same table built from the quoted kernel lines of a
# pinned engine tree. Sections:
#   J  element map: thread t < 512, iterations i < 5 -> half2 element ks_j(t, i)
#   W  partial slots: (w < 16, s < 8, b|a) -> writer slot, reader slot
#   V  launcher variant for sample (KS, S, k)
#   P  block event order around the partial exchange, KS 0..2 x (owner, non-owner)
#   L  the lane order of the warp tree (lane l holds marker S<l>)
#   T  two symbolic task values: (S 2, row 1, a, k2 520, h 1, H 2, bias) and (S 1, row 0, b, k2 3, h 0, H 1)
import Base
import ./gdn_ba_ksplit.bend as Impl

def nshow(+n: Nat) -> String:
  Nat.show(n)

def ex(e: Impl.Ex) -> String:
  match e:
    case Impl.ZeroF{}:
      "0"
    case Impl.Fma{x2, w2, c, acc}:
      "F(" ++ Nat.show(x2) ++ "," ++ Nat.show(w2) ++ "," ++ Nat.show(c) ++ "," ++ ex(acc) ++ ")"
    case Impl.Add{a, b}:
      "A(" ++ ex(a) ++ "," ++ ex(b) ++ ")"
    case Impl.Bias{v, o}:
      "B(" ++ ex(v) ++ "," ++ Nat.show(o) ++ ")"
    case Impl.Stale{q}:
      "S" ++ Nat.show(q)

def ev(e: Impl.Ev) -> String:
  match e:
    case Impl.KsLoad{}:
      "ks_load"
    case Impl.State{}:
      "state"
    case Impl.NormOps{}:
      "norm_ops"
    case Impl.Conv{}:
      "conv"
    case Impl.Gemv{}:
      "gemv"
    case Impl.KsFma{}:
      "ks_fma"
    case Impl.KsTree{}:
      "ks_tree"
    case Impl.PartW{}:
      "part_w"
    case Impl.Bar{}:
      "bar"
    case Impl.Arrive{}:
      "arrive"
    case Impl.WinV{}:
      "win_v"
    case Impl.PartR{}:
      "part_r"
    case Impl.L2{}:
      "l2"
    case Impl.Dot2W{}:
      "dot2_w"

def evs(xs: List<&2, Impl.Ev>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      " " ++ ev(x) ++ evs(rest)

def jrow(fuel: Nat, +t: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+more:
      "J " ++ nshow(t) ++ ":" ++ nshow(Impl.ks_j(t, 0n)) ++ "," ++ nshow(Impl.ks_j(t, 1n)) ++ "," ++
        nshow(Impl.ks_j(t, 2n)) ++ "," ++ nshow(Impl.ks_j(t, 3n)) ++ "," ++ nshow(Impl.ks_j(t, 4n)) ++ "\n" ++
        jrow(more, 1n+t)

def wrow(fuel: Nat, +q: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+more:
      +w = Nat.div(q, 16n)
      +ab = Nat.div(Nat.mod(q, 16n), 8n)
      +s = Nat.mod(q, 8n)
      "W " ++ nshow(w) ++ " " ++ nshow(s) ++ " " ++ nshow(ab) ++ ":" ++ nshow(Impl.wslot(w, s, ab)) ++ "," ++
        nshow(Impl.rslot(w, s, ab)) ++ "\n" ++ wrow(more, 1n+q)

def vrow(+ks: Nat, +S: Nat, +k: Nat) -> String:
  "V " ++ nshow(ks) ++ " " ++ nshow(S) ++ " " ++ nshow(k) ++ ":" ++ nshow(Impl.variant(ks, S, k)) ++ "\n"

def vrows(fuel: Nat, +ks: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+more:
      vrow(ks, 1n, 5120n) ++ vrow(ks, 8n, 5120n) ++ vrow(ks, 9n, 5120n) ++ vrow(ks, 16n, 5120n) ++
      vrow(ks, 8n, 5121n) ++ vrow(ks, 8n, 5122n) ++ vrow(ks, 1n, 2n) ++ vrow(ks, 3n, 6144n) ++ vrows(more, 1n+ks)

def prow(+ks: Nat) -> String:
  "P " ++ nshow(ks) ++ " owner:" ++ evs(Impl.prog(ks, True{})) ++ "\n" ++
  "P " ++ nshow(ks) ++ " other:" ++ evs(Impl.prog(ks, False{})) ++ "\n"

def markers(fuel: Nat, +l: Nat) -> List<&2, Impl.Ex>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+more:
      Impl.Stale{l} <> markers(more, 1n+l)

def table() -> String:
  jrow(512n, 0n) ++ wrow(256n, 0n) ++ vrows(3n, 0n) ++ prow(0n) ++ prow(1n) ++ prow(2n) ++
  "L " ++ ex(Impl.tree(markers(32n, 0n))) ++ "\n" ++
  "T 2 1 1 520 1 2 1:" ++ ex(Impl.task(2n, 1n, 1n, 520n, 1n, 2n, True{})) ++ "\n" ++
  "T 1 0 0 3 0 1 0:" ++ ex(Impl.task(1n, 0n, 0n, 3n, 0n, 1n, False{})) ++ "\n"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(table())
