# Finite differential table of the GDN replay model (bend/gdn_replay.bend),
# compared byte for byte by bend/gdn_replay_diff.py against the pinned engine
# sources. Instance: the state is the trace of consumed rule inputs (step
# appends the token index, so row 0 shows exactly which verified tokens were
# replayed, in order); verify outputs are the trace after each row; conv
# column c of the start buffer holds tag 100 + c, token j's conv input is
# 200 + j. K = 4 (conv_kernel_size), H = 7 (max_history), position 1000.
# Rows: every window k in 0..7, count c in 0..k+1, eos in {0, 1}.
import Base
import ./gdn_replay.bend as Impl
import ./exl3_accept_spec.bend as Accept

def snoc(s: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, s, [x])

def keep(s: List<&2, Nat>, x: Nat) -> List<&2, Nat>:
  s

def upto(n: Nat, +base: Nat, +i: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Nat.add(base, i) <> upto(m, base, 1n+i)

def nats.go(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      match rest:
        case Nil{}:
          Nat.show(x)
        case r <> more:
          Nat.show(x) ++ "," ++ nats.go(r <> more)

def nats(xs: List<&2, Nat>) -> String:
  "[" ++ nats.go(xs) ++ "]"

def traces(xs: List<&2, List<&2, Nat>>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      nats(x) ++ traces(rest)

def flag(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def outcome(o: Impl.Outcome<List<&2, Nat>, Nat>) -> String:
  match o:
    case Impl.Committed{Impl.Engine{r, c, p, l}}:
      "row0=" ++ nats(r) ++ " conv=" ++ nats(c) ++ " pos=" ++ Nat.show(p) ++
        " lh=" ++ Nat.show(l)
    case Impl.Refused{r}:
      "refused row0=" ++ nats(r)

def row(+k: Nat, +c: Nat, +eos: Bool) -> String:
  "k=" ++ Nat.show(k) ++ " c=" ++ Nat.show(c) ++ " eos=" ++ flag(eos) ++ " " ++
    outcome(Impl.round(~List<&2, Nat>, ~Nat, ~Nat, ~snoc, 4n, 7n,
      Impl.Engine{Nil{}, upto(11n, 100n, 0n), 1000n, 0n}, k, upto(1n+k, 0n, 0n),
      upto(1n+k, 200n, 0n), Accept.Verdict{c, eos})) ++ "\n"

# counts c = from..k+1 for one window k (fuel: remaining counts)
def counts(fuel: Nat, +k: Nat, +c: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+more:
      row(k, c, False{}) ++ row(k, c, True{}) ++ counts(more, k, 1n+c)

def verify_row(+k: Nat) -> String:
  "k=" ++ Nat.show(k) ++ " verify=" ++
    traces(Impl.verify(~List<&2, Nat>, ~Nat, ~List<&2, Nat>, ~snoc, ~keep,
      upto(1n+k, 0n, 0n), Nil{})) ++ "\n"

def windows(fuel: Nat, +k: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+more:
      verify_row(k) ++ counts(2n+k, k, 0n) ++ windows(more, 1n+k)

def main() -> String:
  windows(8n, 0n)
