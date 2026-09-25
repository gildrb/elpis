# Independent reference for speculation invariance: plain greedy decoding, one token per step,
# each token being the target's answer for its prefix as the single row (row 0) of its own
# step. It stops after emitting a stop token or when the output budget is spent. No drafts,
# rounds, verdicts or device state appear here.
import Base

def is_stop(stops: List<&2, U32>, +t: U32) -> Bool:
  match stops:
    case Nil{}:
      False{}
    case s <> rest:
      Bool.or(U32.is_eq(s, t), is_stop(rest, t))

# The rest of the output after a token: nothing after a stop token.
def cont(stop: Bool, rest: List<&2, U32>) -> List<&2, U32>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      rest

# Greedy decoding of at most b tokens after the prefix seq.
def greedy(~row: List<&2, U32> -> Nat -> U32, b: Nat, +stops: List<&2, U32>,
    +seq: List<&2, U32>) -> List<&2, U32>:
  match b:
    case 0n:
      Nil{}
    case 1n+bp:
      +t = row(seq, 0n)
      t <> cont(is_stop(stops, t), greedy(~row, bp, stops, List.append(&2, U32, seq, [t])))

# What greedy decoding still emits after a prefix: nothing once the job has ended, else the
# greedy continuation within the remaining budget b.
def after(~row: List<&2, U32> -> Nat -> U32, ended: Bool, +b: Nat, +stops: List<&2, U32>,
    +seq: List<&2, U32>) -> List<&2, U32>:
  match ended:
    case True{}:
      Nil{}
    case False{}:
      greedy(~row, b, stops, seq)
