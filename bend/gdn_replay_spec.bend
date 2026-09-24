# Independent reference for the GDN recurrent state across greedy speculative
# rounds: the state is the left fold of the per-token update over exactly the
# committed tokens, each row's output is the readout of the state after its
# prefix, the conv window is the last K conv inputs of everything committed
# and the position counts the committed tokens. No engine structure (verify
# rows, history, replay jobs, buffer columns) appears here.
import Base

def fold(~S: Data, ~X: Data, ~step: S -> X -> S, xs: List<&2, X>, s: S) -> S:
  match xs:
    case Nil{}:
      s
    case x <> rest:
      fold(~S, ~X, ~step, rest, step(s, x))

# Row i of a verify of xs from s0 (pre = the rows before it): the readout of
# fold over the first i + 1 inputs, recomputed from s0 for every row.
def outputs(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S,
    ~out: S -> X -> O, xs: List<&2, X>, +s0: S, +pre: List<&2, X>)
  -> List<&2, O>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      +upto = List.append(&2, X, pre, [x])
      out(fold(~S, ~X, ~step, upto, s0), x) <>
        outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto)

# The last K entries of a sequence (all of it when shorter).
def last(~Y: Data, +K: Nat, +seq: List<&2, Y>) -> List<&2, Y>:
  List.drop(&2, Y, seq, Nat.sub(List.length(&2, Y, seq), K))
