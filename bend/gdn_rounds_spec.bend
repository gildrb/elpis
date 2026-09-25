# Independent reference for a multi-round GDN job: the committed token stream is the
# concatenation of every round's accepted prefix; the state, outputs and conv window are those of
# one uninterrupted scan over that stream (bend/gdn_replay_spec.bend: fold, outputs, last). No
# round boundary, verify row, replay job or buffer column appears in the scan.
import Base
import ./gdn_rounds.bend as Impl

# The committed rule inputs (the stream ts) and conv inputs, in order.
def stream_x(~X: Data, ~Y: Data, rounds: List<&2, Impl.Round<X, Y>>) -> List<&2, X>:
  match rounds:
    case Nil{}:
      Nil{}
    case Impl.Round{window, xs, ys, +count} <> rest:
      List.append(&2, X, List.take(&2, X, xs, count), stream_x(~X, ~Y, rest))

def stream_y(~X: Data, ~Y: Data, rounds: List<&2, Impl.Round<X, Y>>) -> List<&2, Y>:
  match rounds:
    case Nil{}:
      Nil{}
    case Impl.Round{window, xs, ys, +count} <> rest:
      List.append(&2, Y, List.take(&2, Y, ys, count), stream_y(~X, ~Y, rest))

# Number of committed tokens.
def committed(~X: Data, ~Y: Data, rounds: List<&2, Impl.Round<X, Y>>) -> Nat:
  match rounds:
    case Nil{}:
      0n
    case Impl.Round{window, xs, ys, count} <> rest:
      Nat.add(count, committed(~X, ~Y, rest))
