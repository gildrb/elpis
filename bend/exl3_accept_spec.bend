# Independent reference for one ExLlamaV3 greedy speculative verify round.
# Transcribes the serial generator loop: at position i (n = i + 1 committed),
# the first matching rule wins: stop token, output budget, final (bonus)
# position, then proposal mismatch or recurrent checkpoint boundary.
# Lists are the reference representation only; the production leaf uses
# fixed scalar registers. Model logits, argmax and physical speed are not
# part of this contract.
import Base

# count committed target tokens (verify_ids[:count]); eos ends the job.
type Verdict is Data:
  Verdict{count: Nat, eos: Bool}

# Per-position rule inputs, in the generator's evaluation order.
type Facts is Data:
  Facts{stop: Bool, exhausted: Bool, final: Bool, reject: Bool}

def member(stops: List<&2, U32>, +token: U32) -> Bool:
  match stops:
    case Nil{}:
      False{}
    case s <> rest:
      Bool.or(U32.is_eq(s, token), member(rest, token))

# The final position is the one without a proposal (i == k). A zero
# checkpoint never equals a committed count, so it denotes no boundary.
def facts(targets: List<&2, U32>, proposals: List<&2, U32>,
    +stops: List<&2, U32>, +committed: Nat, +budget: Nat,
    +checkpoint: Nat) -> List<&2, Facts>:
  match targets:
    case Nil{}:
      Nil{}
    case +t <> rest:
      match proposals:
        case Nil{}:
          [Facts{member(stops, t), Nat.is_ge(1n+committed, budget), True{},
            False{}}]
        case p <> more:
          Facts{member(stops, t), Nat.is_ge(1n+committed, budget), False{},
            Bool.or(U32.is_ne(p, t), Nat.is_eq(1n+committed, checkpoint))} <>
            facts(rest, more, stops, 1n+committed, budget, checkpoint)

def decide(facts: List<&2, Facts>, +committed: Nat) -> Verdict:
  match facts:
    case Nil{}:
      Verdict{committed, False{}}
    case Facts{stop, exhausted, final, reject} <> rest:
      match stop:
        case True{}:
          Verdict{1n+committed, True{}}
        case False{}:
          match exhausted:
            case True{}:
              Verdict{1n+committed, True{}}
            case False{}:
              match final:
                case True{}:
                  Verdict{1n+committed, False{}}
                case False{}:
                  match reject:
                    case True{}:
                      Verdict{1n+committed, False{}}
                    case False{}:
                      decide(rest, 1n+committed)

# targets = verify_ids (k + 1), proposals = draft ids (k), stops = stop ids.
def accept(targets: List<&2, U32>, proposals: List<&2, U32>,
    +stops: List<&2, U32>, +budget: Nat, +checkpoint: Nat) -> Verdict:
  decide(facts(targets, proposals, stops, 0n, budget, checkpoint), 0n)

def count(value: Verdict) -> Nat:
  match value:
    case Verdict{n, eos}:
      n

def eos(value: Verdict) -> Bool:
  match value:
    case Verdict{n, flag}:
      flag

# Boolean equality, used to state which positions report eos.
def same(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# Characterization, independent of facts/decide: every one of the first
# `passed` positions satisfies all continue conditions of the serial loop:
# not a stop token, below the budget, and a non-final position whose
# proposal equals the target and whose count is not the checkpoint.
def passes(passed: Nat, targets: List<&2, U32>, proposals: List<&2, U32>,
    +stops: List<&2, U32>, +committed: Nat, +budget: Nat,
    +checkpoint: Nat) -> Bool:
  match passed:
    case 0n:
      True{}
    case 1n+more_passed:
      match targets:
        case Nil{}:
          False{}
        case +t <> rest:
          match proposals:
            case Nil{}:
              False{}
            case p <> more:
              Bool.and(Bool.not(member(stops, t)),
                Bool.and(Bool.not(Nat.is_ge(1n+committed, budget)),
                  Bool.and(
                    Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))),
                    passes(more_passed, rest, more, stops, 1n+committed,
                      budget, checkpoint))))

# The position after `passed` continuing positions exists and halts with the
# given eos: eos iff stop token or exhausted budget; a halt without eos is the
# final (bonus) position, a mismatching proposal, or the checkpoint boundary.
def halts(passed: Nat, targets: List<&2, U32>, proposals: List<&2, U32>,
    +stops: List<&2, U32>, +committed: Nat, +budget: Nat, +checkpoint: Nat,
    +flag: Bool) -> Bool:
  match passed:
    case 0n:
      match targets:
        case Nil{}:
          False{}
        case +t <> rest:
          match proposals:
            case Nil{}:
              same(flag,
                Bool.or(member(stops, t), Nat.is_ge(1n+committed, budget)))
            case p <> more:
              Bool.and(
                Bool.or(flag,
                  Bool.or(U32.is_ne(p, t), Nat.is_eq(1n+committed, checkpoint))),
                same(flag,
                  Bool.or(member(stops, t), Nat.is_ge(1n+committed, budget))))
    case 1n+more_passed:
      match targets:
        case Nil{}:
          False{}
        case t <> rest:
          match proposals:
            case Nil{}:
              False{}
            case p <> more:
              halts(more_passed, rest, more, stops, 1n+committed, budget,
                checkpoint, flag)

# A verdict is explained when its first count - 1 positions pass and the
# position after them halts with the verdict's eos.
def explains(+count: Nat, flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+passed:
      Bool.and(passes(passed, targets, proposals, stops, 0n, budget, checkpoint),
        halts(passed, targets, proposals, stops, 0n, budget, checkpoint, flag))
