# One-pass, constant-state observed-objective classification. No numeric
# comparisons, evidence admission, weighting, or energy veto lives here.
import Base
import ./objectives.bend as Objectives

def step(state: Objectives.Relation, order: Objectives.Order) -> Objectives.Relation:
  match state:
    case Objectives.NoObjectives{}:
      match order:
        case Objectives.Better{}:
          Objectives.Dominates{}
        case Objectives.Same{}:
          Objectives.Equivalent{}
        case Objectives.Worse{}:
          Objectives.Dominated{}
        case Objectives.Missing{}:
          Objectives.Incomplete{}
    case Objectives.Equivalent{}:
      match order:
        case Objectives.Better{}:
          Objectives.Dominates{}
        case Objectives.Same{}:
          Objectives.Equivalent{}
        case Objectives.Worse{}:
          Objectives.Dominated{}
        case Objectives.Missing{}:
          Objectives.Incomplete{}
    case Objectives.Dominates{}:
      match order:
        case Objectives.Better{}:
          Objectives.Dominates{}
        case Objectives.Same{}:
          Objectives.Dominates{}
        case Objectives.Worse{}:
          Objectives.Tradeoff{}
        case Objectives.Missing{}:
          Objectives.Incomplete{}
    case Objectives.Dominated{}:
      match order:
        case Objectives.Better{}:
          Objectives.Tradeoff{}
        case Objectives.Same{}:
          Objectives.Dominated{}
        case Objectives.Worse{}:
          Objectives.Dominated{}
        case Objectives.Missing{}:
          Objectives.Incomplete{}
    case Objectives.Tradeoff{}:
      match order:
        case Objectives.Better{}:
          Objectives.Tradeoff{}
        case Objectives.Same{}:
          Objectives.Tradeoff{}
        case Objectives.Worse{}:
          Objectives.Tradeoff{}
        case Objectives.Missing{}:
          Objectives.Incomplete{}
    case Objectives.Incomplete{}:
      Objectives.Incomplete{}

# The shrinking list comes first, so tail calls compile to a loop. Unlike the
# specification, this allocates no projected list and makes no repeated scans.
# Energy remains in the caller's evidence; it does not update this relation.
def fold(rows: List<&2, Objectives.Observation>, state: Objectives.Relation) -> Objectives.Relation:
  match rows:
    case Nil{}:
      state
    case Objectives.Observation{family, order} <> rest:
      match family:
        case Objectives.Quality{}:
          fold(rest, step(state, order))
        case Objectives.Throughput{}:
          fold(rest, step(state, order))
        case Objectives.FirstToken{}:
          fold(rest, step(state, order))
        case Objectives.Energy{}:
          fold(rest, state)

def classify(rows: List<&2, Objectives.Observation>) -> Objectives.Relation:
  fold(rows, Objectives.NoObjectives{})
