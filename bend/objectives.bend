# Independent observed-objective specification, not a quality or speed oracle.
# The host must first authenticate complete, comparable, frozen observations.
# Better is oriented toward the declared goal: higher Q/rate, lower TTFT.
# Missing never equals zero. Energy is measured/reported, not an implicit veto.
import Base

type Family is Data:
  Quality{}
  Throughput{}
  FirstToken{}
  Energy{}

type Role is Data:
  Objective{}
  Reported{}

type Order is Data:
  Better{}
  Same{}
  Worse{}
  Missing{}

type Observation is Data:
  Observation{family: Family, order: Order}

type Relation is Data:
  NoObjectives{}
  Equivalent{}
  Dominates{}
  Dominated{}
  Tradeoff{}
  Incomplete{}

def role(family: Family) -> Role:
  match family:
    case Quality{}:
      Objective{}
    case Throughput{}:
      Objective{}
    case FirstToken{}:
      Objective{}
    case Energy{}:
      Reported{}

# Project explicit objective roles before defining the product order. Multiple
# observations of a family remain separate coordinates; none is averaged here.
def primary_role(role: Role, order: Order, rest: List<&2, Order>) -> List<&2, Order>:
  match role:
    case Objective{}:
      order <> rest
    case Reported{}:
      rest

def primary(rows: List<&2, Observation>) -> List<&2, Order>:
  match rows:
    case Nil{}:
      Nil{}
    case Observation{family, order} <> rest:
      primary_role(role(family), order, primary(rest))

def present(xs: List<&2, Order>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      True{}

def known(xs: List<&2, Order>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      match h:
        case Better{}:
          known(t)
        case Same{}:
          known(t)
        case Worse{}:
          known(t)
        case Missing{}:
          False{}

def better(xs: List<&2, Order>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      match h:
        case Better{}:
          True{}
        case Same{}:
          better(t)
        case Worse{}:
          better(t)
        case Missing{}:
          better(t)

def worse(xs: List<&2, Order>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      match h:
        case Better{}:
          worse(t)
        case Same{}:
          worse(t)
        case Worse{}:
          True{}
        case Missing{}:
          worse(t)

# Independent quantified predicates: nonempty and known, weak improvement in
# every objective and strict improvement in at least one. No scalar weighting.
def relation(seen: Bool, available: Bool, gain: Bool, loss: Bool) -> Relation:
  match seen:
    case False{}:
      NoObjectives{}
    case True{}:
      match available:
        case False{}:
          Incomplete{}
        case True{}:
          match gain loss:
            case False{} False{}:
              Equivalent{}
            case True{} False{}:
              Dominates{}
            case False{} True{}:
              Dominated{}
            case True{} True{}:
              Tradeoff{}

def classify_orders(+xs: List<&2, Order>) -> Relation:
  relation(present(xs), known(xs), better(xs), worse(xs))

def classify(rows: List<&2, Observation>) -> Relation:
  classify_orders(primary(rows))

def equivalent_rows(kinds: List<&2, Family>) -> List<&2, Observation>:
  match kinds:
    case Nil{}:
      Nil{}
    case h <> t:
      Observation{h, Same{}} <> equivalent_rows(t)
