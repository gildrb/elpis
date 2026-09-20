# Standalone qualification-time program, not a token-path process. The wire
# table is generated from the actual transition function and objective roles.
# IO.print adds the sole final newline. Twenty-four tiny cells stay sequential.
import Base
import ./objectives.bend as Objectives
import ./selection.bend as Selection

def role_code(role: Objectives.Role) -> Nat:
  match role:
    case Objectives.Objective{}:
      0n
    case Objectives.Reported{}:
      1n

def relation_code(state: Objectives.Relation) -> Nat:
  match state:
    case Objectives.NoObjectives{}:
      0n
    case Objectives.Equivalent{}:
      1n
    case Objectives.Dominates{}:
      2n
    case Objectives.Dominated{}:
      3n
    case Objectives.Tradeoff{}:
      4n
    case Objectives.Incomplete{}:
      5n

def roles() -> List<&2, Nat>:
  [role_code(Objectives.role(Objectives.Quality{})),
    role_code(Objectives.role(Objectives.Throughput{})),
    role_code(Objectives.role(Objectives.FirstToken{})),
    role_code(Objectives.role(Objectives.Energy{}))]

def transitions(+state: Objectives.Relation) -> List<&2, Nat>:
  [relation_code(Selection.step(state, Objectives.Better{})),
    relation_code(Selection.step(state, Objectives.Same{})),
    relation_code(Selection.step(state, Objectives.Worse{})),
    relation_code(Selection.step(state, Objectives.Missing{}))]

def table(states: List<&2, Objectives.Relation>) -> List<&2, Nat>:
  match states:
    case Nil{}:
      Nil{}
    case state <> rest:
      List.append(&2, Nat, transitions(state), table(rest))

def rows(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      Nat.show(h) ++ "\n" ++ rows(t)

def protocol() -> String:
  "QWEN_OBJECTIVE_POLICY_V1\nROLES\n" ++ rows(roles()) ++
    "TRANSITIONS\n" ++ rows(table([Objectives.NoObjectives{},
      Objectives.Equivalent{}, Objectives.Dominates{}, Objectives.Dominated{},
      Objectives.Tradeoff{}, Objectives.Incomplete{}])) ++
    "END_QWEN_OBJECTIVE_POLICY"

def main() -> IO(Unit):
  IO.print(protocol())
