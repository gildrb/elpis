# Pure observed-order laws, not claims about GPU arithmetic, empirical
# accuracy, evidence legitimacy, numerical order construction or optimality.
# All list laws quantify arbitrary finite lists; no sample bound is present.
import Base
import ./objectives.bend as Objectives
import ./selection.bend as Selection
import ./SELECT.bend as Wire

law classify_semantics:
  for +rows: List<&2, Objectives.Observation>
  {Selection.classify(rows) == Objectives.classify(rows) : Objectives.Relation}

# Insertion at every position, for every energy order including Missing.
# This removes energy only from the decision, never from the host's record.
law report_only_invariance:
  for +prefix: List<&2, Objectives.Observation>
  for order: Objectives.Order
  for +suffix: List<&2, Objectives.Observation>
  {Selection.classify(List.append(&2, Objectives.Observation, prefix,
    Objectives.Observation{Objectives.Energy{}, order} <> suffix)) ==
   Selection.classify(List.append(&2, Objectives.Observation, prefix, suffix)) : Objectives.Relation}

# A quality gain is sufficient even with arbitrarily many otherwise-equivalent
# families, including repeated quality/speed coordinates and reported energy.
law quality_only_improvement:
  for kinds: List<&2, Objectives.Family>
  {Selection.classify(Objectives.Observation{Objectives.Quality{}, Objectives.Better{}} <>
    Objectives.equivalent_rows(kinds)) == Objectives.Dominates{} : Objectives.Relation}

# Both speed coordinates are explicitly present and unchanged, not omitted.
# Arbitrary reported energy cannot turn the quality gain into a veto.
law no_speed_improvement_required:
  for kinds: List<&2, Objectives.Family>
  for energy: Objectives.Order
  {Selection.classify(Objectives.Observation{Objectives.Quality{}, Objectives.Better{}} <>
    Objectives.Observation{Objectives.Throughput{}, Objectives.Same{}} <>
    Objectives.Observation{Objectives.FirstToken{}, Objectives.Same{}} <>
    Objectives.Observation{Objectives.Energy{}, energy} <>
    Objectives.equivalent_rows(kinds)) == Objectives.Dominates{} : Objectives.Relation}

# These premises use the independent predicates, not the implementation's
# answer. Any missing primary, anywhere, fails closed despite other gains.
law missing_primary_rejected:
  for +rows: List<&2, Objectives.Observation>
  for missing: {Objectives.known(Objectives.primary(rows)) == False{} : Bool}
  {Selection.classify(rows) == Objectives.Incomplete{} : Objectives.Relation}

# Complete evidence with both a gain and a loss is incomparable, not a weighted
# win. Presence follows from the gain; an empty projection cannot meet it.
law mixed_gain_loss_incomparable:
  for +rows: List<&2, Objectives.Observation>
  for known: {Objectives.known(Objectives.primary(rows)) == True{} : Bool}
  for gain: {Objectives.better(Objectives.primary(rows)) == True{} : Bool}
  for loss: {Objectives.worse(Objectives.primary(rows)) == True{} : Bool}
  {Selection.classify(rows) == Objectives.Tradeoff{} : Objectives.Relation}

# Independently fixed wire literal, not generated from the implementation or
# the specification. The final newline is the trusted IO.print boundary.
def expected_wire() -> String:
  "QWEN_OBJECTIVE_POLICY_V1\nROLES\n0\n0\n0\n1\nTRANSITIONS\n2\n1\n3\n5\n2\n1\n3\n5\n2\n2\n4\n5\n4\n3\n3\n5\n4\n4\n4\n5\n5\n5\n5\n5\nEND_QWEN_OBJECTIVE_POLICY"

law policy_wire:
  {Wire.protocol() == expected_wire() : String}
