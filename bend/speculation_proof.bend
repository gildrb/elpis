# Live structural evidence for the accumulator and the complete finite wire.
# No unsafe definitions, axioms, foreign proof code, or answer-table literals.
import Base
import ../LAWS.bend as Laws
import ./speculation.bend as Speculation
import ./speculation_spec.bend as Spec
import ./SPECULATE.bend as Wire
import ./range.bend as Range

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(n: Nat, -m: Nat)
  -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

# Project the reference's accepted count without depending on its private
# recursion helpers. Only the shared decision ABI is used by this proof.
def accepted(value: Spec.Decision) -> Nat:
  match value:
    case Spec.Decision{count, committed, bonus, advance}:
      count

# The accumulator is an arbitrary prior accepted prefix, not a block8 bound.
# Induction follows every finite comparison list, including tails after false.
def scan_reference(+flags: List<&2, Bool>, +acc: Nat)
  -> {Speculation.scan(flags, acc) ==
    Nat.add(accepted(Spec.decide(flags)), acc) : Nat}:
  match flags:
    case Nil{}:
      {==}
    case False{} <> rest:
      {==}
    case True{} <> rest:
      %add_succ(accepted(Spec.decide(rest)), acc) :
        {Speculation.scan(rest, 1n+acc) == _ : Nat}
      scan_reference(rest, 1n+acc)

def scan_zero(+flags: List<&2, Bool>)
  -> {Speculation.scan(flags, 0n) == accepted(Spec.decide(flags)) : Nat}:
  %add_zero(accepted(Spec.decide(flags))) :
    {Speculation.scan(flags, 0n) == _ : Nat}
  scan_reference(flags, 0n)

def Laws.greedy_acceptance(flags):
  %scan_zero(flags) :
    {Speculation.decision(Speculation.scan(flags, 0n)) ==
      Speculation.decision(_) : Spec.Decision}
  {==}

# Congruence is checked with abstract lists, not normalized output tables.
def append_equal(-left: List<&2, Spec.Decision>,
    -expected_left: List<&2, Spec.Decision>,
    -right: List<&2, Spec.Decision>,
    -expected_right: List<&2, Spec.Decision>,
    left_equal: {left == expected_left : List<&2, Spec.Decision>},
    right_equal: {right == expected_right : List<&2, Spec.Decision>})
  -> {List.append(&2, Spec.Decision, left, right) ==
    List.append(&2, Spec.Decision, expected_left, expected_right) : List<&2, Spec.Decision>}:
  %left_equal :
    {List.append(&2, Spec.Decision, left, right) ==
      List.append(&2, Spec.Decision, _, expected_right) : List<&2, Spec.Decision>}
  %right_equal :
    {List.append(&2, Spec.Decision, left, right) ==
      List.append(&2, Spec.Decision, left, _) : List<&2, Spec.Decision>}
  {==}

# This intermediate tree uses the independent decision semantics. It is not
# the wire specification: arithmetic decoding and ascending enumeration are
# related to this tree separately below.
def reference_table(+depth: Nat, +suffix: List<&2, Bool>) -> List<&2, Spec.Decision>:
  match depth:
    case 0n:
      [Spec.decide(suffix)]
    case 1n+p:
      List.append(&2, Spec.Decision,
        reference_table(p, False{} <> suffix), reference_table(p, True{} <> suffix))

def table_reference(+depth: Nat, +suffix: List<&2, Bool>)
  -> {Speculation.table(depth, suffix) == reference_table(depth, suffix) : List<&2, Spec.Decision>}:
  match depth:
    case 0n:
      Equal.cong(Spec.Decision, List<&2, Spec.Decision>, value => [value],
        Speculation.decide(suffix), Spec.decide(suffix), Laws.greedy_acceptance(suffix))
    case 1n+p:
      append_equal(Speculation.table(p, False{} <> suffix),
        reference_table(p, False{} <> suffix),
        Speculation.table(p, True{} <> suffix), reference_table(p, True{} <> suffix),
        table_reference(p, False{} <> suffix), table_reference(p, True{} <> suffix))

# The independent wire's loop, with rendering delayed until after the proof.
def reference_decisions(count: Nat, +index: Nat) -> List<&2, Spec.Decision>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      Spec.decide(Spec.flags(7n, index)) <> reference_decisions(p, 1n+index)

def decisions_split(+count: Nat, +tail_count: Nat, +index: Nat)
  -> {List.append(&2, Spec.Decision, reference_decisions(count, index),
      reference_decisions(tail_count, Nat.add(count, index))) ==
    reference_decisions(Nat.add(count, tail_count), index) : List<&2, Spec.Decision>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, index) :
        {Spec.decide(Spec.flags(7n, index)) <>
          List.append(&2, Spec.Decision, reference_decisions(p, 1n+index),
            reference_decisions(tail_count, _)) ==
          Spec.decide(Spec.flags(7n, index)) <>
            reference_decisions(Nat.add(p, tail_count), 1n+index) : List<&2, Spec.Decision>}
      %decisions_split(p, tail_count, 1n+index) :
        {Spec.decide(Spec.flags(7n, index)) <>
          List.append(&2, Spec.Decision, reference_decisions(p, 1n+index),
            reference_decisions(tail_count, Nat.add(p, 1n+index))) ==
          Spec.decide(Spec.flags(7n, index)) <> _ : List<&2, Spec.Decision>}
      {==}

# A branch requires evidence for BOTH ordered halves; no row can be omitted.
def decode_branch(+depth: Nat, +suffix: List<&2, Bool>, +index: Nat,
    left: {reference_table(depth, False{} <> suffix) ==
      reference_decisions(Range.width(depth), index) : List<&2, Spec.Decision>},
    right: {reference_table(depth, True{} <> suffix) ==
      reference_decisions(Range.width(depth), Nat.add(Range.width(depth), index)) : List<&2, Spec.Decision>})
  -> {reference_table(1n+depth, suffix) ==
    reference_decisions(Range.width(1n+depth), index) : List<&2, Spec.Decision>}:
  Equal.trans(List<&2, Spec.Decision>, reference_table(1n+depth, suffix),
    List.append(&2, Spec.Decision, reference_decisions(Range.width(depth), index),
      reference_decisions(Range.width(depth), Nat.add(Range.width(depth), index))),
    reference_decisions(Range.width(1n+depth), index),
    append_equal(reference_table(depth, False{} <> suffix),
      reference_decisions(Range.width(depth), index),
      reference_table(depth, True{} <> suffix),
      reference_decisions(Range.width(depth), Nat.add(Range.width(depth), index)),
      left, right),
    decisions_split(Range.width(depth), Range.width(depth), index))

# Only the finite ABI's bit-decoding boundary needs closed computation.
# Eight 16-row leaves compare algorithms, never answer-table literals. The
# branch theorem composes all 128 rows without normalizing the full table.
# This finite protocol check does not bound greedy_acceptance/table_reference.
def decode_table()
  -> {reference_table(7n, Nil{}) == reference_decisions(128n, 0n) : List<&2, Spec.Decision>}:
  decode_branch(6n, Nil{}, 0n,
    decode_branch(5n, [False{}], 0n,
      decode_branch(4n, [False{}, False{}], 0n, {==}, {==}),
      decode_branch(4n, [True{}, False{}], 32n, {==}, {==})),
    decode_branch(5n, [True{}], 64n,
      decode_branch(4n, [False{}, True{}], 64n, {==}, {==}),
      decode_branch(4n, [True{}, True{}], 96n, {==}, {==})))

def row_reference(value: Spec.Decision)
  -> {Wire.row(value) == Spec.render(value) : String}:
  match value:
    case Spec.Decision{count, committed, bonus, advance}:
      {==}

def rows_reference(count: Nat, +index: Nat)
  -> {Wire.rows(reference_decisions(count, index)) == Spec.rows(count, index) : String}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %row_reference(Spec.decide(Spec.flags(7n, index))) :
        {Wire.row(Spec.decide(Spec.flags(7n, index))) ++
          Wire.rows(reference_decisions(p, 1n+index)) ==
          _ ++ Spec.rows(p, 1n+index) : String}
      %rows_reference(p, 1n+index) :
        {Wire.row(Spec.decide(Spec.flags(7n, index))) ++
          Wire.rows(reference_decisions(p, 1n+index)) ==
          Wire.row(Spec.decide(Spec.flags(7n, index))) ++ _ : String}
      {==}

def wire_rows(-actual: List<&2, Spec.Decision>, +count: Nat, +index: Nat,
    equal: {actual == reference_decisions(count, index) : List<&2, Spec.Decision>})
  -> {Wire.rows(actual) == Spec.rows(count, index) : String}:
  Equal.trans(String, Wire.rows(actual), Wire.rows(reference_decisions(count, index)),
    Spec.rows(count, index),
    Equal.cong(List<&2, Spec.Decision>, String, Wire.rows,
      actual, reference_decisions(count, index), equal),
    rows_reference(count, index))

def protocol_rows(-actual: String, -expected: String,
    equal: {actual == expected : String})
  -> {"QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n" ++ actual ++ "END_QWEN_DFLASH_GREEDY" ==
    "QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n" ++ expected ++ "END_QWEN_DFLASH_GREEDY" : String}:
  Equal.cong(String, String,
    rows => "QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n" ++ rows ++ "END_QWEN_DFLASH_GREEDY",
    actual, expected, equal)

# Full header, every decision field in order, and trailer remain in the law.
def Laws.greedy_speculation_wire():
  protocol_rows(Wire.rows(Speculation.decisions()), Spec.rows(128n, 0n),
    wire_rows(Speculation.decisions(), 128n, 0n,
      Equal.trans(List<&2, Spec.Decision>, Speculation.decisions(),
        reference_table(7n, Nil{}), reference_decisions(128n, 0n),
        table_reference(7n, Nil{}), decode_table())))
