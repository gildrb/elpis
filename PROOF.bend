# Proof-only entry point: no main, no foreign proof code and no axioms.
# Induction follows Bend2's pure_par_sum and proof_numerics demos.
import Base
import ./LAWS.bend as Laws
import ./bend/range.bend as Range
import ./bend/control.bend as Control
import ./bend/spec.bend as Spec
import ./bend/PLAN.bend as Wire
import ./bend/selection_proof.bend as SelectionProof
import ./bend/speculation_proof.bend as SpeculationProof

def add_succ(n: Nat, -i: Nat) -> {Nat.add(n, 1n+i) == 1n+Nat.add(n, i) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, i) : {1n+Nat.add(p, 1n+i) == 1n+_ : Nat}
      {==}

# The independent forward loop splits at an arbitrary n, not just powers of 2.
def seq_split(n: Nat, +m: Nat, +i: Nat)
  -> {List.append(&2, Nat, Spec.seq(n, i), Spec.seq(m, Nat.add(n, i))) == Spec.seq(Nat.add(n, m), i) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %add_succ(p, i) : {i <> List.append(&2, Nat, Spec.seq(p, 1n+i), Spec.seq(m, _)) == i <> Spec.seq(Nat.add(p, m), 1n+i) : List<&2, Nat>}
      %seq_split(p, m, 1n+i) : {i <> List.append(&2, Nat, Spec.seq(p, 1n+i), Spec.seq(m, Nat.add(p, 1n+i))) == i <> _ : List<&2, Nat>}
      {==}

def Laws.tree_is_seq(d, start):
  match d:
    case 0n:
      {==}
    case 1n++p:
      %seq_split(Range.width(p), Range.width(p), start) : {List.append(&2, Nat, Range.tree(p, start), Range.tree(p, Nat.add(Range.width(p), start))) == _ : List<&2, Nat>}
      %Laws.tree_is_seq(p, start) : {List.append(&2, Nat, Range.tree(p, start), Range.tree(p, Nat.add(Range.width(p), start))) == List.append(&2, Nat, _, Spec.seq(Range.width(p), Nat.add(Range.width(p), start))) : List<&2, Nat>}
      %Laws.tree_is_seq(p, Nat.add(Range.width(p), start)) : {List.append(&2, Nat, Range.tree(p, start), Range.tree(p, Nat.add(Range.width(p), start))) == List.append(&2, Nat, Range.tree(p, start), _) : List<&2, Nat>}
      {==}

def seq_ordered(n: Nat, +start: Nat) -> Spec.Ordered(n, start, Spec.seq(n, start)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      ({==}, seq_ordered(p, 1n+start))

def Laws.tree_exact(d, start):
  %Equal.sym(List<&2, Nat>, Range.tree(d, start), Spec.seq(Range.width(d), start), Laws.tree_is_seq(d, start)) : Spec.Ordered(Range.width(d), start, _)
  seq_ordered(Range.width(d), start)

# Combine tree proofs before specializing depths. The equality constructor
# never has to compare two concrete 2056-element lists.
def trees_split(+left: Nat, +right: Nat, +start: Nat)
  -> {List.append(&2, Nat, Range.tree(left, start),
      Range.tree(right, Nat.add(Range.width(left), start))) ==
    Spec.seq(Nat.add(Range.width(left), Range.width(right)), start) : List<&2, Nat>}:
  %seq_split(Range.width(left), Range.width(right), start) :
    {List.append(&2, Nat, Range.tree(left, start),
      Range.tree(right, Nat.add(Range.width(left), start))) == _ : List<&2, Nat>}
  %Laws.tree_is_seq(left, start) :
    {List.append(&2, Nat, Range.tree(left, start),
      Range.tree(right, Nat.add(Range.width(left), start))) ==
      List.append(&2, Nat, _, Spec.seq(Range.width(right), Nat.add(Range.width(left), start))) : List<&2, Nat>}
  %Laws.tree_is_seq(right, Nat.add(Range.width(left), start)) :
    {List.append(&2, Nat, Range.tree(left, start),
      Range.tree(right, Nat.add(Range.width(left), start))) ==
      List.append(&2, Nat, Range.tree(left, start), _) : List<&2, Nat>}
  {==}

def ordered_transport(+n: Nat, +start: Nat, +xs: List<&2, Nat>,
    equal: {xs == Spec.seq(n, start) : List<&2, Nat>})
  -> Spec.Ordered(n, start, xs):
  %Equal.sym(List<&2, Nat>, xs, Spec.seq(n, start), equal) :
    Spec.Ordered(n, start, _)
  seq_ordered(n, start)

def plan_equal(-fields: List<&2, Nat>, -expected_fields: List<&2, Nat>,
    -pages: List<&2, Nat>, -expected_pages: List<&2, Nat>,
    fields_equal: {fields == expected_fields : List<&2, Nat>},
    pages_equal: {pages == expected_pages : List<&2, Nat>})
  -> {Control.Plan{fields, pages} == Control.Plan{expected_fields, expected_pages} : Control.Plan}:
  %fields_equal :
    {Control.Plan{fields, pages} == Control.Plan{_, expected_pages} : Control.Plan}
  %pages_equal :
    {Control.Plan{fields, pages} == Control.Plan{fields, _} : Control.Plan}
  {==}

# Generic scan unfolds across eight segments; no induction on dimension and
# no specialization to the two numerical examples is used in this theorem.
def Laws.layout_contiguous(dim):
  {==}

# Shape has precisely two constructors. This is exhaustive case analysis of
# every supported shape, separately from the universal layout correspondence.
def Laws.layout_shapes(shape):
  match shape:
    case Control.Target{}:
      ({==}, {==}, {==})
    case Control.Draft{}:
      ({==}, {==}, {==})

def Laws.native_fields():
  {==}

def Laws.native_pages():
  trees_split(11n, 3n, 1n)

def Laws.native_ordered():
  ordered_transport(2056n, 1n, Range.native(), Laws.native_pages())

def Laws.native_resources():
  {==}

def choose_semantics(valid: Bool) -> {Control.choose(valid) == Spec.choose(valid) : Maybe<&2, Control.Plan>}:
  match valid:
    case True{}:
      Equal.cong(Control.Plan, Maybe<&2, Control.Plan>,
        value => Some{value}, Control.native(), Spec.native(),
        plan_equal(Control.fields(), Spec.fields(), Range.native(),
          Spec.seq(2056n, 1n), Laws.native_fields(), Laws.native_pages()))
    case False{}:
      {==}

def Laws.plan_semantics(context, pool, page_size):
  choose_semantics(Control.valid(context, pool, page_size))

def Laws.valid_progress(context, pool, page_size, hc, hp, hs):
  %Equal.sym(Nat, context, 262144n, hc) : {Control.plan(_, pool, page_size) == Some{Spec.native()} : Maybe<&2, Control.Plan>}
  %Equal.sym(Nat, pool, 263168n, hp) : {Control.plan(262144n, _, page_size) == Some{Spec.native()} : Maybe<&2, Control.Plan>}
  %Equal.sym(Nat, page_size, 128n, hs) : {Control.plan(262144n, 263168n, _) == Some{Spec.native()} : Maybe<&2, Control.Plan>}
  Laws.plan_semantics(262144n, 263168n, 128n)

def Laws.invalid_rejected(context, pool, page_size, invalid):
  %Equal.sym(Bool, Control.valid(context, pool, page_size), False{}, invalid) : {Control.choose(_) == None{} : Maybe<&2, Control.Plan>}
  {==}

def Laws.rows_semantics(xs):
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %Laws.rows_semantics(t) : {Nat.show(h) ++ "\n" ++ Wire.rows(t) == Nat.show(h) ++ "\n" ++ _ : String}
      {==}

# Serialization is proved with abstract lists, so Nat.show never runs over
# the native fields or thousands of pages just to establish congruence.
def render_reference(+fields: List<&2, Nat>, +pages: List<&2, Nat>)
  -> {Wire.render(Control.Plan{fields, pages}) ==
    "QWEN_KVARN_PLAN_V2\n" ++ Spec.rows(fields) ++ "FREE_PAGES\n" ++
      Spec.rows(pages) ++ "END_QWEN_KVARN_PLAN" : String}:
  %Laws.rows_semantics(fields) :
    {Wire.render(Control.Plan{fields, pages}) ==
      "QWEN_KVARN_PLAN_V2\n" ++ _ ++ "FREE_PAGES\n" ++
        Spec.rows(pages) ++ "END_QWEN_KVARN_PLAN" : String}
  %Laws.rows_semantics(pages) :
    {Wire.render(Control.Plan{fields, pages}) ==
      "QWEN_KVARN_PLAN_V2\n" ++ Wire.rows(fields) ++ "FREE_PAGES\n" ++
        _ ++ "END_QWEN_KVARN_PLAN" : String}
  {==}

def accepted_reference(-actual: Maybe<&2, Control.Plan>,
    +fields: List<&2, Nat>, +pages: List<&2, Nat>,
    equal: {actual == Some{Control.Plan{fields, pages}} : Maybe<&2, Control.Plan>})
  -> {Wire.accepted(actual) ==
    "QWEN_KVARN_PLAN_V2\n" ++ Spec.rows(fields) ++ "FREE_PAGES\n" ++
      Spec.rows(pages) ++ "END_QWEN_KVARN_PLAN" : String}:
  Equal.trans(String, Wire.accepted(actual),
    Wire.render(Control.Plan{fields, pages}),
    "QWEN_KVARN_PLAN_V2\n" ++ Spec.rows(fields) ++ "FREE_PAGES\n" ++
      Spec.rows(pages) ++ "END_QWEN_KVARN_PLAN",
    Equal.cong(Maybe<&2, Control.Plan>, String, Wire.accepted,
      actual, Some{Control.Plan{fields, pages}}, equal),
    render_reference(fields, pages))

def Laws.native_wire():
  accepted_reference(Control.plan(262144n, 263168n, 128n),
    Spec.fields(), Spec.seq(2056n, 1n),
    Laws.valid_progress(262144n, 263168n, 128n, {==}, {==}, {==}))
