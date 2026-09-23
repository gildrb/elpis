# Executed startup, objective, speculation and host mirror-control contracts,
# plus explicit transaction, ownership, ABI and numerical refinement obligations.
# Universal laws keep arbitrary logical identities, counts and declared domains;
# native specialization is exact output, not representative samples.
# Conditional state laws do not establish absent native observations. Compiler,
# Base/foreign IO, CUDA ordering and machine arithmetic retain explicit boundaries.
import Base
import ./bend/range.bend as Range
import ./bend/control.bend as Control
import ./bend/spec.bend as Spec
import ./bend/PLAN.bend as Wire
import ./bend/selection_laws.bend as SelectionLaws
import ./bend/speculation_laws.bend as SpeculationLaws
import ./bend/speculation.bend as Speculation
import ./bend/speculation_spec.bend as SpeculationSpec
import ./bend/SPECULATE.bend as SpeculationWire
import ./bend/transaction_laws.bend as TransactionLaws
import ./bend/ownership_laws.bend as OwnershipLaws
import ./bend/abi_laws.bend as AbiLaws
import ./bend/numerical_laws.bend as NumericalLaws
import ./bend/selector_laws.bend as SelectorLaws
import ./bend/query_tiles_laws.bend as QueryTilesLaws

# Balanced parallel decomposition preserves the independent ascending loop.
law tree_is_seq:
  for d: Nat
  for +start: Nat
  {Range.tree(d, start) == Spec.seq(Range.width(d), start) : List<&2, Nat>}

# Stronger structural contract: exact length and each successive expected ID.
law tree_exact:
  for +d: Nat
  for +start: Nat
  Spec.Ordered(Range.width(d), start, Range.tree(d, start))

# All dimensions: eight consecutive segments, no padding, overlap or omission.
# The reference scan is independent of the optimized named-offset calculation.
law layout_contiguous:
  for +dim: Nat
  {Control.offsets(dim) == Spec.offsets(dim) : List<&2, Nat>}

# Exhaustive over the two actual supported shapes, not representative samples.
# The final boundary equals the entire one-head tile; every boundary is in it.
law layout_shapes:
  for +shape: Control.Shape
  {Control.dimension(shape) == Spec.dimension(shape) : Nat} &
  {Spec.bounded(Control.offsets(Control.dimension(shape)), Spec.tile_bytes(shape)) == True{} : Bool} &
  {List.last(&2, Nat, Control.offsets(Control.dimension(shape))) == Some{Spec.tile_bytes(shape)} : Maybe<&2, Nat>}

# All 42 emitted fields, including geometry, visibility and query-tile partition.
law native_fields:
  {Control.fields() == Spec.fields() : List<&2, Nat>}

# No page zero, gap, duplicate, reorder, omitted page, or extra page is allowed.
law native_pages:
  {Range.native() == Spec.seq(2056n, 1n) : List<&2, Nat>}

law native_ordered:
  Spec.Ordered(2056n, 1n, Range.native())

# Reserved zero lies outside the allocatable sequence. All physical token IDs
# fit [0,263296), with last ID 263295, not pool-1. Reserving one dummy from the
# 2056 free pages leaves 263040 tokens: full native context plus 896 headroom.
law native_resources:
  {[Control.context(), Control.headroom(), Control.pool(), Control.page_size(), Control.pages(),
    Nat.mul(Nat.sub(Control.pages(), 1n), Control.page_size()),
    Nat.mul(Control.pages(), Control.page_size()),
    Nat.add(Nat.mul(Nat.sub(Control.pages(), 1n), Control.page_size()), Nat.sub(Control.page_size(), 1n)),
    Nat.sub(Control.pool(), Control.page_size()),
    Nat.sub(Nat.sub(Control.pool(), Control.page_size()), Control.context()),
    Control.write_span(), Control.admission_slots()]
   == [262144n, 1024n, 263168n, 128n, 2057n, 263168n, 263296n, 263295n, 263040n, 896n, 2n, 4n]
   : List<&2, Nat>}

# Every request, successful or rejected, must agree with the separate spec.
# A planner which always rejects or always returns an empty plan cannot satisfy
# this law, the progress law, or the exact serialized-output law below.
law plan_semantics:
  for context: Nat
  for pool: Nat
  for page_size: Nat
  {Control.plan(context, pool, page_size) == Spec.plan(context, pool, page_size) : Maybe<&2, Control.Plan>}

law valid_progress:
  for +context: Nat
  for +pool: Nat
  for +page_size: Nat
  for hc: {context == 262144n : Nat}
  for hp: {pool == 263168n : Nat}
  for hs: {page_size == 128n : Nat}
  {Control.plan(context, pool, page_size) == Some{Spec.native()} : Maybe<&2, Control.Plan>}

law invalid_rejected:
  for +context: Nat
  for +pool: Nat
  for +page_size: Nat
  for invalid: {Control.valid(context, pool, page_size) == False{} : Bool}
  {Control.plan(context, pool, page_size) == None{} : Maybe<&2, Control.Plan>}

# Real pure serialization is included: correct unused allocation code is not
# enough. IO.print is the explicit trusted final output boundary.
law rows_semantics:
  for xs: List<&2, Nat>
  {Wire.rows(xs) == Spec.rows(xs) : String}

law native_wire:
  {Wire.protocol() == Spec.protocol() : String}

# Every finite comparison sequence stops at its first mismatch. Committed
# inputs include the anchor; the emitted target bonus is not another input.
law greedy_acceptance:
  for flags: List<&2, Bool>
  {Speculation.decide(flags) == SpeculationSpec.decide(flags) : SpeculationSpec.Decision}

# All 128 masks, four decision columns, row order and serialization are bound
# to the actual parallel program whose output the GPU consumer will load.
law greedy_speculation_wire:
  {SpeculationWire.protocol() == SpeculationSpec.protocol() : String}
