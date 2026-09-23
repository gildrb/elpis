# The shipped policy/wire and exact mathematical ring/ordered-trace contracts.
# No CUDA async, memory, instruction, floating-point or speed theorem is claimed.
import Base
import ./marlin_pipeline.bend as Impl
import ./marlin_pipeline_spec.bend as Spec
import ./spec.bend as Sequence
import ./RUNTIME.bend as Wire

law policy_refinement:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  {Impl.policy(eligible, safe, deterministic) == Spec.policy(eligible, safe, deterministic) : Nat}

law action_range:
  for eligible: Bool
  for safe: Bool
  for deterministic: Bool
  Spec.Action(Impl.policy(eligible, safe, deterministic))

law ineligible_fallback:
  for safe: Bool
  for deterministic: Bool
  {Impl.policy(False{}, safe, deterministic) == 0n : Nat}

law unsafe_fallback:
  for eligible: Bool
  for deterministic: Bool
  {Impl.policy(eligible, False{}, deterministic) == 0n : Nat}

law atomic_fallback:
  for eligible: Bool
  for safe: Bool
  {Impl.policy(eligible, safe, False{}) == 0n : Nat}

law eight_stage_progress:
  {Impl.policy(True{}, True{}, True{}) == 1n : Nat}

# Exact positions, not an unordered multiset or only the successful row.
law table_order:
  {Impl.table(3n, False{}, False{}, False{}) ==
    [Spec.row(0n), Spec.row(1n), Spec.row(2n), Spec.row(3n),
      Spec.row(4n), Spec.row(5n), Spec.row(6n), Spec.row(7n)] : List<&2, Nat>}

law table_lookup:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  {Spec.row(Nat.add(Bool.pick(Nat, eligible, 1n, 0n),
    Nat.add(Nat.mul(2n, Bool.pick(Nat, safe, 1n, 0n)),
      Nat.mul(4n, Bool.pick(Nat, deterministic, 1n, 0n))))) ==
    Impl.policy(eligible, safe, deterministic) : Nat}

law wire_exact:
  {Wire.protocol() == Spec.protocol() : String}

# Native correspondence obligations, NOT premises silently supplied as axioms:
# - The original input is M1..8, fullK, no act-order/no zero-points; actual SM86,
#   BF16/U4B8/group128; the already validated choice is 128 threads, M8/N128/K64.
# - safe observes K%128=0, group_blocks=8, blocks_per_sm=1 and the EXISTING
#   max_shared_mem_new>=51200 reservation. deterministic observes !use_atomic_add.
#   The compiled Bend action alone selects stages=8 instead of retained stages=4.
# - Both paths retain grid, K stripes, slice/reduction grouping, scratch, launch
#   reservation and arguments. Integer conversions/address arithmetic must be
#   in range and refine the Nat indices. Each ring starts on an even group phase.
# - Native fetch/write/read scale addresses must refine slot and phase; A/B/
#   scales must be the same operands. cp.async commit/wait, CTA barriers, ring
#   reuse, predication, final drain and memory safety require separate evidence.
#   Exact source primes seven groups, then wait_group<6> with a CTA barrier;
#   each subsequent fetch commits once, including predicated-off tail fetches.
#   Pending-group bound seven relies on actual per-thread CUDA wait semantics
#   and an eight-group limit, NOT on the phase/trace equalities proved here.
#   The final wait_group<0>, two-register-slot buffering and b_sh_wr_iters=2
#   remain unchanged; the last current-tile MMA consumes its loaded register.
# - Each logical tile executes the same matmul(0),matmul(1), inner MMA order and
#   previous-F32-accumulator recurrence, with identical instruction/rounding
#   semantics; intra/inter-CTA non-atomic reduction order and conversions remain
#   unchanged. recurrence below is a symbolic trace, NOT CUDA instruction truth.
# Compiler/foreign IO/native observation fidelity are external. Exact GPU parity
# of all 624 fixtures (no tolerance) is an acceptance gate, not a model theorem.

# Arbitrarily many wraps: physical phase equals logical phase for either ring.
# This is specific to group period two; no odd-stage claim is made.
law ring8_group_phase:
  for +tile: Nat
  {Spec.phase(Spec.slot(tile, 8n)) == Spec.phase(tile) : Nat}

law ring4_group_phase:
  for +tile: Nat
  {Spec.phase(Spec.slot(tile, 4n)) == Spec.phase(tile) : Nat}

# Every group has its scale-writing even tile followed by its odd tile.
law group_pair_phase:
  for +group: Nat
  {Spec.phase(Nat.double(group)) == 0n : Nat} &
  {Spec.phase(1n+Nat.double(group)) == 1n : Nat}

# Arbitrary finite tile count/start, including zero and partial last chunks.
# Equality plus Ordered forbids omissions, duplicates, reordering and padding.
law tiles8_exact:
  for +count: Nat
  for +start: Nat
  {Spec.tiles8(count, start) == Sequence.seq(count, start) : List<&2, Nat>}

law tiles4_exact:
  for +count: Nat
  for +start: Nat
  {Spec.tiles4(count, start) == Sequence.seq(count, start) : List<&2, Nat>}

law tiles_ordered:
  for +count: Nat
  for +start: Nat
  Sequence.Ordered(count, start, Spec.tiles8(count, start)) &
  Sequence.Ordered(count, start, Spec.tiles4(count, start))

law mma8_exact:
  for +count: Nat
  for +start: Nat
  {Spec.mma_terms(Spec.tiles8(count, start)) ==
    Sequence.seq(Nat.double(count), Nat.double(start)) : List<&2, Nat>}

law mma4_exact:
  for +count: Nat
  for +start: Nat
  {Spec.mma_terms(Spec.tiles4(count, start)) ==
    Sequence.seq(Nat.double(count), Nat.double(start)) : List<&2, Nat>}

law mma_ordered:
  for +count: Nat
  for +start: Nat
  Sequence.Ordered(Nat.double(count), Nat.double(start), Spec.mma_terms(Spec.tiles8(count, start))) &
  Sequence.Ordered(Nat.double(count), Nat.double(start), Spec.mma_terms(Spec.tiles4(count, start)))

law unroll_invariant:
  for +count: Nat
  for +start: Nat
  {Spec.tiles8(count, start) == Spec.tiles4(count, start) : List<&2, Nat>} &
  {Spec.mma_terms(Spec.tiles8(count, start)) == Spec.mma_terms(Spec.tiles4(count, start)) : List<&2, Nat>}

# No associative/commutative law is assumed for the accumulator. The exact
# nested previous-accumulator expression is equal, not merely its term multiset.
law recurrence_invariant:
  for +count: Nat
  for +start: Nat
  for +accumulator: Spec.Accumulator
  {Spec.recurrence(Spec.mma_terms(Spec.tiles8(count, start)), accumulator) ==
    Spec.recurrence(Spec.mma_terms(Spec.tiles4(count, start)), accumulator) : Spec.Accumulator}

# Source-derived layout arithmetic only; actual pointers must refine it.
law selected_shared_layout:
  {[Spec.shared_bytes(8n, 8n), Spec.shared_bytes(8n, 16n),
    Spec.shared_bytes(4n, 8n), Spec.shared_bytes(4n, 16n)] ==
    [43008n, 51200n, 21504n, 25600n] : List<&2, Nat>}

# The explicit native guard uses the conservative padded-M16 stage-eight bound.
# This does not prove an occupancy change or alter the existing launch reserve.
law conservative_shared_bound:
  {Nat.is_le(Spec.shared_bytes(8n, 8n), Spec.shared_bytes(8n, 16n)) == True{} : Bool} &
  {Nat.add(Spec.shared_bytes(8n, 8n), 8192n) == Spec.shared_bytes(8n, 16n) : Nat}

# Only arithmetic identities for the native schedule parameters are asserted.
law schedule_parameters:
  {[Spec.prime_groups(8n), Spec.wait_groups(8n),
    Spec.prime_groups(4n), Spec.wait_groups(4n)] == [7n, 6n, 3n, 2n] : List<&2, Nat>}

law pending_group_arithmetic:
  {1n+Spec.wait_groups(8n) == Spec.prime_groups(8n) : Nat} &
  {Nat.is_lt(Spec.prime_groups(8n), 8n) == True{} : Bool}
