# The shipped policy/wire and exact mathematical ring/ordered-trace contracts.
# No CUDA async, memory, instruction, floating-point or speed theorem is claimed.
import Base
import ./marlin_pipeline.bend as Impl
import ./marlin_pipeline_spec.bend as Spec
import ./spec.bend as Sequence
import ./RUNTIME.bend as Wire
import ./numerical_spec.bend as Order

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
#   original max_shared_mem_new>=51200 capacity. deterministic observes !use_atomic_add.
#   The compiled Bend action alone selects stages=8 instead of retained stages=4;
#   only its successful selected launch consumes Impl.selected_shared_bytes().
# - M normalization is skipped only by that action1 launch with mask85; generic
#   callers retain default mask255. The table bit order is eligible,safe,
#   deterministic (bits0,1,2); its packed policy is128. Static M8 geometry alone
#   does NOT establish logical M. Original M1..8 is captured before act-order
#   normalization, and larger-M tail splits may not enter this selected class.
#   The unchanged host starts rest_m=M and retries divisors64,48,32,16 without
#   changing rest_m. host_split_preserves_m covers every retry and max_par cap;
#   launch passes that prob_m_split and then subtracts it from rest_m.
# - Normalization laws preserve (parallel,effectiveM)=(1,originalM), not just
#   physical M8. Actual-M A-copy, reduction-row and output-gather predicates
#   must refine normalization_predicates. No padding row becomes observable.
#   The stripe formulas below describe selected group128/K64 inputs and the
#   clamped work count, including idle CTAs and row0/next-column restarts.
#   Their lock observation law is congruence for ANY pure observer of those
#   equal inputs, not a proof of native init_slice, locks_off or synchronization.
#   Native signed differences (including initial locks_off=-1), divisions,
#   pointer remaps and later increments must refine these inputs in range.
#   No idle remap, restart, acquire/release or lock reset is removed.
# - Both paths retain grid, K stripes, slice/reduction grouping, scratch, function
#   attribute cap and final kernel capacity argument. Selected reservation is
#   still43008 bytes. Integer conversions/address arithmetic must be in range
#   and refine the Nat indices. Each ring starts on an even group phase.
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
# - FP32 transfer laws below are linked to the same Impl.policy action, not a
#   new runtime decision. Only ScaleRefreshMask!=255 uses local int4 bitcasts;
#   action0 retains the staged source. The model is conditional on that native
#   gate, active t<64, pair=k/2 in0..3, component=f in0..3, C_tmp int4 address
#   512*locks_off+128*pair+t and accumulator coordinate8*pair+component.
#   Own-lane staging/read and __int_as_float must preserve identical bits;
#   accumulator-left/loaded-right FADD order and all first/last branches remain.
# - Acquire, release (including its CTA barrier/fence), scratch publication,
#   lock reset, final conversions and output scatter/gather are unchanged.
#   The output barrier must complete every physical M8 scatter before valid
#   M1..8 gathers, including gathers by lanes64..127. Full N128 and row bounds
#   must refine the output predicate; padding columns128..135 are unobserved.
#   Output overwrites D intersect observed reads, NOT every byte of D.
# - A nonempty restart issues B stage0 vectors128*i+t (i0,1;t0..127).
#   Its unconditional stage0 writes cover D=[0,1024); wait_group<6> after seven
#   commits plus the CTA barrier must make those writes visible before reads.
#   restart noninterference is explicitly conditional on this native wait.
#   No assertion is made that all speculative/tail-prefetched stages are fresh.
# - The source-derived stripe implication !first => this CTA exhausts its
#   stripe after this reduction is NOT represented/proved below: E=I*(block+1)
#   and C=T*(column+1), !first implies E<C; incrementing column clamps next
#   slice_iters to0. That native init_slice correspondence remains external.
#   Nonlast !first therefore has no later shared observer only if this source
#   correspondence holds; it is not supplied as an axiom or hidden theorem.
# - These are conditional symbolic contracts, not compiler/SASS equivalence.
#   The literal selected SASS operand-sequence gate failed after predication/
#   register/scheduling changes; address/FADD-order inspection is narrower than
#   whole-kernel dataflow proof. Neither these laws nor removed-store counts
#   admit that failed gate. Fresh candidate GPU correctness remains required.
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

# Source-derived access envelope; actual native pointers must refine it.
law selected_shared_layout:
  {[Spec.shared_bytes(8n, 8n), Spec.shared_bytes(8n, 16n),
    Spec.shared_bytes(4n, 8n), Spec.shared_bytes(4n, 16n)] ==
    [43008n, 51200n, 21504n, 25600n] : List<&2, Nat>}

# Preserve the conservative padded-M16 admission threshold, independently of the
# smaller selected reservation. No occupancy or execution-time claim follows.
law conservative_shared_bound:
  {Nat.is_le(Spec.shared_bytes(8n, 8n), Spec.shared_bytes(8n, 16n)) == True{} : Bool} &
  {Nat.add(Spec.shared_bytes(8n, 8n), 8192n) == Spec.shared_bytes(8n, 16n) : Nat}

law selected_shared_exact:
  {Impl.selected_shared_bytes() == Spec.shared_bytes(8n, 8n) : Nat} &
  {Impl.selected_shared_bytes() == 43008n : Nat}

# Named4352 is deliberately shown beside actual7168, never used as its bound.
law selected_overlay_extents:
  {[Spec.cta_reduction_bytes(), Spec.output_write_bytes(), Spec.output_read_bytes(),
    Spec.bf16_reduction_bytes(), Spec.fp32_reduction_bytes(),
    Spec.bytes(Spec.nominal_reduction_int4s()), Spec.bytes(Spec.overlay_int4s())] ==
    [7168n, 2160n, 2160n, 2048n, 1024n, 4352n, 32768n] : List<&2, Nat>}

law selected_overlay_coverage:
  Order.Le(Spec.cta_reduction_bytes(), Spec.bytes(Spec.overlay_int4s())) &
  (Order.Le(Spec.output_write_bytes(), Spec.bytes(Spec.overlay_int4s())) &
  (Order.Le(Spec.bf16_reduction_bytes(), Spec.bytes(Spec.overlay_int4s())) &
    Order.Le(Spec.fp32_reduction_bytes(), Spec.bytes(Spec.overlay_int4s()))))

# Spatial separation is only overlay / reserved scale slots / A. Reductions
# and output intentionally alias B; async/barrier lifetime is NOT proved here.
# Odd scale slots remain reserved: deleting their holes would not relocate A.
law selected_regions_disjoint:
  Order.Le(Spec.bytes(Spec.overlay_int4s()), Spec.bytes(Spec.scale_base_int4s())) &
  (Order.Le(Spec.stage_base(Spec.scale_base_int4s(), Spec.s_stage_int4s(), 8n),
    Spec.bytes(Spec.a_base_int4s())) &
  {Spec.stage_base(Spec.a_base_int4s(), Spec.a_stage_int4s(), 8n) ==
    Impl.selected_shared_bytes() : Nat})

law selected_region_offsets:
  {[Spec.bytes(Spec.scale_base_int4s()), Spec.bytes(Spec.a_base_int4s()),
    Impl.selected_shared_bytes()] == [32768n, 34816n, 43008n] : List<&2, Nat>}

law selected_stage_alignment:
  for +tile: Nat
  {Nat.mod(Spec.stage_base(0n, Spec.b_stage_int4s(), Spec.slot(tile, 8n)), 16n) == 0n : Nat} &
  ({Nat.mod(Spec.stage_base(Spec.scale_base_int4s(), Spec.s_stage_int4s(), Spec.slot(tile, 8n)), 16n) == 0n : Nat} &
  {Nat.mod(Spec.stage_base(Spec.a_base_int4s(), Spec.a_stage_int4s(), Spec.slot(tile, 8n)), 16n) == 0n : Nat})

# Universal stage/local bounds include all sixteen bytes, not just the starting
# pointer. The existing modulo-eight lemma covers arbitrary wraps and tail reads.
law selected_a_access_bound:
  for +tile: Nat
  for +local: Nat
  for bounded: Order.Le(1n+local, Spec.a_stage_int4s())
  Order.Le(Spec.access_end(Spec.a_base_int4s(), Spec.a_stage_int4s(), Spec.slot(tile, 8n), local),
    Impl.selected_shared_bytes())

law selected_b_access_bound:
  for +tile: Nat
  for +local: Nat
  for bounded: Order.Le(1n+local, Spec.b_stage_int4s())
  Order.Le(Spec.access_end(0n, Spec.b_stage_int4s(), Spec.slot(tile, 8n), local),
    Impl.selected_shared_bytes())

law selected_scale_access_bound:
  for +tile: Nat
  for +local: Nat
  for bounded: Order.Le(1n+local, Spec.s_stage_int4s())
  Order.Le(Spec.access_end(Spec.scale_base_int4s(), Spec.s_stage_int4s(), Spec.slot(tile, 8n), local),
    Impl.selected_shared_bytes())

# This covers only ACTIVE A cp.async writes. Inactive threads64..127 may form
# larger operands; the native predicated no-op behavior is an external obligation.
law selected_a_active_copy_index:
  for +rows: Nat
  for +thread: Nat
  for admitted: Order.Le(rows, 8n)
  for active: {Spec.a_copy_active(rows, thread) == True{} : Bool}
  Order.Le(1n+thread, Spec.a_stage_int4s())

# Explicit first16-supplier coordinate domain, not a claim that all32 lanes
# independently dereference their operands. The post-XOR column must retain its
# 0..7 domain; preserving the low-three-bit permutation is native refinement.
law selected_a_supplier_column:
  for +lane_half: Nat
  for +warp_pair: Nat
  for +k_half: Nat
  for lane_bound: Order.Le(1n+lane_half, 2n)
  for warp_bound: Order.Le(1n+warp_pair, 2n)
  for k_bound: Order.Le(1n+k_half, 2n)
  Order.Le(1n+Spec.a_supplier_column(lane_half, warp_pair, k_half), 8n)

law selected_a_swizzled_index:
  for +row: Nat
  for +column: Nat
  for row_bound: Order.Le(1n+row, 8n)
  for column_bound: Order.Le(1n+column, 8n)
  Order.Le(1n+Spec.tile_index(8n, row, column), Spec.a_stage_int4s())

law selected_b_local_index:
  for +iteration: Nat
  for +thread: Nat
  for iteration_bound: Order.Le(1n+iteration, 2n)
  for thread_bound: Order.Le(1n+thread, 128n)
  Order.Le(1n+Spec.tile_index(128n, iteration, thread), Spec.b_stage_int4s())

law selected_scale_local_index:
  for +warp_mod2: Nat
  for +lane_div4: Nat
  for warp_bound: Order.Le(1n+warp_mod2, 2n)
  for lane_bound: Order.Le(1n+lane_div4, 8n)
  Order.Le(1n+Spec.tile_index(8n, warp_mod2, lane_div4), Spec.s_stage_int4s())

law selected_cta_reduction_index:
  for +pair: Nat
  for +thread_mod64: Nat
  for pair_bound: Order.Le(pair, 3n)
  for thread_bound: Order.Le(1n+thread_mod64, 64n)
  Order.Le(Spec.bytes(1n+Spec.cta_reduction_index(pair, thread_mod64)),
    Spec.cta_reduction_bytes())

# Only arithmetic identities for the native schedule parameters are asserted.
law schedule_parameters:
  {[Spec.prime_groups(8n), Spec.wait_groups(8n),
    Spec.prime_groups(4n), Spec.wait_groups(4n)] == [7n, 6n, 3n, 2n] : List<&2, Nat>}

law pending_group_arithmetic:
  {1n+Spec.wait_groups(8n) == Spec.prime_groups(8n) : Nat} &
  {Nat.is_lt(Spec.prime_groups(8n), 8n) == True{} : Bool}

# The compiled decision, its exact wire rows, and the LSB-first host mask.
law scale_refresh_refinement:
  for +phase: Nat
  {Impl.scale_refresh(phase) == Spec.scale_refresh_row(phase) : Nat}

law scale_refresh_range:
  for +phase: Nat
  Spec.Action(Impl.scale_refresh(phase))

law scale_refresh_table_exact:
  {Impl.scale_refresh_table(8n, 0n) == [1n, 0n, 1n, 0n, 1n, 0n, 1n, 0n] : List<&2, Nat>}

law scale_refresh_mask_exact:
  {Spec.packed_refresh(Impl.scale_refresh_table(8n, 0n)) == 85n : Nat} &
  {Nat.is_lt(Spec.packed_refresh(Impl.scale_refresh_table(8n, 0n)), 256n) == True{} : Bool}

law scale_refresh_ring:
  for +tile: Nat
  {Impl.scale_refresh(Spec.slot(tile, 8n)) == Impl.scale_refresh(tile) : Nat}

law scale_refresh_wrap:
  for +tile: Nat
  {Impl.scale_refresh(Spec.slot(8n+tile, 8n)) ==
    Impl.scale_refresh(Spec.slot(tile, 8n)) : Nat}

law scale_refresh_seven_to_zero:
  {[Impl.scale_refresh(Spec.slot(7n, 8n)), Impl.scale_refresh(Spec.slot(8n, 8n))] ==
    [0n, 1n] : List<&2, Nat>}

law scale_refresh_index_bound:
  for +tile: Nat
  {Nat.is_lt(Spec.slot(tile, 8n), 8n) == True{} : Bool}

law aligned_scale_start:
  for +group: Nat
  {Nat.div(Nat.double(group), 2n) == group : Nat}

law semantic_group_pair:
  for +group: Nat
  for +column: Nat
  for +element: Nat
  {Spec.required_scale(Spec.next_group(Spec.First{group}), column, element) ==
    Spec.Scale{column, group, element} : Spec.Scale} &
  {Spec.required_scale(Spec.next_group(Spec.Second{group}), column, element) ==
    Spec.Scale{column, 1n+group, element} : Spec.Scale}

law reference_scale_initialization:
  for +needed: Spec.Scale
  {Spec.reference_cache(needed, Spec.Uninitialized{}) == Spec.Loaded{needed} : Spec.ScaleBank}

law reference_scale_reuse:
  for +needed: Spec.Scale
  {Spec.reference_cache(needed, Spec.Loaded{needed}) == Spec.Loaded{needed} : Spec.ScaleBank}

law reference_scale_group_transition:
  for +group: Nat
  for +column: Nat
  for +element: Nat
  {Spec.reference_cache(Spec.Scale{column, 1n+group, element},
    Spec.Loaded{Spec.Scale{column, group, element}}) ==
    Spec.Loaded{Spec.Scale{column, 1n+group, element}} : Spec.ScaleBank}

# Proof-only selected nondefault-mask schedule, deliberately outside Impl/RUNTIME.
# It consumes Impl.scale_refresh, so changing the shipped table invalidates the
# operand/recurrence theorems. Physical ring indices are bounded by eight.
# Copy bank0 to bank1, consume matmul(0) then matmul(1), THEN refresh bank0
# using the already-incremented pipe. No async/shared write intervenes in native.
def scheduled_scale_run(count: Nat, +tile: Nat, +cursor: Spec.GroupCursor,
    +column: Nat, +element: Nat, bank: Spec.ScaleBank,
    accumulator: Spec.ScaleAccumulator) -> Spec.ScaleAccumulator:
  match count:
    case 0n:
      accumulator
    case 1n+p:
      copied = Spec.copy_scale(Spec.ScaleBanks{bank, Spec.Uninitialized{}})
      +advanced = Spec.delayed_scale_tile(tile, Impl.scale_refresh(Spec.slot(1n+tile, 8n)),
        Spec.required_scale(Spec.next_group(cursor), column, element), copied, accumulator)
      scheduled_scale_run(p, 1n+tile, Spec.next_group(cursor), column, element,
        Spec.bank_zero(Spec.scale_state_banks(advanced)), Spec.scale_state_accumulator(advanced))

def scheduled_scale_start(count: Nat, +group: Nat, +column: Nat, +element: Nat,
    previous: Spec.ScaleBank, accumulator: Spec.ScaleAccumulator) -> Spec.ScaleAccumulator:
  scheduled_scale_run(count, 0n, Spec.First{group}, column, element,
    Spec.load_scale(Impl.scale_refresh(0n), Spec.Scale{column, group, element}, previous), accumulator)

law scheduled_scale_initialization:
  for +needed: Spec.Scale
  for previous: Spec.ScaleBank
  {Spec.load_scale(Impl.scale_refresh(0n), needed, previous) == Spec.Loaded{needed} : Spec.ScaleBank}

law scheduled_scale_reuse:
  for +pair: Nat
  for +needed: Spec.Scale
  {Spec.load_scale(Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)), needed,
    Spec.Loaded{needed}) == Spec.reference_cache(needed, Spec.Loaded{needed}) : Spec.ScaleBank}

law scheduled_scale_group_transition:
  for +pair: Nat
  for +group: Nat
  for +column: Nat
  for +element: Nat
  {Spec.load_scale(Impl.scale_refresh(Spec.slot(Nat.double(1n+pair), 8n)),
    Spec.Scale{column, 1n+group, element}, Spec.Loaded{Spec.Scale{column, group, element}}) ==
    Spec.reference_cache(Spec.Scale{column, 1n+group, element},
      Spec.Loaded{Spec.Scale{column, group, element}}) : Spec.ScaleBank}

# Arbitrary distinct current/next operands: final bank1 still holds current
# after the delayed bank0 write. This is a final-state, not a temporal assertion.
law scale_bank_lifetime:
  for +current: Spec.Scale
  for +next: Spec.Scale
  for stale: Spec.ScaleBank
  {Spec.refresh_zero(1n, next, Spec.copy_scale(Spec.ScaleBanks{Spec.Loaded{current}, stale})) ==
    Spec.ScaleBanks{Spec.Loaded{next}, Spec.Loaded{current}} : Spec.ScaleBanks}

# Commutation is only with the bank1 consumer, NOT with matmul(0) or the copy.
# Equality includes both final banks and the exact previous-accumulator term.
law scale_refresh_consumer_commutes:
  for +tile: Nat
  for +refresh: Nat
  for +next: Spec.Scale
  for +state: Spec.ScaleTileState
  {Spec.consume_scale_one(tile, Spec.refresh_scale_state(refresh, next, state)) ==
    Spec.refresh_scale_state(refresh, next, Spec.consume_scale_one(tile, state)) : Spec.ScaleTileState}

law scale_delayed_tile_state:
  for +tile: Nat
  for +refresh: Nat
  for +next: Spec.Scale
  for +bank: Spec.ScaleBank
  for stale: Spec.ScaleBank
  for +accumulator: Spec.ScaleAccumulator
  {Spec.delayed_scale_tile(tile, refresh, next, Spec.copy_scale(Spec.ScaleBanks{bank, stale}), accumulator) ==
    Spec.ScaleTileState{Spec.ScaleBanks{Spec.load_scale(refresh, next, bank), bank},
      Spec.accumulate_scale_tile(tile, bank, accumulator)} : Spec.ScaleTileState}

# Preserve the original pre-refresh snapshot identity as a comparison, not a
# claim of selected source order; the second conjunct covers the delayed model.
law scale_ordered_consumers:
  for +tile: Nat
  for +refresh: Nat
  for +current: Spec.Scale
  for +next: Spec.Scale
  for +accumulator: Spec.ScaleAccumulator
  {Spec.consume_scale_tile(tile, Spec.copy_scale(Spec.ScaleBanks{Spec.Loaded{current}, Spec.Uninitialized{}}),
    Spec.refresh_zero(refresh, next,
      Spec.copy_scale(Spec.ScaleBanks{Spec.Loaded{current}, Spec.Uninitialized{}})), accumulator) ==
    Spec.accumulate_scale_tile(tile, Spec.Loaded{current}, accumulator) : Spec.ScaleAccumulator} &
  {Spec.scale_state_accumulator(Spec.delayed_scale_tile(tile, refresh, next,
    Spec.copy_scale(Spec.ScaleBanks{Spec.Loaded{current}, Spec.Uninitialized{}}), accumulator)) ==
    Spec.accumulate_scale_tile(tile, Spec.Loaded{current}, accumulator) : Spec.ScaleAccumulator}

# All tile counts, including empty/short tails, all aligned group offsets, and
# arbitrarily many ring wraps. This is equality of the exact ordered expression
# with scale operands, not an unordered trace or a sum using associativity.
law scale_accumulator_recurrence:
  for +count: Nat
  for +group: Nat
  for +column: Nat
  for +element: Nat
  for previous: Spec.ScaleBank
  for +accumulator: Spec.ScaleAccumulator
  {scheduled_scale_start(count, group, column, element, previous, accumulator) ==
    Spec.reference_scale_run(count, 0n, Spec.First{group}, column, element, accumulator) : Spec.ScaleAccumulator}

# Each new column invokes start_pipes and zero_accums again. Neither a previous
# column/group's bank nor its last ring phase can bypass phase-zero refresh.
law scale_new_column_reset:
  for +count: Nat
  for +group: Nat
  for +column: Nat
  for +element: Nat
  for old_column: Nat
  for old_group: Nat
  for old_element: Nat
  for +identity: Nat
  {scheduled_scale_start(count, group, column, element,
    Spec.Loaded{Spec.Scale{old_column, old_group, old_element}}, Spec.ScaleInitial{identity}) ==
    Spec.reference_scale_run(count, 0n, Spec.First{group}, column, element,
      Spec.ScaleInitial{identity}) : Spec.ScaleAccumulator}

# Default-mask native instantiations still perform an unconditional load. Its
# native guard/default/template fidelity is external, not a theorem about C++.
law scale_unconditional_load:
  for +needed: Spec.Scale
  for previous: Spec.ScaleBank
  {Spec.load_scale(1n, needed, previous) == Spec.Loaded{needed} : Spec.ScaleBank}

# The existing shipped Boolean action is the sole production link. This helper
# and every structure below remain outside the runtime import graph.
def scheduled_fp32(+eligible: Bool, +safe: Bool, +deterministic: Bool,
    first: Bool, last: Bool, lock: Nat, +lane: Nat, identity: Nat,
    previous: Spec.FP32Shared) -> Spec.FP32State:
  Spec.fp32_transfer(Nat.is_lt(lane, 64n), first, last,
    Impl.policy(eligible, safe, deterministic), lock, lane, identity, previous)

law selected_fp32_transfer_refinement:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +first: Bool
  for +last: Bool
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  for +previous: Spec.FP32Shared
  {Spec.fp32_observable(scheduled_fp32(eligible, safe, deterministic,
    first, last, lock, lane, identity, previous)) ==
    Spec.fp32_observable(Spec.fp32_transfer(Nat.is_lt(lane, 64n), first, last,
      0n, lock, lane, identity, previous)) : Spec.FP32Observable}

# Full state equality is asserted only for fallback, not the changed shared arm.
law selected_fp32_action0_fallback:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +first: Bool
  for +last: Bool
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  for +previous: Spec.FP32Shared
  for fallback: {Impl.policy(eligible, safe, deterministic) == 0n : Nat}
  {scheduled_fp32(eligible, safe, deterministic, first, last, lock, lane, identity, previous) ==
    Spec.fp32_transfer(Nat.is_lt(lane, 64n), first, last, 0n, lock, lane, identity, previous) : Spec.FP32State}

law selected_fp32_transfer_indices:
  for +lock: Nat
  for +pair: Nat
  for +lane: Nat
  for +component: Nat
  {Spec.fp32_scratch_index(lock, pair, lane) ==
    Nat.add(Nat.mul(lock, 512n), Nat.add(Nat.mul(pair, 128n), lane)) : Nat} &
  ({Spec.fp32_accumulator_index(pair, component) == Nat.add(Nat.mul(pair, 8n), component) : Nat} &
  {Spec.fp32_word(Impl.policy(True{}, True{}, True{}), lock, pair, lane, component) ==
    Spec.fp32_read_staged(Spec.fp32_stage(lane,
      Nat.add(Nat.mul(lock, 512n), Nat.add(Nat.mul(pair, 128n), lane))), component) : Spec.FP32Word})

# Independent source constructors fix operand side and component identity.
def fp32_source_value(first: Bool, +lock: Nat, +pair: Nat, +lane: Nat,
    +component: Nat, identity: Nat) -> Spec.FP32Value:
  match first:
    case True{}:
      Spec.FP32Initial{identity, Nat.add(Nat.mul(pair, 8n), component)}
    case False{}:
      Spec.FP32Add{Spec.FP32Initial{identity, Nat.add(Nat.mul(pair, 8n), component)},
        Spec.ScratchBits{Spec.fp32_reference_index(lock, pair, lane), component}}

def fp32_source_values(+first: Bool, +lock: Nat, +pair: Nat, +lane: Nat,
    +identity: Nat) -> List<&2, Spec.FP32Value>:
  [fp32_source_value(first, lock, pair, lane, 0n, identity),
    fp32_source_value(first, lock, pair, lane, 1n, identity),
    fp32_source_value(first, lock, pair, lane, 2n, identity),
    fp32_source_value(first, lock, pair, lane, 3n, identity)]

def fp32_source_pair(+lock: Nat, +pair: Nat, +lane: Nat,
    +identity: Nat) -> List<&2, Spec.FP32Event>:
  [Spec.ScratchRead{Spec.fp32_reference_index(lock, pair, lane)},
    Spec.AccumulatorWrite{Nat.add(Nat.mul(pair, 8n), 0n), fp32_source_value(False{}, lock, pair, lane, 0n, identity)},
    Spec.AccumulatorWrite{Nat.add(Nat.mul(pair, 8n), 1n), fp32_source_value(False{}, lock, pair, lane, 1n, identity)},
    Spec.AccumulatorWrite{Nat.add(Nat.mul(pair, 8n), 2n), fp32_source_value(False{}, lock, pair, lane, 2n, identity)},
    Spec.AccumulatorWrite{Nat.add(Nat.mul(pair, 8n), 3n), fp32_source_value(False{}, lock, pair, lane, 3n, identity)}]

law selected_fp32_ordered_trace:
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  {Spec.fp32_add_events(False{}, Impl.policy(True{}, True{}, True{}), lock, lane, identity) ==
    List.append(&2, Spec.FP32Event, fp32_source_pair(lock, 0n, lane, identity),
      List.append(&2, Spec.FP32Event, fp32_source_pair(lock, 1n, lane, identity),
        List.append(&2, Spec.FP32Event, fp32_source_pair(lock, 2n, lane, identity),
          fp32_source_pair(lock, 3n, lane, identity)))) : List<&2, Spec.FP32Event>}

law selected_fp32_scratch_trace:
  for +first: Bool
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  {Spec.fp32_store_events(False{}, first, Impl.policy(True{}, True{}, True{}), lock, lane, identity) ==
    [Spec.ScratchWrite{Spec.fp32_reference_index(lock, 0n, lane), fp32_source_values(first, lock, 0n, lane, identity)},
      Spec.ScratchWrite{Spec.fp32_reference_index(lock, 1n, lane), fp32_source_values(first, lock, 1n, lane, identity)},
      Spec.ScratchWrite{Spec.fp32_reference_index(lock, 2n, lane), fp32_source_values(first, lock, 2n, lane, identity)},
      Spec.ScratchWrite{Spec.fp32_reference_index(lock, 3n, lane), fp32_source_values(first, lock, 3n, lane, identity)}]
      : List<&2, Spec.FP32Event>}

law selected_fp32_branch_traces:
  for +action: Nat
  for +first: Bool
  for +last: Bool
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  for +previous: Spec.FP32Shared
  {Spec.fp32_transfer(False{}, first, last, action, lock, lane, identity, previous) ==
    Spec.FP32State{Spec.FP32Inactive{identity}, previous} : Spec.FP32State} &
  ({Spec.fp32_add_events(True{}, action, lock, lane, identity) == Nil{} : List<&2, Spec.FP32Event>} &
    {Spec.fp32_store_events(True{}, first, action, lock, lane, identity) == Nil{} : List<&2, Spec.FP32Event>})

# Finite physical coverage is independently checked once, then instantiated for
# any logical M1..8. It is not an extent-only argument or a runtime enumeration.
law selected_fp32_output_coordinate_table:
  {Spec.fp32_output_rows(8n, 0n) == True{} : Bool}

law selected_fp32_output_read_coverage:
  for +rows: Nat
  for +row: Nat
  for +column: Nat
  for nonempty: Order.Le(1n, rows)
  for admitted: Order.Le(rows, 8n)
  for observed_row: Order.Le(1n+row, rows)
  for observed_column: Order.Le(1n+column, 128n)
  {Spec.fp32_output_coordinate_ok(row, column) == True{} : Bool}

# A scalar cell denotes both bytes; arbitrary shared predecessors include the
# entire deleted staging footprint. Only actually observed coordinates qualify.
law selected_fp32_output_noninterference:
  for +rows: Nat
  for +row: Nat
  for +column: Nat
  for +identity: Nat
  for left: Spec.FP32State
  for right: Spec.FP32State
  for nonempty: Order.Le(1n, rows)
  for admitted: Order.Le(rows, 8n)
  for observed_row: Order.Le(1n+row, rows)
  for observed_column: Order.Le(1n+column, 128n)
  {Spec.fp32_output_after(row, column, identity, left) ==
    Spec.fp32_output_after(row, column, identity, right) : Spec.FP32OverlayObservation}

law selected_fp32_padding_unobserved:
  for +rows: Nat
  {Spec.fp32_output_observed(rows, 0n, 128n) == False{} : Bool} &
    Order.Le(1n+Nat.mul(Spec.fp32_output_address(0n, 128n), 2n), Spec.fp32_reduction_bytes())

# D={16*lane+byte | lane<64, byte<16}. Stage0's i0 subset already
# overwrites D; i1 extends the unconditional refill to4096 bytes.
law selected_fp32_restart_cover:
  for +lane: Nat
  for +byte: Nat
  for lane_bound: Order.Le(1n+lane, 64n)
  for byte_bound: Order.Le(1n+byte, 16n)
  Order.Le(1n+lane, 128n) &
    {Spec.fp32_restart_byte(0n, lane, byte) == Spec.fp32_deleted_byte(lane, byte) : Nat}

law selected_fp32_restart_noninterference:
  for +waited: Bool
  for +lane: Nat
  for +byte: Nat
  for +identity: Nat
  for left: Spec.FP32State
  for right: Spec.FP32State
  for lane_bound: Order.Le(1n+lane, 64n)
  for byte_bound: Order.Le(1n+byte, 16n)
  for ready: {waited == True{} : Bool}
  {Spec.fp32_restart_after(waited, lane, byte, identity, left) ==
    Spec.fp32_restart_after(waited, lane, byte, identity, right) : Spec.FP32OverlayObservation}

# Compose the spatial overwrite result with the policy-linked state projection.
# Equality of output fragment inputs is included; native conversion and the
# release/scatter/gather barriers must refine this conditional composition.
law selected_fp32_output_projection:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +first: Bool
  for +lock: Nat
  for +lane: Nat
  for +identity: Nat
  for +previous: Spec.FP32Shared
  for +rows: Nat
  for +row: Nat
  for +column: Nat
  for nonempty: Order.Le(1n, rows)
  for admitted: Order.Le(rows, 8n)
  for observed_row: Order.Le(1n+row, rows)
  for observed_column: Order.Le(1n+column, 128n)
  {Spec.fp32_observable(scheduled_fp32(eligible, safe, deterministic,
    first, True{}, lock, lane, identity, previous)) ==
    Spec.fp32_observable(Spec.fp32_transfer(Nat.is_lt(lane, 64n),
      first, True{}, 0n, lock, lane, identity, previous)) : Spec.FP32Observable} &
  {Spec.fp32_output_after(row, column, identity, scheduled_fp32(eligible, safe, deterministic,
    first, True{}, lock, lane, identity, previous)) ==
    Spec.fp32_output_after(row, column, identity, Spec.fp32_transfer(Nat.is_lt(lane, 64n),
      first, True{}, 0n, lock, lane, identity, previous)) : Spec.FP32OverlayObservation}

law selected_fp32_restart_projection:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +first: Bool
  for +last: Bool
  for +lock: Nat
  for +lane: Nat
  for +byte: Nat
  for +identity: Nat
  for +previous: Spec.FP32Shared
  for +waited: Bool
  for lane_bound: Order.Le(1n+lane, 64n)
  for byte_bound: Order.Le(1n+byte, 16n)
  for ready: {waited == True{} : Bool}
  {Spec.fp32_restart_after(waited, lane, byte, identity,
    scheduled_fp32(eligible, safe, deterministic, first, last, lock, lane, identity, previous)) ==
    Spec.fp32_restart_after(waited, lane, byte, identity, Spec.fp32_transfer(Nat.is_lt(lane, 64n),
      first, last, 0n, lock, lane, identity, previous)) : Spec.FP32OverlayObservation}

# Conditional kernel model linked to the actual shipped action, never a new
# runtime selector. action0 imposes no small-M restriction on fallback geometry.
def NormalizationDomain(action: Nat, rows: Nat, block: Nat) -> Type:
  match action:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Order.Le(1n, rows) & (Order.Le(rows, 8n) & {block == 8n : Nat})
        case 1n+q:
          Empty

def scheduled_normalization(eligible: Bool, safe: Bool, deterministic: Bool,
    rows: Nat, block: Nat) -> Spec.MNormalization:
  Spec.normalization(Impl.policy(eligible, safe, deterministic), rows, block)

law host_retry_bound:
  for +retry: Spec.MRetry
  Order.Le(16n, Spec.retry_divisor(retry))

law host_split_preserves_m:
  for +retry: Spec.MRetry
  for +rows: Nat
  for +max_par: Nat
  for nonempty: Order.Le(1n, rows)
  for bounded: Order.Le(rows, 8n)
  {Nat.div(rows, Spec.retry_divisor(retry)) == 0n : Nat} &
  ({Spec.host_par_count(rows, Spec.retry_divisor(retry), max_par) == 0n : Nat} &
  ({Spec.host_split(rows, Spec.retry_divisor(retry), max_par) == rows : Nat} &
    {Nat.sub(rows, Spec.host_split(rows, Spec.retry_divisor(retry), max_par)) == 0n : Nat}))

law selected_m_pair:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for selected: {Impl.policy(eligible, safe, deterministic) == 1n : Nat}
  for nonempty: Order.Le(1n, rows)
  for bounded: Order.Le(rows, 8n)
  {scheduled_normalization(eligible, safe, deterministic, rows, 8n) ==
    Spec.MNormalization{1n, rows} : Spec.MNormalization}

law normalization_refinement:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +block: Nat
  for admitted: NormalizationDomain(Impl.policy(eligible, safe, deterministic), rows, block)
  {scheduled_normalization(eligible, safe, deterministic, rows, block) ==
    Spec.original_normalization(rows, block) : Spec.MNormalization}

# Stronger than admitted-fallback equality: any mathematical M/block is
# unchanged when action0, while native positive/range checks stay external.
law normalization_action0:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +block: Nat
  for fallback: {Impl.policy(eligible, safe, deterministic) == 0n : Nat}
  {scheduled_normalization(eligible, safe, deterministic, rows, block) ==
    Spec.original_normalization(rows, block) : Spec.MNormalization}

# Original -> every possible retry -> split -> kernel: no M8 padding replaces
# logical M1..8. Both sides explicitly consume the same host-derived split.
law selected_launch_m:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +retry: Spec.MRetry
  for +rows: Nat
  for +max_par: Nat
  for selected: {Impl.policy(eligible, safe, deterministic) == 1n : Nat}
  for nonempty: Order.Le(1n, rows)
  for +bounded: Order.Le(rows, 8n)
  {scheduled_normalization(eligible, safe, deterministic,
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n) ==
    Spec.MNormalization{1n, rows} : Spec.MNormalization} &
  {Spec.original_normalization(Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n) ==
    Spec.MNormalization{1n, rows} : Spec.MNormalization}

law selected_m_predicates:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +retry: Spec.MRetry
  for +rows: Nat
  for +max_par: Nat
  for +thread: Nat
  for +row: Nat
  for +column: Nat
  for selected: {Impl.policy(eligible, safe, deterministic) == 1n : Nat}
  for nonempty: Order.Le(1n, rows)
  for bounded: Order.Le(rows, 8n)
  {Spec.normalization_predicates(scheduled_normalization(eligible, safe, deterministic,
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n), thread, row, column) ==
    [Spec.a_copy_active(rows, thread), Nat.is_lt(row, rows),
      Spec.fp32_output_observed(rows, row, column)] : List<&2, Bool>}

# The common downstream selected-geometry formulas consume equal pairs.
# No assertion that all fallback kernels use group-period2 is made.
law normalization_stripe_inputs:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +m_block: Nat
  for +k: Nat
  for +n: Nat
  for +grid: Nat
  for +block: Nat
  for +column: Nat
  for +row: Nat
  for admitted: NormalizationDomain(Impl.policy(eligible, safe, deterministic), rows, m_block)
  {Spec.stripe_observation(scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block) ==
    Spec.stripe_observation(Spec.original_normalization(rows, m_block), k, n, grid, block)
      : Spec.StripeObservation} &
  {Spec.slice_work(scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block, column, row) ==
    Spec.slice_work(Spec.original_normalization(rows, m_block), k, n, grid, block, column, row) : Nat}

law normalization_tiles:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +m_block: Nat
  for +k: Nat
  for +n: Nat
  for +grid: Nat
  for +block: Nat
  for +column: Nat
  for +row: Nat
  for +start: Nat
  for admitted: NormalizationDomain(Impl.policy(eligible, safe, deterministic), rows, m_block)
  {Spec.tiles8(Spec.slice_work(scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block, column, row), start) ==
    Sequence.seq(Spec.slice_work(Spec.original_normalization(rows, m_block),
      k, n, grid, block, column, row), start) : List<&2, Nat>}

law normalization_recurrence:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +m_block: Nat
  for +k: Nat
  for +n: Nat
  for +grid: Nat
  for +block: Nat
  for +column: Nat
  for +row: Nat
  for +start: Nat
  for +accumulator: Spec.Accumulator
  for admitted: NormalizationDomain(Impl.policy(eligible, safe, deterministic), rows, m_block)
  {Spec.recurrence(Spec.mma_terms(Spec.tiles8(Spec.slice_work(
      scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block, column, row), start)), accumulator) ==
    Spec.recurrence(Spec.mma_terms(Sequence.seq(Spec.slice_work(
      Spec.original_normalization(rows, m_block), k, n, grid, block, column, row), start)),
      accumulator) : Spec.Accumulator}

# Parametric congruence into the existing ordered FP32 observation type. A
# native lock/reduction interpretation must supply the SAME pure observer;
# its implementation, signed offsets and CUDA synchronization are NOT proved.
# Quantifying an observer is not assuming its outputs equal: pair equality
# proves equality for every such function without any native axiom.
law normalization_lock_observation:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +rows: Nat
  for +m_block: Nat
  for +k: Nat
  for +n: Nat
  for +grid: Nat
  for +block: Nat
  for observe: Spec.StripeObservation -> Spec.FP32Observable
  for admitted: NormalizationDomain(Impl.policy(eligible, safe, deterministic), rows, m_block)
  {observe(Spec.stripe_observation(scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block)) ==
    observe(Spec.stripe_observation(Spec.original_normalization(rows, m_block), k, n, grid, block))
      : Spec.FP32Observable}

# Scale-lane optimization: all helpers here are proof-only. The existing
# three-Boolean action supplies mask255 on fallback and the ACTUAL shipped
# scale-refresh table on selection. No new wire field or selector is added.
def scheduled_scale_mask(action: Nat) -> Nat:
  match action:
    case 0n:
      255n
    case 1n+p:
      Spec.packed_refresh(Impl.scale_refresh_table(8n, 0n))

def scheduled_scale_index(eligible: Bool, safe: Bool, deterministic: Bool,
    +thread: Nat) -> Nat:
  Spec.scale_masked_index(scheduled_scale_mask(Impl.policy(eligible, safe, deterministic)),
    thread, Spec.scale_generic_index(thread))

def scheduled_scale_address(eligible: Bool, safe: Bool, deterministic: Bool,
    tile: Nat, thread: Nat) -> Nat:
  Spec.scale_selected_address(scheduled_scale_mask(Impl.policy(eligible, safe, deterministic)),
    tile, thread)

# Exhaustive computation is eliminated below at arbitrary t with t+1<=128.
# These are exact quotient/mod/U32-bit equalities, not just extent checks.
law scale_lane_certificate:
  {Spec.scale_lane_rows(128n, 0n) == True{} : Bool}

law scale_lane_index_refinement:
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.scale_selected_index(thread) == Spec.scale_generic_index(thread) : Nat}

law scale_lane_emitted_bytes:
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.scale_emitted_bytes(thread) == Spec.bytes(Spec.scale_selected_index(thread)) : Nat}

# Finite no-overflow facts for the input and emitted multiplication only.
# Native signed address increments and CUDA pointer interpretation stay external.
law scale_lane_machine_domain:
  for +thread: Nat
  for +bounded: Order.Le(1n+thread, 128n)
  {U32.to_nat(U32.from_nat(thread)) == thread : Nat} &
  ({U32.to_nat(U32.mul(4, U32.from_nat(thread))) == Nat.mul(thread, 4n) : Nat} &
  (Order.Le(Nat.mul(thread, 4n), 508n) &
    Order.Le(1n+Spec.scale_selected_index(thread), Spec.s_stage_int4s())))

law scale_lane_mask_fallback:
  for +mask: Nat
  for thread: Nat
  for +generic: Nat
  for fallback: {Nat.is_eq(mask, 85n) == False{} : Bool}
  {Spec.scale_masked_index(mask, thread, generic) == generic : Nat}

law scale_lane_production_mask:
  {scheduled_scale_mask(Impl.policy(True{}, True{}, True{})) == 85n : Nat} &
  {scheduled_scale_mask(Impl.policy(False{}, True{}, True{})) == 255n : Nat}

law scale_lane_policy_refinement:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {scheduled_scale_index(eligible, safe, deterministic, thread) ==
    Spec.scale_generic_index(thread) : Nat}

# No selected thread/geometry restriction is imposed on the retained arm.
law scale_lane_action0_fallback:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for thread: Nat
  for +generic: Nat
  for fallback: {Impl.policy(eligible, safe, deterministic) == 0n : Nat}
  {Spec.scale_masked_index(scheduled_scale_mask(Impl.policy(eligible, safe, deterministic)),
    thread, generic) == generic : Nat}

# All physical int4 slots, including the odd reserved holes, and the unchanged
# 2048-int4 scale base. Native group128 reads then use the rounded group slot.
law scale_lane_slot_address:
  for +stage: Nat
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.scale_slot_address(stage, Spec.scale_selected_index(thread)) ==
    Nat.add(2048n, Nat.add(Spec.scale_generic_index(thread), Nat.mul(stage, 16n))) : Nat}

law scale_lane_group_slots:
  {[Spec.scale_group_slot(0n), Spec.scale_group_slot(1n),
    Spec.scale_group_slot(2n), Spec.scale_group_slot(3n),
    Spec.scale_group_slot(4n), Spec.scale_group_slot(5n),
    Spec.scale_group_slot(6n), Spec.scale_group_slot(7n),
    Spec.scale_group_slot(8n)] == [0n, 0n, 2n, 2n, 4n, 4n, 6n, 6n, 0n] : List<&2, Nat>}

law scale_lane_address_refinement:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +tile: Nat
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {scheduled_scale_address(eligible, safe, deterministic, tile, thread) ==
    Spec.scale_generic_address(tile, thread) : Nat}

# Both endpoints of the complete sixteen-byte access, not just lane offsets.
# At odd phases these are hypothetical address operands, not issued loads.
law scale_lane_address_bytes:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +tile: Nat
  for +thread: Nat
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.bytes(scheduled_scale_address(eligible, safe, deterministic, tile, thread)) ==
    Spec.bytes(Spec.scale_generic_address(tile, thread)) : Nat} &
  {Spec.bytes(1n+scheduled_scale_address(eligible, safe, deterministic, tile, thread)) ==
    Spec.bytes(1n+Spec.scale_generic_address(tile, thread)) : Nat}

law scale_lane_address_wrap:
  for +mask: Nat
  for +tile: Nat
  for +thread: Nat
  {Spec.scale_selected_address(mask, 8n+tile, thread) ==
    Spec.scale_selected_address(mask, tile, thread) : Nat}

# Parametric memory observation connects address equality to BOTH bank values.
# It assumes no scale contents. CUDA visibility, actual load selection, bitcasts
# and the two-consumer ordering still require the existing native obligations.
law scale_lane_refresh_operands:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +tile: Nat
  for +thread: Nat
  for +previous: Spec.ScaleBanks
  for observe: Nat -> Spec.Scale
  for selected: {Impl.policy(eligible, safe, deterministic) == 1n : Nat}
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.refresh_zero(Impl.scale_refresh(Spec.slot(tile, 8n)),
    observe(scheduled_scale_address(eligible, safe, deterministic, tile, thread)), previous) ==
    Spec.refresh_zero(Impl.scale_refresh(Spec.slot(tile, 8n)),
      observe(Spec.scale_generic_address(tile, thread)), previous) : Spec.ScaleBanks}

# start_pipes uses (k,full_pipe)=(0,0), initially AND after each new-column
# restart. An arbitrary old bank0 is replaced; old bank1 is left for the
# unchanged bank0->bank1 copy. This does not use the previous ring phase.
law scale_lane_initial_restart:
  for +eligible: Bool
  for +safe: Bool
  for +deterministic: Bool
  for +thread: Nat
  for +old_zero: Spec.ScaleBank
  for +old_one: Spec.ScaleBank
  for observe: Nat -> Spec.Scale
  for selected: {Impl.policy(eligible, safe, deterministic) == 1n : Nat}
  for bounded: Order.Le(1n+thread, 128n)
  {Spec.refresh_zero(Impl.scale_refresh(0n),
    observe(scheduled_scale_address(eligible, safe, deterministic, 0n, thread)),
    Spec.ScaleBanks{old_zero, old_one}) ==
    Spec.ScaleBanks{Spec.Loaded{observe(Spec.scale_generic_address(0n, thread))}, old_one}
      : Spec.ScaleBanks}
