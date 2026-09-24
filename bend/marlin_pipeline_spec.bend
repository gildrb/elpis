# Independent policy and proof-only mathematical copy-ring/unroll model.
# Never import this module from marlin_pipeline.bend or the RUNTIME graph.
import Base
import ./spec.bend as Sequence

# Declarative accepted combination, independent of the nested production guards.
def policy(eligible: Bool, safe: Bool, deterministic: Bool) -> Nat:
  match eligible safe deterministic:
    case True{} True{} True{}:
      1n
    case _ _ _:
      0n

def bit(index: Nat) -> Bool:
  Nat.is_ne(Nat.mod(index, 2n), 0n)

def row(+index: Nat) -> Nat:
  policy(bit(index), bit(Nat.div(index, 2n)), bit(Nat.div(index, 4n)))

def Action(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Unit
        case 1n+q:
          Empty

# A mathematical physical slot and its grouped-scale phase. Period two is
# group_blocks/thread_k_blocks = 8/4, not the number of reduction CTAs.
def slot(tile: Nat, stages: Nat) -> Nat:
  Nat.mod(tile, stages)

def phase(tile: Nat) -> Nat:
  Nat.mod(tile, 2n)

# Separate unrolled schedules, including every partial final iteration. They
# model only logical tile visitation, not copies, waits, pointers or barriers.
# A chunk starts at the current logical tile; no padding tile executes an MMA.
# This is an actual eight-tile unroll with seven distinct nonempty short tails.
def tiles8(count: Nat, +start: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      match p:
        case 0n:
          [start]
        case 1n+q:
          match q:
            case 0n:
              Sequence.seq(2n, start)
            case 1n+r:
              match r:
                case 0n:
                  Sequence.seq(3n, start)
                case 1n+s:
                  match s:
                    case 0n:
                      Sequence.seq(4n, start)
                    case 1n+t:
                      match t:
                        case 0n:
                          Sequence.seq(5n, start)
                        case 1n+u:
                          match u:
                            case 0n:
                              Sequence.seq(6n, start)
                            case 1n+v:
                              match v:
                                case 0n:
                                  Sequence.seq(7n, start)
                                case 1n+rest:
                                  List.append(&2, Nat, Sequence.seq(8n, start), tiles8(rest, 8n+start))

def tiles4(count: Nat, +start: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      match p:
        case 0n:
          [start]
        case 1n+q:
          match q:
            case 0n:
              Sequence.seq(2n, start)
            case 1n+r:
              match r:
                case 0n:
                  Sequence.seq(3n, start)
                case 1n+rest:
                  List.append(&2, Nat, Sequence.seq(4n, start), tiles4(rest, 4n+start))

# Each selected K64 tile has b_sh_wr_iters=2. The ordered identifiers below
# mean the matmul(0), matmul(1) call sites at tile t, flattened as 2*t+j.
# They are NOT scalar products to sum or a license to reassociate F32.
def mma_terms(tiles: List<&2, Nat>) -> List<&2, Nat>:
  match tiles:
    case Nil{}:
      Nil{}
    case +tile <> rest:
      +base = Nat.add(tile, tile)
      base <> (1n+base) <> mma_terms(rest)

# Syntactic recurrence retains the previous accumulator as an operand of EACH
# ordered MMA. It assumes no algebraic properties and performs no arithmetic.
type Accumulator is Data:
  Initial{identity: Nat}
  MMA{previous: Accumulator, term: Nat}

def recurrence(terms: List<&2, Nat>, accumulator: Accumulator) -> Accumulator:
  match terms:
    case Nil{}:
      accumulator
    case term <> rest:
      recurrence(rest, MMA{accumulator, term})

# Independent source-derived access envelope, in int4 units until bytes().
# The native sh_red_size=272 is a nominal pointer-layout quantity, NOT the
# largest reduction access: j=0,2,4,6 and t%64 reach 64*6+63=447.
# B/reduction/output share a temporal overlay; these bounds do not prove its
# CUDA lifetime. The selected class has no g_idx, ZP or separate bias region.
def bytes(int4s: Nat) -> Nat:
  Nat.mul(int4s, 16n)

def b_stage_int4s() -> Nat:
  Nat.div(Nat.mul(64n, 128n), 32n)

def s_stage_int4s() -> Nat:
  Nat.div(128n, 8n)

def a_stage_int4s() -> Nat:
  Nat.div(Nat.mul(8n, 64n), 8n)

def nominal_reduction_int4s() -> Nat:
  Nat.mul(1n+Nat.mul(2n, 8n), 16n)

def cta_reduction_bytes() -> Nat:
  bytes(1n+Nat.add(Nat.mul(64n, 6n), 63n))

def bf16_reduction_bytes() -> Nat:
  bytes(1n+Nat.add(64n, 63n))

def fp32_reduction_bytes() -> Nat:
  bytes(1n+63n)

# M8 scalar writes: row term136*6, lane7, warp64, j48, pair8,
# second scalar136. The valid int4 output reads end at row7*17+15.
def output_write_bytes() -> Nat:
  Nat.mul(1n+Nat.add(Nat.mul(136n, 6n),
    Nat.add(7n, Nat.add(64n, Nat.add(48n, Nat.add(8n, 136n))))), 2n)

def output_read_bytes() -> Nat:
  bytes(1n+Nat.add(Nat.mul(7n, 17n), 15n))

def reduction_access_bytes() -> Nat:
  Nat.max(cta_reduction_bytes(), Nat.max(output_write_bytes(),
    Nat.max(output_read_bytes(), Nat.max(bf16_reduction_bytes(), fp32_reduction_bytes()))))

# This envelope includes actual accesses as well as the nominal native layout.
# rows=8 is the physical selected A tile EVEN FOR M1; rows=16 is only the
# conservative admission estimate. stages4/8 both have B dominating the overlay.
def shared_bytes(+stages: Nat, rows: Nat) -> Nat:
  overlay = Nat.max(reduction_access_bytes(),
    bytes(Nat.max(nominal_reduction_int4s(), Nat.mul(stages, b_stage_int4s()))))
  Nat.add(overlay, bytes(Nat.mul(stages,
    Nat.add(s_stage_int4s(), Nat.div(Nat.mul(rows, 64n), 8n)))))

# Native offsets, independently retaining its nominal max expression. The
# coverage laws below establish that the actual7168-byte reduction also fits.
def overlay_int4s() -> Nat:
  Nat.max(nominal_reduction_int4s(), Nat.mul(8n, b_stage_int4s()))

def scale_base_int4s() -> Nat:
  overlay_int4s()

def a_base_int4s() -> Nat:
  Nat.add(scale_base_int4s(), Nat.mul(8n, s_stage_int4s()))

def stage_base(base: Nat, stride: Nat, stage: Nat) -> Nat:
  bytes(Nat.add(base, Nat.mul(stage, stride)))

# Exclusive byte endpoint of one int4 access. Local-first addition makes the
# bounded-index proof structural; native integer/pointer refinement is external.
def access_end(base: Nat, stride: Nat, stage: Nat, local: Nat) -> Nat:
  bytes(Nat.add(base, Nat.add(1n+local, Nat.mul(stage, stride))))

def a_copy_active(rows: Nat, thread: Nat) -> Bool:
  Nat.is_lt(thread, Nat.mul(rows, 8n))

# x2 ldmatrix's first16 lane suppliers have lane_half=floor(lane/8)<2;
# warp_pair=floor(warp/2)<2, and k_half=k%2<2. Other lanes do not supply
# additional row fetches. The low-three-bit XOR permutes the resulting column;
# CUDA x2 semantics and the native swizzle correspondence remain external.
def a_supplier_column(lane_half: Nat, warp_pair: Nat, k_half: Nat) -> Nat:
  Nat.add(lane_half, Nat.add(Nat.mul(warp_pair, 2n), Nat.mul(k_half, 4n)))

def tile_index(stride: Nat, stage: Nat, local: Nat) -> Nat:
  Nat.add(local, Nat.mul(stage, stride))

# Exact selected grouped-scale lane algebra. The reference retains the native
# quotient/remainder expression; the candidate uses Base's actual U32 bits.
# Only t<128 is certified. Nat address arithmetic below does not certify CUDA
# signed conversions, pointer arithmetic, load visibility or BF16 contents.
def scale_generic_index(+thread: Nat) -> Nat:
  Nat.add(Nat.mul(8n, Nat.mod(Nat.div(thread, 32n), 2n)),
    Nat.div(Nat.mod(thread, 32n), 4n))

def scale_selected_index(thread: Nat) -> Nat:
  U32.to_nat(U32.and(U32.shrn(U32.from_nat(thread), 2n), 15))

# The emitted byte offset (4*t)&240, independently expressed in U32.
def scale_emitted_bytes(thread: Nat) -> Nat:
  U32.to_nat(U32.and(U32.mul(4, U32.from_nat(thread)), 240))

# Arbitrary generic values keep EVERY non-85 mask's caller-provided layout,
# including native group=-1 variants outside the selected grouped geometry.
def scale_masked_index(mask: Nat, +thread: Nat, generic: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_eq(mask, 85n), scale_selected_index(thread), generic)

# A proof-only finite certificate, never a production table or runtime list.
# Besides the two exact equalities it records representable input/product and
# the full int4 lane domain. The product equality rules out U32 wrap, rather
# than silently interpreting modular multiplication as Nat multiplication.
def scale_lane_ok(+thread: Nat) -> Bool:
  Bool.and(Nat.is_eq(scale_selected_index(thread), scale_generic_index(thread)),
    Bool.and(Nat.is_eq(scale_emitted_bytes(thread), bytes(scale_selected_index(thread))),
      Bool.and(Nat.is_lt(scale_selected_index(thread), 16n),
        Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
          Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))))))

def scale_lane_rows(count: Nat, +start: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(scale_lane_ok(start), scale_lane_rows(p, 1n+start))

# Raw reserved physical slots include odd holes. Actual grouped-scale reads
# round pipe to 2*(pipe/2); equality for an odd phase is only address algebra,
# NOT a claim that the mask85 schedule issues an LDS on that phase.
def scale_slot_address(stage: Nat, local: Nat) -> Nat:
  Nat.add(scale_base_int4s(), tile_index(s_stage_int4s(), stage, local))

def scale_group_slot(tile: Nat) -> Nat:
  Nat.mul(2n, Nat.div(slot(tile, 8n), 2n))

def scale_generic_address(tile: Nat, thread: Nat) -> Nat:
  Nat.add(scale_base_int4s(), Nat.add(scale_generic_index(thread),
    Nat.mul(Nat.mul(2n, Nat.div(Nat.mod(tile, 8n), 2n)), s_stage_int4s())))

def scale_selected_address(mask: Nat, tile: Nat, +thread: Nat) -> Nat:
  scale_slot_address(scale_group_slot(tile),
    scale_masked_index(mask, thread, scale_generic_index(thread)))

def cta_reduction_index(pair: Nat, thread_mod64: Nat) -> Nat:
  Nat.add(thread_mod64, Nat.mul(pair, 128n))

# Arithmetic parameters from start_pipes and wait_for_stage, not an operational
# CUDA model. Each fetch_to_shared commits once even with pred=False. Under the
# native per-thread wait semantics, priming S-1 groups and thereafter committing
# once after each wait(S-2) bounds pending committed groups by S-1 (7 at S=8),
# below the eight-group hardware limit. Hardware semantics, instruction lowering,
# barriers and memory/reuse ordering remain external correspondence obligations.
def prime_groups(stages: Nat) -> Nat:
  Nat.sub(stages, 1n)

def wait_groups(stages: Nat) -> Nat:
  Nat.sub(stages, 2n)

# Independent full wire literal: existing controls, new section, row order and
# no trailing newline (IO.print supplies it). No production serializer is used.
def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V7\nFREE_MIRROR\n8\n0\n0\n0\n0\n1\n0\n1\n1\nSTATUS\n8\n0\n2\n0\n1\n0\n2\n0\n1\nMARLIN_EIGHT_STAGE\n8\n0\n0\n0\n0\n0\n0\n0\n1\nMARLIN_SCALE_REFRESH\n8\n1\n0\n1\n0\n1\n0\n1\n0\nPACKED_LATE_VALUE\n4\n0\n0\n0\n1\nPACKED_INVERSE_PARTNER\n4\n0\n0\n0\n1\nPACKED_FORWARD_PARTNER_STAGES\n4\n0\n0\n0\n3\nMARLIN_SELECTED_SHARED_BYTES\n1\n43008\nEND_QWEN_RUNTIME_CONTROL"

# Independent pair countdown, not modulo or the production table builder.
def scale_refresh_row(index: Nat) -> Nat:
  match index:
    case 0n:
      1n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+rest:
          scale_refresh_row(rest)

def packed_refresh(rows: List<&2, Nat>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case row <> rest:
      Nat.add(row, Nat.double(packed_refresh(rest)))

# A Scale is the uninterpreted operand S(column,group,element), not its bits.
# All three identifiers are arbitrary. Equality of these terms is preserved by
# any interpretation of S, including distinct values at every group/column.
# Native address correspondence and actual BF16 contents are external.
type Scale is Data:
  Scale{column: Nat, group: Nat, element: Nat}

type ScaleBank is Data:
  Uninitialized{}
  Loaded{scale: Scale}

type ScaleBanks is Data:
  ScaleBanks{zero: ScaleBank, one: ScaleBank}

# Aligned slices start on First{group}, meaning absolute K64 tile 2*group.
# This semantic group cursor has no ring, mask or compiled refresh decision.
type GroupCursor is Data:
  First{group: Nat}
  Second{group: Nat}

def next_group(cursor: GroupCursor) -> GroupCursor:
  match cursor:
    case First{group}:
      Second{group}
    case Second{group}:
      First{1n+group}

def required_scale(cursor: GroupCursor, column: Nat, element: Nat) -> Scale:
  match cursor:
    case First{group}:
      Scale{column, group, element}
    case Second{group}:
      Scale{column, group, element}

# Independent retained-cache machine compares semantic identities. In
# particular, it does not trust that an odd tile is initialized or belongs to
# the same column. Startup/reset can present any previous bank.
def same_scale(left: Scale, right: Scale) -> Bool:
  match left right:
    case Scale{lc, lg, le} Scale{rc, rg, re}:
      Bool.and(Nat.is_eq(lc, rc), Bool.and(Nat.is_eq(lg, rg), Nat.is_eq(le, re)))

def retain_equal(same: Bool, needed: Scale, previous: ScaleBank) -> ScaleBank:
  match same:
    case False{}:
      Loaded{needed}
    case True{}:
      previous

def reference_cache(+needed: Scale, previous: ScaleBank) -> ScaleBank:
  match previous:
    case Uninitialized{}:
      Loaded{needed}
    case Loaded{+old}:
      retain_equal(same_scale(needed, old), needed, Loaded{old})

def load_scale(refresh: Nat, needed: Scale, previous: ScaleBank) -> ScaleBank:
  match refresh:
    case 0n:
      previous
    case 1n+p:
      Loaded{needed}

def copy_scale(banks: ScaleBanks) -> ScaleBanks:
  match banks:
    case ScaleBanks{+zero, one}:
      ScaleBanks{zero, zero}

def refresh_zero(refresh: Nat, needed: Scale, banks: ScaleBanks) -> ScaleBanks:
  match banks:
    case ScaleBanks{zero, one}:
      ScaleBanks{load_scale(refresh, needed, zero), one}

def bank_zero(banks: ScaleBanks) -> ScaleBank:
  match banks:
    case ScaleBanks{zero, one}:
      zero

def bank_one(banks: ScaleBanks) -> ScaleBank:
  match banks:
    case ScaleBanks{zero, one}:
      one

# Free constructors encode the exact previous-accumulator recurrence; no
# arithmetic, associativity, F32 rounding or instruction identity is assumed.
type ScaleAccumulator is Data:
  ScaleInitial{identity: Nat}
  ScaleMMA{previous: ScaleAccumulator, term: Nat, operand: ScaleBank}

def accumulate_scale_tile(+tile: Nat, +operand: ScaleBank,
    accumulator: ScaleAccumulator) -> ScaleAccumulator:
  ScaleMMA{ScaleMMA{accumulator, Nat.double(tile), operand},
    1n+Nat.double(tile), operand}

# Operand snapshots for the two ordered consumers; this helper imposes no
# refresh order. The selected delayed schedule passes the same copied banks.
def consume_scale_tile(+tile: Nat, copied: ScaleBanks, one_snapshot: ScaleBanks,
    accumulator: ScaleAccumulator) -> ScaleAccumulator:
  ScaleMMA{ScaleMMA{accumulator, Nat.double(tile), bank_zero(copied)},
    1n+Nat.double(tile), bank_one(one_snapshot)}

# Pure state transitions expose refresh placement as composition, not as a
# claim about evaluation order or CUDA instruction scheduling. matmul(1) reads
# bank1 and changes only the accumulator; refresh changes only bank0.
type ScaleTileState is Data:
  ScaleTileState{banks: ScaleBanks, accumulator: ScaleAccumulator}

def scale_state_banks(state: ScaleTileState) -> ScaleBanks:
  match state:
    case ScaleTileState{banks, accumulator}:
      banks

def scale_state_accumulator(state: ScaleTileState) -> ScaleAccumulator:
  match state:
    case ScaleTileState{banks, accumulator}:
      accumulator

def consume_scale_one(tile: Nat, state: ScaleTileState) -> ScaleTileState:
  match state:
    case ScaleTileState{+banks, accumulator}:
      ScaleTileState{banks, ScaleMMA{accumulator, 1n+Nat.double(tile), bank_one(banks)}}

def refresh_scale_state(refresh: Nat, needed: Scale, state: ScaleTileState) -> ScaleTileState:
  match state:
    case ScaleTileState{banks, accumulator}:
      ScaleTileState{refresh_zero(refresh, needed, banks), accumulator}

# The selected nondefault-mask geometry has exactly two consumers. The bank0
# to bank1 copy precedes matmul(0); BOTH consumers precede next-tile refresh.
# The unchanged incremented pipe supplies refresh/needed, including wrap and
# the speculative final-tile refresh. Default-mask native ordering is unchanged
# and is not represented by this delayed transition.
def delayed_scale_tile(tile: Nat, refresh: Nat, next: Scale, +copied: ScaleBanks,
    accumulator: ScaleAccumulator) -> ScaleTileState:
  refresh_scale_state(refresh, next,
    ScaleTileState{copied, consume_scale_tile(tile, copied, copied, accumulator)})

# Independent reference always asks for the current semantic group's operand;
# it knows nothing about banks, ring length, masks, prefetch or retention.
def reference_scale_run(count: Nat, +tile: Nat, +cursor: GroupCursor,
    +column: Nat, +element: Nat, accumulator: ScaleAccumulator) -> ScaleAccumulator:
  match count:
    case 0n:
      accumulator
    case 1n+p:
      reference_scale_run(p, 1n+tile, next_group(cursor), column, element,
        accumulate_scale_tile(tile, Loaded{required_scale(cursor, column, element)}, accumulator))

# FP32 global transfer is a proof-only, bit-pattern/ordered-source model.
# Scratch vectors and accumulator coordinates are different address spaces.
# No interpretation of FP32Add (including IEEE addition) is supplied here.
def fp32_scratch_index(lock: Nat, pair: Nat, lane: Nat) -> Nat:
  Nat.add(Nat.mul(lock, 512n), Nat.add(Nat.mul(pair, 128n), lane))

def fp32_accumulator_index(pair: Nat, component: Nat) -> Nat:
  Nat.add(Nat.mul(pair, 8n), component)

# Independent retained-source address, not an alias of the selected helper.
def fp32_reference_index(lock: Nat, pair: Nat, lane: Nat) -> Nat:
  Nat.add(Nat.mul(lock, 512n), Nat.add(Nat.mul(pair, 128n), lane))

type FP32Word is Data:
  ScratchBits{vector: Nat, component: Nat}

type FP32Value is Data:
  FP32Initial{identity: Nat, coordinate: Nat}
  FP32Add{left: FP32Value, right: FP32Word}

type FP32LaneCell is Data:
  FP32LaneCell{owner: Nat, vector: Nat}

def fp32_stage(lane: Nat, vector: Nat) -> FP32LaneCell:
  FP32LaneCell{lane, vector}

# The caller passes the cell it just wrote, never another lane's cell.
def fp32_read_staged(cell: FP32LaneCell, component: Nat) -> FP32Word:
  match cell:
    case FP32LaneCell{owner, vector}:
      ScratchBits{vector, component}

def fp32_word(action: Nat, +lock: Nat, +pair: Nat, +lane: Nat, component: Nat) -> FP32Word:
  match action:
    case 0n:
      fp32_read_staged(fp32_stage(lane, fp32_reference_index(lock, pair, lane)), component)
    case 1n+p:
      ScratchBits{fp32_scratch_index(lock, pair, lane), component}

def fp32_value(first: Bool, action: Nat, lock: Nat, +pair: Nat, lane: Nat,
    +component: Nat, identity: Nat) -> FP32Value:
  match first:
    case True{}:
      FP32Initial{identity, fp32_accumulator_index(pair, component)}
    case False{}:
      FP32Add{FP32Initial{identity, fp32_accumulator_index(pair, component)},
        fp32_word(action, lock, pair, lane, component)}

type FP32Event is Data:
  ScratchRead{vector: Nat}
  AccumulatorWrite{coordinate: Nat, value: FP32Value}
  ScratchWrite{vector: Nat, values: List<&2, FP32Value>}

def fp32_pair_values(+first: Bool, +action: Nat, +lock: Nat, +pair: Nat,
    +lane: Nat, +identity: Nat) -> List<&2, FP32Value>:
  [fp32_value(first, action, lock, pair, lane, 0n, identity),
    fp32_value(first, action, lock, pair, lane, 1n, identity),
    fp32_value(first, action, lock, pair, lane, 2n, identity),
    fp32_value(first, action, lock, pair, lane, 3n, identity)]

def fp32_pair_events(+action: Nat, +lock: Nat, +pair: Nat, +lane: Nat,
    +identity: Nat) -> List<&2, FP32Event>:
  [ScratchRead{fp32_scratch_index(lock, pair, lane)},
    AccumulatorWrite{fp32_accumulator_index(pair, 0n), fp32_value(False{}, action, lock, pair, lane, 0n, identity)},
    AccumulatorWrite{fp32_accumulator_index(pair, 1n), fp32_value(False{}, action, lock, pair, lane, 1n, identity)},
    AccumulatorWrite{fp32_accumulator_index(pair, 2n), fp32_value(False{}, action, lock, pair, lane, 2n, identity)},
    AccumulatorWrite{fp32_accumulator_index(pair, 3n), fp32_value(False{}, action, lock, pair, lane, 3n, identity)}]

def fp32_add_events(first: Bool, +action: Nat, +lock: Nat, +lane: Nat,
    +identity: Nat) -> List<&2, FP32Event>:
  match first:
    case True{}:
      Nil{}
    case False{}:
      List.append(&2, FP32Event, fp32_pair_events(action, lock, 0n, lane, identity),
        List.append(&2, FP32Event, fp32_pair_events(action, lock, 1n, lane, identity),
          List.append(&2, FP32Event, fp32_pair_events(action, lock, 2n, lane, identity),
            fp32_pair_events(action, lock, 3n, lane, identity))))

def fp32_store_events(last: Bool, +first: Bool, +action: Nat, +lock: Nat,
    +lane: Nat, +identity: Nat) -> List<&2, FP32Event>:
  match last:
    case True{}:
      Nil{}
    case False{}:
      [ScratchWrite{fp32_scratch_index(lock, 0n, lane), fp32_pair_values(first, action, lock, 0n, lane, identity)},
        ScratchWrite{fp32_scratch_index(lock, 1n, lane), fp32_pair_values(first, action, lock, 1n, lane, identity)},
        ScratchWrite{fp32_scratch_index(lock, 2n, lane), fp32_pair_values(first, action, lock, 2n, lane, identity)},
        ScratchWrite{fp32_scratch_index(lock, 3n, lane), fp32_pair_values(first, action, lock, 3n, lane, identity)}]

def fp32_values(+first: Bool, +action: Nat, +lock: Nat, +lane: Nat,
    +identity: Nat) -> List<&2, FP32Value>:
  List.append(&2, FP32Value, fp32_pair_values(first, action, lock, 0n, lane, identity),
    List.append(&2, FP32Value, fp32_pair_values(first, action, lock, 1n, lane, identity),
      List.append(&2, FP32Value, fp32_pair_values(first, action, lock, 2n, lane, identity),
        fp32_pair_values(first, action, lock, 3n, lane, identity))))

# Publication describes only the later output's input fragments. BF16
# conversion, scatter/gather, and the release barrier are native obligations.
type FP32Publication is Data:
  NoOutput{}
  OutputFragments{values: List<&2, FP32Value>}

def fp32_publication(last: Bool, values: List<&2, FP32Value>) -> FP32Publication:
  match last:
    case False{}:
      NoOutput{}
    case True{}:
      OutputFragments{values}

type FP32Observable is Data:
  FP32Inactive{identity: Nat}
  FP32Observable{values: List<&2, FP32Value>, events: List<&2, FP32Event>, output: FP32Publication}

# This is the intentionally unobserved shared difference, not an assertion
# that the actual overlay is disjoint. D is the first64 lane-owned int4s.
type FP32Shared is Data:
  SharedBefore{identity: Nat}
  SharedStaged{lane: Nat, vector: Nat, previous: FP32Shared}

def fp32_shared(action: Nat, first: Bool, +lock: Nat, +lane: Nat,
    previous: FP32Shared) -> FP32Shared:
  match action:
    case 0n:
      match first:
        case True{}:
          previous
        case False{}:
          SharedStaged{lane, fp32_reference_index(lock, 3n, lane), previous}
    case 1n+p:
      previous

type FP32State is Data:
  FP32State{observable: FP32Observable, shared: FP32Shared}

def fp32_transfer(active: Bool, +first: Bool, +last: Bool, +action: Nat,
    +lock: Nat, +lane: Nat, +identity: Nat, previous: FP32Shared) -> FP32State:
  match active:
    case False{}:
      FP32State{FP32Inactive{identity}, previous}
    case True{}:
      +values = fp32_values(first, action, lock, lane, identity)
      FP32State{FP32Observable{values,
        List.append(&2, FP32Event, fp32_add_events(first, action, lock, lane, identity),
          fp32_store_events(last, first, action, lock, lane, identity)),
        fp32_publication(last, values)}, fp32_shared(action, first, lock, lane, previous)}

def fp32_observable(state: FP32State) -> FP32Observable:
  match state:
    case FP32State{observable, shared}:
      observable

def fp32_shared_state(state: FP32State) -> FP32Shared:
  match state:
    case FP32State{observable, shared}:
      shared

# Concrete output scalar_t indices and inverse for the selected physical M8.
# Scatter writes all8 rows regardless of logical M. Padding columns128..135
# are not written and not observed. In particular not all of D is overwritten.
def fp32_output_address(row: Nat, column: Nat) -> Nat:
  Nat.add(Nat.mul(row, 136n), column)

def fp32_output_thread(row: Nat, +column: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(column, 64n), 32n),
    Nat.add(Nat.mul(Nat.mod(column, 8n), 4n), Nat.div(row, 2n)))

def fp32_output_j(column: Nat) -> Nat:
  Nat.div(Nat.mod(column, 64n), 16n)

def fp32_output_pair(column: Nat) -> Nat:
  Nat.div(Nat.mod(column, 16n), 8n)

def fp32_output_scalar(row: Nat) -> Nat:
  Nat.mod(row, 2n)

def fp32_output_scatter(+thread: Nat, j: Nat, pair: Nat, scalar: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.double(Nat.mod(thread, 4n)), 136n),
    Nat.add(Nat.div(Nat.mod(thread, 32n), 4n),
      Nat.add(Nat.mul(Nat.div(thread, 32n), 64n),
        Nat.add(Nat.mul(j, 16n), Nat.add(Nat.mul(pair, 8n), Nat.mul(scalar, 136n))))))

def fp32_output_writer(+row: Nat, +column: Nat) -> Nat:
  fp32_output_scatter(fp32_output_thread(row, column), fp32_output_j(column),
    fp32_output_pair(column), fp32_output_scalar(row))

# Vector17*r+floor(c/8), component c%8: all eight two-byte scalars of
# every valid int4 gather are represented, not just the vector's base address.
def fp32_output_reader(row: Nat, +column: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(row, 17n), Nat.div(column, 8n)), 8n),
    Nat.mod(column, 8n))

def fp32_output_observed(rows: Nat, row: Nat, column: Nat) -> Bool:
  Bool.and(Nat.is_lt(row, rows), Nat.is_lt(column, 128n))

# A closed finite arithmetic predicate, later eliminated with Order.Le.
# It is proof-only and does not introduce production runtime lists or checks.
def fp32_output_coordinate_ok(+row: Nat, +column: Nat) -> Bool:
  Bool.and(Nat.is_lt(fp32_output_thread(row, column), 64n),
    Bool.and(Nat.is_lt(fp32_output_j(column), 4n),
      Bool.and(Nat.is_lt(fp32_output_pair(column), 2n),
        Bool.and(Nat.is_lt(fp32_output_scalar(row), 2n),
          Bool.and(Nat.is_eq(fp32_output_writer(row, column), fp32_output_address(row, column)),
            Nat.is_eq(fp32_output_reader(row, column), fp32_output_address(row, column)))))))
def fp32_output_columns(count: Nat, +row: Nat, +start: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(fp32_output_coordinate_ok(row, start), fp32_output_columns(p, row, 1n+start))

def fp32_output_rows(count: Nat, +start: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(fp32_output_columns(128n, start, 0n), fp32_output_rows(p, 1n+start))
type FP32OverlayObservation is Data:
  PriorOverlay{address: Nat, shared: FP32Shared}
  OverwrittenOverlay{address: Nat, identity: Nat}

def fp32_overwrite_observe(covered: Bool, address: Nat, identity: Nat,
    shared: FP32Shared) -> FP32OverlayObservation:
  match covered:
    case False{}:
      PriorOverlay{address, shared}
    case True{}:
      OverwrittenOverlay{address, identity}

def fp32_output_after(+row: Nat, +column: Nat, identity: Nat,
    state: FP32State) -> FP32OverlayObservation:
  fp32_overwrite_observe(Nat.is_eq(fp32_output_writer(row, column), fp32_output_reader(row, column)),
    fp32_output_reader(row, column), identity, fp32_shared_state(state))

def fp32_deleted_byte(lane: Nat, byte: Nat) -> Nat:
  Nat.add(Nat.mul(lane, 16n), byte)

def fp32_restart_byte(iteration: Nat, thread: Nat, byte: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(iteration, 128n), thread), 16n), byte)

# waited=True is an explicit conditional boundary, not inferred CUDA semantics.
# Every nonempty restart issues stage0 B writes for i=0,1 and t=0..127.
def fp32_restart_after(waited: Bool, +lane: Nat, +byte: Nat, identity: Nat,
    state: FP32State) -> FP32OverlayObservation:
  fp32_overwrite_observe(Bool.and(waited,
    Nat.is_eq(fp32_restart_byte(0n, lane, byte), fp32_deleted_byte(lane, byte))),
    fp32_deleted_byte(lane, byte), identity, fp32_shared_state(state))

# Proof-only host split and kernel M normalization. The retry constructors
# enumerate max_thread_m_blocks=4,3,2,1, including failed-config retries before
# the same rest_m is launched. Native max_par is16 or128; the proof permits any.
type MRetry is Data:
  Retry4{}
  Retry3{}
  Retry2{}
  Retry1{}

def retry_divisor(retry: MRetry) -> Nat:
  match retry:
    case Retry4{}:
      64n
    case Retry3{}:
      48n
    case Retry2{}:
      32n
    case Retry1{}:
      16n

def host_par_count(rows: Nat, divisor: Nat, max_par: Nat) -> Nat:
  Nat.min(Nat.div(rows, divisor), max_par)

def host_split_count(count: Nat, rows: Nat, divisor: Nat) -> Nat:
  match count:
    case 0n:
      rows
    case 1n+p:
      Nat.mul(1n+p, divisor)

def host_split(+rows: Nat, +divisor: Nat, max_par: Nat) -> Nat:
  host_split_count(host_par_count(rows, divisor, max_par), rows, divisor)

type MNormalization is Data:
  MNormalization{parallel: Nat, rows: Nat}

# Independent retained-source branch: the comparison is strict, and the
# quotient uses the original rows before the effective M is clamped.
def original_normalization(+rows: Nat, +block: Nat) -> MNormalization:
  Bool.pick(MNormalization, Nat.is_gt(rows, block),
    MNormalization{Nat.div(rows, block), block}, MNormalization{1n, rows})

# Exactly action1 bypasses normalization. The actual policy has range{0,1};
# other mathematical actions also keep the reference, not a positive-action gate.
def normalization(action: Nat, +rows: Nat, block: Nat) -> MNormalization:
  Bool.pick(MNormalization, Nat.is_eq(action, 1n),
    MNormalization{1n, rows}, original_normalization(rows, block))

def normalization_parallel(normalized: MNormalization) -> Nat:
  match normalized:
    case MNormalization{parallel, rows}:
      parallel

def normalization_rows(normalized: MNormalization) -> Nat:
  match normalized:
    case MNormalization{parallel, rows}:
      rows

def normalization_predicates(normalized: MNormalization, thread: Nat, +row: Nat,
    column: Nat) -> List<&2, Bool>:
  match normalized:
    case MNormalization{parallel, +rows}:
      [a_copy_active(rows, thread), Nat.is_lt(row, rows),
        fp32_output_observed(rows, row, column)]

# Selected group128/K64 rounds stripe length to a multiple of two. Divisors
# k,n,grid must be positive in native, and all intermediate products in range.
def ceil_div(value: Nat, +divisor: Nat) -> Nat:
  Nat.div(Nat.add(value, Nat.sub(divisor, 1n)), divisor)

def stripe_iterations(normalized: MNormalization, k: Nat, n: Nat, grid: Nat) -> Nat:
  Nat.mul(2n, ceil_div(ceil_div(Nat.mul(Nat.mul(k, n),
    normalization_parallel(normalized)), grid), 2n))

# Inputs/decisions used by native init_slice and lock routing, not an
# operational lock machine. Keep the idle-CTA remapping even when parallel=1.
type StripeObservation is Data:
  StripeObservation{iters: Nat, row: Nat, column_par: Nat, column: Nat,
    par_id: Nat, dense_locks: Bool, normalized: MNormalization}

def stripe_observation(+normalized: MNormalization, +k: Nat, +n: Nat,
    +grid: Nat, block: Nat) -> StripeObservation:
  +iters = stripe_iterations(normalized, k, n, grid)
  +flat = Nat.mul(iters, block)
  +column_par = Nat.div(flat, k)
  +remap = Nat.is_ge(column_par, n)
  StripeObservation{iters, Nat.mod(flat, k), column_par,
    Bool.pick(Nat, remap, Nat.mod(column_par, n), column_par),
    Bool.pick(Nat, remap, Nat.div(column_par, n), 0n),
    Nat.is_ge(Nat.mul(normalization_parallel(normalized), n), grid), normalized}

# Native clamps negative work and exhausted/idle columns to zero. Nat.sub
# models that clamp, not signed C++ subtraction or overflow. Arbitrary row and
# column include initial slices and restarts (row=0, column_par incremented).
def slice_work(+normalized: MNormalization, +k: Nat, +n: Nat, grid: Nat,
    block: Nat, +column: Nat, +row: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(column, Nat.mul(n, normalization_parallel(normalized))),
    Nat.min(Nat.sub(k, row),
      Nat.sub(Nat.mul(stripe_iterations(normalized, k, n, grid), 1n+block),
        Nat.add(Nat.mul(k, column), row))), 0n)
