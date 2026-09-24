# Constructor proofs and structural Nat/list induction; no assumed native facts.
# Main owns the pinned-toolchain root proof/production checks after this freezes.
import Base
import ./marlin_pipeline.bend as Impl
import ./marlin_pipeline_spec.bend as Spec
import ./marlin_pipeline_laws.bend as Laws
import ./spec.bend as Sequence
import ./numerical_proof.bend as NumericalProof
import ./numerical_spec.bend as Order

# The complete three-Boolean domain, independent from the table enumeration.
def Laws.policy_refinement(eligible, safe, deterministic):
  match eligible safe deterministic:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Laws.action_range(eligible, safe, deterministic):
  match eligible:
    case False{}:
      Unit{}
    case True{}:
      match safe:
        case False{}:
          Unit{}
        case True{}:
          match deterministic:
            case False{}:
              Unit{}
            case True{}:
              Unit{}

def Laws.ineligible_fallback(safe, deterministic):
  {==}

def Laws.unsafe_fallback(eligible, deterministic):
  match eligible:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.atomic_fallback(eligible, safe):
  match eligible:
    case False{}:
      {==}
    case True{}:
      match safe:
        case False{}:
          {==}
        case True{}:
          {==}

def Laws.eight_stage_progress():
  {==}

def Laws.table_order():
  {==}

def Laws.table_lookup(eligible, safe, deterministic):
  match eligible safe deterministic:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Laws.wire_exact():
  {==}

# The remainder of Base's actual countdown division worker is independent of
# the accumulated quotient. This proves the wrap equations rather than assuming
# arithmetic modulo laws or checking a bounded number of wraps.
def remainder_quotient(n: Nat, m: Nat, left: Nat, right: Nat, r: Nat)
  -> {Nat.mod.fin(Nat.divmod.go(n, m, left, r)) ==
    Nat.mod.fin(Nat.divmod.go(n, m, right, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match m:
        case 0n:
          remainder_quotient(p, r, 1n+left, 1n+right, 0n)
        case 1n+q:
          remainder_quotient(p, q, left, right, 1n+r)

def mod2_period(n: Nat) -> {Nat.mod(2n+n, 2n) == Nat.mod(n, 2n) : Nat}:
  remainder_quotient(n, 1n, 1n, 0n, 0n)

def mod4_period(n: Nat) -> {Nat.mod(4n+n, 4n) == Nat.mod(n, 4n) : Nat}:
  remainder_quotient(n, 3n, 1n, 0n, 0n)

def mod8_period(n: Nat) -> {Nat.mod(8n+n, 8n) == Nat.mod(n, 8n) : Nat}:
  remainder_quotient(n, 7n, 1n, 0n, 0n)

def phase_period4(+n: Nat) -> {Spec.phase(4n+n) == Spec.phase(n) : Nat}:
  Equal.trans(Nat, Spec.phase(4n+n), Spec.phase(2n+n), Spec.phase(n),
    mod2_period(2n+n), mod2_period(n))

def phase_period8(+n: Nat) -> {Spec.phase(8n+n) == Spec.phase(n) : Nat}:
  Equal.trans(Nat, Spec.phase(8n+n), Spec.phase(4n+n), Spec.phase(n),
    phase_period4(4n+n), phase_period4(n))

def Laws.ring8_group_phase(tile):
  match tile:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  {==}
                case 1n+s:
                  match s:
                    case 0n:
                      {==}
                    case 1n+t:
                      match t:
                        case 0n:
                          {==}
                        case 1n+u:
                          match u:
                            case 0n:
                              {==}
                            case 1n+v:
                              match v:
                                case 0n:
                                  {==}
                                case 1n+rest:
                                  Equal.trans(Nat, Spec.phase(Spec.slot(8n+rest, 8n)),
                                    Spec.phase(Spec.slot(rest, 8n)), Spec.phase(8n+rest),
                                    Equal.cong(Nat, Nat, Spec.phase,
                                      Spec.slot(8n+rest, 8n), Spec.slot(rest, 8n), mod8_period(rest)),
                                    Equal.trans(Nat, Spec.phase(Spec.slot(rest, 8n)),
                                      Spec.phase(rest), Spec.phase(8n+rest), Laws.ring8_group_phase(rest),
                                      Equal.sym(Nat, Spec.phase(8n+rest), Spec.phase(rest), phase_period8(rest))))

def Laws.ring4_group_phase(tile):
  match tile:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  {==}
                case 1n+rest:
                  Equal.trans(Nat, Spec.phase(Spec.slot(4n+rest, 4n)),
                    Spec.phase(Spec.slot(rest, 4n)), Spec.phase(4n+rest),
                    Equal.cong(Nat, Nat, Spec.phase,
                      Spec.slot(4n+rest, 4n), Spec.slot(rest, 4n), mod4_period(rest)),
                    Equal.trans(Nat, Spec.phase(Spec.slot(rest, 4n)),
                      Spec.phase(rest), Spec.phase(4n+rest), Laws.ring4_group_phase(rest),
                      Equal.sym(Nat, Spec.phase(4n+rest), Spec.phase(rest), phase_period4(rest))))

# Destructure the proof parameter, never a computed recursive result.
def group_pair_step(+p: Nat,
    phases: {Spec.phase(Nat.double(p)) == 0n : Nat} &
      {Spec.phase(1n+Nat.double(p)) == 1n : Nat})
  -> {Spec.phase(Nat.double(1n+p)) == 0n : Nat} &
    {Spec.phase(1n+Nat.double(1n+p)) == 1n : Nat}:
  (even, odd) = phases
  (Equal.trans(Nat, Spec.phase(2n+Nat.double(p)), Spec.phase(Nat.double(p)),
    0n, mod2_period(Nat.double(p)), even),
   Equal.trans(Nat, Spec.phase(3n+Nat.double(p)), Spec.phase(1n+Nat.double(p)),
    1n, mod2_period(1n+Nat.double(p)), odd))

def Laws.group_pair_phase(group):
  match group:
    case 0n:
      ({==}, {==})
    case 1n+p:
      group_pair_step(p, Laws.group_pair_phase(p))

# Unroll boundaries are traversed structurally, including every short tail;
# no divisibility or padding assumption restricts the logical tile count.
def Laws.tiles8_exact(count, start):
  match count:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  {==}
                case 1n+s:
                  match s:
                    case 0n:
                      {==}
                    case 1n+t:
                      match t:
                        case 0n:
                          {==}
                        case 1n+u:
                          match u:
                            case 0n:
                              {==}
                            case 1n+v:
                              match v:
                                case 0n:
                                  {==}
                                case 1n+rest:
                                  Equal.cong(List<&2, Nat>, List<&2, Nat>,
                                    xs => start <> (1n+start) <> (2n+start) <> (3n+start) <>
                                      (4n+start) <> (5n+start) <> (6n+start) <> (7n+start) <> xs,
                                    Spec.tiles8(rest, 8n+start), Sequence.seq(rest, 8n+start),
                                    Laws.tiles8_exact(rest, 8n+start))

def Laws.tiles4_exact(count, start):
  match count:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  {==}
                case 1n+rest:
                  Equal.cong(List<&2, Nat>, List<&2, Nat>,
                    xs => start <> (1n+start) <> (2n+start) <> (3n+start) <> xs,
                    Spec.tiles4(rest, 4n+start), Sequence.seq(rest, 4n+start),
                    Laws.tiles4_exact(rest, 4n+start))

# Sequence.Ordered is the existing exact-length/no-gap/no-duplicate contract.
# Its proof is local because importing the root PROOF would create a cycle.
def seq_ordered(n: Nat, +start: Nat) -> Sequence.Ordered(n, start, Sequence.seq(n, start)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      ({==}, seq_ordered(p, 1n+start))

def ordered_transport(+n: Nat, +start: Nat, +xs: List<&2, Nat>,
    equal: {xs == Sequence.seq(n, start) : List<&2, Nat>})
  -> Sequence.Ordered(n, start, xs):
  %Equal.sym(List<&2, Nat>, xs, Sequence.seq(n, start), equal) :
    Sequence.Ordered(n, start, _)
  seq_ordered(n, start)

def Laws.tiles_ordered(count, start):
  (ordered_transport(count, start, Spec.tiles8(count, start), Laws.tiles8_exact(count, start)),
    ordered_transport(count, start, Spec.tiles4(count, start), Laws.tiles4_exact(count, start)))

# Existing numerical double_add connects the independent t+t term encoding to
# the canonical doubled interval; no new arithmetic or floating axiom is used.
def mma_sequence(+count: Nat, +start: Nat)
  -> {Spec.mma_terms(Sequence.seq(count, start)) ==
    Sequence.seq(Nat.double(count), Nat.double(start)) : List<&2, Nat>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(List<&2, Nat>, Spec.mma_terms(Sequence.seq(1n+p, start)),
        Nat.double(start) <> (1n+Nat.double(start)) <> Spec.mma_terms(Sequence.seq(p, 1n+start)),
        Sequence.seq(Nat.double(1n+p), Nat.double(start)),
        Equal.cong(Nat, List<&2, Nat>,
          +base => base <> (1n+base) <> Spec.mma_terms(Sequence.seq(p, 1n+start)),
          Nat.add(start, start), Nat.double(start),
          Equal.sym(Nat, Nat.double(start), Nat.add(start, start), NumericalProof.double_add(start))),
        Equal.cong(List<&2, Nat>, List<&2, Nat>,
          xs => Nat.double(start) <> (1n+Nat.double(start)) <> xs,
          Spec.mma_terms(Sequence.seq(p, 1n+start)),
          Sequence.seq(Nat.double(p), Nat.double(1n+start)), mma_sequence(p, 1n+start)))

def Laws.mma8_exact(count, start):
  Equal.trans(List<&2, Nat>, Spec.mma_terms(Spec.tiles8(count, start)),
    Spec.mma_terms(Sequence.seq(count, start)), Sequence.seq(Nat.double(count), Nat.double(start)),
    Equal.cong(List<&2, Nat>, List<&2, Nat>, Spec.mma_terms,
      Spec.tiles8(count, start), Sequence.seq(count, start), Laws.tiles8_exact(count, start)),
    mma_sequence(count, start))

def Laws.mma4_exact(count, start):
  Equal.trans(List<&2, Nat>, Spec.mma_terms(Spec.tiles4(count, start)),
    Spec.mma_terms(Sequence.seq(count, start)), Sequence.seq(Nat.double(count), Nat.double(start)),
    Equal.cong(List<&2, Nat>, List<&2, Nat>, Spec.mma_terms,
      Spec.tiles4(count, start), Sequence.seq(count, start), Laws.tiles4_exact(count, start)),
    mma_sequence(count, start))

def Laws.mma_ordered(count, start):
  (ordered_transport(Nat.double(count), Nat.double(start),
      Spec.mma_terms(Spec.tiles8(count, start)), Laws.mma8_exact(count, start)),
    ordered_transport(Nat.double(count), Nat.double(start),
      Spec.mma_terms(Spec.tiles4(count, start)), Laws.mma4_exact(count, start)))

def tiles_same(+count: Nat, +start: Nat)
  -> {Spec.tiles8(count, start) == Spec.tiles4(count, start) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Spec.tiles8(count, start), Sequence.seq(count, start),
    Spec.tiles4(count, start), Laws.tiles8_exact(count, start),
    Equal.sym(List<&2, Nat>, Spec.tiles4(count, start), Sequence.seq(count, start),
      Laws.tiles4_exact(count, start)))

def mma_same(+count: Nat, +start: Nat)
  -> {Spec.mma_terms(Spec.tiles8(count, start)) == Spec.mma_terms(Spec.tiles4(count, start)) : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, Spec.mma_terms,
    Spec.tiles8(count, start), Spec.tiles4(count, start), tiles_same(count, start))

def Laws.unroll_invariant(count, start):
  (tiles_same(count, start), mma_same(count, start))

def Laws.recurrence_invariant(count, start, accumulator):
  Equal.cong(List<&2, Nat>, Spec.Accumulator, terms => Spec.recurrence(terms, accumulator),
    Spec.mma_terms(Spec.tiles8(count, start)), Spec.mma_terms(Spec.tiles4(count, start)),
    mma_same(count, start))

def Laws.selected_shared_layout():
  {==}

def Laws.conservative_shared_bound():
  ({==}, {==})

def Laws.schedule_parameters():
  {==}

def Laws.pending_group_arithmetic():
  ({==}, {==})

def Laws.scale_refresh_refinement(phase):
  match phase:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+rest:
          Equal.trans(Nat, Impl.scale_refresh(2n+rest), Impl.scale_refresh(rest),
            Spec.scale_refresh_row(rest),
            Equal.cong(Nat, Nat, r => Nat.sub(1n, r),
              Spec.phase(2n+rest), Spec.phase(rest), mod2_period(rest)),
            Laws.scale_refresh_refinement(rest))

def reference_refresh_range(phase: Nat) -> Spec.Action(Spec.scale_refresh_row(phase)):
  match phase:
    case 0n:
      Unit{}
    case 1n+p:
      match p:
        case 0n:
          Unit{}
        case 1n+rest:
          reference_refresh_range(rest)

def Laws.scale_refresh_range(phase):
  %Equal.sym(Nat, Impl.scale_refresh(phase), Spec.scale_refresh_row(phase),
    Laws.scale_refresh_refinement(phase)) : Spec.Action(_)
  reference_refresh_range(phase)

def Laws.scale_refresh_table_exact():
  {==}

def Laws.scale_refresh_mask_exact():
  ({==}, {==})

def Laws.scale_refresh_ring(tile):
  Equal.cong(Nat, Nat, p => Nat.sub(1n, p),
    Spec.phase(Spec.slot(tile, 8n)), Spec.phase(tile), Laws.ring8_group_phase(tile))

def Laws.scale_refresh_wrap(tile):
  Equal.cong(Nat, Nat, Impl.scale_refresh,
    Spec.slot(8n+tile, 8n), Spec.slot(tile, 8n), mod8_period(tile))

def Laws.scale_refresh_seven_to_zero():
  {==}

def Laws.scale_refresh_index_bound(tile):
  match tile:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              match r:
                case 0n:
                  {==}
                case 1n+s:
                  match s:
                    case 0n:
                      {==}
                    case 1n+t:
                      match t:
                        case 0n:
                          {==}
                        case 1n+u:
                          match u:
                            case 0n:
                              {==}
                            case 1n+v:
                              match v:
                                case 0n:
                                  {==}
                                case 1n+rest:
                                  Equal.trans(Bool,
                                    Nat.is_lt(Spec.slot(8n+rest, 8n), 8n),
                                    Nat.is_lt(Spec.slot(rest, 8n), 8n), True{},
                                    Equal.cong(Nat, Bool, index => Nat.is_lt(index, 8n),
                                      Spec.slot(8n+rest, 8n), Spec.slot(rest, 8n), mod8_period(rest)),
                                    Laws.scale_refresh_index_bound(rest))

def double_quotient(+group: Nat, +seed: Nat)
  -> {Nat.div.fin(Nat.divmod.go(Nat.double(group), 1n, seed, 0n)) == Nat.add(group, seed) : Nat}:
  match group:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.div.fin(Nat.divmod.go(Nat.double(p), 1n, 1n+seed, 0n)),
        Nat.add(p, 1n+seed), 1n+Nat.add(p, seed),
        double_quotient(p, 1n+seed), NumericalProof.add_succ(p, seed))

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, add_zero(p))

def Laws.aligned_scale_start(group):
  Equal.trans(Nat, Nat.div(Nat.double(group), 2n), Nat.add(group, 0n), group,
    double_quotient(group, 0n), add_zero(group))

def Laws.semantic_group_pair(group, column, element):
  ({==}, {==})

def Laws.reference_scale_initialization(needed):
  {==}

def and_true(+a: Bool, +b: Bool, left: {a == True{} : Bool}, right: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(True{}, b), True{},
    Equal.cong(Bool, Bool, value => Bool.and(value, b), a, True{}, left), right)

def same_scale_self(+scale: Spec.Scale) -> {Spec.same_scale(scale, scale) == True{} : Bool}:
  match scale:
    case Spec.Scale{column, group, element}:
      and_true(Nat.is_eq(column, column), Bool.and(Nat.is_eq(group, group), Nat.is_eq(element, element)),
        NumericalProof.nat_eq(column),
        and_true(Nat.is_eq(group, group), Nat.is_eq(element, element),
          NumericalProof.nat_eq(group), NumericalProof.nat_eq(element)))

def next_group_not_old(+group: Nat) -> {Nat.is_eq(1n+group, group) == False{} : Bool}:
  match group:
    case 0n:
      {==}
    case 1n+p:
      next_group_not_old(p)

def same_scale_next(+column: Nat, +group: Nat, +element: Nat)
  -> {Spec.same_scale(Spec.Scale{column, 1n+group, element},
    Spec.Scale{column, group, element}) == False{} : Bool}:
  Equal.trans(Bool,
    Bool.and(Nat.is_eq(column, column), Bool.and(Nat.is_eq(1n+group, group), Nat.is_eq(element, element))),
    Bool.and(True{}, Bool.and(Nat.is_eq(1n+group, group), Nat.is_eq(element, element))), False{},
    Equal.cong(Bool, Bool,
      same => Bool.and(same, Bool.and(Nat.is_eq(1n+group, group), Nat.is_eq(element, element))),
      Nat.is_eq(column, column), True{}, NumericalProof.nat_eq(column)),
    Equal.cong(Bool, Bool, same => Bool.and(same, Nat.is_eq(element, element)),
      Nat.is_eq(1n+group, group), False{}, next_group_not_old(group)))

def Laws.reference_scale_reuse(needed):
  Equal.cong(Bool, Spec.ScaleBank, same => Spec.retain_equal(same, needed, Spec.Loaded{needed}),
    Spec.same_scale(needed, needed), True{}, same_scale_self(needed))

def Laws.reference_scale_group_transition(group, column, element):
  Equal.cong(Bool, Spec.ScaleBank,
    same => Spec.retain_equal(same, Spec.Scale{column, 1n+group, element},
      Spec.Loaded{Spec.Scale{column, group, element}}),
    Spec.same_scale(Spec.Scale{column, 1n+group, element}, Spec.Scale{column, group, element}),
    False{}, same_scale_next(column, group, element))

# Physical-ring decisions for every pair, not just the first eight tiles.
def even_refresh_from_phase(+pair: Nat, even: {Spec.phase(Nat.double(pair)) == 0n : Nat})
  -> {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat}:
  Equal.trans(Nat, Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)),
    Impl.scale_refresh(Nat.double(pair)), 1n, Laws.scale_refresh_ring(Nat.double(pair)),
    Equal.cong(Nat, Nat, phase => Nat.sub(1n, phase), Spec.phase(Nat.double(pair)), 0n, even))

def odd_refresh_from_phase(+pair: Nat, odd: {Spec.phase(1n+Nat.double(pair)) == 1n : Nat})
  -> {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat}:
  Equal.trans(Nat, Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)),
    Impl.scale_refresh(1n+Nat.double(pair)), 0n, Laws.scale_refresh_ring(1n+Nat.double(pair)),
    Equal.cong(Nat, Nat, phase => Nat.sub(1n, phase), Spec.phase(1n+Nat.double(pair)), 1n, odd))

def pair_refresh(+pair: Nat,
    phases: {Spec.phase(Nat.double(pair)) == 0n : Nat} &
      {Spec.phase(1n+Nat.double(pair)) == 1n : Nat})
  -> {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat} &
    {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat}:
  (even, odd) = phases
  (even_refresh_from_phase(pair, even), odd_refresh_from_phase(pair, odd))

def first_refresh(+pair: Nat,
    decisions: {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat} &
      {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat})
  -> {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat}:
  (even, odd) = decisions
  even

def second_refresh(+pair: Nat,
    decisions: {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat} &
      {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat})
  -> {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat}:
  (even, odd) = decisions
  odd

def even_refresh(+pair: Nat) -> {Impl.scale_refresh(Spec.slot(Nat.double(pair), 8n)) == 1n : Nat}:
  first_refresh(pair, pair_refresh(pair, Laws.group_pair_phase(pair)))

def odd_refresh(+pair: Nat) -> {Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)) == 0n : Nat}:
  second_refresh(pair, pair_refresh(pair, Laws.group_pair_phase(pair)))

def Laws.scheduled_scale_initialization(needed, previous):
  {==}

def Laws.scheduled_scale_reuse(pair, needed):
  Equal.trans(Spec.ScaleBank,
    Spec.load_scale(Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)), needed, Spec.Loaded{needed}),
    Spec.Loaded{needed}, Spec.reference_cache(needed, Spec.Loaded{needed}),
    Equal.cong(Nat, Spec.ScaleBank, refresh => Spec.load_scale(refresh, needed, Spec.Loaded{needed}),
      Impl.scale_refresh(Spec.slot(1n+Nat.double(pair), 8n)), 0n, odd_refresh(pair)),
    Equal.sym(Spec.ScaleBank, Spec.reference_cache(needed, Spec.Loaded{needed}), Spec.Loaded{needed},
      Laws.reference_scale_reuse(needed)))

def Laws.scheduled_scale_group_transition(pair, group, column, element):
  Equal.trans(Spec.ScaleBank,
    Spec.load_scale(Impl.scale_refresh(Spec.slot(Nat.double(1n+pair), 8n)),
      Spec.Scale{column, 1n+group, element}, Spec.Loaded{Spec.Scale{column, group, element}}),
    Spec.Loaded{Spec.Scale{column, 1n+group, element}},
    Spec.reference_cache(Spec.Scale{column, 1n+group, element}, Spec.Loaded{Spec.Scale{column, group, element}}),
    Equal.cong(Nat, Spec.ScaleBank, refresh => Spec.load_scale(refresh,
      Spec.Scale{column, 1n+group, element}, Spec.Loaded{Spec.Scale{column, group, element}}),
      Impl.scale_refresh(Spec.slot(Nat.double(1n+pair), 8n)), 1n, even_refresh(1n+pair)),
    Equal.sym(Spec.ScaleBank,
      Spec.reference_cache(Spec.Scale{column, 1n+group, element}, Spec.Loaded{Spec.Scale{column, group, element}}),
      Spec.Loaded{Spec.Scale{column, 1n+group, element}},
      Laws.reference_scale_group_transition(group, column, element)))

def Laws.scale_bank_lifetime(current, next, stale):
  {==}

def Laws.scale_refresh_consumer_commutes(tile, refresh, next, state):
  match state:
    case Spec.ScaleTileState{Spec.ScaleBanks{zero, one}, accumulator}:
      {==}

def Laws.scale_delayed_tile_state(tile, refresh, next, bank, stale, accumulator):
  +after_zero = {Spec.ScaleTileState{Spec.copy_scale(Spec.ScaleBanks{bank, stale}),
    Spec.ScaleMMA{accumulator, Nat.double(tile), bank}} : Spec.ScaleTileState}
  Equal.sym(Spec.ScaleTileState,
    Spec.consume_scale_one(tile, Spec.refresh_scale_state(refresh, next, after_zero)),
    Spec.refresh_scale_state(refresh, next, Spec.consume_scale_one(tile, after_zero)),
    Laws.scale_refresh_consumer_commutes(tile, refresh, next, after_zero))

def Laws.scale_ordered_consumers(tile, refresh, current, next, accumulator):
  ({==}, Equal.cong(Spec.ScaleTileState, Spec.ScaleAccumulator, Spec.scale_state_accumulator,
    Spec.delayed_scale_tile(tile, refresh, next,
      Spec.copy_scale(Spec.ScaleBanks{Spec.Loaded{current}, Spec.Uninitialized{}}), accumulator),
    Spec.ScaleTileState{Spec.ScaleBanks{Spec.load_scale(refresh, next, Spec.Loaded{current}), Spec.Loaded{current}},
      Spec.accumulate_scale_tile(tile, Spec.Loaded{current}, accumulator)},
    Laws.scale_delayed_tile_state(tile, refresh, next, Spec.Loaded{current}, Spec.Uninitialized{}, accumulator)))

# The final-state/commutation law feeds the production-linked induction below.
# Both ordered consumers precede refresh; only the NEXT iteration sees new bank0.
def scheduled_step(+count: Nat, +tile: Nat, +cursor: Spec.GroupCursor,
    +column: Nat, +element: Nat, +bank: Spec.ScaleBank,
    +accumulator: Spec.ScaleAccumulator, +decision: Nat,
    refresh: {Impl.scale_refresh(Spec.slot(1n+tile, 8n)) == decision : Nat})
  -> {Laws.scheduled_scale_run(1n+count, tile, cursor, column, element, bank, accumulator) ==
    Laws.scheduled_scale_run(count, 1n+tile, Spec.next_group(cursor), column, element,
      Spec.load_scale(decision, Spec.required_scale(Spec.next_group(cursor), column, element), bank),
      Spec.accumulate_scale_tile(tile, bank, accumulator)) : Spec.ScaleAccumulator}:
  +selected = Impl.scale_refresh(Spec.slot(1n+tile, 8n))
  +needed = Spec.required_scale(Spec.next_group(cursor), column, element)
  Equal.trans(Spec.ScaleAccumulator,
    Laws.scheduled_scale_run(1n+count, tile, cursor, column, element, bank, accumulator),
    Laws.scheduled_scale_run(count, 1n+tile, Spec.next_group(cursor), column, element,
      Spec.load_scale(selected, needed, bank), Spec.accumulate_scale_tile(tile, bank, accumulator)),
    Laws.scheduled_scale_run(count, 1n+tile, Spec.next_group(cursor), column, element,
      Spec.load_scale(decision, needed, bank), Spec.accumulate_scale_tile(tile, bank, accumulator)),
    Equal.cong(Spec.ScaleTileState, Spec.ScaleAccumulator,
      +state => Laws.scheduled_scale_run(count, 1n+tile, Spec.next_group(cursor), column, element,
        Spec.bank_zero(Spec.scale_state_banks(state)), Spec.scale_state_accumulator(state)),
      Spec.delayed_scale_tile(tile, selected, needed,
        Spec.copy_scale(Spec.ScaleBanks{bank, Spec.Uninitialized{}}), accumulator),
      Spec.ScaleTileState{Spec.ScaleBanks{Spec.load_scale(selected, needed, bank), bank},
        Spec.accumulate_scale_tile(tile, bank, accumulator)},
      Laws.scale_delayed_tile_state(tile, selected, needed, bank, Spec.Uninitialized{}, accumulator)),
    Equal.cong(Nat, Spec.ScaleAccumulator,
      action => Laws.scheduled_scale_run(count, 1n+tile, Spec.next_group(cursor), column, element,
        Spec.load_scale(action, needed, bank), Spec.accumulate_scale_tile(tile, bank, accumulator)),
      selected, decision, refresh))

# Pair induction follows the independent semantic group cursor, not a bounded
# list of example scales. Arbitrary count includes a final single-tile tail.
def scale_run_pairs(+count: Nat, +pair: Nat, +group: Nat, +column: Nat, +element: Nat,
    +accumulator: Spec.ScaleAccumulator)
  -> {Laws.scheduled_scale_run(count, Nat.double(pair), Spec.First{group}, column, element,
      Spec.Loaded{Spec.Scale{column, group, element}}, accumulator) ==
    Spec.reference_scale_run(count, Nat.double(pair), Spec.First{group}, column, element,
      accumulator) : Spec.ScaleAccumulator}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          scheduled_step(0n, Nat.double(pair), Spec.First{group}, column, element,
            Spec.Loaded{Spec.Scale{column, group, element}}, accumulator, 0n, odd_refresh(pair))
        case 1n+rest:
          +bank = {Spec.Loaded{Spec.Scale{column, group, element}} : Spec.ScaleBank}
          +first = Spec.accumulate_scale_tile(Nat.double(pair), bank, accumulator)
          +second = Spec.accumulate_scale_tile(1n+Nat.double(pair), bank, first)
          Equal.trans(Spec.ScaleAccumulator,
            Laws.scheduled_scale_run(2n+rest, Nat.double(pair), Spec.First{group}, column, element, bank, accumulator),
            Laws.scheduled_scale_run(1n+rest, 1n+Nat.double(pair), Spec.Second{group}, column, element, bank, first),
            Spec.reference_scale_run(2n+rest, Nat.double(pair), Spec.First{group}, column, element, accumulator),
            scheduled_step(1n+rest, Nat.double(pair), Spec.First{group}, column, element,
              bank, accumulator, 0n, odd_refresh(pair)),
            Equal.trans(Spec.ScaleAccumulator,
              Laws.scheduled_scale_run(1n+rest, 1n+Nat.double(pair), Spec.Second{group}, column, element, bank, first),
              Laws.scheduled_scale_run(rest, Nat.double(1n+pair), Spec.First{1n+group}, column, element,
                Spec.Loaded{Spec.Scale{column, 1n+group, element}}, second),
              Spec.reference_scale_run(2n+rest, Nat.double(pair), Spec.First{group}, column, element, accumulator),
              scheduled_step(rest, 1n+Nat.double(pair), Spec.Second{group}, column, element,
                bank, first, 1n, even_refresh(1n+pair)),
              scale_run_pairs(rest, 1n+pair, 1n+group, column, element, second)))

def Laws.scale_accumulator_recurrence(count, group, column, element, previous, accumulator):
  scale_run_pairs(count, 0n, group, column, element, accumulator)

def Laws.scale_new_column_reset(count, group, column, element, old_column, old_group, old_element, identity):
  Laws.scale_accumulator_recurrence(count, group, column, element,
    Spec.Loaded{Spec.Scale{old_column, old_group, old_element}}, Spec.ScaleInitial{identity})

def Laws.scale_unconditional_load(needed, previous):
  {==}

# Small structural order lemmas: no finite access-list enumeration or native
# semantics are hidden in these arithmetic proofs.
def order_refl(n: Nat) -> Order.Le(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      order_refl(p)

def order_weaken(+a: Nat, +b: Nat, bounded: Order.Le(a, b)) -> Order.Le(a, 1n+b):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+p 0n:
      Empty.absurd(Order.Le(1n+p, 1n), bounded)
    case 1n+p 1n+q:
      order_weaken(p, q, bounded)

def order_add_left(prefix: Nat, +a: Nat, +b: Nat, bounded: Order.Le(a, b))
  -> Order.Le(Nat.add(prefix, a), Nat.add(prefix, b)):
  match prefix:
    case 0n:
      bounded
    case 1n+p:
      order_add_left(p, a, b, bounded)

def order_add_right(+a: Nat, +b: Nat, +suffix: Nat, bounded: Order.Le(a, b))
  -> Order.Le(Nat.add(a, suffix), Nat.add(b, suffix)):
  match a b:
    case 0n 0n:
      order_refl(suffix)
    case 0n 1n+q:
      order_weaken(suffix, Nat.add(q, suffix),
        order_add_right(0n, q, suffix, NumericalProof.le_zero(q)))
    case 1n+p 0n:
      Empty.absurd(Order.Le(Nat.add(1n+p, suffix), suffix), bounded)
    case 1n+p 1n+q:
      order_add_right(p, q, suffix, bounded)

def order_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat,
    ab: Order.Le(a, b), cd: Order.Le(c, d))
  -> Order.Le(Nat.add(a, c), Nat.add(b, d)):
  NumericalProof.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d),
    order_add_right(a, b, c, ab), order_add_left(b, c, d, cd))

def order_scale(+a: Nat, +b: Nat, +width: Nat, bounded: Order.Le(a, b))
  -> Order.Le(Nat.mul(a, width), Nat.mul(b, width)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      NumericalProof.le_zero(Nat.mul(1n+q, width))
    case 1n+p 0n:
      Empty.absurd(Order.Le(Nat.mul(1n+p, width), 0n), bounded)
    case 1n+p 1n+q:
      order_add_left(width, Nat.mul(p, width), Nat.mul(q, width),
        order_scale(p, q, width, bounded))

def tile_index_bound(+stages: Nat, +stride: Nat, +stage: Nat, +local: Nat,
    stage_bound: Order.Le(1n+stage, stages), local_bound: Order.Le(1n+local, stride))
  -> Order.Le(1n+Spec.tile_index(stride, stage, local), Nat.mul(stages, stride)):
  NumericalProof.le_trans(Nat.add(1n+local, Nat.mul(stage, stride)),
    Nat.mul(1n+stage, stride), Nat.mul(stages, stride),
    order_add_right(1n+local, stride, Nat.mul(stage, stride), local_bound),
    order_scale(1n+stage, stages, stride, stage_bound))

def ring_access_bound(+base: Nat, +stride: Nat, +tile: Nat, +local: Nat,
    bounded: Order.Le(1n+local, stride))
  -> Order.Le(Spec.access_end(base, stride, Spec.slot(tile, 8n), local),
    Spec.stage_base(base, stride, 8n)):
  order_scale(Nat.add(base, Nat.add(1n+local, Nat.mul(Spec.slot(tile, 8n), stride))),
    Nat.add(base, Nat.mul(8n, stride)), 16n,
    order_add_left(base, Nat.add(1n+local, Nat.mul(Spec.slot(tile, 8n), stride)),
      Nat.mul(8n, stride),
      tile_index_bound(8n, stride, Spec.slot(tile, 8n), local,
        NumericalProof.lt_sound(Spec.slot(tile, 8n), 8n, Laws.scale_refresh_index_bound(tile)),
        bounded)))

def int4_alignment(+int4s: Nat) -> {Nat.mod(Spec.bytes(int4s), 16n) == 0n : Nat}:
  match int4s:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mod(16n+Spec.bytes(p), 16n), Nat.mod(Spec.bytes(p), 16n), 0n,
        remainder_quotient(Spec.bytes(p), 15n, 1n, 0n, 0n), int4_alignment(p))

def Laws.selected_shared_exact():
  ({==}, {==})

def Laws.selected_overlay_extents():
  {==}

def Laws.selected_overlay_coverage():
  (Unit{}, (Unit{}, (Unit{}, Unit{})))

def Laws.selected_regions_disjoint():
  (Unit{}, (Unit{}, {==}))

def Laws.selected_region_offsets():
  {==}

def Laws.selected_stage_alignment(tile):
  (int4_alignment(Nat.mul(Spec.slot(tile, 8n), Spec.b_stage_int4s())),
    (int4_alignment(Nat.add(Spec.scale_base_int4s(), Nat.mul(Spec.slot(tile, 8n), Spec.s_stage_int4s()))),
      int4_alignment(Nat.add(Spec.a_base_int4s(), Nat.mul(Spec.slot(tile, 8n), Spec.a_stage_int4s())))))

def Laws.selected_a_access_bound(tile, local, bounded):
  ring_access_bound(Spec.a_base_int4s(), Spec.a_stage_int4s(), tile, local, bounded)

def Laws.selected_b_access_bound(tile, local, bounded):
  NumericalProof.le_trans(Spec.access_end(0n, Spec.b_stage_int4s(), Spec.slot(tile, 8n), local),
    Spec.stage_base(0n, Spec.b_stage_int4s(), 8n), Impl.selected_shared_bytes(),
    ring_access_bound(0n, Spec.b_stage_int4s(), tile, local, bounded), Unit{})

def Laws.selected_scale_access_bound(tile, local, bounded):
  NumericalProof.le_trans(Spec.access_end(Spec.scale_base_int4s(), Spec.s_stage_int4s(), Spec.slot(tile, 8n), local),
    Spec.stage_base(Spec.scale_base_int4s(), Spec.s_stage_int4s(), 8n), Impl.selected_shared_bytes(),
    ring_access_bound(Spec.scale_base_int4s(), Spec.s_stage_int4s(), tile, local, bounded), Unit{})

def Laws.selected_a_active_copy_index(rows, thread, admitted, active):
  NumericalProof.le_trans(1n+thread, Nat.mul(rows, 8n), Spec.a_stage_int4s(),
    NumericalProof.lt_sound(thread, Nat.mul(rows, 8n), active),
    order_scale(rows, 8n, 8n, admitted))

def Laws.selected_a_supplier_column(lane_half, warp_pair, k_half, lane_bound, warp_bound, k_bound):
  order_add(lane_half, 1n, Nat.add(Nat.mul(warp_pair, 2n), Nat.mul(k_half, 4n)), 6n,
    lane_bound,
    order_add(Nat.mul(warp_pair, 2n), 2n, Nat.mul(k_half, 4n), 4n,
      order_scale(warp_pair, 1n, 2n, warp_bound), order_scale(k_half, 1n, 4n, k_bound)))

def Laws.selected_a_swizzled_index(row, column, row_bound, column_bound):
  tile_index_bound(8n, 8n, row, column, row_bound, column_bound)

def Laws.selected_b_local_index(iteration, thread, iteration_bound, thread_bound):
  tile_index_bound(2n, 128n, iteration, thread, iteration_bound, thread_bound)

def Laws.selected_scale_local_index(warp_mod2, lane_div4, warp_bound, lane_bound):
  tile_index_bound(2n, 8n, warp_mod2, lane_div4, warp_bound, lane_bound)

def Laws.selected_cta_reduction_index(pair, thread_mod64, pair_bound, thread_bound):
  order_scale(1n+Spec.cta_reduction_index(pair, thread_mod64), 448n, 16n,
    order_add(1n+thread_mod64, 64n, Nat.mul(pair, 128n), 384n,
      thread_bound, order_scale(pair, 3n, 128n, pair_bound)))

# The two machines differ in shared state only. No property of FP32Add is
# assumed: equal constructor operands remain equal under any interpretation.
def fp32_local_refinement(active: Bool, first: Bool, +last: Bool, +lock: Nat,
    +lane: Nat, +identity: Nat, +previous: Spec.FP32Shared)
  -> {Spec.fp32_observable(Spec.fp32_transfer(active, first, last, 1n, lock, lane, identity, previous)) ==
    Spec.fp32_observable(Spec.fp32_transfer(active, first, last, 0n, lock, lane, identity, previous))
      : Spec.FP32Observable}:
  match active first last:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def fp32_action_refinement(action: Nat, +active: Bool, +first: Bool, +last: Bool,
    +lock: Nat, +lane: Nat, +identity: Nat, +previous: Spec.FP32Shared,
    valid: Spec.Action(action))
  -> {Spec.fp32_observable(Spec.fp32_transfer(active, first, last, action, lock, lane, identity, previous)) ==
    Spec.fp32_observable(Spec.fp32_transfer(active, first, last, 0n, lock, lane, identity, previous))
      : Spec.FP32Observable}:
  match action:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          fp32_local_refinement(active, first, last, lock, lane, identity, previous)
        case 1n+q:
          Empty.absurd({Spec.fp32_observable(Spec.fp32_transfer(active, first, last, 2n+q,
            lock, lane, identity, previous)) ==
              Spec.fp32_observable(Spec.fp32_transfer(active, first, last, 0n,
                lock, lane, identity, previous)) : Spec.FP32Observable}, valid)

def Laws.selected_fp32_transfer_refinement(eligible, safe, deterministic,
    first, last, lock, lane, identity, previous):
  fp32_action_refinement(Impl.policy(eligible, safe, deterministic), Nat.is_lt(lane, 64n),
    first, last, lock, lane, identity, previous, Laws.action_range(eligible, safe, deterministic))

def Laws.selected_fp32_action0_fallback(eligible, safe, deterministic,
    first, last, lock, lane, identity, previous, fallback):
  Equal.cong(Nat, Spec.FP32State, action => Spec.fp32_transfer(Nat.is_lt(lane, 64n),
    first, last, action, lock, lane, identity, previous),
    Impl.policy(eligible, safe, deterministic), 0n, fallback)

def Laws.selected_fp32_transfer_indices(lock, pair, lane, component):
  ({==}, ({==}, {==}))

def Laws.selected_fp32_ordered_trace(lock, lane, identity):
  {==}

def Laws.selected_fp32_scratch_trace(first, lock, lane, identity):
  match first:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.selected_fp32_branch_traces(action, first, last, lock, lane, identity, previous):
  ({==}, ({==}, {==}))

def Laws.selected_fp32_output_coordinate_table():
  {==}

def fp32_true_left(+a: Bool, +b: Bool, accepted: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  Pair.fst({a == True{} : Bool}, {b == True{} : Bool}, NumericalProof.and_true(a, b, accepted))

def fp32_true_right(+a: Bool, +b: Bool, accepted: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  Pair.snd({a == True{} : Bool}, {b == True{} : Bool}, NumericalProof.and_true(a, b, accepted))

# Eliminate the closed coordinate certificate at an arbitrary bounded index.
# These proofs do not replace the inverse with a byte-extent bound.
def fp32_output_column_at(+count: Nat, +index: Nat, +row: Nat, +start: Nat,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.fp32_output_columns(count, row, start) == True{} : Bool})
  -> {Spec.fp32_output_coordinate_ok(row, Nat.add(start, index)) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.fp32_output_coordinate_ok(row, Nat.add(start, index)) == True{} : Bool}, bounded)
    case 1n+p 0n:
      here = fp32_true_left(Spec.fp32_output_coordinate_ok(row, start),
        Spec.fp32_output_columns(p, row, 1n+start), accepted)
      Equal.trans(Bool, Spec.fp32_output_coordinate_ok(row, Nat.add(start, 0n)),
        Spec.fp32_output_coordinate_ok(row, start), True{},
        Equal.cong(Nat, Bool, column => Spec.fp32_output_coordinate_ok(row, column),
          Nat.add(start, 0n), start, add_zero(start)), here)
    case 1n+p 1n+q:
      rest = fp32_true_right(Spec.fp32_output_coordinate_ok(row, start),
        Spec.fp32_output_columns(p, row, 1n+start), accepted)
      Equal.trans(Bool, Spec.fp32_output_coordinate_ok(row, Nat.add(start, 1n+q)),
        Spec.fp32_output_coordinate_ok(row, 1n+Nat.add(start, q)), True{},
        Equal.cong(Nat, Bool, column => Spec.fp32_output_coordinate_ok(row, column),
          Nat.add(start, 1n+q), 1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        fp32_output_column_at(p, q, row, 1n+start, bounded, rest))

def fp32_output_row_at(+count: Nat, +index: Nat, +start: Nat,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.fp32_output_rows(count, start) == True{} : Bool})
  -> {Spec.fp32_output_columns(128n, Nat.add(start, index), 0n) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.fp32_output_columns(128n, Nat.add(start, index), 0n) == True{} : Bool}, bounded)
    case 1n+p 0n:
      here = fp32_true_left(Spec.fp32_output_columns(128n, start, 0n),
        Spec.fp32_output_rows(p, 1n+start), accepted)
      Equal.trans(Bool, Spec.fp32_output_columns(128n, Nat.add(start, 0n), 0n),
        Spec.fp32_output_columns(128n, start, 0n), True{},
        Equal.cong(Nat, Bool, row => Spec.fp32_output_columns(128n, row, 0n),
          Nat.add(start, 0n), start, add_zero(start)), here)
    case 1n+p 1n+q:
      rest = fp32_true_right(Spec.fp32_output_columns(128n, start, 0n),
        Spec.fp32_output_rows(p, 1n+start), accepted)
      Equal.trans(Bool, Spec.fp32_output_columns(128n, Nat.add(start, 1n+q), 0n),
        Spec.fp32_output_columns(128n, 1n+Nat.add(start, q), 0n), True{},
        Equal.cong(Nat, Bool, row => Spec.fp32_output_columns(128n, row, 0n),
          Nat.add(start, 1n+q), 1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        fp32_output_row_at(p, q, 1n+start, bounded, rest))

def Laws.selected_fp32_output_read_coverage(rows, row, column,
    nonempty, admitted, observed_row, observed_column):
  fp32_output_column_at(128n, column, row, 0n, observed_column,
    fp32_output_row_at(8n, row, 0n,
      NumericalProof.le_trans(1n+row, rows, 8n, observed_row, admitted),
      Laws.selected_fp32_output_coordinate_table()))

def fp32_output_addresses_join(+row: Nat, +column: Nat,
    proofs: {Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)) == True{} : Bool} &
      {Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column)) == True{} : Bool})
  -> {Spec.fp32_output_writer(row, column) == Spec.fp32_output_reader(row, column) : Nat}:
  (writer, reader) = proofs
  Equal.trans(Nat, Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column),
    Spec.fp32_output_reader(row, column),
    NumericalProof.nat_eq_sound(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column), writer),
    Equal.sym(Nat, Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column),
      NumericalProof.nat_eq_sound(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column), reader)))

def fp32_output_addresses(+row: Nat, +column: Nat,
    accepted: {Spec.fp32_output_coordinate_ok(row, column) == True{} : Bool})
  -> {Spec.fp32_output_writer(row, column) == Spec.fp32_output_reader(row, column) : Nat}:
  rest0 = fp32_true_right(Nat.is_lt(Spec.fp32_output_thread(row, column), 64n),
    Bool.and(Nat.is_lt(Spec.fp32_output_j(column), 4n),
      Bool.and(Nat.is_lt(Spec.fp32_output_pair(column), 2n),
        Bool.and(Nat.is_lt(Spec.fp32_output_scalar(row), 2n),
          Bool.and(Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)),
            Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column)))))), accepted)
  rest1 = fp32_true_right(Nat.is_lt(Spec.fp32_output_j(column), 4n),
    Bool.and(Nat.is_lt(Spec.fp32_output_pair(column), 2n),
      Bool.and(Nat.is_lt(Spec.fp32_output_scalar(row), 2n),
        Bool.and(Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)),
          Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column))))), rest0)
  rest2 = fp32_true_right(Nat.is_lt(Spec.fp32_output_pair(column), 2n),
    Bool.and(Nat.is_lt(Spec.fp32_output_scalar(row), 2n),
      Bool.and(Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)),
        Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column)))), rest1)
  rest3 = fp32_true_right(Nat.is_lt(Spec.fp32_output_scalar(row), 2n),
    Bool.and(Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)),
      Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column))), rest2)
  fp32_output_addresses_join(row, column, NumericalProof.and_true(
    Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_address(row, column)),
    Nat.is_eq(Spec.fp32_output_reader(row, column), Spec.fp32_output_address(row, column)), rest3))

def fp32_address_truth(+left: Nat, +right: Nat, same: {left == right : Nat})
  -> {Nat.is_eq(left, right) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_eq(left, right), Nat.is_eq(right, right), True{},
    Equal.cong(Nat, Bool, value => Nat.is_eq(value, right), left, right, same),
    NumericalProof.nat_eq(right))

def Laws.selected_fp32_output_noninterference(rows, row, column, identity, left, right,
    nonempty, admitted, observed_row, observed_column):
  %Equal.sym(Bool, Nat.is_eq(Spec.fp32_output_writer(row, column), Spec.fp32_output_reader(row, column)),
    True{}, fp32_address_truth(Spec.fp32_output_writer(row, column), Spec.fp32_output_reader(row, column),
      fp32_output_addresses(row, column, Laws.selected_fp32_output_read_coverage(rows, row, column,
        nonempty, admitted, observed_row, observed_column)))) :
      {Spec.fp32_overwrite_observe(_, Spec.fp32_output_reader(row, column), identity, Spec.fp32_shared_state(left)) ==
        Spec.fp32_overwrite_observe(_, Spec.fp32_output_reader(row, column), identity, Spec.fp32_shared_state(right))
          : Spec.FP32OverlayObservation}
  {==}

def Laws.selected_fp32_padding_unobserved(rows):
  match rows:
    case 0n:
      ({==}, Unit{})
    case 1n+p:
      ({==}, Unit{})

def Laws.selected_fp32_restart_cover(lane, byte, lane_bound, byte_bound):
  (NumericalProof.le_trans(1n+lane, 64n, 128n, lane_bound, Unit{}), {==})

def Laws.selected_fp32_restart_noninterference(waited, lane, byte, identity, left, right,
    lane_bound, byte_bound, ready):
  address = Pair.snd(Order.Le(1n+lane, 128n),
    {Spec.fp32_restart_byte(0n, lane, byte) == Spec.fp32_deleted_byte(lane, byte) : Nat},
    Laws.selected_fp32_restart_cover(lane, byte, lane_bound, byte_bound))
  covered = and_true(waited,
    Nat.is_eq(Spec.fp32_restart_byte(0n, lane, byte), Spec.fp32_deleted_byte(lane, byte)), ready,
    fp32_address_truth(Spec.fp32_restart_byte(0n, lane, byte), Spec.fp32_deleted_byte(lane, byte), address))
  %Equal.sym(Bool, Bool.and(waited,
    Nat.is_eq(Spec.fp32_restart_byte(0n, lane, byte), Spec.fp32_deleted_byte(lane, byte))), True{}, covered) :
      {Spec.fp32_overwrite_observe(_, Spec.fp32_deleted_byte(lane, byte), identity, Spec.fp32_shared_state(left)) ==
        Spec.fp32_overwrite_observe(_, Spec.fp32_deleted_byte(lane, byte), identity, Spec.fp32_shared_state(right))
          : Spec.FP32OverlayObservation}
  {==}

def Laws.selected_fp32_output_projection(eligible, safe, deterministic, first, lock, lane,
    identity, previous, rows, row, column, nonempty, admitted, observed_row, observed_column):
  (Laws.selected_fp32_transfer_refinement(eligible, safe, deterministic,
    first, True{}, lock, lane, identity, previous),
    Laws.selected_fp32_output_noninterference(rows, row, column, identity,
      Laws.scheduled_fp32(eligible, safe, deterministic, first, True{}, lock, lane, identity, previous),
      Spec.fp32_transfer(Nat.is_lt(lane, 64n), first, True{}, 0n, lock, lane, identity, previous),
      nonempty, admitted, observed_row, observed_column))

def Laws.selected_fp32_restart_projection(eligible, safe, deterministic, first, last, lock, lane,
    byte, identity, previous, waited, lane_bound, byte_bound, ready):
  Laws.selected_fp32_restart_noninterference(waited, lane, byte, identity,
    Laws.scheduled_fp32(eligible, safe, deterministic, first, last, lock, lane, identity, previous),
    Spec.fp32_transfer(Nat.is_lt(lane, 64n), first, last, 0n, lock, lane, identity, previous),
    lane_bound, byte_bound, ready)

# Structural arithmetic, not an eight-row example table or a large closed
# normalization. The countdown worker cannot increment its quotient before
# the numerator exhausts the remaining divisor.
def normalization_quotient_zero(n: Nat, remaining: Nat, +remainder: Nat,
    bounded: Order.Le(n, remaining))
  -> {Nat.div.fin(Nat.divmod.go(n, remaining, 0n, remainder)) == 0n : Nat}:
  match n remaining:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.div.fin(Nat.divmod.go(1n+p, 0n, 0n, remainder)) == 0n : Nat}, bounded)
    case 1n+p 1n+q:
      normalization_quotient_zero(p, q, 1n+remainder, bounded)

def normalization_div_below(+rows: Nat, divisor: Nat,
    bounded: Order.Le(1n+rows, divisor)) -> {Nat.div(rows, divisor) == 0n : Nat}:
  match divisor:
    case 0n:
      Empty.absurd({Nat.div(rows, 0n) == 0n : Nat}, bounded)
    case 1n+p:
      normalization_quotient_zero(rows, p, 0n, bounded)

def normalization_sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      normalization_sub_self(p)

def normalization_not_gt(a: Nat, b: Nat, bounded: Order.Le(a, b))
  -> {Nat.is_gt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_gt(1n+p, 0n) == False{} : Bool}, bounded)
    case 1n+p 1n+q:
      normalization_not_gt(p, q, bounded)

def original_small_normalization(+rows: Nat, +block: Nat, bounded: Order.Le(rows, block))
  -> {Spec.original_normalization(rows, block) == Spec.MNormalization{1n, rows} : Spec.MNormalization}:
  Equal.cong(Bool, Spec.MNormalization,
    large => Bool.pick(Spec.MNormalization, large,
      Spec.MNormalization{Nat.div(rows, block), block}, Spec.MNormalization{1n, rows}),
    Nat.is_gt(rows, block), False{}, normalization_not_gt(rows, block, bounded))

def Laws.host_retry_bound(retry):
  match retry:
    case Spec.Retry4{}:
      Unit{}
    case Spec.Retry3{}:
      Unit{}
    case Spec.Retry2{}:
      Unit{}
    case Spec.Retry1{}:
      Unit{}

def Laws.host_split_preserves_m(retry, rows, max_par, nonempty, bounded):
  +divisor = Spec.retry_divisor(retry)
  +quotient = normalization_div_below(rows, divisor,
    NumericalProof.le_trans(1n+rows, 9n, divisor, bounded,
      NumericalProof.le_trans(9n, 16n, divisor, Unit{}, Laws.host_retry_bound(retry))))
  +count = Equal.cong(Nat, Nat, q => Nat.min(q, max_par),
    Nat.div(rows, divisor), 0n, quotient)
  +split = Equal.cong(Nat, Nat, q => Spec.host_split_count(q, rows, divisor),
    Spec.host_par_count(rows, divisor, max_par), 0n, count)
  (quotient, (count, (split,
    Equal.trans(Nat, Nat.sub(rows, Spec.host_split(rows, divisor, max_par)),
      Nat.sub(rows, rows), 0n,
      Equal.cong(Nat, Nat, m => Nat.sub(rows, m),
        Spec.host_split(rows, divisor, max_par), rows, split),
      normalization_sub_self(rows)))))

def Laws.selected_m_pair(eligible, safe, deterministic, rows, selected, nonempty, bounded):
  Equal.cong(Nat, Spec.MNormalization, action => Spec.normalization(action, rows, 8n),
    Impl.policy(eligible, safe, deterministic), 1n, selected)

def normalization_action_refinement(action: Nat, +rows: Nat, +block: Nat,
    admitted: Laws.NormalizationDomain(action, rows, block))
  -> {Spec.normalization(action, rows, block) == Spec.original_normalization(rows, block)
    : Spec.MNormalization}:
  match action:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          (nonempty, rest) = admitted
          (bounded, geometry) = rest
          %Equal.sym(Nat, block, 8n, geometry) :
            {Spec.normalization(1n, rows, _) == Spec.original_normalization(rows, _) : Spec.MNormalization}
          Equal.sym(Spec.MNormalization, Spec.original_normalization(rows, 8n),
            Spec.MNormalization{1n, rows}, original_small_normalization(rows, 8n, bounded))
        case 1n+q:
          Empty.absurd({Spec.normalization(2n+q, rows, block) ==
            Spec.original_normalization(rows, block) : Spec.MNormalization}, admitted)

def Laws.normalization_refinement(eligible, safe, deterministic, rows, block, admitted):
  normalization_action_refinement(Impl.policy(eligible, safe, deterministic), rows, block, admitted)

def Laws.normalization_action0(eligible, safe, deterministic, rows, block, fallback):
  Equal.cong(Nat, Spec.MNormalization, action => Spec.normalization(action, rows, block),
    Impl.policy(eligible, safe, deterministic), 0n, fallback)

def normalization_host_split(+rows: Nat, +divisor: Nat, +max_par: Nat,
    proofs: {Nat.div(rows, divisor) == 0n : Nat} &
      ({Spec.host_par_count(rows, divisor, max_par) == 0n : Nat} &
      ({Spec.host_split(rows, divisor, max_par) == rows : Nat} &
        {Nat.sub(rows, Spec.host_split(rows, divisor, max_par)) == 0n : Nat})))
  -> {Spec.host_split(rows, divisor, max_par) == rows : Nat}:
  (quotient, rest) = proofs
  (count, split_rest) = rest
  (split, remaining) = split_rest
  split

def Laws.selected_launch_m(eligible, safe, deterministic, retry, rows, max_par,
    selected, nonempty, bounded):
  +split = normalization_host_split(rows, Spec.retry_divisor(retry), max_par,
    Laws.host_split_preserves_m(retry, rows, max_par, nonempty, bounded))
  (Equal.trans(Spec.MNormalization,
    Laws.scheduled_normalization(eligible, safe, deterministic,
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n),
    Laws.scheduled_normalization(eligible, safe, deterministic, rows, 8n),
    Spec.MNormalization{1n, rows},
    Equal.cong(Nat, Spec.MNormalization,
      m => Laws.scheduled_normalization(eligible, safe, deterministic, m, 8n),
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), rows, split),
    Equal.cong(Nat, Spec.MNormalization, action => Spec.normalization(action, rows, 8n),
      Impl.policy(eligible, safe, deterministic), 1n, selected)),
    Equal.trans(Spec.MNormalization,
      Spec.original_normalization(Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n),
      Spec.original_normalization(rows, 8n), Spec.MNormalization{1n, rows},
      Equal.cong(Nat, Spec.MNormalization, m => Spec.original_normalization(m, 8n),
        Spec.host_split(rows, Spec.retry_divisor(retry), max_par), rows, split),
      original_small_normalization(rows, 8n, bounded)))

def Laws.selected_m_predicates(eligible, safe, deterministic, retry, rows, max_par,
    thread, row, column, selected, nonempty, bounded):
  same = Pair.fst(
    {Laws.scheduled_normalization(eligible, safe, deterministic,
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n) ==
      Spec.MNormalization{1n, rows} : Spec.MNormalization},
    {Spec.original_normalization(Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n) ==
      Spec.MNormalization{1n, rows} : Spec.MNormalization},
    Laws.selected_launch_m(eligible, safe, deterministic, retry, rows, max_par, selected, nonempty, bounded))
  Equal.cong(Spec.MNormalization, List<&2, Bool>,
    pair => Spec.normalization_predicates(pair, thread, row, column),
    Laws.scheduled_normalization(eligible, safe, deterministic,
      Spec.host_split(rows, Spec.retry_divisor(retry), max_par), 8n),
    Spec.MNormalization{1n, rows}, same)

def Laws.normalization_stripe_inputs(eligible, safe, deterministic, rows, m_block,
    k, n, grid, block, column, row, admitted):
  +same = Laws.normalization_refinement(eligible, safe, deterministic, rows, m_block, admitted)
  (Equal.cong(Spec.MNormalization, Spec.StripeObservation,
    pair => Spec.stripe_observation(pair, k, n, grid, block),
    Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
    Spec.original_normalization(rows, m_block), same),
    Equal.cong(Spec.MNormalization, Nat,
      pair => Spec.slice_work(pair, k, n, grid, block, column, row),
      Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      Spec.original_normalization(rows, m_block), same))

def Laws.normalization_tiles(eligible, safe, deterministic, rows, m_block,
    k, n, grid, block, column, row, start, admitted):
  work = Equal.cong(Spec.MNormalization, Nat,
    pair => Spec.slice_work(pair, k, n, grid, block, column, row),
    Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
    Spec.original_normalization(rows, m_block),
    Laws.normalization_refinement(eligible, safe, deterministic, rows, m_block, admitted))
  +original = Spec.slice_work(Spec.original_normalization(rows, m_block), k, n, grid, block, column, row)
  Equal.trans(List<&2, Nat>,
    Spec.tiles8(Spec.slice_work(Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block, column, row), start),
    Spec.tiles8(original, start), Sequence.seq(original, start),
    Equal.cong(Nat, List<&2, Nat>, count => Spec.tiles8(count, start),
      Spec.slice_work(Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
        k, n, grid, block, column, row), original, work),
    Laws.tiles8_exact(original, start))

def Laws.normalization_recurrence(eligible, safe, deterministic, rows, m_block,
    k, n, grid, block, column, row, start, accumulator, admitted):
  Equal.cong(List<&2, Nat>, Spec.Accumulator,
    tiles => Spec.recurrence(Spec.mma_terms(tiles), accumulator),
    Spec.tiles8(Spec.slice_work(Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
      k, n, grid, block, column, row), start),
    Sequence.seq(Spec.slice_work(Spec.original_normalization(rows, m_block),
      k, n, grid, block, column, row), start),
    Laws.normalization_tiles(eligible, safe, deterministic, rows, m_block,
      k, n, grid, block, column, row, start, admitted))

def Laws.normalization_lock_observation(eligible, safe, deterministic, rows, m_block,
    k, n, grid, block, observe, admitted):
  Equal.cong(Spec.MNormalization, Spec.FP32Observable,
    pair => observe(Spec.stripe_observation(pair, k, n, grid, block)),
    Laws.scheduled_normalization(eligible, safe, deterministic, rows, m_block),
    Spec.original_normalization(rows, m_block),
    Laws.normalization_refinement(eligible, safe, deterministic, rows, m_block, admitted))

def Laws.scale_lane_certificate():
  {==}

# Reuse the existing finite-coordinate certificate convention, eliminating the
# actual 128-row arithmetic/bit computation at an arbitrary bounded thread.
def scale_lane_at(+count: Nat, +index: Nat, +start: Nat,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.scale_lane_rows(count, start) == True{} : Bool})
  -> {Spec.scale_lane_ok(Nat.add(start, index)) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.scale_lane_ok(Nat.add(start, index)) == True{} : Bool}, bounded)
    case 1n+p 0n:
      here = fp32_true_left(Spec.scale_lane_ok(start), Spec.scale_lane_rows(p, 1n+start), accepted)
      Equal.trans(Bool, Spec.scale_lane_ok(Nat.add(start, 0n)), Spec.scale_lane_ok(start), True{},
        Equal.cong(Nat, Bool, thread => Spec.scale_lane_ok(thread),
          Nat.add(start, 0n), start, add_zero(start)), here)
    case 1n+p 1n+q:
      rest = fp32_true_right(Spec.scale_lane_ok(start), Spec.scale_lane_rows(p, 1n+start), accepted)
      Equal.trans(Bool, Spec.scale_lane_ok(Nat.add(start, 1n+q)),
        Spec.scale_lane_ok(1n+Nat.add(start, q)), True{},
        Equal.cong(Nat, Bool, thread => Spec.scale_lane_ok(thread), Nat.add(start, 1n+q),
          1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        scale_lane_at(p, q, 1n+start, bounded, rest))

def scale_lane_after_index(+thread: Nat, accepted: {Spec.scale_lane_ok(thread) == True{} : Bool})
  -> {Bool.and(Nat.is_eq(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread))),
    Bool.and(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
      Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
        Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))))) == True{} : Bool}:
  fp32_true_right(Nat.is_eq(Spec.scale_selected_index(thread), Spec.scale_generic_index(thread)),
    Bool.and(Nat.is_eq(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread))),
      Bool.and(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
        Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
          Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))))), accepted)

def Laws.scale_lane_index_refinement(thread, bounded):
  NumericalProof.nat_eq_sound(Spec.scale_selected_index(thread), Spec.scale_generic_index(thread),
    fp32_true_left(Nat.is_eq(Spec.scale_selected_index(thread), Spec.scale_generic_index(thread)),
      Bool.and(Nat.is_eq(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread))),
        Bool.and(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
          Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
            Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))))),
      scale_lane_at(128n, thread, 0n, bounded, Laws.scale_lane_certificate())))

def Laws.scale_lane_emitted_bytes(thread, bounded):
  NumericalProof.nat_eq_sound(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread)),
    fp32_true_left(Nat.is_eq(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread))),
      Bool.and(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
        Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
          Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n)))),
      scale_lane_after_index(thread, scale_lane_at(128n, thread, 0n, bounded, Laws.scale_lane_certificate()))))

def Laws.scale_lane_machine_domain(thread, bounded):
  +tail = fp32_true_right(
    Nat.is_eq(Spec.scale_emitted_bytes(thread), Spec.bytes(Spec.scale_selected_index(thread))),
    Bool.and(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
      Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
        Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n)))),
    scale_lane_after_index(thread, scale_lane_at(128n, thread, 0n, bounded, Laws.scale_lane_certificate())))
  +casts = fp32_true_right(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
    Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
      Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))), tail)
  (NumericalProof.nat_eq_sound(U32.to_nat(U32.from_nat(thread)), thread,
    fp32_true_left(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
      Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n)), casts)),
    (NumericalProof.nat_eq_sound(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n),
      fp32_true_right(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
        Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n)), casts)),
      (order_scale(thread, 127n, 4n, bounded),
        NumericalProof.lt_sound(Spec.scale_selected_index(thread), 16n,
          fp32_true_left(Nat.is_lt(Spec.scale_selected_index(thread), 16n),
            Bool.and(Nat.is_eq(U32.to_nat(U32.from_nat(thread)), thread),
              Nat.is_eq(U32.to_nat(U32.mul(4, U32.from_nat(thread))), Nat.mul(thread, 4n))), tail)))))

def Laws.scale_lane_mask_fallback(mask, thread, generic, fallback):
  Equal.cong(Bool, Nat, selected => Bool.pick(Nat, selected, Spec.scale_selected_index(thread), generic),
    Nat.is_eq(mask, 85n), False{}, fallback)

def Laws.scale_lane_production_mask():
  ({==}, {==})

def Laws.scale_lane_policy_refinement(eligible, safe, deterministic, thread, bounded):
  match eligible:
    case False{}:
      {==}
    case True{}:
      match safe:
        case False{}:
          {==}
        case True{}:
          match deterministic:
            case False{}:
              {==}
            case True{}:
              Laws.scale_lane_index_refinement(thread, bounded)

def Laws.scale_lane_action0_fallback(eligible, safe, deterministic, thread, generic, fallback):
  Equal.cong(Nat, Nat, action => Spec.scale_masked_index(Laws.scheduled_scale_mask(action), thread, generic),
    Impl.policy(eligible, safe, deterministic), 0n, fallback)

def Laws.scale_lane_slot_address(stage, thread, bounded):
  Equal.cong(Nat, Nat, local => Spec.scale_slot_address(stage, local),
    Spec.scale_selected_index(thread), Spec.scale_generic_index(thread),
    Laws.scale_lane_index_refinement(thread, bounded))

def Laws.scale_lane_group_slots():
  {==}

def Laws.scale_lane_address_refinement(eligible, safe, deterministic, tile, thread, bounded):
  Equal.cong(Nat, Nat, local => Spec.scale_slot_address(Spec.scale_group_slot(tile), local),
    Laws.scheduled_scale_index(eligible, safe, deterministic, thread), Spec.scale_generic_index(thread),
    Laws.scale_lane_policy_refinement(eligible, safe, deterministic, thread, bounded))

def Laws.scale_lane_address_bytes(eligible, safe, deterministic, tile, thread, bounded):
  +same = Laws.scale_lane_address_refinement(eligible, safe, deterministic, tile, thread, bounded)
  (Equal.cong(Nat, Nat, Spec.bytes,
    Laws.scheduled_scale_address(eligible, safe, deterministic, tile, thread),
    Spec.scale_generic_address(tile, thread), same),
    Equal.cong(Nat, Nat, address => Spec.bytes(1n+address),
      Laws.scheduled_scale_address(eligible, safe, deterministic, tile, thread),
      Spec.scale_generic_address(tile, thread), same))

def Laws.scale_lane_address_wrap(mask, tile, thread):
  Equal.cong(Nat, Nat, pipe => Spec.scale_slot_address(Nat.mul(2n, Nat.div(pipe, 2n)),
    Spec.scale_masked_index(mask, thread, Spec.scale_generic_index(thread))),
    Spec.slot(8n+tile, 8n), Spec.slot(tile, 8n), mod8_period(tile))

def Laws.scale_lane_refresh_operands(eligible, safe, deterministic, tile, thread,
    previous, observe, selected, bounded):
  Equal.cong(Nat, Spec.ScaleBanks,
    address => Spec.refresh_zero(Impl.scale_refresh(Spec.slot(tile, 8n)), observe(address), previous),
    Laws.scheduled_scale_address(eligible, safe, deterministic, tile, thread),
    Spec.scale_generic_address(tile, thread),
    Laws.scale_lane_address_refinement(eligible, safe, deterministic, tile, thread, bounded))

def Laws.scale_lane_initial_restart(eligible, safe, deterministic, thread,
    old_zero, old_one, observe, selected, bounded):
  Equal.cong(Nat, Spec.ScaleBanks,
    address => Spec.ScaleBanks{Spec.Loaded{observe(address)}, old_one},
    Laws.scheduled_scale_address(eligible, safe, deterministic, 0n, thread),
    Spec.scale_generic_address(0n, thread),
    Laws.scale_lane_address_refinement(eligible, safe, deterministic, 0n, thread, bounded))
