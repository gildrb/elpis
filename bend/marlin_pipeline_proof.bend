# Constructor proofs and structural Nat/list induction; no assumed native facts.
# Main owns the pinned-toolchain root proof/production checks after this freezes.
import Base
import ./marlin_pipeline.bend as Impl
import ./marlin_pipeline_spec.bend as Spec
import ./marlin_pipeline_laws.bend as Laws
import ./spec.bend as Sequence
import ./numerical_proof.bend as NumericalProof

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
