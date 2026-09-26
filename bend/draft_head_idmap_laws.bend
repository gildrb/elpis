# Semantic obligations for the pruned int4 draft head of ext patch 9005c (S: / Q: / D: refs as in
# draft_head_idmap.bend) over the Nat / list model draft_head_idmap.bend and its independent reference
# draft_head_idmap_spec.bend. Quantified over every vocabulary of V = 128 nb ids, every kept-block list, block order,
# candidate list, per-token value assignment, policy state and anchor / reset sequence (the served instance is
# V = 248320, nb = 1940, N = 896 or 1024, window 32, trigger 2, hold 128, top-16). Model boundaries as stated in
# draft_head_idmap.bend: Nat values for the kernel's fp32 values under their order, the merge network by its top-k
# contract, column-local packing (equal per-token values in the permuted copy) and Python / torch / CUDA semantics.
import Base
import ./draft_head_idmap.bend as Impl
import ./draft_head_idmap_spec.bend as Spec

# ==== 1. the column -> token id map is a bijection on [0, V) ====

# The map Q4DraftHead builds (kept rows, then the other rows, per 128-id block) is the reference "kept ids ascending,
# then every other id ascending", for any kept-block list.
law idmap_equals_spec:
  for +kept: List<&2, Nat>
  for +nb: Nat
  {Impl.idm_id_map(kept, nb) == Spec.ids_id_map(kept, nb) : List<&2, Nat>}

# V columns ...
law idmap_length:
  for +kept: List<&2, Nat>
  for +nb: Nat
  {List.length(&2, Nat, Impl.idm_id_map(kept, nb)) == Nat.mul(nb, 128n) : Nat}

# ... carrying every token id t < V exactly once and no id >= V: a bijection from columns onto [0, V).
law idmap_bijection:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +t: Nat
  {Spec.ids_count(Impl.idm_id_map(kept, nb), t) == Spec.ids_bit(Nat.is_lt(t, Nat.mul(nb, 128n))) : Nat}

# ==== 2. the first 128 N columns are the kept blocks' ids, strictly increasing ====

# For N distinct kept blocks < nb, the pruned call's map im[:keep_cols] is exactly the kept ids ascending ...
law idmap_prefix_kept_ids:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool}
  {List.take(&2, Nat, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept)) == Spec.ids_kept_ids(kept, nb) : List<&2, Nat>}

# ... of length 128 N ...
law idmap_prefix_length:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool}
  {Impl.idm_keep_cols(kept) == Nat.mul(128n, List.length(&2, Nat, kept)) : Nat}

# ... strictly increasing ...
law idmap_prefix_increasing:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool}
  {Spec.ids_increasing(List.take(&2, Nat, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept))) == True{} : Bool}

# ... and landing exactly on the kept blocks' ids: every id of a kept block once, nothing else.
law idmap_prefix_exact:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +t: Nat
  for ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool}
  {Spec.ids_count(List.take(&2, Nat, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept)), t) ==
    Spec.ids_bit(Bool.and(Nat.is_lt(t, Nat.mul(nb, 128n)), Spec.ids_member(kept, Nat.div(t, 128n)))) : Nat}

# ==== 3. kept blocks = sorted(order[:N]); invalid block lists are rejected ====

# The table check accepts exactly the prefixes of N >= 1 distinct whole blocks inside the vocabulary: any duplicate,
# out-of-range entry or too-short order is rejected.
law kept_accepts_exactly:
  for +order: List<&2, Nat>
  for +n: Nat
  for +vocab: Nat
  {Impl.idm_kept_ok(order, n, vocab) == Spec.ids_prefix_ok(order, n, vocab) : Bool}

# A permutation of the nb blocks is accepted for every 1 <= N <= nb.
law kept_perm_accepted:
  for +order: List<&2, Nat>
  for +nb: Nat
  for +n: Nat
  for perm: {Spec.ids_is_perm(order, nb) == True{} : Bool}
  for range: {Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, nb)) == True{} : Bool}
  {Impl.idm_kept_ok(order, n, Nat.mul(nb, 128n)) == True{} : Bool}

# sorted(order[:N]) has the entries of order[:N] ...
law kept_members:
  for +order: List<&2, Nat>
  for +n: Nat
  for +b: Nat
  {Spec.ids_member(Impl.idm_kept_blocks(order, n), b) == Spec.ids_member(List.take(&2, Nat, order, n), b) : Bool}

# ... as many of them ...
law kept_length:
  for +order: List<&2, Nat>
  for +n: Nat
  {List.length(&2, Nat, Impl.idm_kept_blocks(order, n)) == List.length(&2, Nat, List.take(&2, Nat, order, n)) : Nat}

# ... strictly increasing when they are distinct (so it is the unique ascending listing of that set).
law kept_increasing:
  for +order: List<&2, Nat>
  for +n: Nat
  for nd: {Spec.ids_nodup(List.take(&2, Nat, order, n)) == True{} : Bool}
  {Spec.ids_increasing(Impl.idm_kept_blocks(order, n)) == True{} : Bool}

# An accepted table yields distinct kept blocks < nb (the id-map and top-k laws' precondition) ...
law kept_blocks_in:
  for +order: List<&2, Nat>
  for +n: Nat
  for +nb: Nat
  for ok: {Impl.idm_kept_ok(order, n, Nat.mul(nb, 128n)) == True{} : Bool}
  {Spec.ids_blocks_in(Impl.idm_kept_blocks(order, n), nb) == True{} : Bool}

# ... that Q4DraftHead's own check accepts.
law kept_head_accepts:
  for +order: List<&2, Nat>
  for +n: Nat
  for +nb: Nat
  for ok: {Impl.idm_kept_ok(order, n, Nat.mul(nb, 128n)) == True{} : Bool}
  {Impl.idm_head_ok(Impl.idm_kept_blocks(order, n), Nat.mul(nb, 128n)) == True{} : Bool}

# ==== 4. top-k by (value desc, token id asc) does not depend on column order ====

# The running top-k list is the first k entries of the full ranking.
law topk_ranked_prefix:
  for +k: Nat
  for +xs: List<&2, Spec.IdmCand>
  {Impl.idm_topk(k, xs) == Spec.ids_topk(k, xs) : List<&2, Spec.IdmCand>}

# Two duplicate-free column lists with the same entries, in any orders, give the same top-k.
law topk_order_free:
  for +k: Nat
  for +xs: List<&2, Spec.IdmCand>
  for +ys: List<&2, Spec.IdmCand>
  for nx: {Spec.ids_cnodup(xs) == True{} : Bool}
  for ny: {Spec.ids_cnodup(ys) == True{} : Bool}
  for same: {Spec.ids_same_set(xs, ys) == True{} : Bool}
  {Impl.idm_topk(k, xs) == Impl.idm_topk(k, ys) : List<&2, Spec.IdmCand>}

# The full call on the permuted copy (id_map over all V columns) equals the identity call, for any kept list.
law topk_full_call:
  for +k: Nat
  for +vals: Impl.IdmVals
  for +kept: List<&2, Nat>
  for +nb: Nat
  {Impl.idm_head_call(k, vals, kept, nb, False{}) == Impl.idm_call(k, vals, None{}, Nat.mul(nb, 128n)) : List<&2, Spec.IdmCand>}

# The prefix call equals the full ranking restricted to kept ids, cut to k.
law topk_pruned_call:
  for +k: Nat
  for +vals: Impl.IdmVals
  for +kept: List<&2, Nat>
  for +nb: Nat
  for ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool}
  {Impl.idm_head_call(k, vals, kept, nb, True{}) ==
    List.take(&2, Spec.IdmCand, Spec.ids_keep_kept(Spec.ids_rank(Impl.idm_cols(vals, Impl.idm_tokens(None{}, Nat.mul(nb, 128n)))), kept), k) : List<&2, Spec.IdmCand>}

# ==== 5. the switch-back policy as a state machine ====

# The initial state is valid in either mode ...
law policy_init_valid:
  for +adaptive: Bool
  {Spec.ids_valid_pol(adaptive, Impl.idm_init(), Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}

# ... and selects the pruned head.
law policy_init_pruned:
  {Impl.idm_use(Impl.idm_init()) == True{} : Bool}

# Every observe_anchor preserves validity in the policy's mode (adaptive or static; any anchor, any kept list).
law policy_step_valid:
  for +adaptive: Bool
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +st: Spec.IdmPol
  for +tok: Impl.IdmTok
  for v: {Spec.ids_valid_pol(adaptive, st, Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}
  {Spec.ids_valid_pol(adaptive, Impl.idm_observe(adaptive, kept, nb, st, tok), Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}

# reset() returns exactly the initial state, from any state (mid-hold included).
law policy_reset_initial:
  for +st: Spec.IdmPol
  {Impl.idm_reset(st) == Impl.idm_init() : Spec.IdmPol}

# Every state reachable by observe_anchor / reset calls is valid.
law policy_run_valid:
  for +evs: List<&2, Impl.IdmEv>
  for +adaptive: Bool
  for +kept: List<&2, Nat>
  for +nb: Nat
  {Spec.ids_valid_pol(adaptive, Impl.idm_run(evs, adaptive, kept, nb, Impl.idm_init()), Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}

# The pruned head is never selected while a hold is pending, in any valid (so any reachable) state.
law policy_never_pruned_in_hold:
  for +adaptive: Bool
  for +st: Spec.IdmPol
  for v: {Spec.ids_valid_pol(adaptive, st, Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}
  {Bool.and(Impl.idm_use(st), Nat.is_lt(0n, Impl.idm_hold(st))) == False{} : Bool}

# A second out-of-subset anchor inside the window (one set flag among the last 31) triggers the fallback: that round
# and the next FALLBACK_HOLD - 1 rounds use the full head, whatever their anchors, and the round after is pruned
# again: exactly FALLBACK_HOLD full rounds counting the triggering round.
law policy_hold_exact:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +recent: List<&2, Bool>
  for +t0: Impl.IdmTok
  for +toks: List<&2, Impl.IdmTok>
  for one: {Spec.ids_trues(List.take(&2, Bool, recent, 31n)) == 1n : Nat}
  for hit: {Impl.idm_oos(kept, nb, t0) == True{} : Bool}
  for len: {List.length(&2, Impl.IdmTok, toks) == Impl.idm_hold_len() : Nat}
  {Impl.idm_uses(t0 <> toks, True{}, kept, nb, Spec.IdmPol{recent, 0n, True{}}) ==
    List.append(&2, Bool, Spec.ids_falses(Impl.idm_hold_len()), True{} <> Nil{}) : List<&2, Bool>}

# Anchors outside [0, vocab) are not evidence: token ids >= V ...
law policy_big_not_evidence:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +t: Nat
  for big: {Nat.is_le(Nat.mul(nb, 128n), t) == True{} : Bool}
  {Impl.idm_oos(kept, nb, Impl.IdmPos{t}) == False{} : Bool}

# ... and negative anchors ...
law policy_negative_not_evidence:
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +m: Nat
  {Impl.idm_oos(kept, nb, Impl.IdmNeg{m}) == False{} : Bool}

# ... and a non-evidence anchor never starts or extends a hold ...
law policy_no_evidence_no_hold:
  for +adaptive: Bool
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +st: Spec.IdmPol
  for +tok: Impl.IdmTok
  for v: {Spec.ids_valid_pol(adaptive, st, Impl.idm_window(), Impl.idm_trigger(), Impl.idm_hold_len()) == True{} : Bool}
  for no: {Impl.idm_oos(kept, nb, tok) == False{} : Bool}
  {Nat.is_le(Impl.idm_hold(Impl.idm_observe(adaptive, kept, nb, st, tok)), Impl.idm_hold(st)) == True{} : Bool}

# ... nor adds a set flag to the window.
law policy_no_evidence_no_flag:
  for +adaptive: Bool
  for +kept: List<&2, Nat>
  for +nb: Nat
  for +st: Spec.IdmPol
  for +tok: Impl.IdmTok
  for no: {Impl.idm_oos(kept, nb, tok) == False{} : Bool}
  {Nat.is_le(Spec.ids_trues(Impl.idm_recent(Impl.idm_observe(adaptive, kept, nb, st, tok))), Spec.ids_trues(Impl.idm_recent(st))) == True{} : Bool}
