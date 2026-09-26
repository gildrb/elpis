# Proof of the pruned draft head laws (draft_head_idmap_laws.bend) about the Bend model draft_head_idmap.bend and its
# reference draft_head_idmap_spec.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign proof
# code or answer tables. Every def precedes its uses. Arithmetic lemmas (ar_*) come from the proven m16 partition
# proof module.
import Base
import ./draft_head_idmap.bend as Impl
import ./draft_head_idmap_spec.bend as Spec
import ./draft_head_idmap_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as MP

# ==== Bool helpers ====

def idp_beq_refl(b: Bool) -> {Spec.ids_beq(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# not(b) == True forces b == False.
def idp_not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MP.ar_false_true(e))
    case False{}:
      {==}

# x < 2 forces 2 <= x to be False.
def idp_lt2(+x: Nat, e: {Nat.is_lt(x, 2n) == True{} : Bool}) -> {Nat.is_le(2n, x) == False{} : Bool}:
  idp_not_true(Nat.is_le(2n, x), Equal.trans(Bool, Bool.not(Nat.is_le(2n, x)), Nat.is_lt(x, 2n), True{},
    Equal.sym(Bool, Nat.is_lt(x, 2n), Bool.not(Nat.is_le(2n, x)), MP.ar_lt_not_le(x, 2n)), e))

# ==== list helpers ====

# |take(xs, n)| <= n
def idp_len_take_le(-A: Data, xs: List<&2, A>, +n: Nat)
  -> {Nat.is_le(List.length(&2, A, List.take(&2, A, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      MP.ar_h_le_zero(n)
    case (h <> t) 0n:
      {==}
    case (h <> t) 1n+p:
      idp_len_take_le(A, t, p)

# trues(take(r, n)) <= trues(r)
def idp_trues_take_le(r: List<&2, Bool>, +n: Nat)
  -> {Nat.is_le(Spec.ids_trues(List.take(&2, Bool, r, n)), Spec.ids_trues(r)) == True{} : Bool}:
  match r n:
    case Nil{} _:
      {==}
    case (+h <> +t) 0n:
      MP.ar_h_le_zero(Spec.ids_trues(h <> t))
    case (+h <> +t) 1n+p:
      %Equal.sym(Bool, Nat.is_le(Nat.add(Spec.ids_bit(h), Spec.ids_trues(List.take(&2, Bool, t, p))), Nat.add(Spec.ids_bit(h), Spec.ids_trues(t))),
        Nat.is_le(Spec.ids_trues(List.take(&2, Bool, t, p)), Spec.ids_trues(t)),
        MP.ar_le_add_cancel(Spec.ids_bit(h), Spec.ids_trues(List.take(&2, Bool, t, p)), Spec.ids_trues(t))) : {_ == True{} : Bool}
      idp_trues_take_le(t, p)

# ==== policy: validity parts ====

def idp_mk(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    p1: {Spec.ids_beq(use, Spec.ids_is_zero(hold)) == True{} : Bool},
    p2: {Nat.is_le(hold, 128n) == True{} : Bool},
    p3: {Nat.is_le(List.length(&2, Bool, recent), 32n) == True{} : Bool},
    p4: {Nat.is_lt(Spec.ids_trues(recent), 2n) == True{} : Bool},
    p5: {Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)) == True{} : Bool})
  -> {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool}:
  MP.ar_and_intro(Spec.ids_beq(use, Spec.ids_is_zero(hold)),
    Bool.and(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))))),
    p1,
    MP.ar_and_intro(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)))),
      p2,
      MP.ar_and_intro(Nat.is_le(List.length(&2, Bool, recent), 32n),
        Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))),
        p3,
        MP.ar_and_intro(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)),
          p4, p5))))

# The conjuncts after the first one.
def idp_r1(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Bool.and(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))))) == True{} : Bool}:
  MP.ar_and_r(Spec.ids_beq(use, Spec.ids_is_zero(hold)),
    Bool.and(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))))), v)

def idp_v1(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Spec.ids_beq(use, Spec.ids_is_zero(hold)) == True{} : Bool}:
  MP.ar_and_l(Spec.ids_beq(use, Spec.ids_is_zero(hold)),
    Bool.and(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))))), v)

def idp_v2(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Nat.is_le(hold, 128n) == True{} : Bool}:
  MP.ar_and_l(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
    Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)))),
    idp_r1(recent, hold, use, v))

def idp_r2(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
      Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)))) == True{} : Bool}:
  MP.ar_and_r(Nat.is_le(hold, 128n), Bool.and(Nat.is_le(List.length(&2, Bool, recent), 32n),
    Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)))),
    idp_r1(recent, hold, use, v))

def idp_v3(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, Bool, recent), 32n) == True{} : Bool}:
  MP.ar_and_l(Nat.is_le(List.length(&2, Bool, recent), 32n),
    Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))),
    idp_r2(recent, hold, use, v))

def idp_r3(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))) == True{} : Bool}:
  MP.ar_and_r(Nat.is_le(List.length(&2, Bool, recent), 32n),
    Bool.and(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent))),
    idp_r2(recent, hold, use, v))

def idp_v4(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Nat.is_lt(Spec.ids_trues(recent), 2n) == True{} : Bool}:
  MP.ar_and_l(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)),
    idp_r3(recent, hold, use, v))

def idp_v5(+recent: List<&2, Bool>, +hold: Nat, +use: Bool,
    v: {Spec.ids_valid(recent, hold, use, 32n, 2n, 128n) == True{} : Bool})
  -> {Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)) == True{} : Bool}:
  MP.ar_and_r(Nat.is_lt(Spec.ids_trues(recent), 2n), Bool.or(Spec.ids_is_zero(hold), Spec.ids_is_nil(recent)),
    idp_r3(recent, hold, use, v))

# ==== law 5: policy ====

def Laws.policy_init_valid(adaptive):
  match adaptive:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.policy_init_pruned():
  {==}

def Laws.policy_reset_initial(st):
  {==}

# A window step on a list of <= 32 flags is valid in adaptive mode.
def idp_fire_valid(f: Bool, +r: List<&2, Bool>, e: {Nat.is_le(2n, Spec.ids_trues(r)) == f : Bool},
    lr: {Nat.is_le(List.length(&2, Bool, r), 32n) == True{} : Bool})
  -> {Spec.ids_valid_pol(True{}, Impl.idm_fire(f, r), 32n, 2n, 128n) == True{} : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      idp_mk(r, 0n, True{}, {==}, {==}, lr,
        Equal.trans(Bool, Nat.is_lt(Spec.ids_trues(r), 2n), Bool.not(Nat.is_le(2n, Spec.ids_trues(r))), True{},
          MP.ar_lt_not_le(Spec.ids_trues(r), 2n),
          Equal.cong(Bool, Bool, x => Bool.not(x), Nat.is_le(2n, Spec.ids_trues(r)), False{}, e)),
        {==})

def Laws.policy_step_valid(adaptive, kept, nb, st, tok, v):
  match adaptive:
    case False{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          match hold:
            case 0n:
              +vv = v
              idp_mk(recent, 0n, True{}, {==}, {==}, idp_v3(recent, 0n, use, vv), idp_v4(recent, 0n, use, vv), {==})
            case 1n+h:
              v
    case True{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          match hold:
            case 0n:
              +r2 = Impl.idm_push(Impl.idm_oos(kept, nb, tok), recent)
              idp_fire_valid(Nat.is_le(2n, Spec.ids_trues(r2)), r2, {==},
                idp_len_take_le(Bool, Impl.idm_oos(kept, nb, tok) <> recent, 32n))
            case 1n+h:
              +vv = v
              +h1 = h
              idp_mk(recent, h1, Spec.ids_is_zero(h1), idp_beq_refl(Spec.ids_is_zero(h1)),
                MP.ar_le_trans(h1, 1n+h1, 128n, MP.ar_h_le_succ(h1), idp_v2(recent, 1n+h1, use, vv)),
                idp_v3(recent, 1n+h1, use, vv), idp_v4(recent, 1n+h1, use, vv),
                idp_or_r(Spec.ids_is_zero(h1), Spec.ids_is_nil(recent), idp_v5(recent, 1n+h1, use, vv)))

# Validity along any call sequence, from any valid state.
def idp_run_valid(evs: List<&2, Impl.IdmEv>, +adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, +st: Spec.IdmPol,
    v: {Spec.ids_valid_pol(adaptive, st, 32n, 2n, 128n) == True{} : Bool})
  -> {Spec.ids_valid_pol(adaptive, Impl.idm_run(evs, adaptive, kept, nb, st), 32n, 2n, 128n) == True{} : Bool}:
  match evs:
    case Nil{}:
      v
    case ev <> rest:
      match ev:
        case Impl.IdmObs{tok}:
          +t1 = tok
          idp_run_valid(rest, adaptive, kept, nb, Impl.idm_observe(adaptive, kept, nb, st, t1),
            Laws.policy_step_valid(adaptive, kept, nb, st, t1, v))
        case Impl.IdmReset{}:
          idp_run_valid(rest, adaptive, kept, nb, Impl.idm_init(), Laws.policy_init_valid(adaptive))

def Laws.policy_run_valid(evs, adaptive, kept, nb):
  idp_run_valid(evs, adaptive, kept, nb, Impl.idm_init(), Laws.policy_init_valid(adaptive))

def idp_never(+recent: List<&2, Bool>, hd: Nat, u: Bool,
    p1: {Spec.ids_beq(u, Spec.ids_is_zero(hd)) == True{} : Bool})
  -> {Bool.and(u, Nat.is_lt(0n, hd)) == False{} : Bool}:
  match hd:
    case 0n:
      match u:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+h:
      match u:
        case True{}:
          Empty.absurd({True{} == False{} : Bool}, MP.ar_false_true(p1))
        case False{}:
          {==}

def Laws.policy_never_pruned_in_hold(adaptive, st, v):
  match st:
    case Spec.IdmPol{recent, hold, use}:
      +hd = hold
      +us = use
      idp_never(recent, hd, us, idp_v1(recent, hd, us,
        MP.ar_and_r(Bool.or(adaptive, Spec.ids_is_zero(hd)), Spec.ids_valid(recent, hd, us, 32n, 2n, 128n), v)))

# The second set flag in the window fires the fallback.
def idp_first(f: Bool, +recent: List<&2, Bool>, hf: {f == True{} : Bool},
    one: {Spec.ids_trues(List.take(&2, Bool, recent, 31n)) == 1n : Nat})
  -> {Impl.idm_window_step(Impl.idm_push(f, recent)) == Spec.IdmPol{Nil{}, 128n, False{}} : Spec.IdmPol}:
  match f:
    case True{}:
      %Equal.sym(Nat, Spec.ids_trues(List.take(&2, Bool, recent, 31n)), 1n, one) : {Impl.idm_fire(Nat.is_le(2n, Nat.add(1n, _)), True{} <> List.take(&2, Bool, recent, 31n)) == Spec.IdmPol{Nil{}, 128n, False{}} : Spec.IdmPol}
      {==}
    case False{}:
      Empty.absurd({Impl.idm_window_step(Impl.idm_push(False{}, recent)) == Spec.IdmPol{Nil{}, 128n, False{}} : Spec.IdmPol},
        MP.ar_false_true(hf))

# From hold 1 + h, the next rounds are full while the hold lasts, then pruned: h full rounds, then a pruned one.
def idp_countdown(h: Nat, toks: List<&2, Impl.IdmTok>, +kept: List<&2, Nat>, +nb: Nat,
    len: {List.length(&2, Impl.IdmTok, toks) == 1n+h : Nat})
  -> {Impl.idm_uses(toks, True{}, kept, nb, Spec.IdmPol{Nil{}, 1n+h, False{}}) ==
      List.append(&2, Bool, Spec.ids_falses(h), True{} <> Nil{}) : List<&2, Bool>}:
  match h:
    case 0n:
      match toks:
        case Nil{}:
          Empty.absurd({Impl.idm_uses(Nil{}, True{}, kept, nb, Spec.IdmPol{Nil{}, 1n, False{}}) ==
            True{} <> Nil{} : List<&2, Bool>}, MP.ar_zero_succ(0n, len))
        case tok <> rest:
          match rest:
            case Nil{}:
              {==}
            case r <> more:
              Empty.absurd({Impl.idm_uses(tok <> r <> more, True{}, kept, nb, Spec.IdmPol{Nil{}, 1n, False{}}) ==
                True{} <> Nil{} : List<&2, Bool>},
                MP.ar_zero_succ(List.length(&2, Impl.IdmTok, more),
                  Equal.sym(Nat, 1n+List.length(&2, Impl.IdmTok, more), 0n,
                    MP.ar_succ_inj(1n+List.length(&2, Impl.IdmTok, more), 0n, len))))
    case 1n+g:
      match toks:
        case Nil{}:
          Empty.absurd({Impl.idm_uses(Nil{}, True{}, kept, nb, Spec.IdmPol{Nil{}, 1n+1n+g, False{}}) ==
            List.append(&2, Bool, Spec.ids_falses(1n+g), True{} <> Nil{}) : List<&2, Bool>}, MP.ar_zero_succ(1n+g, len))
        case tok <> rest:
          Equal.cong(List<&2, Bool>, List<&2, Bool>, x => False{} <> x,
            Impl.idm_uses(rest, True{}, kept, nb, Spec.IdmPol{Nil{}, 1n+g, False{}}),
            List.append(&2, Bool, Spec.ids_falses(g), True{} <> Nil{}),
            idp_countdown(g, rest, kept, nb, MP.ar_succ_inj(List.length(&2, Impl.IdmTok, rest), 1n+g, len)))

def Laws.policy_hold_exact(kept, nb, recent, t0, toks, one, hit, len):
  %Equal.sym(Spec.IdmPol, Impl.idm_window_step(Impl.idm_push(Impl.idm_oos(kept, nb, t0), recent)), Spec.IdmPol{Nil{}, 128n, False{}},
    idp_first(Impl.idm_oos(kept, nb, t0), recent, hit, one)) : {Impl.idm_use(_) <> Impl.idm_uses(toks, True{}, kept, nb, _) == List.append(&2, Bool, Spec.ids_falses(128n), True{} <> Nil{}) : List<&2, Bool>}
  Equal.cong(List<&2, Bool>, List<&2, Bool>, x => False{} <> x,
    Impl.idm_uses(toks, True{}, kept, nb, Spec.IdmPol{Nil{}, 128n, False{}}),
    List.append(&2, Bool, Spec.ids_falses(127n), True{} <> Nil{}),
    idp_countdown(127n, toks, kept, nb, len))

def Laws.policy_big_not_evidence(kept, nb, t, big):
  %Equal.sym(Bool, Nat.is_lt(Nat.div(t, 128n), nb), Nat.is_lt(t, Nat.mul(nb, 128n)), MP.ar_div_lt(nb, t, 128n, {==})) : {Bool.and(_, Bool.not(Spec.ids_member(kept, Nat.div(t, 128n)))) == False{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(t, Nat.mul(nb, 128n)), Bool.not(Nat.is_le(Nat.mul(nb, 128n), t)), MP.ar_lt_not_le(t, Nat.mul(nb, 128n))) : {Bool.and(_, Bool.not(Spec.ids_member(kept, Nat.div(t, 128n)))) == False{} : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.mul(nb, 128n), t), True{}, big) : {Bool.and(Bool.not(_), Bool.not(Spec.ids_member(kept, Nat.div(t, 128n)))) == False{} : Bool}
  {==}

def Laws.policy_negative_not_evidence(kept, nb, m):
  {==}

def idp_fire_hold0(f: Bool, +r: List<&2, Bool>, e: {f == False{} : Bool})
  -> {Nat.is_le(Impl.idm_hold(Impl.idm_fire(f, r)), 0n) == True{} : Bool}:
  match f:
    case True{}:
      Empty.absurd({Nat.is_le(Impl.idm_hold(Impl.idm_fire(True{}, r)), 0n) == True{} : Bool}, MP.ar_true_false(e))
    case False{}:
      {==}

def Laws.policy_no_evidence_no_hold(adaptive, kept, nb, st, tok, v, no):
  match adaptive:
    case False{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          MP.ar_le_refl(hold)
    case True{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          match hold:
            case 1n+h:
              MP.ar_h_le_succ(h)
            case 0n:
              +r = recent
              +x = Spec.ids_trues(List.take(&2, Bool, r, 31n))
              +vv = v
              %Equal.sym(Bool, Impl.idm_oos(kept, nb, tok), False{}, no) : {Nat.is_le(Impl.idm_hold(Impl.idm_window_step(Impl.idm_push(_, r))), 0n) == True{} : Bool}
              idp_fire_hold0(Nat.is_le(2n, x), False{} <> List.take(&2, Bool, r, 31n),
                idp_lt2(x, MP.ar_le_lt_trans(x, Spec.ids_trues(r), 2n, idp_trues_take_le(r, 31n), idp_v4(r, 0n, use, vv))))

def idp_fire_recent_le(f: Bool, +r: List<&2, Bool>, +x: Nat, h: {Nat.is_le(Spec.ids_trues(r), x) == True{} : Bool})
  -> {Nat.is_le(Spec.ids_trues(Impl.idm_recent(Impl.idm_fire(f, r))), x) == True{} : Bool}:
  match f:
    case True{}:
      MP.ar_h_le_zero(x)
    case False{}:
      h

def Laws.policy_no_evidence_no_flag(adaptive, kept, nb, st, tok, no):
  match adaptive:
    case False{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          MP.ar_le_refl(Spec.ids_trues(recent))
    case True{}:
      match st:
        case Spec.IdmPol{recent, hold, use}:
          match hold:
            case 1n+h:
              MP.ar_le_refl(Spec.ids_trues(recent))
            case 0n:
              +r = recent
              %Equal.sym(Bool, Impl.idm_oos(kept, nb, tok), False{}, no) : {Nat.is_le(Spec.ids_trues(Impl.idm_recent(Impl.idm_window_step(Impl.idm_push(_, r)))), Spec.ids_trues(r)) == True{} : Bool}
              idp_fire_recent_le(Nat.is_le(2n, Spec.ids_trues(List.take(&2, Bool, r, 31n))), False{} <> List.take(&2, Bool, r, 31n),
                Spec.ids_trues(r), idp_trues_take_le(r, 31n))

# ==== law 1: id map ====

# -- generic list lemmas --

def idp_take0(-A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, 0n) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def idp_len_app(-A: Data, xs: List<&2, A>, +ys: List<&2, A>)
  -> {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      +r = rest
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, A, List.append(&2, A, r, ys)),
        Nat.add(List.length(&2, A, r), List.length(&2, A, ys)), idp_len_app(A, r, ys))

def idp_take_app(-A: Data, xs: List<&2, A>, +ys: List<&2, A>)
  -> {List.take(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      idp_take0(A, ys)
    case +x <> +rest:
      Equal.cong(List<&2, A>, List<&2, A>, l => x <> l, List.take(&2, A, List.append(&2, A, rest, ys), List.length(&2, A, rest)),
        rest, idp_take_app(A, rest, ys))

def idp_count_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +t: Nat)
  -> {Spec.ids_count(List.append(&2, Nat, xs, ys), t) == Nat.add(Spec.ids_count(xs, t), Spec.ids_count(ys, t)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Nat, Spec.ids_count(List.append(&2, Nat, rest, ys), t), Nat.add(Spec.ids_count(rest, t), Spec.ids_count(ys, t)), idp_count_app(rest, ys, t)) : {Nat.add(Spec.ids_bit(Nat.is_eq(x, t)), _) == Nat.add(Spec.ids_count(x <> rest, t), Spec.ids_count(ys, t)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(Spec.ids_bit(Nat.is_eq(x, t)), Spec.ids_count(rest, t)), Spec.ids_count(ys, t)),
        Nat.add(Spec.ids_bit(Nat.is_eq(x, t)), Nat.add(Spec.ids_count(rest, t), Spec.ids_count(ys, t))),
        MP.ar_add_assoc(Spec.ids_bit(Nat.is_eq(x, t)), Spec.ids_count(rest, t), Spec.ids_count(ys, t)))

# -- Spec.ids_range --

def idp_rcons_app(p: Bool, +x: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>)
  -> {Spec.ids_range.cons(p, x, List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Spec.ids_range.cons(p, x, xs), ys) : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# range over m + n ids = range over the first m, then over the next n.
def idp_range_split(m: Nat, +n: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat)
  -> {Spec.ids_range(Nat.add(m, n), want, kept, lo) ==
      List.append(&2, Nat, Spec.ids_range(m, want, kept, lo), Spec.ids_range(n, want, kept, Nat.add(m, lo))) : List<&2, Nat>}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      +q1 = q
      +p = Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n)))
      %MP.ar_add_succ_r(q1, lo) : {Spec.ids_range(Nat.add(1n+q1, n), want, kept, lo) == List.append(&2, Nat, Spec.ids_range(1n+q1, want, kept, lo), Spec.ids_range(n, want, kept, _)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Spec.ids_range(Nat.add(q1, n), want, kept, 1n+lo), List.append(&2, Nat, Spec.ids_range(q1, want, kept, 1n+lo), Spec.ids_range(n, want, kept, Nat.add(q1, 1n+lo))), idp_range_split(q1, n, want, kept, 1n+lo)) : {Spec.ids_range.cons(p, lo, _) == List.append(&2, Nat, Spec.ids_range.cons(p, lo, Spec.ids_range(q1, want, kept, 1n+lo)), Spec.ids_range(n, want, kept, Nat.add(q1, 1n+lo))) : List<&2, Nat>}
      idp_rcons_app(p, lo, Spec.ids_range(q1, want, kept, 1n+lo), Spec.ids_range(n, want, kept, Nat.add(q1, 1n+lo)))

def idp_sel(p: Bool, xs: List<&2, Nat>) -> List<&2, Nat>:
  match p:
    case True{}:
      xs
    case False{}:
      Nil{}

def idp_sel_nil(p: Bool) -> {Nil{} == idp_sel(p, Nil{}) : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_sel_cons(p: Bool, +x: Nat, +xs: List<&2, Nat>)
  -> {Spec.ids_range.cons(p, x, idp_sel(p, xs)) == idp_sel(p, x <> xs) : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# j < j + 1 + l <= 128 gives j < 128.
def idp_j_small(+j: Nat, +l: Nat, h: {Nat.is_le(Nat.add(j, 1n+l), 128n) == True{} : Bool})
  -> {Nat.is_lt(j, 128n) == True{} : Bool}:
  MP.ar_lt_le_trans(j, Nat.add(j, 1n+l), 128n,
    Equal.trans(Bool, Nat.is_lt(j, Nat.add(j, 1n+l)), Nat.is_le(1n+j, Nat.add(j, 1n+l)), True{},
      MP.ar_lt_succ_le(j, Nat.add(j, 1n+l)),
      %Equal.sym(Nat, Nat.add(j, 1n+l), 1n+Nat.add(j, l), MP.ar_add_succ_r(j, l)) : {Nat.is_le(1n+j, _) == True{} : Bool}
      MP.ar_le_add_r(j, l)),
    h)

# Inside one 128-id block b (offsets j .. j + len - 1 <= 127) the range keeps all ids or none.
def idp_block(len: Nat, +want: Bool, +kept: List<&2, Nat>, +b: Nat, +j: Nat,
    h: {Nat.is_le(Nat.add(j, len), 128n) == True{} : Bool})
  -> {Spec.ids_range(len, want, kept, Nat.add(Nat.mul(b, 128n), j)) ==
      idp_sel(Spec.ids_pick(want, Spec.ids_member(kept, b)), Impl.idm_row(len, Nat.add(Nat.mul(b, 128n), j))) : List<&2, Nat>}:
  match len:
    case 0n:
      idp_sel_nil(Spec.ids_pick(want, Spec.ids_member(kept, b)))
    case 1n+l:
      +l1 = l
      +hh = h
      +lo = Nat.add(Nat.mul(b, 128n), j)
      +p = Spec.ids_pick(want, Spec.ids_member(kept, b))
      +dq = MP.ard_fst({Nat.div(Nat.add(Nat.mul(b, 128n), j), 128n) == b : Nat}, {Nat.mod(Nat.add(Nat.mul(b, 128n), j), 128n) == j : Nat},
        MP.ar_div_unique(b, j, 128n, idp_j_small(j, l1, hh)))
      %Equal.sym(Nat, Nat.div(lo, 128n), b, dq) : {Spec.ids_range.cons(Spec.ids_pick(want, Spec.ids_member(kept, _)), lo, Spec.ids_range(l1, want, kept, 1n+lo)) == idp_sel(p, lo <> Impl.idm_row(l1, 1n+lo)) : List<&2, Nat>}
      %MP.ar_add_succ_r(Nat.mul(b, 128n), j) : {Spec.ids_range.cons(p, lo, Spec.ids_range(l1, want, kept, _)) == idp_sel(p, lo <> Impl.idm_row(l1, _)) : List<&2, Nat>}
      +m1 = Nat.add(Nat.mul(b, 128n), 1n+j)
      %Equal.sym(List<&2, Nat>, Spec.ids_range(l1, want, kept, m1), idp_sel(p, Impl.idm_row(l1, m1)),
        idp_block(l1, want, kept, b, 1n+j, %MP.ar_add_succ_r(j, l1) : {Nat.is_le(_, 128n) == True{} : Bool}; hh)) : {Spec.ids_range.cons(p, lo, _) == idp_sel(p, lo <> Impl.idm_row(l1, Nat.add(Nat.mul(b, 128n), 1n+j))) : List<&2, Nat>}
      idp_sel_cons(p, lo, Impl.idm_row(l1, Nat.add(Nat.mul(b, 128n), 1n+j)))

def idp_pick_eq(want: Bool, v: Bool) -> {Spec.ids_pick(want, v) == Impl.idm_mask_pick(want, v) : Bool}:
  match want:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_rows_cons(p: Bool, +row: List<&2, Nat>, +rest: List<&2, Nat>)
  -> {Impl.idm_rows.cons(p, row, rest) == List.append(&2, Nat, idp_sel(p, row), rest) : List<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# One whole block at offset 0.
def idp_block0(+want: Bool, +kept: List<&2, Nat>, +b: Nat)
  -> {Spec.ids_range(128n, want, kept, Nat.mul(b, 128n)) ==
      idp_sel(Spec.ids_pick(want, Spec.ids_member(kept, b)), Impl.idm_row(128n, Nat.mul(b, 128n))) : List<&2, Nat>}:
  %MP.ar_add_zero_r(Nat.mul(b, 128n)) : {Spec.ids_range(128n, want, kept, _) == idp_sel(Spec.ids_pick(want, Spec.ids_member(kept, b)), Impl.idm_row(128n, _)) : List<&2, Nat>}
  idp_block(128n, want, kept, b, 0n, {==})

# The rows of blocks b .. b + cnt - 1 are the reference range over their ids.
def idp_rows(cnt: Nat, +want: Bool, +kept: List<&2, Nat>, +b: Nat)
  -> {Impl.idm_rows(cnt, want, kept, b) == Spec.ids_range(Nat.mul(cnt, 128n), want, kept, Nat.mul(b, 128n)) : List<&2, Nat>}:
  match cnt:
    case 0n:
      {==}
    case 1n+c:
      +c1 = c
      +lo = Nat.mul(b, 128n)
      +m = Spec.ids_member(kept, b)
      +R = Impl.idm_row(128n, lo)
      +X = Spec.ids_range(Nat.mul(c1, 128n), want, kept, Nat.add(128n, lo))
      %Equal.sym(List<&2, Nat>, Impl.idm_rows(c1, want, kept, 1n+b), X, idp_rows(c1, want, kept, 1n+b)) : {Impl.idm_rows.cons(Impl.idm_mask_pick(want, m), R, _) == Spec.ids_range(Nat.add(128n, Nat.mul(c1, 128n)), want, kept, lo) : List<&2, Nat>}
      %idp_pick_eq(want, m) : {Impl.idm_rows.cons(_, R, X) == Spec.ids_range(Nat.add(128n, Nat.mul(c1, 128n)), want, kept, lo) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Spec.ids_range(Nat.add(128n, Nat.mul(c1, 128n)), want, kept, lo),
        List.append(&2, Nat, Spec.ids_range(128n, want, kept, lo), X), idp_range_split(128n, Nat.mul(c1, 128n), want, kept, lo)) : {Impl.idm_rows.cons(Spec.ids_pick(want, m), R, X) == _ : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Spec.ids_range(128n, want, kept, lo), idp_sel(Spec.ids_pick(want, m), R), idp_block0(want, kept, b)) : {Impl.idm_rows.cons(Spec.ids_pick(want, m), R, X) == List.append(&2, Nat, _, X) : List<&2, Nat>}
      idp_rows_cons(Spec.ids_pick(want, m), R, X)

def Laws.idmap_equals_spec(kept, nb):
  +V = Nat.mul(nb, 128n)
  %Equal.sym(List<&2, Nat>, Impl.idm_rows(nb, True{}, kept, 0n), Spec.ids_range(V, True{}, kept, 0n), idp_rows(nb, True{}, kept, 0n)) : {List.append(&2, Nat, _, Impl.idm_rows(nb, False{}, kept, 0n)) == Spec.ids_id_map(kept, nb) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Impl.idm_rows(nb, False{}, kept, 0n), Spec.ids_range(V, False{}, kept, 0n), idp_rows(nb, False{}, kept, 0n)) : {List.append(&2, Nat, Spec.ids_range(V, True{}, kept, 0n), _) == Spec.ids_id_map(kept, nb) : List<&2, Nat>}
  {==}

# -- length --

def idp_len_rcons(p: Bool, +x: Nat, +rest: List<&2, Nat>)
  -> {List.length(&2, Nat, Spec.ids_range.cons(p, x, rest)) == Nat.add(Spec.ids_bit(p), List.length(&2, Nat, rest)) : Nat}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_len_step(m: Bool, +A: Nat, +B: Nat, -l: Nat, ih: {Nat.add(A, B) == l : Nat})
  -> {Nat.add(Nat.add(Spec.ids_bit(m), A), Nat.add(Spec.ids_bit(Bool.not(m)), B)) == 1n+l : Nat}:
  match m:
    case True{}:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(A, B), l, ih)
    case False{}:
      %Equal.sym(Nat, Nat.add(A, 1n+B), 1n+Nat.add(A, B), MP.ar_add_succ_r(A, B)) : {_ == 1n+l : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(A, B), l, ih)

def idp_range_len(len: Nat, +kept: List<&2, Nat>, +lo: Nat)
  -> {Nat.add(List.length(&2, Nat, Spec.ids_range(len, True{}, kept, lo)), List.length(&2, Nat, Spec.ids_range(len, False{}, kept, lo))) == len : Nat}:
  match len:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      +m = Spec.ids_member(kept, Nat.div(lo, 128n))
      +rT = Spec.ids_range(l1, True{}, kept, 1n+lo)
      +rF = Spec.ids_range(l1, False{}, kept, 1n+lo)
      %Equal.sym(Nat, List.length(&2, Nat, Spec.ids_range.cons(m, lo, rT)), Nat.add(Spec.ids_bit(m), List.length(&2, Nat, rT)), idp_len_rcons(m, lo, rT)) : {Nat.add(_, List.length(&2, Nat, Spec.ids_range.cons(Bool.not(m), lo, rF))) == 1n+l1 : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, Spec.ids_range.cons(Bool.not(m), lo, rF)), Nat.add(Spec.ids_bit(Bool.not(m)), List.length(&2, Nat, rF)), idp_len_rcons(Bool.not(m), lo, rF)) : {Nat.add(Nat.add(Spec.ids_bit(m), List.length(&2, Nat, rT)), _) == 1n+l1 : Nat}
      idp_len_step(m, List.length(&2, Nat, rT), List.length(&2, Nat, rF), l1, idp_range_len(l1, kept, 1n+lo))

def Laws.idmap_length(kept, nb):
  +V = Nat.mul(nb, 128n)
  %Equal.sym(List<&2, Nat>, Impl.idm_id_map(kept, nb), Spec.ids_id_map(kept, nb), Laws.idmap_equals_spec(kept, nb)) : {List.length(&2, Nat, _) == V : Nat}
  %Equal.sym(Nat, List.length(&2, Nat, Spec.ids_id_map(kept, nb)), Nat.add(List.length(&2, Nat, Spec.ids_range(V, True{}, kept, 0n)), List.length(&2, Nat, Spec.ids_range(V, False{}, kept, 0n))),
    idp_len_app(Nat, Spec.ids_range(V, True{}, kept, 0n), Spec.ids_range(V, False{}, kept, 0n))) : {_ == V : Nat}
  idp_range_len(V, kept, 0n)

# -- counts --

def idp_count_rcons(p: Bool, +x: Nat, +rest: List<&2, Nat>, +t: Nat)
  -> {Spec.ids_count(Spec.ids_range.cons(p, x, rest), t) == Nat.add(Spec.ids_bit(Bool.and(p, Nat.is_eq(x, t))), Spec.ids_count(rest, t)) : Nat}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_le_lt(+lo: Nat, +t: Nat) -> {Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, lo)) == False{} : Bool}:
  match lo t:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      idp_le_lt(a, b)

def idp_bit_and_true(p: Bool) -> {Nat.add(Spec.ids_bit(Bool.and(p, True{})), 0n) == Spec.ids_bit(p) : Nat}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_bsum(E: Bool, A: Bool, B: Bool, P0: Bool, Pt: Bool,
    ea: {E == True{} : Bool} -> {A == False{} : Bool},
    eb: {E == True{} : Bool} -> {B == True{} : Bool},
    ep: {E == True{} : Bool} -> {P0 == Pt : Bool})
  -> {Nat.add(Spec.ids_bit(Bool.and(P0, E)), Spec.ids_bit(Bool.and(Bool.and(A, B), Pt))) ==
      Spec.ids_bit(Bool.and(Bool.and(Bool.or(E, A), B), Pt)) : Nat}:
  match E:
    case False{}:
      match P0:
        case True{}:
          {==}
        case False{}:
          {==}
    case True{}:
      %Equal.sym(Bool, A, False{}, ea({==})) : {Nat.add(Spec.ids_bit(Bool.and(P0, True{})), Spec.ids_bit(Bool.and(Bool.and(_, B), Pt))) == Spec.ids_bit(Bool.and(Bool.and(Bool.or(True{}, _), B), Pt)) : Nat}
      %Equal.sym(Bool, B, True{}, eb({==})) : {Nat.add(Spec.ids_bit(Bool.and(P0, True{})), Spec.ids_bit(Bool.and(Bool.and(False{}, _), Pt))) == Spec.ids_bit(Bool.and(Bool.and(True{}, _), Pt)) : Nat}
      %Equal.sym(Bool, P0, Pt, ep({==})) : {Nat.add(Spec.ids_bit(Bool.and(_, True{})), 0n) == Spec.ids_bit(Pt) : Nat}
      idp_bit_and_true(Pt)

def idp_ea(+lo: Nat, +t: Nat, e: {Nat.is_eq(lo, t) == True{} : Bool}) -> {Nat.is_le(1n+lo, t) == False{} : Bool}:
  %Equal.sym(Nat, lo, t, MP.ar_eq_true(lo, t, e)) : {Nat.is_le(1n+_, t) == False{} : Bool}
  %MP.ar_lt_succ_le(t, t) : {_ == False{} : Bool}
  MP.ar_lt_irrefl(t)

def idp_eb(+lo: Nat, +t: Nat, +l: Nat, e: {Nat.is_eq(lo, t) == True{} : Bool})
  -> {Nat.is_lt(t, 1n+Nat.add(l, lo)) == True{} : Bool}:
  %Equal.sym(Nat, lo, t, MP.ar_eq_true(lo, t, e)) : {Nat.is_lt(t, 1n+Nat.add(l, _)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(t, 1n+Nat.add(l, t)), Nat.is_le(1n+t, 1n+Nat.add(l, t)), MP.ar_lt_succ_le(t, 1n+Nat.add(l, t))) : {_ == True{} : Bool}
  MP.ar_le_add_l(l, t)

def idp_ep(+want: Bool, +kept: List<&2, Nat>, +lo: Nat, +t: Nat, e: {Nat.is_eq(lo, t) == True{} : Bool})
  -> {Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n))) == Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(t, 128n))) : Bool}:
  Equal.cong(Nat, Bool, x => Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(x, 128n))), lo, t, MP.ar_eq_true(lo, t, e))

# count of t in the range over [lo, lo + len): 1 iff lo <= t < lo + len and t's block is selected.
def idp_rc(len: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat, +t: Nat)
  -> {Spec.ids_count(Spec.ids_range(len, want, kept, lo), t) ==
      Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, Nat.add(len, lo))),
        Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(t, 128n))))) : Nat}:
  match len:
    case 0n:
      %Equal.sym(Bool, Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, lo)), False{}, idp_le_lt(lo, t)) : {0n == Spec.ids_bit(Bool.and(_, Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(t, 128n))))) : Nat}
      {==}
    case 1n+l:
      +l1 = l
      +P0 = Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n)))
      +Pt = Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(t, 128n)))
      +rest = Spec.ids_range(l1, want, kept, 1n+lo)
      %Equal.sym(Nat, Spec.ids_count(Spec.ids_range.cons(P0, lo, rest), t), Nat.add(Spec.ids_bit(Bool.and(P0, Nat.is_eq(lo, t))), Spec.ids_count(rest, t)), idp_count_rcons(P0, lo, rest, t)) : {_ == Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, 1n+Nat.add(l1, lo))), Pt)) : Nat}
      %Equal.sym(Nat, Spec.ids_count(rest, t), Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(1n+lo, t), Nat.is_lt(t, Nat.add(l1, 1n+lo))), Pt)), idp_rc(l1, want, kept, 1n+lo, t)) : {Nat.add(Spec.ids_bit(Bool.and(P0, Nat.is_eq(lo, t))), _) == Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, 1n+Nat.add(l1, lo))), Pt)) : Nat}
      %Equal.sym(Nat, Nat.add(l1, 1n+lo), 1n+Nat.add(l1, lo), MP.ar_add_succ_r(l1, lo)) : {Nat.add(Spec.ids_bit(Bool.and(P0, Nat.is_eq(lo, t))), Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(1n+lo, t), Nat.is_lt(t, _)), Pt))) == Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(lo, t), Nat.is_lt(t, 1n+Nat.add(l1, lo))), Pt)) : Nat}
      %Equal.sym(Bool, Nat.is_le(lo, t), Bool.or(Nat.is_eq(lo, t), Nat.is_le(1n+lo, t)), MP.p8_le_split(lo, t)) : {Nat.add(Spec.ids_bit(Bool.and(P0, Nat.is_eq(lo, t))), Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(1n+lo, t), Nat.is_lt(t, 1n+Nat.add(l1, lo))), Pt))) == Spec.ids_bit(Bool.and(Bool.and(_, Nat.is_lt(t, 1n+Nat.add(l1, lo))), Pt)) : Nat}
      idp_bsum(Nat.is_eq(lo, t), Nat.is_le(1n+lo, t), Nat.is_lt(t, 1n+Nat.add(l1, lo)), P0, Pt,
        e => idp_ea(lo, t, e), e => idp_eb(lo, t, l1, e), e => idp_ep(want, kept, lo, t, e))

def idp_split_bit(R: Bool, m: Bool)
  -> {Nat.add(Spec.ids_bit(Bool.and(R, m)), Spec.ids_bit(Bool.and(R, Bool.not(m)))) == Spec.ids_bit(R) : Nat}:
  match R:
    case True{}:
      match m:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def Laws.idmap_bijection(kept, nb, t):
  +V = Nat.mul(nb, 128n)
  +m = Spec.ids_member(kept, Nat.div(t, 128n))
  +R = Bool.and(Nat.is_le(0n, t), Nat.is_lt(t, Nat.add(V, 0n)))
  %Equal.sym(List<&2, Nat>, Impl.idm_id_map(kept, nb), Spec.ids_id_map(kept, nb), Laws.idmap_equals_spec(kept, nb)) : {Spec.ids_count(_, t) == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Nat, Spec.ids_count(Spec.ids_id_map(kept, nb), t), Nat.add(Spec.ids_count(Spec.ids_range(V, True{}, kept, 0n), t), Spec.ids_count(Spec.ids_range(V, False{}, kept, 0n), t)),
    idp_count_app(Spec.ids_range(V, True{}, kept, 0n), Spec.ids_range(V, False{}, kept, 0n), t)) : {_ == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Nat, Spec.ids_count(Spec.ids_range(V, True{}, kept, 0n), t), Spec.ids_bit(Bool.and(R, m)), idp_rc(V, True{}, kept, 0n, t)) : {Nat.add(_, Spec.ids_count(Spec.ids_range(V, False{}, kept, 0n), t)) == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Nat, Spec.ids_count(Spec.ids_range(V, False{}, kept, 0n), t), Spec.ids_bit(Bool.and(R, Bool.not(m))), idp_rc(V, False{}, kept, 0n, t)) : {Nat.add(Spec.ids_bit(Bool.and(R, m)), _) == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Nat, Nat.add(Spec.ids_bit(Bool.and(R, m)), Spec.ids_bit(Bool.and(R, Bool.not(m)))), Spec.ids_bit(R), idp_split_bit(R, m)) : {_ == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Bool, Nat.is_le(0n, t), True{}, MP.ar_h_le_zero(t)) : {Spec.ids_bit(Bool.and(_, Nat.is_lt(t, Nat.add(V, 0n)))) == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  %Equal.sym(Nat, Nat.add(V, 0n), V, MP.ar_add_zero_r(V)) : {Spec.ids_bit(Nat.is_lt(t, _)) == Spec.ids_bit(Nat.is_lt(t, V)) : Nat}
  {==}

# ==== law 2: the kept prefix ====

# Number of kept blocks among b .. b + cnt - 1.
def idp_nk(cnt: Nat, +kept: List<&2, Nat>, +b: Nat) -> Nat:
  match cnt:
    case 0n:
      0n
    case 1n+c:
      Nat.add(Spec.ids_bit(Spec.ids_member(kept, b)), idp_nk(c, kept, 1n+b))

def idp_len_row(n: Nat, +x: Nat) -> {List.length(&2, Nat, Impl.idm_row(n, x)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +m1 = m
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, Impl.idm_row(m1, 1n+x)), m1, idp_len_row(m1, 1n+x))

def idp_len_rowscons(p: Bool, +x: Nat, +rest: List<&2, Nat>)
  -> {List.length(&2, Nat, Impl.idm_rows.cons(p, Impl.idm_row(128n, x), rest)) ==
      Nat.add(Nat.mul(Spec.ids_bit(p), 128n), List.length(&2, Nat, rest)) : Nat}:
  match p:
    case True{}:
      %idp_len_app(Nat, Impl.idm_row(128n, x), rest) : {_ == Nat.add(128n, List.length(&2, Nat, rest)) : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, Impl.idm_row(128n, x)), 128n, idp_len_row(128n, x)) : {Nat.add(_, List.length(&2, Nat, rest)) == Nat.add(128n, List.length(&2, Nat, rest)) : Nat}
      {==}
    case False{}:
      {==}

# |kept rows of blocks b .. b + cnt - 1| = 128 * (number of kept blocks among them)
def idp_rows_len(cnt: Nat, +kept: List<&2, Nat>, +b: Nat)
  -> {List.length(&2, Nat, Impl.idm_rows(cnt, True{}, kept, b)) == Nat.mul(idp_nk(cnt, kept, b), 128n) : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n+c:
      +c1 = c
      +m = Spec.ids_member(kept, b)
      %Equal.sym(Nat, List.length(&2, Nat, Impl.idm_rows.cons(m, Impl.idm_row(128n, Nat.mul(b, 128n)), Impl.idm_rows(c1, True{}, kept, 1n+b))),
        Nat.add(Nat.mul(Spec.ids_bit(m), 128n), List.length(&2, Nat, Impl.idm_rows(c1, True{}, kept, 1n+b))),
        idp_len_rowscons(m, Nat.mul(b, 128n), Impl.idm_rows(c1, True{}, kept, 1n+b))) : {_ == Nat.mul(Nat.add(Spec.ids_bit(m), idp_nk(c1, kept, 1n+b)), 128n) : Nat}
      %Equal.sym(Nat, List.length(&2, Nat, Impl.idm_rows(c1, True{}, kept, 1n+b)), Nat.mul(idp_nk(c1, kept, 1n+b), 128n), idp_rows_len(c1, kept, 1n+b)) : {Nat.add(Nat.mul(Spec.ids_bit(m), 128n), _) == Nat.mul(Nat.add(Spec.ids_bit(m), idp_nk(c1, kept, 1n+b)), 128n) : Nat}
      Equal.sym(Nat, Nat.mul(Nat.add(Spec.ids_bit(m), idp_nk(c1, kept, 1n+b)), 128n),
        Nat.add(Nat.mul(Spec.ids_bit(m), 128n), Nat.mul(idp_nk(c1, kept, 1n+b), 128n)),
        MP.ar_mul_add_l(Spec.ids_bit(m), idp_nk(c1, kept, 1n+b), 128n))

def idp_nk_nil(cnt: Nat, +b: Nat) -> {idp_nk(cnt, Nil{}, b) == 0n : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n+c:
      idp_nk_nil(c, 1n+b)

def idp_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      idp_eq_sym(x, y)

def idp_nsum(E: Bool, M: Bool, A: Bool, B: Bool, +N: Nat,
    ea: {E == True{} : Bool} -> {A == False{} : Bool},
    eb: {E == True{} : Bool} -> {B == True{} : Bool},
    em: {E == True{} : Bool} -> {M == False{} : Bool})
  -> {Nat.add(Spec.ids_bit(Bool.or(E, M)), Nat.add(Spec.ids_bit(Bool.and(A, B)), N)) ==
      Nat.add(Spec.ids_bit(Bool.and(Bool.or(E, A), B)), Nat.add(Spec.ids_bit(M), N)) : Nat}:
  match E:
    case False{}:
      MP.ar_h_add_swap(Spec.ids_bit(M), Spec.ids_bit(Bool.and(A, B)), N)
    case True{}:
      %Equal.sym(Bool, A, False{}, ea({==})) : {Nat.add(1n, Nat.add(Spec.ids_bit(Bool.and(_, B)), N)) == Nat.add(Spec.ids_bit(Bool.and(Bool.or(True{}, _), B)), Nat.add(Spec.ids_bit(M), N)) : Nat}
      %Equal.sym(Bool, B, True{}, eb({==})) : {Nat.add(1n, Nat.add(Spec.ids_bit(Bool.and(False{}, _)), N)) == Nat.add(Spec.ids_bit(Bool.and(True{}, _)), Nat.add(Spec.ids_bit(M), N)) : Nat}
      %Equal.sym(Bool, M, False{}, em({==})) : {Nat.add(1n, N) == Nat.add(1n, Nat.add(Spec.ids_bit(_), N)) : Nat}
      {==}

def idp_em(+k: Nat, +ks: List<&2, Nat>, +b: Nat, out: {Spec.ids_member(ks, k) == False{} : Bool},
    e: {Nat.is_eq(k, b) == True{} : Bool}) -> {Spec.ids_member(ks, b) == False{} : Bool}:
  %MP.ar_eq_true(k, b, e) : {Spec.ids_member(ks, _) == False{} : Bool}
  out

# Adding a block k (not yet kept) to the kept list adds 1 to the count of a range holding k.
def idp_nk_cons(cnt: Nat, +k: Nat, +ks: List<&2, Nat>, +b: Nat, +out: {Spec.ids_member(ks, k) == False{} : Bool})
  -> {idp_nk(cnt, k <> ks, b) == Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(b, k), Nat.is_lt(k, Nat.add(cnt, b)))), idp_nk(cnt, ks, b)) : Nat}:
  match cnt:
    case 0n:
      %Equal.sym(Bool, Bool.and(Nat.is_le(b, k), Nat.is_lt(k, b)), False{}, idp_le_lt(b, k)) : {0n == Nat.add(Spec.ids_bit(_), 0n) : Nat}
      {==}
    case 1n+c:
      +c1 = c
      +N = idp_nk(c1, ks, 1n+b)
      %Equal.sym(Nat, idp_nk(c1, k <> ks, 1n+b), Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(1n+b, k), Nat.is_lt(k, Nat.add(c1, 1n+b)))), N), idp_nk_cons(c1, k, ks, 1n+b, out)) : {Nat.add(Spec.ids_bit(Bool.or(Nat.is_eq(k, b), Spec.ids_member(ks, b))), _) == Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(b, k), Nat.is_lt(k, 1n+Nat.add(c1, b)))), Nat.add(Spec.ids_bit(Spec.ids_member(ks, b)), N)) : Nat}
      %Equal.sym(Nat, Nat.add(c1, 1n+b), 1n+Nat.add(c1, b), MP.ar_add_succ_r(c1, b)) : {Nat.add(Spec.ids_bit(Bool.or(Nat.is_eq(k, b), Spec.ids_member(ks, b))), Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(1n+b, k), Nat.is_lt(k, _))), N)) == Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(b, k), Nat.is_lt(k, 1n+Nat.add(c1, b)))), Nat.add(Spec.ids_bit(Spec.ids_member(ks, b)), N)) : Nat}
      %Equal.sym(Bool, Nat.is_le(b, k), Bool.or(Nat.is_eq(b, k), Nat.is_le(1n+b, k)), MP.p8_le_split(b, k)) : {Nat.add(Spec.ids_bit(Bool.or(Nat.is_eq(k, b), Spec.ids_member(ks, b))), Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(1n+b, k), Nat.is_lt(k, 1n+Nat.add(c1, b)))), N)) == Nat.add(Spec.ids_bit(Bool.and(_, Nat.is_lt(k, 1n+Nat.add(c1, b)))), Nat.add(Spec.ids_bit(Spec.ids_member(ks, b)), N)) : Nat}
      %idp_eq_sym(k, b) : {Nat.add(Spec.ids_bit(Bool.or(Nat.is_eq(k, b), Spec.ids_member(ks, b))), Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(1n+b, k), Nat.is_lt(k, 1n+Nat.add(c1, b)))), N)) == Nat.add(Spec.ids_bit(Bool.and(Bool.or(_, Nat.is_le(1n+b, k)), Nat.is_lt(k, 1n+Nat.add(c1, b)))), Nat.add(Spec.ids_bit(Spec.ids_member(ks, b)), N)) : Nat}
      idp_nsum(Nat.is_eq(k, b), Spec.ids_member(ks, b), Nat.is_le(1n+b, k), Nat.is_lt(k, 1n+Nat.add(c1, b)), N,
        e => idp_ea(b, k, %idp_eq_sym(k, b) : {_ == True{} : Bool}; e),
        e => idp_eb(b, k, c1, %idp_eq_sym(k, b) : {_ == True{} : Bool}; e),
        e => idp_em(k, ks, b, out, e))

def idp_blocks_head(+k: Nat, +ks: List<&2, Nat>, +nb: Nat, ok: {Spec.ids_blocks_in(k <> ks, nb) == True{} : Bool})
  -> {Spec.ids_member(ks, k) == False{} : Bool}:
  idp_not_true(Spec.ids_member(ks, k), MP.ar_and_l(Bool.not(Spec.ids_member(ks, k)), Spec.ids_nodup(ks),
    MP.ar_and_l(Spec.ids_nodup(k <> ks), Spec.ids_all_lt(k <> ks, nb), ok)))

def idp_blocks_lt(+k: Nat, +ks: List<&2, Nat>, +nb: Nat, ok: {Spec.ids_blocks_in(k <> ks, nb) == True{} : Bool})
  -> {Nat.is_lt(k, nb) == True{} : Bool}:
  MP.ar_and_l(Nat.is_lt(k, nb), Spec.ids_all_lt(ks, nb), MP.ar_and_r(Spec.ids_nodup(k <> ks), Spec.ids_all_lt(k <> ks, nb), ok))

def idp_blocks_tail(+k: Nat, +ks: List<&2, Nat>, +nb: Nat, +ok: {Spec.ids_blocks_in(k <> ks, nb) == True{} : Bool})
  -> {Spec.ids_blocks_in(ks, nb) == True{} : Bool}:
  MP.ar_and_intro(Spec.ids_nodup(ks), Spec.ids_all_lt(ks, nb),
    MP.ar_and_r(Bool.not(Spec.ids_member(ks, k)), Spec.ids_nodup(ks),
      MP.ar_and_l(Spec.ids_nodup(k <> ks), Spec.ids_all_lt(k <> ks, nb), ok)),
    MP.ar_and_r(Nat.is_lt(k, nb), Spec.ids_all_lt(ks, nb), MP.ar_and_r(Spec.ids_nodup(k <> ks), Spec.ids_all_lt(k <> ks, nb), ok)))

# N distinct blocks < nb: exactly N of the blocks 0 .. nb - 1 are kept.
def idp_nk_all(kept: List<&2, Nat>, +nb: Nat, ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool})
  -> {idp_nk(nb, kept, 0n) == List.length(&2, Nat, kept) : Nat}:
  match kept:
    case Nil{}:
      idp_nk_nil(nb, 0n)
    case +k <> +ks:
      +okk = ok
      %Equal.sym(Nat, idp_nk(nb, k <> ks, 0n), Nat.add(Spec.ids_bit(Bool.and(Nat.is_le(0n, k), Nat.is_lt(k, Nat.add(nb, 0n)))), idp_nk(nb, ks, 0n)),
        idp_nk_cons(nb, k, ks, 0n, idp_blocks_head(k, ks, nb, okk))) : {_ == 1n+List.length(&2, Nat, ks) : Nat}
      %Equal.sym(Bool, Nat.is_le(0n, k), True{}, MP.ar_h_le_zero(k)) : {Nat.add(Spec.ids_bit(Bool.and(_, Nat.is_lt(k, Nat.add(nb, 0n)))), idp_nk(nb, ks, 0n)) == 1n+List.length(&2, Nat, ks) : Nat}
      %Equal.sym(Nat, Nat.add(nb, 0n), nb, MP.ar_add_zero_r(nb)) : {Nat.add(Spec.ids_bit(Nat.is_lt(k, _)), idp_nk(nb, ks, 0n)) == 1n+List.length(&2, Nat, ks) : Nat}
      %Equal.sym(Bool, Nat.is_lt(k, nb), True{}, idp_blocks_lt(k, ks, nb, okk)) : {Nat.add(Spec.ids_bit(_), idp_nk(nb, ks, 0n)) == 1n+List.length(&2, Nat, ks) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, idp_nk(nb, ks, 0n), List.length(&2, Nat, ks), idp_nk_all(ks, nb, idp_blocks_tail(k, ks, nb, okk)))

# len(set(xs)) == len(xs) for distinct entries.
def idp_card_nodup(xs: List<&2, Nat>, nd: {Spec.ids_nodup(xs) == True{} : Bool})
  -> {Impl.idm_card(xs) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      +n2 = nd
      %Equal.sym(Bool, Spec.ids_member(rest, y), False{}, idp_not_true(Spec.ids_member(rest, y), MP.ar_and_l(Bool.not(Spec.ids_member(rest, y)), Spec.ids_nodup(rest), n2))) : {Nat.add(Spec.ids_bit(Bool.not(_)), Impl.idm_card(rest)) == 1n+List.length(&2, Nat, rest) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, Impl.idm_card(rest), List.length(&2, Nat, rest),
        idp_card_nodup(rest, MP.ar_and_r(Bool.not(Spec.ids_member(rest, y)), Spec.ids_nodup(rest), n2)))

def Laws.idmap_prefix_length(kept, nb, ok):
  %Equal.sym(Nat, Impl.idm_card(kept), List.length(&2, Nat, kept), idp_card_nodup(kept, MP.ar_and_l(Spec.ids_nodup(kept), Spec.ids_all_lt(kept, nb), ok))) : {Nat.mul(128n, _) == Nat.mul(128n, List.length(&2, Nat, kept)) : Nat}
  {==}

# The kept rows are keep_cols long.
def idp_keep_len(+kept: List<&2, Nat>, +nb: Nat, +ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool})
  -> {Impl.idm_keep_cols(kept) == List.length(&2, Nat, Spec.ids_range(Nat.mul(nb, 128n), True{}, kept, 0n)) : Nat}:
  %idp_rows(nb, True{}, kept, 0n) : {Impl.idm_keep_cols(kept) == List.length(&2, Nat, _) : Nat}
  %Equal.sym(Nat, List.length(&2, Nat, Impl.idm_rows(nb, True{}, kept, 0n)), Nat.mul(idp_nk(nb, kept, 0n), 128n), idp_rows_len(nb, kept, 0n)) : {Impl.idm_keep_cols(kept) == _ : Nat}
  %Equal.sym(Nat, idp_nk(nb, kept, 0n), List.length(&2, Nat, kept), idp_nk_all(kept, nb, ok)) : {Impl.idm_keep_cols(kept) == Nat.mul(_, 128n) : Nat}
  %Equal.sym(Nat, Impl.idm_keep_cols(kept), Nat.mul(128n, List.length(&2, Nat, kept)), Laws.idmap_prefix_length(kept, nb, ok)) : {_ == Nat.mul(List.length(&2, Nat, kept), 128n) : Nat}
  MP.ar_mul_comm(128n, List.length(&2, Nat, kept))

def Laws.idmap_prefix_kept_ids(kept, nb, ok):
  +V = Nat.mul(nb, 128n)
  +rT = Spec.ids_range(V, True{}, kept, 0n)
  +rF = Spec.ids_range(V, False{}, kept, 0n)
  %Equal.sym(List<&2, Nat>, Impl.idm_id_map(kept, nb), Spec.ids_id_map(kept, nb), Laws.idmap_equals_spec(kept, nb)) : {List.take(&2, Nat, _, Impl.idm_keep_cols(kept)) == rT : List<&2, Nat>}
  %Equal.sym(Nat, Impl.idm_keep_cols(kept), List.length(&2, Nat, rT), idp_keep_len(kept, nb, ok)) : {List.take(&2, Nat, List.append(&2, Nat, rT, rF), _) == rT : List<&2, Nat>}
  idp_take_app(Nat, rT, rF)

def idp_lt_succ(+n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      idp_lt_succ(m)

def idp_gt_rcons(p: Bool, +x: Nat, +lo: Nat, +rest: List<&2, Nat>, h: {Nat.is_lt(x, lo) == True{} : Bool},
    g: {Spec.ids_all_gt(rest, x) == True{} : Bool})
  -> {Spec.ids_all_gt(Spec.ids_range.cons(p, lo, rest), x) == True{} : Bool}:
  match p:
    case True{}:
      MP.ar_and_intro(Nat.is_lt(x, lo), Spec.ids_all_gt(rest, x), h, g)
    case False{}:
      g

# Every id of a range from lo is above x < lo.
def idp_range_gt(len: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat, +x: Nat, +h: {Nat.is_lt(x, lo) == True{} : Bool})
  -> {Spec.ids_all_gt(Spec.ids_range(len, want, kept, lo), x) == True{} : Bool}:
  match len:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      idp_gt_rcons(Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n))), x, lo, Spec.ids_range(l1, want, kept, 1n+lo), h,
        idp_range_gt(l1, want, kept, 1n+lo, x, MP.ar_lt_trans(x, lo, 1n+lo, h, idp_lt_succ(lo))))

def idp_inc_rcons(p: Bool, +x: Nat, +rest: List<&2, Nat>, g: {Spec.ids_all_gt(rest, x) == True{} : Bool},
    i: {Spec.ids_increasing(rest) == True{} : Bool})
  -> {Spec.ids_increasing(Spec.ids_range.cons(p, x, rest)) == True{} : Bool}:
  match p:
    case True{}:
      MP.ar_and_intro(Spec.ids_all_gt(rest, x), Spec.ids_increasing(rest), g, i)
    case False{}:
      i

def idp_range_inc(len: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat)
  -> {Spec.ids_increasing(Spec.ids_range(len, want, kept, lo)) == True{} : Bool}:
  match len:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      idp_inc_rcons(Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n))), lo, Spec.ids_range(l1, want, kept, 1n+lo),
        idp_range_gt(l1, want, kept, 1n+lo, lo, idp_lt_succ(lo)), idp_range_inc(l1, want, kept, 1n+lo))

def Laws.idmap_prefix_increasing(kept, nb, ok):
  %Equal.sym(List<&2, Nat>, List.take(&2, Nat, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept)), Spec.ids_kept_ids(kept, nb), Laws.idmap_prefix_kept_ids(kept, nb, ok)) : {Spec.ids_increasing(_) == True{} : Bool}
  idp_range_inc(Nat.mul(nb, 128n), True{}, kept, 0n)

def Laws.idmap_prefix_exact(kept, nb, t, ok):
  +V = Nat.mul(nb, 128n)
  +m = Spec.ids_member(kept, Nat.div(t, 128n))
  %Equal.sym(List<&2, Nat>, List.take(&2, Nat, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept)), Spec.ids_kept_ids(kept, nb), Laws.idmap_prefix_kept_ids(kept, nb, ok)) : {Spec.ids_count(_, t) == Spec.ids_bit(Bool.and(Nat.is_lt(t, V), m)) : Nat}
  %Equal.sym(Nat, Spec.ids_count(Spec.ids_range(V, True{}, kept, 0n), t), Spec.ids_bit(Bool.and(Bool.and(Nat.is_le(0n, t), Nat.is_lt(t, Nat.add(V, 0n))), m)), idp_rc(V, True{}, kept, 0n, t)) : {_ == Spec.ids_bit(Bool.and(Nat.is_lt(t, V), m)) : Nat}
  %Equal.sym(Bool, Nat.is_le(0n, t), True{}, MP.ar_h_le_zero(t)) : {Spec.ids_bit(Bool.and(Bool.and(_, Nat.is_lt(t, Nat.add(V, 0n))), m)) == Spec.ids_bit(Bool.and(Nat.is_lt(t, V), m)) : Nat}
  %Equal.sym(Nat, Nat.add(V, 0n), V, MP.ar_add_zero_r(V)) : {Spec.ids_bit(Bool.and(Nat.is_lt(t, _), m)) == Spec.ids_bit(Bool.and(Nat.is_lt(t, V), m)) : Nat}
  {==}

# ==== law 3: kept blocks = sorted(order[:N]) ====

def idp_or_swap(a: Bool, c: Bool, +d: Bool) -> {Bool.or(c, Bool.or(a, d)) == Bool.or(a, Bool.or(c, d)) : Bool}:
  match a:
    case True{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def idp_and_swap(a: Bool, c: Bool, +d: Bool) -> {Bool.and(c, Bool.and(a, d)) == Bool.and(a, Bool.and(c, d)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

# -- insertion into an ascending list --

def idp_mem_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, deeper: List<&2, Nat>, +b: Nat,
    ih: {Spec.ids_member(deeper, b) == Bool.or(Nat.is_eq(x, b), Spec.ids_member(rest, b)) : Bool})
  -> {Spec.ids_member(Impl.idm_sort.sel(g, x, y, rest, deeper), b) == Bool.or(Nat.is_eq(x, b), Bool.or(Nat.is_eq(y, b), Spec.ids_member(rest, b))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_member(deeper, b), Bool.or(Nat.is_eq(x, b), Spec.ids_member(rest, b)), ih) : {Bool.or(Nat.is_eq(y, b), _) == Bool.or(Nat.is_eq(x, b), Bool.or(Nat.is_eq(y, b), Spec.ids_member(rest, b))) : Bool}
      idp_or_swap(Nat.is_eq(x, b), Nat.is_eq(y, b), Spec.ids_member(rest, b))

def idp_mem_ins(ys: List<&2, Nat>, +x: Nat, +b: Nat)
  -> {Spec.ids_member(Impl.idm_sort.ins(ys, x), b) == Bool.or(Nat.is_eq(x, b), Spec.ids_member(ys, b)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_mem_sel(Nat.is_le(x, y), x, y, rest, Impl.idm_sort.ins(rest, x), b, idp_mem_ins(rest, x, b))

def idp_mem_sort(xs: List<&2, Nat>, +b: Nat) -> {Spec.ids_member(Impl.idm_sort(xs), b) == Spec.ids_member(xs, b) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_member(Impl.idm_sort.ins(Impl.idm_sort(rest), x), b), Bool.or(Nat.is_eq(x, b), Spec.ids_member(Impl.idm_sort(rest), b)), idp_mem_ins(Impl.idm_sort(rest), x, b)) : {_ == Bool.or(Nat.is_eq(x, b), Spec.ids_member(rest, b)) : Bool}
      %Equal.sym(Bool, Spec.ids_member(Impl.idm_sort(rest), b), Spec.ids_member(rest, b), idp_mem_sort(rest, b)) : {Bool.or(Nat.is_eq(x, b), _) == Bool.or(Nat.is_eq(x, b), Spec.ids_member(rest, b)) : Bool}
      {==}

def Laws.kept_members(order, n, b):
  idp_mem_sort(List.take(&2, Nat, order, n), b)

def idp_len_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, deeper: List<&2, Nat>,
    ih: {List.length(&2, Nat, deeper) == 1n+List.length(&2, Nat, rest) : Nat})
  -> {List.length(&2, Nat, Impl.idm_sort.sel(g, x, y, rest, deeper)) == 1n+1n+List.length(&2, Nat, rest) : Nat}:
  match g:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, deeper), 1n+List.length(&2, Nat, rest), ih)

def idp_len_ins(ys: List<&2, Nat>, +x: Nat) -> {List.length(&2, Nat, Impl.idm_sort.ins(ys, x)) == 1n+List.length(&2, Nat, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_len_sel(Nat.is_le(x, y), x, y, rest, Impl.idm_sort.ins(rest, x), idp_len_ins(rest, x))

def idp_len_sort(xs: List<&2, Nat>) -> {List.length(&2, Nat, Impl.idm_sort(xs)) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Nat, List.length(&2, Nat, Impl.idm_sort.ins(Impl.idm_sort(rest), x)), 1n+List.length(&2, Nat, Impl.idm_sort(rest)), idp_len_ins(Impl.idm_sort(rest), x)) : {_ == 1n+List.length(&2, Nat, rest) : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, Impl.idm_sort(rest)), List.length(&2, Nat, rest), idp_len_sort(rest))

def Laws.kept_length(order, n):
  idp_len_sort(List.take(&2, Nat, order, n))

# -- nodup and all_lt through insertion --

def idp_nd_bool(E: Bool, Mry: Bool, Mrx: Bool, +D: Bool)
  -> {Bool.and(Bool.not(Bool.or(E, Mry)), Bool.and(Bool.not(Mrx), D)) == Bool.and(Bool.not(Bool.or(E, Mrx)), Bool.and(Bool.not(Mry), D)) : Bool}:
  match E:
    case True{}:
      {==}
    case False{}:
      idp_and_swap(Bool.not(Mrx), Bool.not(Mry), D)

def idp_nd_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, +deeper: List<&2, Nat>,
    ih: {Spec.ids_nodup(deeper) == Bool.and(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest)) : Bool},
    mi: {Spec.ids_member(deeper, y) == Bool.or(Nat.is_eq(x, y), Spec.ids_member(rest, y)) : Bool})
  -> {Spec.ids_nodup(Impl.idm_sort.sel(g, x, y, rest, deeper)) == Bool.and(Bool.not(Spec.ids_member(y <> rest, x)), Spec.ids_nodup(y <> rest)) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_nodup(deeper), Bool.and(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest)), ih) : {Bool.and(Bool.not(Spec.ids_member(deeper, y)), _) == Bool.and(Bool.not(Bool.or(Nat.is_eq(y, x), Spec.ids_member(rest, x))), Bool.and(Bool.not(Spec.ids_member(rest, y)), Spec.ids_nodup(rest))) : Bool}
      %Equal.sym(Bool, Spec.ids_member(deeper, y), Bool.or(Nat.is_eq(x, y), Spec.ids_member(rest, y)), mi) : {Bool.and(Bool.not(_), Bool.and(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest))) == Bool.and(Bool.not(Bool.or(Nat.is_eq(y, x), Spec.ids_member(rest, x))), Bool.and(Bool.not(Spec.ids_member(rest, y)), Spec.ids_nodup(rest))) : Bool}
      %idp_eq_sym(x, y) : {Bool.and(Bool.not(Bool.or(Nat.is_eq(x, y), Spec.ids_member(rest, y))), Bool.and(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest))) == Bool.and(Bool.not(Bool.or(_, Spec.ids_member(rest, x))), Bool.and(Bool.not(Spec.ids_member(rest, y)), Spec.ids_nodup(rest))) : Bool}
      idp_nd_bool(Nat.is_eq(x, y), Spec.ids_member(rest, y), Spec.ids_member(rest, x), Spec.ids_nodup(rest))

def idp_nd_ins(ys: List<&2, Nat>, +x: Nat)
  -> {Spec.ids_nodup(Impl.idm_sort.ins(ys, x)) == Bool.and(Bool.not(Spec.ids_member(ys, x)), Spec.ids_nodup(ys)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_nd_sel(Nat.is_le(x, y), x, y, rest, Impl.idm_sort.ins(rest, x), idp_nd_ins(rest, x), idp_mem_ins(rest, x, y))

def idp_nd_sort(xs: List<&2, Nat>) -> {Spec.ids_nodup(Impl.idm_sort(xs)) == Spec.ids_nodup(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_nodup(Impl.idm_sort.ins(Impl.idm_sort(rest), x)), Bool.and(Bool.not(Spec.ids_member(Impl.idm_sort(rest), x)), Spec.ids_nodup(Impl.idm_sort(rest))), idp_nd_ins(Impl.idm_sort(rest), x)) : {_ == Spec.ids_nodup(x <> rest) : Bool}
      %Equal.sym(Bool, Spec.ids_member(Impl.idm_sort(rest), x), Spec.ids_member(rest, x), idp_mem_sort(rest, x)) : {Bool.and(Bool.not(_), Spec.ids_nodup(Impl.idm_sort(rest))) == Spec.ids_nodup(x <> rest) : Bool}
      %Equal.sym(Bool, Spec.ids_nodup(Impl.idm_sort(rest)), Spec.ids_nodup(rest), idp_nd_sort(rest)) : {Bool.and(Bool.not(Spec.ids_member(rest, x)), _) == Spec.ids_nodup(x <> rest) : Bool}
      {==}

def idp_lt_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, deeper: List<&2, Nat>, +D: Nat,
    ih: {Spec.ids_all_lt(deeper, D) == Bool.and(Nat.is_lt(x, D), Spec.ids_all_lt(rest, D)) : Bool})
  -> {Spec.ids_all_lt(Impl.idm_sort.sel(g, x, y, rest, deeper), D) == Bool.and(Nat.is_lt(x, D), Bool.and(Nat.is_lt(y, D), Spec.ids_all_lt(rest, D))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_all_lt(deeper, D), Bool.and(Nat.is_lt(x, D), Spec.ids_all_lt(rest, D)), ih) : {Bool.and(Nat.is_lt(y, D), _) == Bool.and(Nat.is_lt(x, D), Bool.and(Nat.is_lt(y, D), Spec.ids_all_lt(rest, D))) : Bool}
      idp_and_swap(Nat.is_lt(x, D), Nat.is_lt(y, D), Spec.ids_all_lt(rest, D))

def idp_lt_ins(ys: List<&2, Nat>, +x: Nat, +D: Nat)
  -> {Spec.ids_all_lt(Impl.idm_sort.ins(ys, x), D) == Bool.and(Nat.is_lt(x, D), Spec.ids_all_lt(ys, D)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_lt_sel(Nat.is_le(x, y), x, y, rest, Impl.idm_sort.ins(rest, x), D, idp_lt_ins(rest, x, D))

def idp_lt_sort(xs: List<&2, Nat>, +D: Nat) -> {Spec.ids_all_lt(Impl.idm_sort(xs), D) == Spec.ids_all_lt(xs, D) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_all_lt(Impl.idm_sort.ins(Impl.idm_sort(rest), x), D), Bool.and(Nat.is_lt(x, D), Spec.ids_all_lt(Impl.idm_sort(rest), D)), idp_lt_ins(Impl.idm_sort(rest), x, D)) : {_ == Spec.ids_all_lt(x <> rest, D) : Bool}
      %Equal.sym(Bool, Spec.ids_all_lt(Impl.idm_sort(rest), D), Spec.ids_all_lt(rest, D), idp_lt_sort(rest, D)) : {Bool.and(Nat.is_lt(x, D), _) == Spec.ids_all_lt(x <> rest, D) : Bool}
      {==}

# -- strictly increasing through insertion --

def idp_or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def idp_or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, MP.ar_true_false(e))
    case False{}:
      e

def idp_gt_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, deeper: List<&2, Nat>, +z: Nat,
    ih: {Spec.ids_all_gt(deeper, z) == Bool.and(Nat.is_lt(z, x), Spec.ids_all_gt(rest, z)) : Bool})
  -> {Spec.ids_all_gt(Impl.idm_sort.sel(g, x, y, rest, deeper), z) == Bool.and(Nat.is_lt(z, x), Bool.and(Nat.is_lt(z, y), Spec.ids_all_gt(rest, z))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_all_gt(deeper, z), Bool.and(Nat.is_lt(z, x), Spec.ids_all_gt(rest, z)), ih) : {Bool.and(Nat.is_lt(z, y), _) == Bool.and(Nat.is_lt(z, x), Bool.and(Nat.is_lt(z, y), Spec.ids_all_gt(rest, z))) : Bool}
      idp_and_swap(Nat.is_lt(z, x), Nat.is_lt(z, y), Spec.ids_all_gt(rest, z))

def idp_gt_ins(ys: List<&2, Nat>, +x: Nat, +z: Nat)
  -> {Spec.ids_all_gt(Impl.idm_sort.ins(ys, x), z) == Bool.and(Nat.is_lt(z, x), Spec.ids_all_gt(ys, z)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_gt_sel(Nat.is_le(x, y), x, y, rest, Impl.idm_sort.ins(rest, x), z, idp_gt_ins(rest, x, z))

# x < y and every entry > y: every entry > x.
def idp_gt_mono(xs: List<&2, Nat>, +x: Nat, +y: Nat, +xy: {Nat.is_lt(x, y) == True{} : Bool},
    g: {Spec.ids_all_gt(xs, y) == True{} : Bool}) -> {Spec.ids_all_gt(xs, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +r <> +rest:
      +gg = g
      MP.ar_and_intro(Nat.is_lt(x, r), Spec.ids_all_gt(rest, x),
        MP.ar_lt_trans(x, y, r, xy, MP.ar_and_l(Nat.is_lt(y, r), Spec.ids_all_gt(rest, y), gg)),
        idp_gt_mono(rest, x, y, xy, MP.ar_and_r(Nat.is_lt(y, r), Spec.ids_all_gt(rest, y), gg)))

def idp_or_true_r(a: Bool, -b: Bool, ea: {a == False{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, MP.ar_true_false(ea))
    case False{}:
      e

# x <= y and x != y: x < y.
def idp_le_ne_lt(+x: Nat, +y: Nat, le: {Nat.is_le(x, y) == True{} : Bool}, ne: {Nat.is_eq(y, x) == False{} : Bool})
  -> {Nat.is_lt(x, y) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(x, y), Nat.is_le(1n+x, y), MP.ar_lt_succ_le(x, y)) : {_ == True{} : Bool}
  idp_or_true_r(Nat.is_eq(x, y), Nat.is_le(1n+x, y),
    Equal.trans(Bool, Nat.is_eq(x, y), Nat.is_eq(y, x), False{}, idp_eq_sym(x, y), ne),
    Equal.trans(Bool, Bool.or(Nat.is_eq(x, y), Nat.is_le(1n+x, y)), Nat.is_le(x, y), True{},
      Equal.sym(Bool, Nat.is_le(x, y), Bool.or(Nat.is_eq(x, y), Nat.is_le(1n+x, y)), MP.p8_le_split(x, y)), le))

def idp_inc_sel(g: Bool, +x: Nat, +y: Nat, +rest: List<&2, Nat>, +e: {Nat.is_le(x, y) == g : Bool},
    +incy: {Spec.ids_increasing(y <> rest) == True{} : Bool},
    +nexy: {Nat.is_eq(y, x) == False{} : Bool},
    ihr: {Spec.ids_increasing(Impl.idm_sort.ins(rest, x)) == True{} : Bool})
  -> {Spec.ids_increasing(Impl.idm_sort.sel(g, x, y, rest, Impl.idm_sort.ins(rest, x))) == True{} : Bool}:
  match g:
    case True{}:
      +gy = MP.ar_and_l(Spec.ids_all_gt(rest, y), Spec.ids_increasing(rest), incy)
      +xy = idp_le_ne_lt(x, y, e, nexy)
      MP.ar_and_intro(Spec.ids_all_gt(y <> rest, x), Spec.ids_increasing(y <> rest),
        MP.ar_and_intro(Nat.is_lt(x, y), Spec.ids_all_gt(rest, x), xy, idp_gt_mono(rest, x, y, xy, gy)),
        incy)
    case False{}:
      %Equal.sym(Bool, Spec.ids_all_gt(Impl.idm_sort.ins(rest, x), y), Bool.and(Nat.is_lt(y, x), Spec.ids_all_gt(rest, y)), idp_gt_ins(rest, x, y)) : {Bool.and(_, Spec.ids_increasing(Impl.idm_sort.ins(rest, x))) == True{} : Bool}
      MP.ar_and_intro(Bool.and(Nat.is_lt(y, x), Spec.ids_all_gt(rest, y)), Spec.ids_increasing(Impl.idm_sort.ins(rest, x)),
        MP.ar_and_intro(Nat.is_lt(y, x), Spec.ids_all_gt(rest, y),
          %Equal.sym(Bool, Nat.is_lt(y, x), Bool.not(Nat.is_le(x, y)), MP.ar_lt_not_le(y, x)) : {_ == True{} : Bool}
          %Equal.sym(Bool, Nat.is_le(x, y), False{}, e) : {Bool.not(_) == True{} : Bool}
          {==},
          MP.ar_and_l(Spec.ids_all_gt(rest, y), Spec.ids_increasing(rest), incy)),
        ihr)

def idp_inc_ins(ys: List<&2, Nat>, +x: Nat, inc: {Spec.ids_increasing(ys) == True{} : Bool},
    nm: {Spec.ids_member(ys, x) == False{} : Bool})
  -> {Spec.ids_increasing(Impl.idm_sort.ins(ys, x)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      +n2 = nm
      +i2 = inc
      idp_inc_sel(Nat.is_le(x, y), x, y, rest, {==}, i2,
        idp_or_false_l(Nat.is_eq(y, x), Spec.ids_member(rest, x), n2),
        idp_inc_ins(rest, x, MP.ar_and_r(Spec.ids_all_gt(rest, y), Spec.ids_increasing(rest), i2),
          idp_or_false_r(Nat.is_eq(y, x), Spec.ids_member(rest, x), n2)))

def idp_inc_sort(xs: List<&2, Nat>, nd: {Spec.ids_nodup(xs) == True{} : Bool})
  -> {Spec.ids_increasing(Impl.idm_sort(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +n2 = nd
      idp_inc_ins(Impl.idm_sort(rest), x, idp_inc_sort(rest, MP.ar_and_r(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest), n2)),
        %Equal.sym(Bool, Spec.ids_member(Impl.idm_sort(rest), x), Spec.ids_member(rest, x), idp_mem_sort(rest, x)) : {_ == False{} : Bool}
        idp_not_true(Spec.ids_member(rest, x), MP.ar_and_l(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest), n2)))

def Laws.kept_increasing(order, n, nd):
  idp_inc_sort(List.take(&2, Nat, order, n), nd)

# -- len(set(xs)) --

def idp_card_le_step(M: Bool, +c: Nat, +L: Nat, h: {Nat.is_le(c, L) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Spec.ids_bit(Bool.not(M)), c), 1n+L) == True{} : Bool}:
  match M:
    case False{}:
      h
    case True{}:
      MP.ar_le_trans(c, L, 1n+L, h, MP.ar_h_le_succ(L))

def idp_card_le(xs: List<&2, Nat>) -> {Nat.is_le(Impl.idm_card(xs), List.length(&2, Nat, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_card_le_step(Spec.ids_member(rest, y), Impl.idm_card(rest), List.length(&2, Nat, rest), idp_card_le(rest))

def idp_lt_ne(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, MP.ar_false_true(h))
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      idp_lt_ne(x, y, h)

def idp_card_step(M: Bool, +c: Nat, +L: Nat, +m: Nat, +D: Bool,
    ih: {Nat.is_eq(c, m) == Bool.and(Nat.is_eq(L, m), D) : Bool},
    cl: {Nat.is_le(c, L) == True{} : Bool}, lm: {Nat.is_le(L, m) == True{} : Bool})
  -> {Nat.is_eq(Nat.add(Spec.ids_bit(Bool.not(M)), c), 1n+m) == Bool.and(Nat.is_eq(L, m), Bool.and(Bool.not(M), D)) : Bool}:
  match M:
    case False{}:
      ih
    case True{}:
      Equal.trans(Bool, Nat.is_eq(c, 1n+m), False{}, Bool.and(Nat.is_eq(L, m), False{}),
        idp_lt_ne(c, 1n+m, Equal.trans(Bool, Nat.is_lt(c, 1n+m), Nat.is_le(1n+c, 1n+m), True{}, MP.ar_lt_succ_le(c, 1n+m),
          MP.ar_le_trans(c, L, m, cl, lm))),
        MP.ar_h_and_false_r(Nat.is_eq(L, m)))

# len(set(xs)) == m iff len(xs) == m and xs has no duplicate, for len(xs) <= m.
def idp_card_eq(xs: List<&2, Nat>, +m: Nat, h: {Nat.is_le(List.length(&2, Nat, xs), m) == True{} : Bool})
  -> {Nat.is_eq(Impl.idm_card(xs), m) == Bool.and(Nat.is_eq(List.length(&2, Nat, xs), m), Spec.ids_nodup(xs)) : Bool}:
  match xs:
    case Nil{}:
      match m:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case +y <> +rest:
      match m:
        case 0n:
          Empty.absurd({Nat.is_eq(Impl.idm_card(y <> rest), 0n) == Bool.and(Nat.is_eq(List.length(&2, Nat, y <> rest), 0n), Spec.ids_nodup(y <> rest)) : Bool},
            MP.ar_false_true(h))
        case 1n+q:
          +q1 = q
          +hh = h
          idp_card_step(Spec.ids_member(rest, y), Impl.idm_card(rest), List.length(&2, Nat, rest), q1, Spec.ids_nodup(rest),
            idp_card_eq(rest, q1, hh), idp_card_le(rest), hh)

def idp_and_true_r(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_and_imp(a: Bool, X: Bool, h: {X == True{} : Bool} -> {a == True{} : Bool}) -> {Bool.and(a, X) == X : Bool}:
  match X:
    case True{}:
      %Equal.sym(Bool, a, True{}, h({==})) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      Equal.sym(Bool, False{}, Bool.and(a, False{}), MP.ar_h_and_false_r(a))

# For a nonempty strictly increasing list, the last-entry check is "every entry is a whole block inside vocab".
def idp_lfa(xs: List<&2, Nat>, +vocab: Nat, -k: Nat, len: {List.length(&2, Nat, xs) == 1n+k : Nat},
    inc: {Spec.ids_increasing(xs) == True{} : Bool})
  -> {Impl.idm_last_fits(xs, vocab) == Spec.ids_all_lt(xs, Nat.div(vocab, 128n)) : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Impl.idm_last_fits(Nil{}, vocab) == Spec.ids_all_lt(Nil{}, Nat.div(vocab, 128n)) : Bool}, MP.ar_zero_succ(k, len))
    case +y <> +rest:
      match rest:
        case Nil{}:
          Equal.trans(Bool, Nat.is_le(Nat.mul(1n+y, 128n), vocab), Nat.is_lt(y, Nat.div(vocab, 128n)), Bool.and(Nat.is_lt(y, Nat.div(vocab, 128n)), True{}),
            Equal.trans(Bool, Nat.is_le(Nat.mul(1n+y, 128n), vocab), Nat.is_le(1n+y, Nat.div(vocab, 128n)), Nat.is_lt(y, Nat.div(vocab, 128n)),
              MP.ar_div_le(1n+y, vocab, 128n, {==}),
              Equal.sym(Bool, Nat.is_lt(y, Nat.div(vocab, 128n)), Nat.is_le(1n+y, Nat.div(vocab, 128n)), MP.ar_lt_succ_le(y, Nat.div(vocab, 128n)))),
            Equal.sym(Bool, Bool.and(Nat.is_lt(y, Nat.div(vocab, 128n)), True{}), Nat.is_lt(y, Nat.div(vocab, 128n)), idp_and_true_r(Nat.is_lt(y, Nat.div(vocab, 128n)))))
        case +z <> +more:
          +D = Nat.div(vocab, 128n)
          +i2 = inc
          +gy = MP.ar_and_l(Spec.ids_all_gt(z <> more, y), Spec.ids_increasing(z <> more), i2)
          +yz = MP.ar_and_l(Nat.is_lt(y, z), Spec.ids_all_gt(more, y), gy)
          Equal.trans(Bool, Impl.idm_last_fits(z <> more, vocab), Spec.ids_all_lt(z <> more, D), Bool.and(Nat.is_lt(y, D), Spec.ids_all_lt(z <> more, D)),
            idp_lfa(z <> more, vocab, List.length(&2, Nat, more), {==}, MP.ar_and_r(Spec.ids_all_gt(z <> more, y), Spec.ids_increasing(z <> more), i2)),
            Equal.sym(Bool, Bool.and(Nat.is_lt(y, D), Spec.ids_all_lt(z <> more, D)), Spec.ids_all_lt(z <> more, D),
              idp_and_imp(Nat.is_lt(y, D), Spec.ids_all_lt(z <> more, D),
                al => MP.ar_lt_trans(y, z, D, yz, MP.ar_and_l(Nat.is_lt(z, D), Spec.ids_all_lt(more, D), al)))))

def idp_and3(E: Bool, N: Bool, LF: Bool, A: Bool, h: {E == True{} : Bool} -> {N == True{} : Bool} -> {LF == A : Bool})
  -> {Bool.and(Bool.and(E, N), LF) == Bool.and(E, Bool.and(N, A)) : Bool}:
  match E:
    case False{}:
      {==}
    case True{}:
      match N:
        case False{}:
          {==}
        case True{}:
          h({==})({==})

def Laws.kept_accepts_exactly(order, n, vocab):
  match n:
    case 0n:
      %Equal.sym(List<&2, Nat>, List.take(&2, Nat, order, 0n), Nil{}, idp_take0(Nat, order)) : {Bool.and(Nat.is_eq(Impl.idm_card(Impl.idm_sort(_)), 0n), Impl.idm_last_fits(Impl.idm_sort(_), vocab)) == False{} : Bool}
      {==}
    case 1n+q:
      +q1 = q
      +m : Nat = 1n+q1
      +p = List.take(&2, Nat, order, m)
      +bq = Impl.idm_sort(p)
      +D = Nat.div(vocab, 128n)
      +hq = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, bq), m), Nat.is_le(List.length(&2, Nat, p), m), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, m), List.length(&2, Nat, bq), List.length(&2, Nat, p), idp_len_sort(p)),
        idp_len_take_le(Nat, order, m))
      %Equal.sym(Bool, Nat.is_eq(Impl.idm_card(bq), m), Bool.and(Nat.is_eq(List.length(&2, Nat, bq), m), Spec.ids_nodup(bq)), idp_card_eq(bq, m, hq)) : {Bool.and(_, Impl.idm_last_fits(bq, vocab)) == Bool.and(Nat.is_eq(List.length(&2, Nat, p), m), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, D))) : Bool}
      %Equal.sym(Nat, List.length(&2, Nat, bq), List.length(&2, Nat, p), idp_len_sort(p)) : {Bool.and(Bool.and(Nat.is_eq(_, m), Spec.ids_nodup(bq)), Impl.idm_last_fits(bq, vocab)) == Bool.and(Nat.is_eq(List.length(&2, Nat, p), m), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, D))) : Bool}
      %Equal.sym(Bool, Spec.ids_nodup(bq), Spec.ids_nodup(p), idp_nd_sort(p)) : {Bool.and(Bool.and(Nat.is_eq(List.length(&2, Nat, p), m), _), Impl.idm_last_fits(bq, vocab)) == Bool.and(Nat.is_eq(List.length(&2, Nat, p), m), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, D))) : Bool}
      idp_and3(Nat.is_eq(List.length(&2, Nat, p), m), Spec.ids_nodup(p), Impl.idm_last_fits(bq, vocab), Spec.ids_all_lt(p, D),
        e1 => e2 => Equal.trans(Bool, Impl.idm_last_fits(bq, vocab), Spec.ids_all_lt(bq, D), Spec.ids_all_lt(p, D),
          idp_lfa(bq, vocab, q1, Equal.trans(Nat, List.length(&2, Nat, bq), List.length(&2, Nat, p), m, idp_len_sort(p), MP.ar_eq_true(List.length(&2, Nat, p), m, e1)),
            idp_inc_sort(p, e2)),
          idp_lt_sort(p, D)))

# -- prefixes of a permutation --

def idp_len_take(xs: List<&2, Nat>, +n: Nat, h: {Nat.is_le(n, List.length(&2, Nat, xs)) == True{} : Bool})
  -> {List.length(&2, Nat, List.take(&2, Nat, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      Empty.absurd({List.length(&2, Nat, List.take(&2, Nat, Nil{}, 1n+q)) == 1n+q : Nat}, MP.ar_false_true(h))
    case (y <> t) 0n:
      {==}
    case (y <> t) 1n+q:
      +q1 = q
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, List.take(&2, Nat, t, q1)), q1, idp_len_take(t, q1, h))

def idp_mem_take_false(xs: List<&2, Nat>, +n: Nat, +x: Nat, e: {Spec.ids_member(xs, x) == False{} : Bool})
  -> {Spec.ids_member(List.take(&2, Nat, xs, n), x) == False{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case (y <> t) 0n:
      {==}
    case (+y <> +t) 1n+q:
      +ee = e
      %Equal.sym(Bool, Nat.is_eq(y, x), False{}, idp_or_false_l(Nat.is_eq(y, x), Spec.ids_member(t, x), ee)) : {Bool.or(_, Spec.ids_member(List.take(&2, Nat, t, q), x)) == False{} : Bool}
      idp_mem_take_false(t, q, x, idp_or_false_r(Nat.is_eq(y, x), Spec.ids_member(t, x), ee))

def idp_nd_take(xs: List<&2, Nat>, +n: Nat, nd: {Spec.ids_nodup(xs) == True{} : Bool})
  -> {Spec.ids_nodup(List.take(&2, Nat, xs, n)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case (y <> t) 0n:
      {==}
    case (+y <> +t) 1n+q:
      +n2 = nd
      %Equal.sym(Bool, Spec.ids_member(List.take(&2, Nat, t, q), y), False{},
        idp_mem_take_false(t, q, y, idp_not_true(Spec.ids_member(t, y), MP.ar_and_l(Bool.not(Spec.ids_member(t, y)), Spec.ids_nodup(t), n2)))) : {Bool.and(Bool.not(_), Spec.ids_nodup(List.take(&2, Nat, t, q))) == True{} : Bool}
      idp_nd_take(t, q, MP.ar_and_r(Bool.not(Spec.ids_member(t, y)), Spec.ids_nodup(t), n2))

def idp_lt_take(xs: List<&2, Nat>, +n: Nat, +D: Nat, h: {Spec.ids_all_lt(xs, D) == True{} : Bool})
  -> {Spec.ids_all_lt(List.take(&2, Nat, xs, n), D) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case (y <> t) 0n:
      {==}
    case (+y <> +t) 1n+q:
      +hh = h
      MP.ar_and_intro(Nat.is_lt(y, D), Spec.ids_all_lt(List.take(&2, Nat, t, q), D),
        MP.ar_and_l(Nat.is_lt(y, D), Spec.ids_all_lt(t, D), hh),
        idp_lt_take(t, q, D, MP.ar_and_r(Nat.is_lt(y, D), Spec.ids_all_lt(t, D), hh)))

# (128 nb) / 128 == nb and (128 nb) % 128 == 0
def idp_divmod_v(+nb: Nat) -> {Nat.div(Nat.mul(nb, 128n), 128n) == nb : Nat} & {Nat.mod(Nat.mul(nb, 128n), 128n) == 0n : Nat}:
  %MP.ar_add_zero_r(Nat.mul(nb, 128n)) : {Nat.div(_, 128n) == nb : Nat} & {Nat.mod(_, 128n) == 0n : Nat}
  MP.ar_div_unique(nb, 0n, 128n, {==})

def idp_div_v(+nb: Nat) -> {Nat.div(Nat.mul(nb, 128n), 128n) == nb : Nat}:
  MP.ard_fst({Nat.div(Nat.mul(nb, 128n), 128n) == nb : Nat}, {Nat.mod(Nat.mul(nb, 128n), 128n) == 0n : Nat}, idp_divmod_v(nb))

def idp_mod_v(+nb: Nat) -> {Nat.mod(Nat.mul(nb, 128n), 128n) == 0n : Nat}:
  MP.ard_snd({Nat.div(Nat.mul(nb, 128n), 128n) == nb : Nat}, {Nat.mod(Nat.mul(nb, 128n), 128n) == 0n : Nat}, idp_divmod_v(nb))

def Laws.kept_perm_accepted(order, nb, n, perm, range):
  +V = Nat.mul(nb, 128n)
  +p = List.take(&2, Nat, order, n)
  +pm = perm
  +rg = range
  +lenb = MP.ar_eq_true(List.length(&2, Nat, order), nb, MP.ar_and_l(Nat.is_eq(List.length(&2, Nat, order), nb), Spec.ids_blocks_in(order, nb), pm))
  +bi = MP.ar_and_r(Nat.is_eq(List.length(&2, Nat, order), nb), Spec.ids_blocks_in(order, nb), pm)
  +nd = MP.ar_and_l(Spec.ids_nodup(order), Spec.ids_all_lt(order, nb), bi)
  +al = MP.ar_and_r(Spec.ids_nodup(order), Spec.ids_all_lt(order, nb), bi)
  +nle = MP.ar_and_r(Nat.is_lt(0n, n), Nat.is_le(n, nb), rg)
  +lenp = idp_len_take(order, n, %Equal.sym(Nat, List.length(&2, Nat, order), nb, lenb) : {Nat.is_le(n, _) == True{} : Bool}; nle)
  %Equal.sym(Bool, Impl.idm_kept_ok(order, n, V), Spec.ids_prefix_ok(order, n, V), Laws.kept_accepts_exactly(order, n, V)) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.div(V, 128n), nb, idp_div_v(nb)) : {Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, _)))) == True{} : Bool}
  MP.ar_and_intro(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, nb))),
    MP.ar_and_l(Nat.is_lt(0n, n), Nat.is_le(n, nb), rg),
    MP.ar_and_intro(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, nb)),
      %Equal.sym(Nat, List.length(&2, Nat, p), n, lenp) : {Nat.is_eq(_, n) == True{} : Bool}; MP.ar_eq_refl(n),
      MP.ar_and_intro(Spec.ids_nodup(p), Spec.ids_all_lt(p, nb), idp_nd_take(order, n, nd), idp_lt_take(order, n, nb, al))))

# An accepted table: its prefix is accepted by the reference.
def idp_pre(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {Spec.ids_prefix_ok(order, n, vocab) == True{} : Bool}:
  Equal.trans(Bool, Spec.ids_prefix_ok(order, n, vocab), Impl.idm_kept_ok(order, n, vocab), True{},
    Equal.sym(Bool, Impl.idm_kept_ok(order, n, vocab), Spec.ids_prefix_ok(order, n, vocab), Laws.kept_accepts_exactly(order, n, vocab)), ok)

def idp_pre_rest(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {Bool.and(Nat.is_eq(List.length(&2, Nat, List.take(&2, Nat, order, n)), n), Bool.and(Spec.ids_nodup(List.take(&2, Nat, order, n)),
      Spec.ids_all_lt(List.take(&2, Nat, order, n), Nat.div(vocab, 128n)))) == True{} : Bool}:
  +p = List.take(&2, Nat, order, n)
  MP.ar_and_r(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n)))),
    idp_pre(order, n, vocab, ok))

def idp_pre_nd(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {Spec.ids_nodup(List.take(&2, Nat, order, n)) == True{} : Bool}:
  +p = List.take(&2, Nat, order, n)
  MP.ar_and_l(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n)),
    MP.ar_and_r(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n))), idp_pre_rest(order, n, vocab, ok)))

def idp_pre_lt(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {Spec.ids_all_lt(List.take(&2, Nat, order, n), Nat.div(vocab, 128n)) == True{} : Bool}:
  +p = List.take(&2, Nat, order, n)
  MP.ar_and_r(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n)),
    MP.ar_and_r(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n))), idp_pre_rest(order, n, vocab, ok)))

def idp_pre_len(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {List.length(&2, Nat, List.take(&2, Nat, order, n)) == n : Nat}:
  +p = List.take(&2, Nat, order, n)
  MP.ar_eq_true(List.length(&2, Nat, p), n, MP.ar_and_l(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n))),
    idp_pre_rest(order, n, vocab, ok)))

def idp_pre_pos(+order: List<&2, Nat>, +n: Nat, +vocab: Nat, ok: {Impl.idm_kept_ok(order, n, vocab) == True{} : Bool})
  -> {Nat.is_lt(0n, n) == True{} : Bool}:
  +p = List.take(&2, Nat, order, n)
  MP.ar_and_l(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(List.length(&2, Nat, p), n), Bool.and(Spec.ids_nodup(p), Spec.ids_all_lt(p, Nat.div(vocab, 128n)))),
    idp_pre(order, n, vocab, ok))

def Laws.kept_blocks_in(order, n, nb, ok):
  +V = Nat.mul(nb, 128n)
  +p = List.take(&2, Nat, order, n)
  +o2 = ok
  MP.ar_and_intro(Spec.ids_nodup(Impl.idm_sort(p)), Spec.ids_all_lt(Impl.idm_sort(p), nb),
    %Equal.sym(Bool, Spec.ids_nodup(Impl.idm_sort(p)), Spec.ids_nodup(p), idp_nd_sort(p)) : {_ == True{} : Bool}; idp_pre_nd(order, n, V, o2),
    %Equal.sym(Bool, Spec.ids_all_lt(Impl.idm_sort(p), nb), Spec.ids_all_lt(p, nb), idp_lt_sort(p, nb)) : {_ == True{} : Bool}; %idp_div_v(nb) : {Spec.ids_all_lt(p, _) == True{} : Bool}; idp_pre_lt(order, n, V, o2))

def idp_adj(xs: List<&2, Nat>, inc: {Spec.ids_increasing(xs) == True{} : Bool}) -> {Impl.idm_adj_incr(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match rest:
        case Nil{}:
          {==}
        case +z <> +more:
          +i2 = inc
          +gy = MP.ar_and_l(Spec.ids_all_gt(z <> more, y), Spec.ids_increasing(z <> more), i2)
          MP.ar_and_intro(Nat.is_lt(y, z), Impl.idm_adj_incr(z <> more),
            MP.ar_and_l(Nat.is_lt(y, z), Spec.ids_all_gt(more, y), gy),
            idp_adj(z <> more, MP.ar_and_r(Spec.ids_all_gt(z <> more, y), Spec.ids_increasing(z <> more), i2)))

def idp_le16(k: Nat, pos: {Nat.is_lt(0n, k) == True{} : Bool}) -> {Nat.is_le(16n, Nat.mul(k, 128n)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(16n, Nat.mul(0n, 128n)) == True{} : Bool}, MP.ar_false_true(pos))
    case 1n+j:
      {==}

def Laws.kept_head_accepts(order, n, nb, ok):
  +V = Nat.mul(nb, 128n)
  +p = List.take(&2, Nat, order, n)
  +q = Impl.idm_sort(p)
  +o2 = ok
  +lq = Equal.trans(Nat, List.length(&2, Nat, q), List.length(&2, Nat, p), n, idp_len_sort(p), idp_pre_len(order, n, V, o2))
  +pos = idp_pre_pos(order, n, V, o2)
  %Equal.sym(Nat, List.length(&2, Nat, q), n, lq) : {Bool.and(Nat.is_eq(Nat.mod(V, 128n), 0n), Bool.and(Nat.is_lt(0n, _), Bool.and(Nat.is_le(16n, Nat.mul(_, 128n)), Bool.and(Impl.idm_last_fits(q, V), Impl.idm_adj_incr(q))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mod(V, 128n), 0n, idp_mod_v(nb)) : {Bool.and(Nat.is_eq(_, 0n), Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_le(16n, Nat.mul(n, 128n)), Bool.and(Impl.idm_last_fits(q, V), Impl.idm_adj_incr(q))))) == True{} : Bool}
  MP.ar_and_intro(Nat.is_lt(0n, n), Bool.and(Nat.is_le(16n, Nat.mul(n, 128n)), Bool.and(Impl.idm_last_fits(q, V), Impl.idm_adj_incr(q))), pos,
    MP.ar_and_intro(Nat.is_le(16n, Nat.mul(n, 128n)), Bool.and(Impl.idm_last_fits(q, V), Impl.idm_adj_incr(q)), idp_le16(n, pos),
      MP.ar_and_intro(Impl.idm_last_fits(q, V), Impl.idm_adj_incr(q),
        MP.ar_and_r(Nat.is_eq(Impl.idm_card(q), n), Impl.idm_last_fits(q, V), o2),
        idp_adj(q, idp_inc_sort(p, idp_pre_nd(order, n, V, o2))))))

# ==== law 4: top-k ====

# -- the kernel's better() is the reference order --

def idp_better(a: Spec.IdmCand, b: Spec.IdmCand) -> {Impl.idm_better(a, b) == Spec.ids_before(a, b) : Bool}:
  match a b:
    case Spec.IdmCand{+va, +ta} Spec.IdmCand{+vb, +tb}:
      %Equal.sym(Bool, Nat.is_gt(va, vb), Nat.is_lt(vb, va), MP.ar_gt_flip(va, vb)) : {Bool.or(_, Bool.and(Nat.is_eq(va, vb), Nat.is_lt(ta, tb))) == Spec.ids_before(Spec.IdmCand{va, ta}, Spec.IdmCand{vb, tb}) : Bool}
      {==}

# -- (value desc, token asc) is a strict total order on candidates --

def idp_or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({b == True{} : Bool}, MP.ar_false_true(e))

def idp_irr(a: Spec.IdmCand) -> {Spec.ids_before(a, a) == False{} : Bool}:
  match a:
    case Spec.IdmCand{+v, +t}:
      %Equal.sym(Bool, Nat.is_lt(v, v), False{}, MP.ar_lt_irrefl(v)) : {Bool.or(_, Bool.and(Nat.is_eq(v, v), Nat.is_lt(t, t))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(v, v), True{}, MP.ar_eq_refl(v)) : {Bool.or(False{}, Bool.and(_, Nat.is_lt(t, t))) == False{} : Bool}
      MP.ar_lt_irrefl(t)

def idp_tr(+va: Nat, +ta: Nat, +vb: Nat, +tb: Nat, +vc: Nat, +tc: Nat,
    L1: Bool, e1: {Nat.is_lt(vb, va) == L1 : Bool}, L2: Bool, e2: {Nat.is_lt(vc, vb) == L2 : Bool},
    h1: {Bool.or(L1, Bool.and(Nat.is_eq(va, vb), Nat.is_lt(ta, tb))) == True{} : Bool},
    h2: {Bool.or(L2, Bool.and(Nat.is_eq(vb, vc), Nat.is_lt(tb, tc))) == True{} : Bool})
  -> {Bool.or(Nat.is_lt(vc, va), Bool.and(Nat.is_eq(va, vc), Nat.is_lt(ta, tc))) == True{} : Bool}:
  match L1:
    case True{}:
      match L2:
        case True{}:
          idp_or_l(Nat.is_lt(vc, va), Bool.and(Nat.is_eq(va, vc), Nat.is_lt(ta, tc)), MP.ar_lt_trans(vc, vb, va, e2, e1))
        case False{}:
          +q = MP.ar_eq_true(vb, vc, MP.ar_and_l(Nat.is_eq(vb, vc), Nat.is_lt(tb, tc), h2))
          idp_or_l(Nat.is_lt(vc, va), Bool.and(Nat.is_eq(va, vc), Nat.is_lt(ta, tc)), %q : {Nat.is_lt(_, va) == True{} : Bool}; e1)
    case False{}:
      match L2:
        case True{}:
          +q1 = MP.ar_eq_true(va, vb, MP.ar_and_l(Nat.is_eq(va, vb), Nat.is_lt(ta, tb), h1))
          idp_or_l(Nat.is_lt(vc, va), Bool.and(Nat.is_eq(va, vc), Nat.is_lt(ta, tc)), %Equal.sym(Nat, va, vb, q1) : {Nat.is_lt(vc, _) == True{} : Bool}; e2)
        case False{}:
          +hh = h1
          +q1 = MP.ar_eq_true(va, vb, MP.ar_and_l(Nat.is_eq(va, vb), Nat.is_lt(ta, tb), hh))
          +lt1 = MP.ar_and_r(Nat.is_eq(va, vb), Nat.is_lt(ta, tb), hh)
          +h22 = h2
          +q2 = MP.ar_eq_true(vb, vc, MP.ar_and_l(Nat.is_eq(vb, vc), Nat.is_lt(tb, tc), h22))
          +lt2 = MP.ar_and_r(Nat.is_eq(vb, vc), Nat.is_lt(tb, tc), h22)
          idp_or_r(Nat.is_lt(vc, va), Bool.and(Nat.is_eq(va, vc), Nat.is_lt(ta, tc)),
            MP.ar_and_intro(Nat.is_eq(va, vc), Nat.is_lt(ta, tc),
              MP.p8_eq_of(va, vc, Equal.trans(Nat, va, vb, vc, q1, q2)), MP.ar_lt_trans(ta, tb, tc, lt1, lt2)))

def idp_trans(a: Spec.IdmCand, b: Spec.IdmCand, c: Spec.IdmCand,
    h1: {Spec.ids_before(a, b) == True{} : Bool}, h2: {Spec.ids_before(b, c) == True{} : Bool})
  -> {Spec.ids_before(a, c) == True{} : Bool}:
  match a b c:
    case Spec.IdmCand{+va, +ta} Spec.IdmCand{+vb, +tb} Spec.IdmCand{+vc, +tc}:
      idp_tr(va, ta, vb, tb, vc, tc, Nat.is_lt(vb, va), {==}, Nat.is_lt(vc, vb), {==}, h1, h2)

# lt(a, b) and lt(b, a) both False: a == b.
def idp_tri(+a: Nat, +b: Nat, x: {Nat.is_lt(a, b) == False{} : Bool}, y: {Nat.is_lt(b, a) == False{} : Bool})
  -> {Nat.is_eq(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_eq(0n, 1n+q) == True{} : Bool}, MP.ar_true_false(x))
    case 1n+p 0n:
      Empty.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool}, MP.ar_true_false(y))
    case 1n+p 1n+q:
      idp_tri(p, q, x, y)

# lt(a, b) and eq(a, b) both False: b < a.
def idp_tri2(+a: Nat, +b: Nat, x: {Nat.is_lt(a, b) == False{} : Bool}, y: {Nat.is_eq(a, b) == False{} : Bool})
  -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, MP.ar_true_false(y))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, MP.ar_true_false(x))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      idp_tri2(p, q, x, y)

def idp_to(+va: Nat, +ta: Nat, +vb: Nat, +tb: Nat, L: Bool, e: {Nat.is_lt(va, vb) == L : Bool},
    ne: {Bool.and(Nat.is_eq(va, vb), Nat.is_eq(ta, tb)) == False{} : Bool},
    nb: {Bool.or(Nat.is_lt(vb, va), Bool.and(Nat.is_eq(va, vb), Nat.is_lt(ta, tb))) == False{} : Bool})
  -> {Bool.or(L, Bool.and(Nat.is_eq(vb, va), Nat.is_lt(tb, ta))) == True{} : Bool}:
  match L:
    case True{}:
      {==}
    case False{}:
      +nb2 = nb
      +ev = idp_tri(va, vb, e, idp_or_false_l(Nat.is_lt(vb, va), Bool.and(Nat.is_eq(va, vb), Nat.is_lt(ta, tb)), nb2))
      +x = idp_or_false_r(Nat.is_lt(vb, va), Bool.and(Nat.is_eq(va, vb), Nat.is_lt(ta, tb)), nb2)
      +lt0 : {Nat.is_lt(ta, tb) == False{} : Bool} = %ev : {Bool.and(_, Nat.is_lt(ta, tb)) == False{} : Bool}; x
      +eq0 : {Nat.is_eq(ta, tb) == False{} : Bool} = %ev : {Bool.and(_, Nat.is_eq(ta, tb)) == False{} : Bool}; ne
      MP.ar_and_intro(Nat.is_eq(vb, va), Nat.is_lt(tb, ta),
        Equal.trans(Bool, Nat.is_eq(vb, va), Nat.is_eq(va, vb), True{}, idp_eq_sym(vb, va), ev),
        idp_tri2(ta, tb, lt0, eq0))

def idp_total(a: Spec.IdmCand, b: Spec.IdmCand, ne: {Spec.ids_ceq(a, b) == False{} : Bool},
    nb: {Spec.ids_before(a, b) == False{} : Bool}) -> {Spec.ids_before(b, a) == True{} : Bool}:
  match a b:
    case Spec.IdmCand{+va, +ta} Spec.IdmCand{+vb, +tb}:
      idp_to(va, ta, vb, tb, Nat.is_lt(va, vb), {==}, ne, nb)

def idp_asym_b(B: Bool, +a: Spec.IdmCand, +b: Spec.IdmCand, e: {Spec.ids_before(b, a) == B : Bool},
    h: {Spec.ids_before(a, b) == True{} : Bool}) -> {B == False{} : Bool}:
  match B:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MP.ar_false_true(Equal.trans(Bool, False{}, Spec.ids_before(a, a), True{},
        Equal.sym(Bool, Spec.ids_before(a, a), False{}, idp_irr(a)), idp_trans(a, b, a, h, e))))

def idp_asym(+a: Spec.IdmCand, +b: Spec.IdmCand, h: {Spec.ids_before(a, b) == True{} : Bool})
  -> {Spec.ids_before(b, a) == False{} : Bool}:
  idp_asym_b(Spec.ids_before(b, a), a, b, {==}, h)

def idp_ceq_eq(a: Spec.IdmCand, b: Spec.IdmCand, e: {Spec.ids_ceq(a, b) == True{} : Bool}) -> {a == b : Spec.IdmCand}:
  match a b:
    case Spec.IdmCand{+va, +ta} Spec.IdmCand{+vb, +tb}:
      +ee = e
      %MP.ar_eq_true(va, vb, MP.ar_and_l(Nat.is_eq(va, vb), Nat.is_eq(ta, tb), ee)) : {Spec.IdmCand{va, ta} == Spec.IdmCand{_, tb} : Spec.IdmCand}
      %MP.ar_eq_true(ta, tb, MP.ar_and_r(Nat.is_eq(va, vb), Nat.is_eq(ta, tb), ee)) : {Spec.IdmCand{va, ta} == Spec.IdmCand{va, _} : Spec.IdmCand}
      {==}

def idp_ceq_sym(a: Spec.IdmCand, b: Spec.IdmCand) -> {Spec.ids_ceq(a, b) == Spec.ids_ceq(b, a) : Bool}:
  match a b:
    case Spec.IdmCand{+va, +ta} Spec.IdmCand{+vb, +tb}:
      %idp_eq_sym(vb, va) : {Bool.and(_, Nat.is_eq(ta, tb)) == Bool.and(Nat.is_eq(vb, va), Nat.is_eq(tb, ta)) : Bool}
      %idp_eq_sym(tb, ta) : {Bool.and(Nat.is_eq(vb, va), _) == Bool.and(Nat.is_eq(vb, va), Nat.is_eq(tb, ta)) : Bool}
      {==}

def idp_bf_ne_b(C: Bool, +a: Spec.IdmCand, +b: Spec.IdmCand, e: {Spec.ids_ceq(a, b) == C : Bool},
    h: {Spec.ids_before(a, b) == True{} : Bool}) -> {C == False{} : Bool}:
  match C:
    case False{}:
      {==}
    case True{}:
      +q = idp_ceq_eq(a, b, e)
      Empty.absurd({True{} == False{} : Bool}, MP.ar_false_true(Equal.trans(Bool, False{}, Spec.ids_before(a, a), True{},
        Equal.sym(Bool, Spec.ids_before(a, a), False{}, idp_irr(a)), %Equal.sym(Spec.IdmCand, a, b, q) : {Spec.ids_before(a, _) == True{} : Bool}; h)))

# a before b: a and b differ.
def idp_bf_ne(+a: Spec.IdmCand, +b: Spec.IdmCand, h: {Spec.ids_before(a, b) == True{} : Bool})
  -> {Spec.ids_ceq(a, b) == False{} : Bool}:
  idp_bf_ne_b(Spec.ids_ceq(a, b), a, b, {==}, h)

# -- the running top-k list is the ranked prefix --

def idp_sel_eq(g: Bool, +c: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>, +deeper: List<&2, Spec.IdmCand>)
  -> {Impl.idm_ins.sel(g, c, y, rest, deeper) == Spec.ids_insert.sel(g, c, y, rest, deeper) : List<&2, Spec.IdmCand>}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_ins_eq(ys: List<&2, Spec.IdmCand>, +c: Spec.IdmCand) -> {Impl.idm_ins(ys, c) == Spec.ids_insert(ys, c) : List<&2, Spec.IdmCand>}:
  match ys:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Impl.idm_better(c, y), Spec.ids_before(c, y), idp_better(c, y)) : {Impl.idm_ins.sel(_, c, y, rest, Impl.idm_ins(rest, c)) == Spec.ids_insert.sel(Spec.ids_before(c, y), c, y, rest, Spec.ids_insert(rest, c)) : List<&2, Spec.IdmCand>}
      %Equal.sym(List<&2, Spec.IdmCand>, Impl.idm_ins(rest, c), Spec.ids_insert(rest, c), idp_ins_eq(rest, c)) : {Impl.idm_ins.sel(Spec.ids_before(c, y), c, y, rest, _) == Spec.ids_insert.sel(Spec.ids_before(c, y), c, y, rest, Spec.ids_insert(rest, c)) : List<&2, Spec.IdmCand>}
      idp_sel_eq(Spec.ids_before(c, y), c, y, rest, Spec.ids_insert(rest, c))

def idp_take_take(-A: Data, xs: List<&2, A>, +j: Nat) -> {List.take(&2, A, List.take(&2, A, xs, 1n+j), j) == List.take(&2, A, xs, j) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +t:
      match j:
        case 0n:
          {==}
        case 1n+i:
          +i1 = i
          Equal.cong(List<&2, A>, List<&2, A>, l => y <> l, List.take(&2, A, List.take(&2, A, t, 1n+i1), i1), List.take(&2, A, t, i1), idp_take_take(A, t, i1))

def idp_tct(+r: Spec.IdmCand, +R: List<&2, Spec.IdmCand>, k: Nat)
  -> {List.take(&2, Spec.IdmCand, r <> List.take(&2, Spec.IdmCand, R, k), k) == List.take(&2, Spec.IdmCand, r <> R, k) : List<&2, Spec.IdmCand>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +j1 = j
      Equal.cong(List<&2, Spec.IdmCand>, List<&2, Spec.IdmCand>, l => r <> l, List.take(&2, Spec.IdmCand, List.take(&2, Spec.IdmCand, R, 1n+j1), j1),
        List.take(&2, Spec.IdmCand, R, j1), idp_take_take(Spec.IdmCand, R, j1))

def idp_ti_sel(g: Bool, +x: Spec.IdmCand, +r: Spec.IdmCand, +R: List<&2, Spec.IdmCand>, +k: Nat,
    ih: {List.take(&2, Spec.IdmCand, Spec.ids_insert(List.take(&2, Spec.IdmCand, R, k), x), k) == List.take(&2, Spec.IdmCand, Spec.ids_insert(R, x), k) : List<&2, Spec.IdmCand>})
  -> {List.take(&2, Spec.IdmCand, Spec.ids_insert.sel(g, x, r, List.take(&2, Spec.IdmCand, R, k), Spec.ids_insert(List.take(&2, Spec.IdmCand, R, k), x)), 1n+k) ==
      List.take(&2, Spec.IdmCand, Spec.ids_insert.sel(g, x, r, R, Spec.ids_insert(R, x)), 1n+k) : List<&2, Spec.IdmCand>}:
  match g:
    case True{}:
      Equal.cong(List<&2, Spec.IdmCand>, List<&2, Spec.IdmCand>, l => x <> l, List.take(&2, Spec.IdmCand, r <> List.take(&2, Spec.IdmCand, R, k), k),
        List.take(&2, Spec.IdmCand, r <> R, k), idp_tct(r, R, k))
    case False{}:
      Equal.cong(List<&2, Spec.IdmCand>, List<&2, Spec.IdmCand>, l => r <> l, List.take(&2, Spec.IdmCand, Spec.ids_insert(List.take(&2, Spec.IdmCand, R, k), x), k),
        List.take(&2, Spec.IdmCand, Spec.ids_insert(R, x), k), ih)

# Cutting the list to k before inserting does not change its first k entries.
def idp_take_ins(R: List<&2, Spec.IdmCand>, +x: Spec.IdmCand, +k: Nat)
  -> {List.take(&2, Spec.IdmCand, Spec.ids_insert(List.take(&2, Spec.IdmCand, R, k), x), k) == List.take(&2, Spec.IdmCand, Spec.ids_insert(R, x), k) : List<&2, Spec.IdmCand>}:
  match R k:
    case Nil{} _:
      {==}
    case (+r <> +R2) 0n:
      Equal.sym(List<&2, Spec.IdmCand>, List.take(&2, Spec.IdmCand, Spec.ids_insert(r <> R2, x), 0n), Nil{}, idp_take0(Spec.IdmCand, Spec.ids_insert(r <> R2, x)))
    case (+r <> +R2) 1n+j:
      idp_ti_sel(Spec.ids_before(x, r), x, r, R2, j, idp_take_ins(R2, x, j))

def idp_topk_rank(+k: Nat, xs: List<&2, Spec.IdmCand>) -> {Impl.idm_topk(k, xs) == Spec.ids_topk(k, xs) : List<&2, Spec.IdmCand>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(List<&2, Spec.IdmCand>, Impl.idm_ins(Impl.idm_topk(k, rest), x), Spec.ids_insert(Impl.idm_topk(k, rest), x), idp_ins_eq(Impl.idm_topk(k, rest), x)) : {List.take(&2, Spec.IdmCand, _, k) == List.take(&2, Spec.IdmCand, Spec.ids_insert(Spec.ids_rank(rest), x), k) : List<&2, Spec.IdmCand>}
      %Equal.sym(List<&2, Spec.IdmCand>, Impl.idm_topk(k, rest), List.take(&2, Spec.IdmCand, Spec.ids_rank(rest), k), idp_topk_rank(k, rest)) : {List.take(&2, Spec.IdmCand, Spec.ids_insert(_, x), k) == List.take(&2, Spec.IdmCand, Spec.ids_insert(Spec.ids_rank(rest), x), k) : List<&2, Spec.IdmCand>}
      idp_take_ins(Spec.ids_rank(rest), x, k)

def Laws.topk_ranked_prefix(k, xs):
  idp_topk_rank(k, xs)

# -- rankings are strictly sorted and determined by their entries --

# Every entry ranks after c.
def idp_aft(xs: List<&2, Spec.IdmCand>, +c: Spec.IdmCand) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case y <> rest:
      Bool.and(Spec.ids_before(c, y), idp_aft(rest, c))

# Strictly sorted by the ranking order.
def idp_ss(xs: List<&2, Spec.IdmCand>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +rest:
      Bool.and(idp_aft(rest, y), idp_ss(rest))

def idp_aft_mono(xs: List<&2, Spec.IdmCand>, +c: Spec.IdmCand, +y: Spec.IdmCand, +cy: {Spec.ids_before(c, y) == True{} : Bool},
    a: {idp_aft(xs, y) == True{} : Bool}) -> {idp_aft(xs, c) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +z <> +rest:
      +aa = a
      MP.ar_and_intro(Spec.ids_before(c, z), idp_aft(rest, c),
        idp_trans(c, y, z, cy, MP.ar_and_l(Spec.ids_before(y, z), idp_aft(rest, y), aa)),
        idp_aft_mono(rest, c, y, cy, MP.ar_and_r(Spec.ids_before(y, z), idp_aft(rest, y), aa)))

def idp_aft_sel(g: Bool, +x: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>, deeper: List<&2, Spec.IdmCand>, +c: Spec.IdmCand,
    ih: {idp_aft(deeper, c) == Bool.and(Spec.ids_before(c, x), idp_aft(rest, c)) : Bool})
  -> {idp_aft(Spec.ids_insert.sel(g, x, y, rest, deeper), c) == Bool.and(Spec.ids_before(c, x), Bool.and(Spec.ids_before(c, y), idp_aft(rest, c))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, idp_aft(deeper, c), Bool.and(Spec.ids_before(c, x), idp_aft(rest, c)), ih) : {Bool.and(Spec.ids_before(c, y), _) == Bool.and(Spec.ids_before(c, x), Bool.and(Spec.ids_before(c, y), idp_aft(rest, c))) : Bool}
      idp_and_swap(Spec.ids_before(c, x), Spec.ids_before(c, y), idp_aft(rest, c))

def idp_aft_ins(R: List<&2, Spec.IdmCand>, +x: Spec.IdmCand, +c: Spec.IdmCand)
  -> {idp_aft(Spec.ids_insert(R, x), c) == Bool.and(Spec.ids_before(c, x), idp_aft(R, c)) : Bool}:
  match R:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_aft_sel(Spec.ids_before(x, y), x, y, rest, Spec.ids_insert(rest, x), c, idp_aft_ins(rest, x, c))

def idp_cmem_sel(g: Bool, +x: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>, deeper: List<&2, Spec.IdmCand>, +d: Spec.IdmCand,
    ih: {Spec.ids_cmember(deeper, d) == Bool.or(Spec.ids_ceq(x, d), Spec.ids_cmember(rest, d)) : Bool})
  -> {Spec.ids_cmember(Spec.ids_insert.sel(g, x, y, rest, deeper), d) == Bool.or(Spec.ids_ceq(x, d), Bool.or(Spec.ids_ceq(y, d), Spec.ids_cmember(rest, d))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_cmember(deeper, d), Bool.or(Spec.ids_ceq(x, d), Spec.ids_cmember(rest, d)), ih) : {Bool.or(Spec.ids_ceq(y, d), _) == Bool.or(Spec.ids_ceq(x, d), Bool.or(Spec.ids_ceq(y, d), Spec.ids_cmember(rest, d))) : Bool}
      idp_or_swap(Spec.ids_ceq(x, d), Spec.ids_ceq(y, d), Spec.ids_cmember(rest, d))

def idp_cmem_ins(R: List<&2, Spec.IdmCand>, +x: Spec.IdmCand, +d: Spec.IdmCand)
  -> {Spec.ids_cmember(Spec.ids_insert(R, x), d) == Bool.or(Spec.ids_ceq(x, d), Spec.ids_cmember(R, d)) : Bool}:
  match R:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_cmem_sel(Spec.ids_before(x, y), x, y, rest, Spec.ids_insert(rest, x), d, idp_cmem_ins(rest, x, d))

def idp_cmem_rank(xs: List<&2, Spec.IdmCand>, +d: Spec.IdmCand) -> {Spec.ids_cmember(Spec.ids_rank(xs), d) == Spec.ids_cmember(xs, d) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_cmember(Spec.ids_insert(Spec.ids_rank(rest), x), d), Bool.or(Spec.ids_ceq(x, d), Spec.ids_cmember(Spec.ids_rank(rest), d)), idp_cmem_ins(Spec.ids_rank(rest), x, d)) : {_ == Spec.ids_cmember(x <> rest, d) : Bool}
      %Equal.sym(Bool, Spec.ids_cmember(Spec.ids_rank(rest), d), Spec.ids_cmember(rest, d), idp_cmem_rank(rest, d)) : {Bool.or(Spec.ids_ceq(x, d), _) == Spec.ids_cmember(x <> rest, d) : Bool}
      {==}

def idp_ss_sel(g: Bool, +x: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>, +e: {Spec.ids_before(x, y) == g : Bool},
    +ssy: {idp_ss(y <> rest) == True{} : Bool}, +nxy: {Spec.ids_ceq(y, x) == False{} : Bool},
    ihr: {idp_ss(Spec.ids_insert(rest, x)) == True{} : Bool})
  -> {idp_ss(Spec.ids_insert.sel(g, x, y, rest, Spec.ids_insert(rest, x))) == True{} : Bool}:
  match g:
    case True{}:
      MP.ar_and_intro(idp_aft(y <> rest, x), idp_ss(y <> rest),
        MP.ar_and_intro(Spec.ids_before(x, y), idp_aft(rest, x), e,
          idp_aft_mono(rest, x, y, e, MP.ar_and_l(idp_aft(rest, y), idp_ss(rest), ssy))),
        ssy)
    case False{}:
      %Equal.sym(Bool, idp_aft(Spec.ids_insert(rest, x), y), Bool.and(Spec.ids_before(y, x), idp_aft(rest, y)), idp_aft_ins(rest, x, y)) : {Bool.and(_, idp_ss(Spec.ids_insert(rest, x))) == True{} : Bool}
      MP.ar_and_intro(Bool.and(Spec.ids_before(y, x), idp_aft(rest, y)), idp_ss(Spec.ids_insert(rest, x)),
        MP.ar_and_intro(Spec.ids_before(y, x), idp_aft(rest, y),
          idp_total(x, y, Equal.trans(Bool, Spec.ids_ceq(x, y), Spec.ids_ceq(y, x), False{}, idp_ceq_sym(x, y), nxy), e),
          MP.ar_and_l(idp_aft(rest, y), idp_ss(rest), ssy)),
        ihr)

def idp_ss_ins(R: List<&2, Spec.IdmCand>, +x: Spec.IdmCand, ss: {idp_ss(R) == True{} : Bool},
    nm: {Spec.ids_cmember(R, x) == False{} : Bool}) -> {idp_ss(Spec.ids_insert(R, x)) == True{} : Bool}:
  match R:
    case Nil{}:
      {==}
    case +y <> +rest:
      +s2 = ss
      +n2 = nm
      idp_ss_sel(Spec.ids_before(x, y), x, y, rest, {==}, s2, idp_or_false_l(Spec.ids_ceq(y, x), Spec.ids_cmember(rest, x), n2),
        idp_ss_ins(rest, x, MP.ar_and_r(idp_aft(rest, y), idp_ss(rest), s2), idp_or_false_r(Spec.ids_ceq(y, x), Spec.ids_cmember(rest, x), n2)))

def idp_ss_rank(xs: List<&2, Spec.IdmCand>, nd: {Spec.ids_cnodup(xs) == True{} : Bool}) -> {idp_ss(Spec.ids_rank(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +n2 = nd
      idp_ss_ins(Spec.ids_rank(rest), x, idp_ss_rank(rest, MP.ar_and_r(Bool.not(Spec.ids_cmember(rest, x)), Spec.ids_cnodup(rest), n2)),
        %Equal.sym(Bool, Spec.ids_cmember(Spec.ids_rank(rest), x), Spec.ids_cmember(rest, x), idp_cmem_rank(rest, x)) : {_ == False{} : Bool}
        idp_not_true(Spec.ids_cmember(rest, x), MP.ar_and_l(Bool.not(Spec.ids_cmember(rest, x)), Spec.ids_cnodup(rest), n2)))

def idp_sub_sel(g: Bool, +x: Spec.IdmCand, +y: Spec.IdmCand, +rest: List<&2, Spec.IdmCand>, deeper: List<&2, Spec.IdmCand>, +B: List<&2, Spec.IdmCand>,
    ih: {Spec.ids_subset(deeper, B) == Bool.and(Spec.ids_cmember(B, x), Spec.ids_subset(rest, B)) : Bool})
  -> {Spec.ids_subset(Spec.ids_insert.sel(g, x, y, rest, deeper), B) == Bool.and(Spec.ids_cmember(B, x), Bool.and(Spec.ids_cmember(B, y), Spec.ids_subset(rest, B))) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Spec.ids_subset(deeper, B), Bool.and(Spec.ids_cmember(B, x), Spec.ids_subset(rest, B)), ih) : {Bool.and(Spec.ids_cmember(B, y), _) == Bool.and(Spec.ids_cmember(B, x), Bool.and(Spec.ids_cmember(B, y), Spec.ids_subset(rest, B))) : Bool}
      idp_and_swap(Spec.ids_cmember(B, x), Spec.ids_cmember(B, y), Spec.ids_subset(rest, B))

def idp_sub_ins(R: List<&2, Spec.IdmCand>, +x: Spec.IdmCand, +B: List<&2, Spec.IdmCand>)
  -> {Spec.ids_subset(Spec.ids_insert(R, x), B) == Bool.and(Spec.ids_cmember(B, x), Spec.ids_subset(R, B)) : Bool}:
  match R:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_sub_sel(Spec.ids_before(x, y), x, y, rest, Spec.ids_insert(rest, x), B, idp_sub_ins(rest, x, B))

def idp_sub_rank_l(xs: List<&2, Spec.IdmCand>, +B: List<&2, Spec.IdmCand>) -> {Spec.ids_subset(Spec.ids_rank(xs), B) == Spec.ids_subset(xs, B) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_subset(Spec.ids_insert(Spec.ids_rank(rest), x), B), Bool.and(Spec.ids_cmember(B, x), Spec.ids_subset(Spec.ids_rank(rest), B)), idp_sub_ins(Spec.ids_rank(rest), x, B)) : {_ == Spec.ids_subset(x <> rest, B) : Bool}
      %Equal.sym(Bool, Spec.ids_subset(Spec.ids_rank(rest), B), Spec.ids_subset(rest, B), idp_sub_rank_l(rest, B)) : {Bool.and(Spec.ids_cmember(B, x), _) == Spec.ids_subset(x <> rest, B) : Bool}
      {==}

def idp_sub_rank_r(A: List<&2, Spec.IdmCand>, +ys: List<&2, Spec.IdmCand>) -> {Spec.ids_subset(A, Spec.ids_rank(ys)) == Spec.ids_subset(A, ys) : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Bool, Spec.ids_cmember(Spec.ids_rank(ys), a), Spec.ids_cmember(ys, a), idp_cmem_rank(ys, a)) : {Bool.and(_, Spec.ids_subset(rest, Spec.ids_rank(ys))) == Spec.ids_subset(a <> rest, ys) : Bool}
      %Equal.sym(Bool, Spec.ids_subset(rest, Spec.ids_rank(ys)), Spec.ids_subset(rest, ys), idp_sub_rank_r(rest, ys)) : {Bool.and(Spec.ids_cmember(ys, a), _) == Spec.ids_subset(a <> rest, ys) : Bool}
      {==}

def idp_aft_mem.step(C: Bool, +y: Spec.IdmCand, +c: Spec.IdmCand, +d: Spec.IdmCand, +L: List<&2, Spec.IdmCand>,
    e: {Spec.ids_ceq(y, d) == C : Bool}, a1: {Spec.ids_before(c, y) == True{} : Bool},
    m: {Bool.or(C, Spec.ids_cmember(L, d)) == True{} : Bool},
    ih: {Spec.ids_cmember(L, d) == True{} : Bool} -> {Spec.ids_before(c, d) == True{} : Bool})
  -> {Spec.ids_before(c, d) == True{} : Bool}:
  match C:
    case True{}:
      %idp_ceq_eq(y, d, e) : {Spec.ids_before(c, _) == True{} : Bool}
      a1
    case False{}:
      ih(m)

# Every entry of L ranks after c, and d is an entry: d ranks after c.
def idp_aft_mem(L: List<&2, Spec.IdmCand>, +c: Spec.IdmCand, +d: Spec.IdmCand, a: {idp_aft(L, c) == True{} : Bool},
    m: {Spec.ids_cmember(L, d) == True{} : Bool}) -> {Spec.ids_before(c, d) == True{} : Bool}:
  match L:
    case Nil{}:
      Empty.absurd({Spec.ids_before(c, d) == True{} : Bool}, MP.ar_false_true(m))
    case +y <> +rest:
      +aa = a
      idp_aft_mem.step(Spec.ids_ceq(y, d), y, c, d, rest, {==}, MP.ar_and_l(Spec.ids_before(c, y), idp_aft(rest, c), aa), m,
        r => idp_aft_mem(rest, c, d, MP.ar_and_r(Spec.ids_before(c, y), idp_aft(rest, c), aa), r))

def idp_sub_drop(A: List<&2, Spec.IdmCand>, +b: Spec.IdmCand, +B: List<&2, Spec.IdmCand>,
    h: {Spec.ids_subset(A, b <> B) == True{} : Bool}, af: {idp_aft(A, b) == True{} : Bool})
  -> {Spec.ids_subset(A, B) == True{} : Bool}:
  match A:
    case Nil{}:
      {==}
    case +c <> +rest:
      +hh = h
      +aa = af
      MP.ar_and_intro(Spec.ids_cmember(B, c), Spec.ids_subset(rest, B),
        idp_or_true_r(Spec.ids_ceq(b, c), Spec.ids_cmember(B, c),
          idp_bf_ne(b, c, MP.ar_and_l(Spec.ids_before(b, c), idp_aft(rest, b), aa)),
          MP.ar_and_l(Spec.ids_cmember(b <> B, c), Spec.ids_subset(rest, b <> B), hh)),
        idp_sub_drop(rest, b, B, MP.ar_and_r(Spec.ids_cmember(b <> B, c), Spec.ids_subset(rest, b <> B), hh),
          MP.ar_and_r(Spec.ids_before(b, c), idp_aft(rest, b), aa)))

def idp_head_eq(C: Bool, +a: Spec.IdmCand, +b: Spec.IdmCand, +A: List<&2, Spec.IdmCand>, +B: List<&2, Spec.IdmCand>,
    e: {Spec.ids_ceq(a, b) == C : Bool},
    aA: {idp_aft(A, a) == True{} : Bool}, bB: {idp_aft(B, b) == True{} : Bool},
    ab: {Bool.or(Spec.ids_ceq(b, a), Spec.ids_cmember(B, a)) == True{} : Bool},
    ba: {Bool.or(C, Spec.ids_cmember(A, b)) == True{} : Bool})
  -> {a == b : Spec.IdmCand}:
  match C:
    case True{}:
      idp_ceq_eq(a, b, e)
    case False{}:
      +ee = e
      +x = idp_aft_mem(A, a, b, aA, ba)
      +y = idp_aft_mem(B, b, a, bB, idp_or_true_r(Spec.ids_ceq(b, a), Spec.ids_cmember(B, a),
        Equal.trans(Bool, Spec.ids_ceq(b, a), Spec.ids_ceq(a, b), False{}, idp_ceq_sym(b, a), ee), ab))
      Empty.absurd({a == b : Spec.IdmCand}, MP.ar_false_true(Equal.trans(Bool, False{}, Spec.ids_before(b, a), True{},
        Equal.sym(Bool, Spec.ids_before(b, a), False{}, idp_asym(a, b, x)), y)))

# Two strictly sorted lists with the same entries are equal.
def idp_unique(A: List<&2, Spec.IdmCand>, B: List<&2, Spec.IdmCand>, sA: {idp_ss(A) == True{} : Bool}, sB: {idp_ss(B) == True{} : Bool},
    AB: {Spec.ids_subset(A, B) == True{} : Bool}, BA: {Spec.ids_subset(B, A) == True{} : Bool}) -> {A == B : List<&2, Spec.IdmCand>}:
  match A:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case b <> B2:
          Empty.absurd({Nil{} == b <> B2 : List<&2, Spec.IdmCand>}, MP.ar_false_true(BA))
    case +a <> +A2:
      match B:
        case Nil{}:
          Empty.absurd({a <> A2 == Nil{} : List<&2, Spec.IdmCand>}, MP.ar_false_true(AB))
        case +b <> +B2:
          +s1 = sA
          +s2 = sB
          +h1 = AB
          +h2 = BA
          +aA = MP.ar_and_l(idp_aft(A2, a), idp_ss(A2), s1)
          +bB = MP.ar_and_l(idp_aft(B2, b), idp_ss(B2), s2)
          +q = idp_head_eq(Spec.ids_ceq(a, b), a, b, A2, B2, {==}, aA, bB,
            MP.ar_and_l(Spec.ids_cmember(b <> B2, a), Spec.ids_subset(A2, b <> B2), h1),
            MP.ar_and_l(Spec.ids_cmember(a <> A2, b), Spec.ids_subset(B2, a <> A2), h2))
          +ih = idp_unique(A2, B2, MP.ar_and_r(idp_aft(A2, a), idp_ss(A2), s1), MP.ar_and_r(idp_aft(B2, b), idp_ss(B2), s2),
            idp_sub_drop(A2, b, B2, MP.ar_and_r(Spec.ids_cmember(b <> B2, a), Spec.ids_subset(A2, b <> B2), h1),
              %q : {idp_aft(A2, _) == True{} : Bool}; aA),
            idp_sub_drop(B2, a, A2, MP.ar_and_r(Spec.ids_cmember(a <> A2, b), Spec.ids_subset(B2, a <> A2), h2),
              %Equal.sym(Spec.IdmCand, a, b, q) : {idp_aft(B2, _) == True{} : Bool}; bB))
          %q : {a <> A2 == _ <> B2 : List<&2, Spec.IdmCand>}
          Equal.cong(List<&2, Spec.IdmCand>, List<&2, Spec.IdmCand>, l => a <> l, A2, B2, ih)

def idp_rank_eq(+xs: List<&2, Spec.IdmCand>, +ys: List<&2, Spec.IdmCand>, nx: {Spec.ids_cnodup(xs) == True{} : Bool},
    ny: {Spec.ids_cnodup(ys) == True{} : Bool}, same: {Spec.ids_same_set(xs, ys) == True{} : Bool})
  -> {Spec.ids_rank(xs) == Spec.ids_rank(ys) : List<&2, Spec.IdmCand>}:
  +sm = same
  idp_unique(Spec.ids_rank(xs), Spec.ids_rank(ys), idp_ss_rank(xs, nx), idp_ss_rank(ys, ny),
    %Equal.sym(Bool, Spec.ids_subset(Spec.ids_rank(xs), Spec.ids_rank(ys)), Spec.ids_subset(xs, Spec.ids_rank(ys)), idp_sub_rank_l(xs, Spec.ids_rank(ys))) : {_ == True{} : Bool}
    %Equal.sym(Bool, Spec.ids_subset(xs, Spec.ids_rank(ys)), Spec.ids_subset(xs, ys), idp_sub_rank_r(xs, ys)) : {_ == True{} : Bool}
    MP.ar_and_l(Spec.ids_subset(xs, ys), Spec.ids_subset(ys, xs), sm),
    %Equal.sym(Bool, Spec.ids_subset(Spec.ids_rank(ys), Spec.ids_rank(xs)), Spec.ids_subset(ys, Spec.ids_rank(xs)), idp_sub_rank_l(ys, Spec.ids_rank(xs))) : {_ == True{} : Bool}
    %Equal.sym(Bool, Spec.ids_subset(ys, Spec.ids_rank(xs)), Spec.ids_subset(ys, xs), idp_sub_rank_r(ys, xs)) : {_ == True{} : Bool}
    MP.ar_and_r(Spec.ids_subset(xs, ys), Spec.ids_subset(ys, xs), sm))

def Laws.topk_order_free(k, xs, ys, nx, ny, same):
  Equal.trans(List<&2, Spec.IdmCand>, Impl.idm_topk(k, xs), Spec.ids_topk(k, xs), Impl.idm_topk(k, ys), idp_topk_rank(k, xs),
    %Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_rank(xs), Spec.ids_rank(ys), idp_rank_eq(xs, ys, nx, ny, same)) : {List.take(&2, Spec.IdmCand, _, k) == Impl.idm_topk(k, ys) : List<&2, Spec.IdmCand>}
    Equal.sym(List<&2, Spec.IdmCand>, Impl.idm_topk(k, ys), Spec.ids_topk(k, ys), idp_topk_rank(k, ys)))

# -- candidate columns of token lists --

# Every entry of A occurs in B (token lists).
def idp_nsub(A: List<&2, Nat>, +B: List<&2, Nat>) -> Bool:
  match A:
    case Nil{}:
      True{}
    case a <> rest:
      Bool.and(Spec.ids_member(B, a), idp_nsub(rest, B))

def idp_ceq_cand_b(E: Bool, +vals: Impl.IdmVals, +y: Nat, +t: Nat, e: {Nat.is_eq(y, t) == E : Bool})
  -> {Bool.and(Nat.is_eq(Impl.idm_value(vals, y), Impl.idm_value(vals, t)), E) == E : Bool}:
  match E:
    case True{}:
      %Equal.sym(Nat, y, t, MP.ar_eq_true(y, t, e)) : {Bool.and(Nat.is_eq(Impl.idm_value(vals, _), Impl.idm_value(vals, t)), True{}) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(Impl.idm_value(vals, t), Impl.idm_value(vals, t)), True{}, MP.ar_eq_refl(Impl.idm_value(vals, t))) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      Equal.sym(Bool, False{}, Bool.and(Nat.is_eq(Impl.idm_value(vals, y), Impl.idm_value(vals, t)), False{}), MP.ar_h_and_false_r(Nat.is_eq(Impl.idm_value(vals, y), Impl.idm_value(vals, t))))

def idp_cmem_cols(+vals: Impl.IdmVals, L: List<&2, Nat>, +t: Nat)
  -> {Spec.ids_cmember(Impl.idm_cols(vals, L), Spec.IdmCand{Impl.idm_value(vals, t), t}) == Spec.ids_member(L, t) : Bool}:
  match L:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Bool.and(Nat.is_eq(Impl.idm_value(vals, y), Impl.idm_value(vals, t)), Nat.is_eq(y, t)), Nat.is_eq(y, t), idp_ceq_cand_b(Nat.is_eq(y, t), vals, y, t, {==})) : {Bool.or(_, Spec.ids_cmember(Impl.idm_cols(vals, rest), Spec.IdmCand{Impl.idm_value(vals, t), t})) == Spec.ids_member(y <> rest, t) : Bool}
      %Equal.sym(Bool, Spec.ids_cmember(Impl.idm_cols(vals, rest), Spec.IdmCand{Impl.idm_value(vals, t), t}), Spec.ids_member(rest, t), idp_cmem_cols(vals, rest, t)) : {Bool.or(Nat.is_eq(y, t), _) == Spec.ids_member(y <> rest, t) : Bool}
      {==}

def idp_cnd_cols(+vals: Impl.IdmVals, L: List<&2, Nat>) -> {Spec.ids_cnodup(Impl.idm_cols(vals, L)) == Spec.ids_nodup(L) : Bool}:
  match L:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Spec.ids_cmember(Impl.idm_cols(vals, rest), Spec.IdmCand{Impl.idm_value(vals, y), y}), Spec.ids_member(rest, y), idp_cmem_cols(vals, rest, y)) : {Bool.and(Bool.not(_), Spec.ids_cnodup(Impl.idm_cols(vals, rest))) == Spec.ids_nodup(y <> rest) : Bool}
      %Equal.sym(Bool, Spec.ids_cnodup(Impl.idm_cols(vals, rest)), Spec.ids_nodup(rest), idp_cnd_cols(vals, rest)) : {Bool.and(Bool.not(Spec.ids_member(rest, y)), _) == Spec.ids_nodup(y <> rest) : Bool}
      {==}

def idp_sub_cols(+vals: Impl.IdmVals, A: List<&2, Nat>, +B: List<&2, Nat>)
  -> {Spec.ids_subset(Impl.idm_cols(vals, A), Impl.idm_cols(vals, B)) == idp_nsub(A, B) : Bool}:
  match A:
    case Nil{}:
      {==}
    case +a <> +rest:
      %Equal.sym(Bool, Spec.ids_cmember(Impl.idm_cols(vals, B), Spec.IdmCand{Impl.idm_value(vals, a), a}), Spec.ids_member(B, a), idp_cmem_cols(vals, B, a)) : {Bool.and(_, Spec.ids_subset(Impl.idm_cols(vals, rest), Impl.idm_cols(vals, B))) == idp_nsub(a <> rest, B) : Bool}
      %Equal.sym(Bool, Spec.ids_subset(Impl.idm_cols(vals, rest), Impl.idm_cols(vals, B)), idp_nsub(rest, B), idp_sub_cols(vals, rest, B)) : {Bool.and(Spec.ids_member(B, a), _) == idp_nsub(a <> rest, B) : Bool}
      {==}

# -- membership in the id map and in rows --

def idp_mem_count_b(E: Bool, +c: Nat, M: Bool, ih: {M == Nat.is_lt(0n, c) : Bool})
  -> {Bool.or(E, M) == Nat.is_lt(0n, Nat.add(Spec.ids_bit(E), c)) : Bool}:
  match E:
    case True{}:
      {==}
    case False{}:
      ih

def idp_mem_count(xs: List<&2, Nat>, +t: Nat) -> {Spec.ids_member(xs, t) == Nat.is_lt(0n, Spec.ids_count(xs, t)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      idp_mem_count_b(Nat.is_eq(y, t), Spec.ids_count(rest, t), Spec.ids_member(rest, t), idp_mem_count(rest, t))

def idp_lt_bit(b: Bool) -> {Nat.is_lt(0n, Spec.ids_bit(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_mem_idmap(+kept: List<&2, Nat>, +nb: Nat, +t: Nat)
  -> {Spec.ids_member(Impl.idm_id_map(kept, nb), t) == Nat.is_lt(t, Nat.mul(nb, 128n)) : Bool}:
  %Equal.sym(Bool, Spec.ids_member(Impl.idm_id_map(kept, nb), t), Nat.is_lt(0n, Spec.ids_count(Impl.idm_id_map(kept, nb), t)), idp_mem_count(Impl.idm_id_map(kept, nb), t)) : {_ == Nat.is_lt(t, Nat.mul(nb, 128n)) : Bool}
  %Equal.sym(Nat, Spec.ids_count(Impl.idm_id_map(kept, nb), t), Spec.ids_bit(Nat.is_lt(t, Nat.mul(nb, 128n))), Laws.idmap_bijection(kept, nb, t)) : {Nat.is_lt(0n, _) == Nat.is_lt(t, Nat.mul(nb, 128n)) : Bool}
  idp_lt_bit(Nat.is_lt(t, Nat.mul(nb, 128n)))

# Rows below V are inside the id map.
def idp_row_in(n: Nat, +x: Nat, +kept: List<&2, Nat>, +nb: Nat, h: {Nat.is_le(Nat.add(n, x), Nat.mul(nb, 128n)) == True{} : Bool})
  -> {idp_nsub(Impl.idm_row(n, x), Impl.idm_id_map(kept, nb)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      +hh = h
      MP.ar_and_intro(Spec.ids_member(Impl.idm_id_map(kept, nb), x), idp_nsub(Impl.idm_row(l1, 1n+x), Impl.idm_id_map(kept, nb)),
        %Equal.sym(Bool, Spec.ids_member(Impl.idm_id_map(kept, nb), x), Nat.is_lt(x, Nat.mul(nb, 128n)), idp_mem_idmap(kept, nb, x)) : {_ == True{} : Bool}
        MP.ar_lt_le_trans(x, 1n+Nat.add(l1, x), Nat.mul(nb, 128n),
          %Equal.sym(Bool, Nat.is_lt(x, 1n+Nat.add(l1, x)), Nat.is_le(1n+x, 1n+Nat.add(l1, x)), MP.ar_lt_succ_le(x, 1n+Nat.add(l1, x))) : {_ == True{} : Bool}
          MP.ar_le_add_l(l1, x), hh),
        idp_row_in(l1, 1n+x, kept, nb, %Equal.sym(Nat, Nat.add(l1, 1n+x), 1n+Nat.add(l1, x), MP.ar_add_succ_r(l1, x)) : {Nat.is_le(_, Nat.mul(nb, 128n)) == True{} : Bool}; hh))

def idp_row_has.step(E: Bool, +x: Nat, +y: Nat, +l: Nat, e: {Nat.is_eq(x, y) == E : Bool},
    h1: {Nat.is_le(x, y) == True{} : Bool},
    ih: {Nat.is_le(1n+x, y) == True{} : Bool} -> {Spec.ids_member(Impl.idm_row(l, 1n+x), y) == True{} : Bool})
  -> {Bool.or(E, Spec.ids_member(Impl.idm_row(l, 1n+x), y)) == True{} : Bool}:
  match E:
    case True{}:
      {==}
    case False{}:
      ih(idp_or_true_r(Nat.is_eq(x, y), Nat.is_le(1n+x, y), e,
        Equal.trans(Bool, Bool.or(Nat.is_eq(x, y), Nat.is_le(1n+x, y)), Nat.is_le(x, y), True{},
          Equal.sym(Bool, Nat.is_le(x, y), Bool.or(Nat.is_eq(x, y), Nat.is_le(1n+x, y)), MP.p8_le_split(x, y)), h1)))

# x <= y < x + n: y is in the row [x, x + n).
def idp_row_has(n: Nat, +x: Nat, +y: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, Nat.add(n, x)) == True{} : Bool})
  -> {Spec.ids_member(Impl.idm_row(n, x), y) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Spec.ids_member(Nil{}, y) == True{} : Bool}, MP.ar_false_true(
        Equal.trans(Bool, False{}, Bool.and(Nat.is_le(x, y), Nat.is_lt(y, x)), True{},
          Equal.sym(Bool, Bool.and(Nat.is_le(x, y), Nat.is_lt(y, x)), False{}, idp_le_lt(x, y)),
          MP.ar_and_intro(Nat.is_le(x, y), Nat.is_lt(y, x), h1, h2))))
    case 1n+l:
      +l1 = l
      +hh2 = h2
      idp_row_has.step(Nat.is_eq(x, y), x, y, l1, {==}, h1,
        g => idp_row_has(l1, 1n+x, y, g, %Equal.sym(Nat, Nat.add(l1, 1n+x), 1n+Nat.add(l1, x), MP.ar_add_succ_r(l1, x)) : {Nat.is_lt(y, _) == True{} : Bool}; hh2))

def idp_nsub_row(L: List<&2, Nat>, +V: Nat, al: {Spec.ids_all_lt(L, V) == True{} : Bool}) -> {idp_nsub(L, Impl.idm_row(V, 0n)) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case +y <> +rest:
      +a2 = al
      MP.ar_and_intro(Spec.ids_member(Impl.idm_row(V, 0n), y), idp_nsub(rest, Impl.idm_row(V, 0n)),
        idp_row_has(V, 0n, y, MP.ar_h_le_zero(y),
          %Equal.sym(Nat, Nat.add(V, 0n), V, MP.ar_add_zero_r(V)) : {Nat.is_lt(y, _) == True{} : Bool}
          MP.ar_and_l(Nat.is_lt(y, V), Spec.ids_all_lt(rest, V), a2)),
        idp_nsub_row(rest, V, MP.ar_and_r(Nat.is_lt(y, V), Spec.ids_all_lt(rest, V), a2)))

def idp_lt_rcons(p: Bool, +x: Nat, +rest: List<&2, Nat>, +B: Nat, h: {Nat.is_lt(x, B) == True{} : Bool},
    g: {Spec.ids_all_lt(rest, B) == True{} : Bool}) -> {Spec.ids_all_lt(Spec.ids_range.cons(p, x, rest), B) == True{} : Bool}:
  match p:
    case True{}:
      MP.ar_and_intro(Nat.is_lt(x, B), Spec.ids_all_lt(rest, B), h, g)
    case False{}:
      g

def idp_range_lt(len: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat, +B: Nat, h: {Nat.is_le(Nat.add(len, lo), B) == True{} : Bool})
  -> {Spec.ids_all_lt(Spec.ids_range(len, want, kept, lo), B) == True{} : Bool}:
  match len:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      +hh = h
      idp_lt_rcons(Spec.ids_pick(want, Spec.ids_member(kept, Nat.div(lo, 128n))), lo, Spec.ids_range(l1, want, kept, 1n+lo), B,
        MP.ar_lt_le_trans(lo, 1n+Nat.add(l1, lo), B,
          %Equal.sym(Bool, Nat.is_lt(lo, 1n+Nat.add(l1, lo)), Nat.is_le(1n+lo, 1n+Nat.add(l1, lo)), MP.ar_lt_succ_le(lo, 1n+Nat.add(l1, lo))) : {_ == True{} : Bool}
          MP.ar_le_add_l(l1, lo), hh),
        idp_range_lt(l1, want, kept, 1n+lo, B, %Equal.sym(Nat, Nat.add(l1, 1n+lo), 1n+Nat.add(l1, lo), MP.ar_add_succ_r(l1, lo)) : {Nat.is_le(_, B) == True{} : Bool}; hh))

def idp_lt_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +B: Nat, a: {Spec.ids_all_lt(xs, B) == True{} : Bool}, b: {Spec.ids_all_lt(ys, B) == True{} : Bool})
  -> {Spec.ids_all_lt(List.append(&2, Nat, xs, ys), B) == True{} : Bool}:
  match xs:
    case Nil{}:
      b
    case +x <> +rest:
      +aa = a
      MP.ar_and_intro(Nat.is_lt(x, B), Spec.ids_all_lt(List.append(&2, Nat, rest, ys), B), MP.ar_and_l(Nat.is_lt(x, B), Spec.ids_all_lt(rest, B), aa),
        idp_lt_app(rest, ys, B, MP.ar_and_r(Nat.is_lt(x, B), Spec.ids_all_lt(rest, B), aa), b))

def idp_V0(+V: Nat) -> {Nat.is_le(Nat.add(V, 0n), V) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(V, 0n), V, MP.ar_add_zero_r(V)) : {Nat.is_le(_, V) == True{} : Bool}
  MP.ar_le_refl(V)

def idp_idmap_lt(+kept: List<&2, Nat>, +nb: Nat) -> {Spec.ids_all_lt(Impl.idm_id_map(kept, nb), Nat.mul(nb, 128n)) == True{} : Bool}:
  +V = Nat.mul(nb, 128n)
  %Equal.sym(List<&2, Nat>, Impl.idm_id_map(kept, nb), Spec.ids_id_map(kept, nb), Laws.idmap_equals_spec(kept, nb)) : {Spec.ids_all_lt(_, V) == True{} : Bool}
  idp_lt_app(Spec.ids_range(V, True{}, kept, 0n), Spec.ids_range(V, False{}, kept, 0n), V,
    idp_range_lt(V, True{}, kept, 0n, V, idp_V0(V)), idp_range_lt(V, False{}, kept, 0n, V, idp_V0(V)))

# -- no duplicates --

def idp_gt_notmem(xs: List<&2, Nat>, +y: Nat, g: {Spec.ids_all_gt(xs, y) == True{} : Bool}) -> {Spec.ids_member(xs, y) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +z <> +rest:
      +gg = g
      %Equal.sym(Bool, Nat.is_eq(z, y), False{}, Equal.trans(Bool, Nat.is_eq(z, y), Nat.is_eq(y, z), False{}, idp_eq_sym(z, y),
        idp_lt_ne(y, z, MP.ar_and_l(Nat.is_lt(y, z), Spec.ids_all_gt(rest, y), gg)))) : {Bool.or(_, Spec.ids_member(rest, y)) == False{} : Bool}
      idp_gt_notmem(rest, y, MP.ar_and_r(Nat.is_lt(y, z), Spec.ids_all_gt(rest, y), gg))

def idp_inc_nd(xs: List<&2, Nat>, inc: {Spec.ids_increasing(xs) == True{} : Bool}) -> {Spec.ids_nodup(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      +i2 = inc
      %Equal.sym(Bool, Spec.ids_member(rest, y), False{}, idp_gt_notmem(rest, y, MP.ar_and_l(Spec.ids_all_gt(rest, y), Spec.ids_increasing(rest), i2))) : {Bool.and(Bool.not(_), Spec.ids_nodup(rest)) == True{} : Bool}
      idp_inc_nd(rest, MP.ar_and_r(Spec.ids_all_gt(rest, y), Spec.ids_increasing(rest), i2))

def idp_row_gt(n: Nat, +x: Nat, +y: Nat, +h: {Nat.is_lt(y, x) == True{} : Bool}) -> {Spec.ids_all_gt(Impl.idm_row(n, x), y) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+l:
      MP.ar_and_intro(Nat.is_lt(y, x), Spec.ids_all_gt(Impl.idm_row(l, 1n+x), y), h,
        idp_row_gt(l, 1n+x, y, MP.ar_lt_trans(y, x, 1n+x, h, idp_lt_succ(x))))

def idp_row_inc(n: Nat, +x: Nat) -> {Spec.ids_increasing(Impl.idm_row(n, x)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      MP.ar_and_intro(Spec.ids_all_gt(Impl.idm_row(l1, 1n+x), x), Spec.ids_increasing(Impl.idm_row(l1, 1n+x)),
        idp_row_gt(l1, 1n+x, x, idp_lt_succ(x)), idp_row_inc(l1, 1n+x))

def idp_disj(A: List<&2, Nat>, +B: List<&2, Nat>) -> Bool:
  match A:
    case Nil{}:
      True{}
    case a <> rest:
      Bool.and(Bool.not(Spec.ids_member(B, a)), idp_disj(rest, B))

def idp_or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_mem_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +a: Nat)
  -> {Spec.ids_member(List.append(&2, Nat, xs, ys), a) == Bool.or(Spec.ids_member(xs, a), Spec.ids_member(ys, a)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Spec.ids_member(List.append(&2, Nat, rest, ys), a), Bool.or(Spec.ids_member(rest, a), Spec.ids_member(ys, a)), idp_mem_app(rest, ys, a)) : {Bool.or(Nat.is_eq(x, a), _) == Bool.or(Bool.or(Nat.is_eq(x, a), Spec.ids_member(rest, a)), Spec.ids_member(ys, a)) : Bool}
      idp_or_assoc(Nat.is_eq(x, a), Spec.ids_member(rest, a), Spec.ids_member(ys, a))

def idp_nd_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, nx: {Spec.ids_nodup(xs) == True{} : Bool}, +ny: {Spec.ids_nodup(ys) == True{} : Bool},
    dj: {idp_disj(xs, ys) == True{} : Bool}) -> {Spec.ids_nodup(List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ny
    case +x <> +rest:
      +n2 = nx
      +d2 = dj
      %Equal.sym(Bool, Spec.ids_member(List.append(&2, Nat, rest, ys), x), Bool.or(Spec.ids_member(rest, x), Spec.ids_member(ys, x)), idp_mem_app(rest, ys, x)) : {Bool.and(Bool.not(_), Spec.ids_nodup(List.append(&2, Nat, rest, ys))) == True{} : Bool}
      %Equal.sym(Bool, Spec.ids_member(rest, x), False{}, idp_not_true(Spec.ids_member(rest, x), MP.ar_and_l(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest), n2))) : {Bool.and(Bool.not(Bool.or(_, Spec.ids_member(ys, x))), Spec.ids_nodup(List.append(&2, Nat, rest, ys))) == True{} : Bool}
      %Equal.sym(Bool, Spec.ids_member(ys, x), False{}, idp_not_true(Spec.ids_member(ys, x), MP.ar_and_l(Bool.not(Spec.ids_member(ys, x)), idp_disj(rest, ys), d2))) : {Bool.and(Bool.not(Bool.or(False{}, _)), Spec.ids_nodup(List.append(&2, Nat, rest, ys))) == True{} : Bool}
      idp_nd_app(rest, ys, MP.ar_and_r(Bool.not(Spec.ids_member(rest, x)), Spec.ids_nodup(rest), n2), ny,
        MP.ar_and_r(Bool.not(Spec.ids_member(ys, x)), idp_disj(rest, ys), d2))

# An id of a kept block is not among the other ids.
def idp_memF(+len: Nat, +kept: List<&2, Nat>, +lo: Nat, +a: Nat, ma: {Spec.ids_member(kept, Nat.div(a, 128n)) == True{} : Bool})
  -> {Spec.ids_member(Spec.ids_range(len, False{}, kept, lo), a) == False{} : Bool}:
  +R = Bool.and(Nat.is_le(lo, a), Nat.is_lt(a, Nat.add(len, lo)))
  %Equal.sym(Bool, Spec.ids_member(Spec.ids_range(len, False{}, kept, lo), a), Nat.is_lt(0n, Spec.ids_count(Spec.ids_range(len, False{}, kept, lo), a)), idp_mem_count(Spec.ids_range(len, False{}, kept, lo), a)) : {_ == False{} : Bool}
  %Equal.sym(Nat, Spec.ids_count(Spec.ids_range(len, False{}, kept, lo), a), Spec.ids_bit(Bool.and(R, Bool.not(Spec.ids_member(kept, Nat.div(a, 128n))))), idp_rc(len, False{}, kept, lo, a)) : {Nat.is_lt(0n, _) == False{} : Bool}
  %Equal.sym(Bool, Spec.ids_member(kept, Nat.div(a, 128n)), True{}, ma) : {Nat.is_lt(0n, Spec.ids_bit(Bool.and(R, Bool.not(_)))) == False{} : Bool}
  %MP.ar_h_and_false_r(R) : {Nat.is_lt(0n, Spec.ids_bit(_)) == False{} : Bool}
  {==}

def idp_disj_rc(p: Bool, +x: Nat, +rest: List<&2, Nat>, +B: List<&2, Nat>,
    nb: {p == True{} : Bool} -> {Spec.ids_member(B, x) == False{} : Bool}, d: {idp_disj(rest, B) == True{} : Bool})
  -> {idp_disj(Spec.ids_range.cons(p, x, rest), B) == True{} : Bool}:
  match p:
    case True{}:
      MP.ar_and_intro(Bool.not(Spec.ids_member(B, x)), idp_disj(rest, B),
        %Equal.sym(Bool, Spec.ids_member(B, x), False{}, nb({==})) : {Bool.not(_) == True{} : Bool}
        {==}, d)
    case False{}:
      d

# The kept ids and the other ids share no id.
def idp_disj_range(len: Nat, +kept: List<&2, Nat>, +lo: Nat, +V: Nat, +lo2: Nat)
  -> {idp_disj(Spec.ids_range(len, True{}, kept, lo), Spec.ids_range(V, False{}, kept, lo2)) == True{} : Bool}:
  match len:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      idp_disj_rc(Spec.ids_member(kept, Nat.div(lo, 128n)), lo, Spec.ids_range(l1, True{}, kept, 1n+lo), Spec.ids_range(V, False{}, kept, lo2),
        e => idp_memF(V, kept, lo2, lo, e), idp_disj_range(l1, kept, 1n+lo, V, lo2))

def idp_nd_idmap(+kept: List<&2, Nat>, +nb: Nat) -> {Spec.ids_nodup(Impl.idm_id_map(kept, nb)) == True{} : Bool}:
  +V = Nat.mul(nb, 128n)
  %Equal.sym(List<&2, Nat>, Impl.idm_id_map(kept, nb), Spec.ids_id_map(kept, nb), Laws.idmap_equals_spec(kept, nb)) : {Spec.ids_nodup(_) == True{} : Bool}
  idp_nd_app(Spec.ids_range(V, True{}, kept, 0n), Spec.ids_range(V, False{}, kept, 0n),
    idp_inc_nd(Spec.ids_range(V, True{}, kept, 0n), idp_range_inc(V, True{}, kept, 0n)),
    idp_inc_nd(Spec.ids_range(V, False{}, kept, 0n), idp_range_inc(V, False{}, kept, 0n)),
    idp_disj_range(V, kept, 0n, V, 0n))

def Laws.topk_full_call(k, vals, kept, nb):
  +V = Nat.mul(nb, 128n)
  +M = Impl.idm_id_map(kept, nb)
  +R0 = Impl.idm_row(V, 0n)
  %Equal.sym(Bool, Nat.is_eq(V, V), True{}, MP.ar_eq_refl(V)) : {Impl.idm_topk(k, Impl.idm_cols(vals, Impl.idm_slice(_, M, V))) == Impl.idm_topk(k, Impl.idm_cols(vals, R0)) : List<&2, Spec.IdmCand>}
  Laws.topk_order_free(k, Impl.idm_cols(vals, M), Impl.idm_cols(vals, R0),
    Equal.trans(Bool, Spec.ids_cnodup(Impl.idm_cols(vals, M)), Spec.ids_nodup(M), True{}, idp_cnd_cols(vals, M), idp_nd_idmap(kept, nb)),
    Equal.trans(Bool, Spec.ids_cnodup(Impl.idm_cols(vals, R0)), Spec.ids_nodup(R0), True{}, idp_cnd_cols(vals, R0), idp_inc_nd(R0, idp_row_inc(V, 0n))),
    MP.ar_and_intro(Spec.ids_subset(Impl.idm_cols(vals, M), Impl.idm_cols(vals, R0)), Spec.ids_subset(Impl.idm_cols(vals, R0), Impl.idm_cols(vals, M)),
      Equal.trans(Bool, Spec.ids_subset(Impl.idm_cols(vals, M), Impl.idm_cols(vals, R0)), idp_nsub(M, R0), True{}, idp_sub_cols(vals, M, R0),
        idp_nsub_row(M, V, idp_idmap_lt(kept, nb))),
      Equal.trans(Bool, Spec.ids_subset(Impl.idm_cols(vals, R0), Impl.idm_cols(vals, M)), idp_nsub(R0, M), True{}, idp_sub_cols(vals, R0, M),
        idp_row_in(V, 0n, kept, nb, idp_V0(V)))))

# -- the pruned call: restricting the ranking to kept ids --

def idp_kept_of(+c: Spec.IdmCand, +kept: List<&2, Nat>) -> Bool:
  Spec.ids_member(kept, Nat.div(Spec.ids_t(c), 128n))

def idp_ifins(P: Bool, +c: Spec.IdmCand, L: List<&2, Spec.IdmCand>) -> List<&2, Spec.IdmCand>:
  match P:
    case True{}:
      Spec.ids_insert(L, c)
    case False{}:
      L

def idp_rank_kkc(P: Bool, +c: Spec.IdmCand, +L: List<&2, Spec.IdmCand>)
  -> {Spec.ids_rank(Spec.ids_keep_kept.cons(P, c, L)) == idp_ifins(P, c, Spec.ids_rank(L)) : List<&2, Spec.IdmCand>}:
  match P:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_ins_front(L: List<&2, Spec.IdmCand>, +c: Spec.IdmCand, a: {idp_aft(L, c) == True{} : Bool})
  -> {Spec.ids_insert(L, c) == c <> L : List<&2, Spec.IdmCand>}:
  match L:
    case Nil{}:
      {==}
    case +y <> +rest:
      %Equal.sym(Bool, Spec.ids_before(c, y), True{}, MP.ar_and_l(Spec.ids_before(c, y), idp_aft(rest, c), a)) : {Spec.ids_insert.sel(_, c, y, rest, Spec.ids_insert(rest, c)) == c <> y <> rest : List<&2, Spec.IdmCand>}
      {==}

def idp_aft_kkc(p: Bool, +c: Spec.IdmCand, +y: Spec.IdmCand, +X: List<&2, Spec.IdmCand>, b: {Spec.ids_before(c, y) == True{} : Bool},
    i: {idp_aft(X, c) == True{} : Bool}) -> {idp_aft(Spec.ids_keep_kept.cons(p, y, X), c) == True{} : Bool}:
  match p:
    case True{}:
      MP.ar_and_intro(Spec.ids_before(c, y), idp_aft(X, c), b, i)
    case False{}:
      i

def idp_aft_kk(L: List<&2, Spec.IdmCand>, +c: Spec.IdmCand, +kept: List<&2, Nat>, a: {idp_aft(L, c) == True{} : Bool})
  -> {idp_aft(Spec.ids_keep_kept(L, kept), c) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case +y <> +rest:
      +aa = a
      idp_aft_kkc(idp_kept_of(y, kept), c, y, Spec.ids_keep_kept(rest, kept), MP.ar_and_l(Spec.ids_before(c, y), idp_aft(rest, c), aa),
        idp_aft_kk(rest, c, kept, MP.ar_and_r(Spec.ids_before(c, y), idp_aft(rest, c), aa)))

def idp_kk1(P: Bool, +c: Spec.IdmCand) -> {Spec.ids_keep_kept.cons(P, c, Nil{}) == idp_ifins(P, c, Nil{}) : List<&2, Spec.IdmCand>}:
  match P:
    case True{}:
      {==}
    case False{}:
      {==}

def idp_kk_front(P: Bool, +c: Spec.IdmCand, +X: List<&2, Spec.IdmCand>, a: {idp_aft(X, c) == True{} : Bool})
  -> {Spec.ids_keep_kept.cons(P, c, X) == idp_ifins(P, c, X) : List<&2, Spec.IdmCand>}:
  match P:
    case True{}:
      Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_insert(X, c), c <> X, idp_ins_front(X, c, a))
    case False{}:
      {==}

def idp_kk_back(Pc: Bool, Pr: Bool, +c: Spec.IdmCand, +r: Spec.IdmCand, +Y: List<&2, Spec.IdmCand>, e: {Spec.ids_before(c, r) == False{} : Bool})
  -> {Spec.ids_keep_kept.cons(Pr, r, idp_ifins(Pc, c, Y)) == idp_ifins(Pc, c, Spec.ids_keep_kept.cons(Pr, r, Y)) : List<&2, Spec.IdmCand>}:
  match Pc:
    case False{}:
      {==}
    case True{}:
      match Pr:
        case True{}:
          %Equal.sym(Bool, Spec.ids_before(c, r), False{}, e) : {r <> Spec.ids_insert(Y, c) == Spec.ids_insert.sel(_, c, r, Y, Spec.ids_insert(Y, c)) : List<&2, Spec.IdmCand>}
          {==}
        case False{}:
          {==}

def idp_kk_sel(g: Bool, +c: Spec.IdmCand, +r: Spec.IdmCand, +R: List<&2, Spec.IdmCand>, +kept: List<&2, Nat>,
    e: {Spec.ids_before(c, r) == g : Bool}, ss: {idp_ss(r <> R) == True{} : Bool},
    ih: {Spec.ids_keep_kept(Spec.ids_insert(R, c), kept) == idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(R, kept)) : List<&2, Spec.IdmCand>})
  -> {Spec.ids_keep_kept(Spec.ids_insert.sel(g, c, r, R, Spec.ids_insert(R, c)), kept) ==
      idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(r <> R, kept)) : List<&2, Spec.IdmCand>}:
  match g:
    case True{}:
      +ee = e
      idp_kk_front(idp_kept_of(c, kept), c, Spec.ids_keep_kept(r <> R, kept),
        idp_aft_kk(r <> R, c, kept, MP.ar_and_intro(Spec.ids_before(c, r), idp_aft(R, c), ee,
          idp_aft_mono(R, c, r, ee, MP.ar_and_l(idp_aft(R, r), idp_ss(R), ss)))))
    case False{}:
      %Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_keep_kept(Spec.ids_insert(R, c), kept), idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(R, kept)), ih) : {Spec.ids_keep_kept.cons(idp_kept_of(r, kept), r, _) == idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(r <> R, kept)) : List<&2, Spec.IdmCand>}
      idp_kk_back(idp_kept_of(c, kept), idp_kept_of(r, kept), c, r, Spec.ids_keep_kept(R, kept), e)

# Keeping the kept entries of a strictly sorted list after inserting c = inserting c (if kept) into its kept entries.
def idp_kk_ins(R: List<&2, Spec.IdmCand>, +c: Spec.IdmCand, +kept: List<&2, Nat>, ss: {idp_ss(R) == True{} : Bool})
  -> {Spec.ids_keep_kept(Spec.ids_insert(R, c), kept) == idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(R, kept)) : List<&2, Spec.IdmCand>}:
  match R:
    case Nil{}:
      idp_kk1(idp_kept_of(c, kept), c)
    case +r <> +rest:
      +s2 = ss
      idp_kk_sel(Spec.ids_before(c, r), c, r, rest, kept, {==}, s2, idp_kk_ins(rest, c, kept, MP.ar_and_r(idp_aft(rest, r), idp_ss(rest), s2)))

# Restricting the ranking to kept ids = ranking the kept columns.
def idp_kk_rank(C: List<&2, Spec.IdmCand>, +kept: List<&2, Nat>, nd: {Spec.ids_cnodup(C) == True{} : Bool})
  -> {Spec.ids_keep_kept(Spec.ids_rank(C), kept) == Spec.ids_rank(Spec.ids_keep_kept(C, kept)) : List<&2, Spec.IdmCand>}:
  match C:
    case Nil{}:
      {==}
    case +c <> +rest:
      +n2 = MP.ar_and_r(Bool.not(Spec.ids_cmember(rest, c)), Spec.ids_cnodup(rest), nd)
      %Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_keep_kept(Spec.ids_insert(Spec.ids_rank(rest), c), kept), idp_ifins(idp_kept_of(c, kept), c, Spec.ids_keep_kept(Spec.ids_rank(rest), kept)), idp_kk_ins(Spec.ids_rank(rest), c, kept, idp_ss_rank(rest, n2))) : {_ == Spec.ids_rank(Spec.ids_keep_kept(c <> rest, kept)) : List<&2, Spec.IdmCand>}
      %Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_keep_kept(Spec.ids_rank(rest), kept), Spec.ids_rank(Spec.ids_keep_kept(rest, kept)), idp_kk_rank(rest, kept, n2)) : {idp_ifins(idp_kept_of(c, kept), c, _) == Spec.ids_rank(Spec.ids_keep_kept(c <> rest, kept)) : List<&2, Spec.IdmCand>}
      Equal.sym(List<&2, Spec.IdmCand>, Spec.ids_rank(Spec.ids_keep_kept.cons(idp_kept_of(c, kept), c, Spec.ids_keep_kept(rest, kept))),
        idp_ifins(idp_kept_of(c, kept), c, Spec.ids_rank(Spec.ids_keep_kept(rest, kept))),
        idp_rank_kkc(idp_kept_of(c, kept), c, Spec.ids_keep_kept(rest, kept)))

def idp_kkc(p: Bool, +vals: Impl.IdmVals, +x: Nat, A: List<&2, Spec.IdmCand>, B: List<&2, Nat>,
    ih: {A == Impl.idm_cols(vals, B) : List<&2, Spec.IdmCand>})
  -> {Spec.ids_keep_kept.cons(p, Spec.IdmCand{Impl.idm_value(vals, x), x}, A) == Impl.idm_cols(vals, Spec.ids_range.cons(p, x, B)) : List<&2, Spec.IdmCand>}:
  match p:
    case True{}:
      Equal.cong(List<&2, Spec.IdmCand>, List<&2, Spec.IdmCand>, l => Spec.IdmCand{Impl.idm_value(vals, x), x} <> l, A, Impl.idm_cols(vals, B), ih)
    case False{}:
      ih

# The kept columns of the identity head are the columns of the kept ids.
def idp_cols_kk(n: Nat, +vals: Impl.IdmVals, +kept: List<&2, Nat>, +x: Nat)
  -> {Spec.ids_keep_kept(Impl.idm_cols(vals, Impl.idm_row(n, x)), kept) == Impl.idm_cols(vals, Spec.ids_range(n, True{}, kept, x)) : List<&2, Spec.IdmCand>}:
  match n:
    case 0n:
      {==}
    case 1n+l:
      +l1 = l
      idp_kkc(Spec.ids_member(kept, Nat.div(x, 128n)), vals, x, Spec.ids_keep_kept(Impl.idm_cols(vals, Impl.idm_row(l1, 1n+x)), kept),
        Spec.ids_range(l1, True{}, kept, 1n+x), idp_cols_kk(l1, vals, kept, 1n+x))

def idp_take_len(-A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      Equal.cong(List<&2, A>, List<&2, A>, l => y <> l, List.take(&2, A, rest, List.length(&2, A, rest)), rest, idp_take_len(A, rest))

def idp_slice_b(g: Bool, +kept: List<&2, Nat>, +nb: Nat, e: {Nat.is_eq(Impl.idm_keep_cols(kept), Nat.mul(nb, 128n)) == g : Bool},
    ok: {Spec.ids_blocks_in(kept, nb) == True{} : Bool})
  -> {Impl.idm_slice(g, Impl.idm_id_map(kept, nb), Impl.idm_keep_cols(kept)) == Spec.ids_kept_ids(kept, nb) : List<&2, Nat>}:
  match g:
    case False{}:
      Laws.idmap_prefix_kept_ids(kept, nb, ok)
    case True{}:
      +M = Impl.idm_id_map(kept, nb)
      +KC = Impl.idm_keep_cols(kept)
      Equal.trans(List<&2, Nat>, M, List.take(&2, Nat, M, KC), Spec.ids_kept_ids(kept, nb),
        Equal.trans(List<&2, Nat>, M, List.take(&2, Nat, M, List.length(&2, Nat, M)), List.take(&2, Nat, M, KC),
          Equal.sym(List<&2, Nat>, List.take(&2, Nat, M, List.length(&2, Nat, M)), M, idp_take_len(Nat, M)),
          %Equal.sym(Nat, List.length(&2, Nat, M), Nat.mul(nb, 128n), Laws.idmap_length(kept, nb)) : {List.take(&2, Nat, M, _) == List.take(&2, Nat, M, KC) : List<&2, Nat>}
          %MP.ar_eq_true(KC, Nat.mul(nb, 128n), e) : {List.take(&2, Nat, M, _) == List.take(&2, Nat, M, KC) : List<&2, Nat>}
          {==}),
        Laws.idmap_prefix_kept_ids(kept, nb, ok))

def Laws.topk_pruned_call(k, vals, kept, nb, ok):
  +V = Nat.mul(nb, 128n)
  +KC = Impl.idm_keep_cols(kept)
  +KI = Spec.ids_kept_ids(kept, nb)
  +R0 = Impl.idm_row(V, 0n)
  +o2 = ok
  %Equal.sym(List<&2, Nat>, Impl.idm_slice(Nat.is_eq(KC, V), Impl.idm_id_map(kept, nb), KC), KI, idp_slice_b(Nat.is_eq(KC, V), kept, nb, {==}, o2)) : {Impl.idm_topk(k, Impl.idm_cols(vals, _)) == List.take(&2, Spec.IdmCand, Spec.ids_keep_kept(Spec.ids_rank(Impl.idm_cols(vals, R0)), kept), k) : List<&2, Spec.IdmCand>}
  %Equal.sym(List<&2, Spec.IdmCand>, Impl.idm_topk(k, Impl.idm_cols(vals, KI)), Spec.ids_topk(k, Impl.idm_cols(vals, KI)), idp_topk_rank(k, Impl.idm_cols(vals, KI))) : {_ == List.take(&2, Spec.IdmCand, Spec.ids_keep_kept(Spec.ids_rank(Impl.idm_cols(vals, R0)), kept), k) : List<&2, Spec.IdmCand>}
  %idp_cols_kk(V, vals, kept, 0n) : {List.take(&2, Spec.IdmCand, Spec.ids_rank(_), k) == List.take(&2, Spec.IdmCand, Spec.ids_keep_kept(Spec.ids_rank(Impl.idm_cols(vals, R0)), kept), k) : List<&2, Spec.IdmCand>}
  %idp_kk_rank(Impl.idm_cols(vals, R0), kept, Equal.trans(Bool, Spec.ids_cnodup(Impl.idm_cols(vals, R0)), Spec.ids_nodup(R0), True{}, idp_cnd_cols(vals, R0), idp_inc_nd(R0, idp_row_inc(V, 0n)))) : {List.take(&2, Spec.IdmCand, _, k) == List.take(&2, Spec.IdmCand, Spec.ids_keep_kept(Spec.ids_rank(Impl.idm_cols(vals, R0)), kept), k) : List<&2, Spec.IdmCand>}
  {==}
