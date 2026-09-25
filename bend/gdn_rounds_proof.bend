# Proofs of the multi-round GDN laws (bend/gdn_rounds_laws.bend). Structural evidence only: no
# unsafe definitions, axioms, holes or answer tables. Each round step reuses the proven one-round
# laws of bend/gdn_replay_laws.bend (commit_prefix, commit_happens, position_advance, conv_window)
# and the list / fold lemmas of bend/gdn_replay_proof.bend.
import Base
import ./gdn_rounds.bend as Impl
import ./gdn_rounds_spec.bend as Spec
import ./gdn_rounds_laws.bend as Laws
import ./gdn_replay.bend as GR
import ./gdn_replay_spec.bend as GS
import ./gdn_replay_laws.bend as GRL
import ./gdn_replay_proof.bend as GP
import ./exl3_accept_spec.bend as Accept
import ./gemm_m16_partition_proof.bend as Ar

# ---------------------------------------------------------------- round facts from rounds_ok

def gq_r1(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Bool.and(Nat.is_eq(List.length(&2, Y, ys), 1n+w), Bool.and(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H),
       Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))))) == True{} : Bool}:
  Ar.ar_and_r(Nat.is_eq(List.length(&2, X, xs), 1n+w), Bool.and(Nat.is_eq(List.length(&2, Y, ys), 1n+w), Bool.and(Nat.is_le(1n, w),
    Bool.and(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))))), h)

def gq_r3(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Bool.and(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))) == True{} : Bool}:
  +r1 = gq_r1(~X, ~Y, H, w, xs, ys, c, h)
  +r2 = Ar.ar_and_r(Nat.is_eq(List.length(&2, Y, ys), 1n+w), Bool.and(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H),
    Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)))), r1)
  Ar.ar_and_r(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))), r2)

def gq_shx(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {List.length(&2, X, xs) == 1n+w : Nat}:
  Ar.ar_eq_true(List.length(&2, X, xs), 1n+w, Ar.ar_and_l(Nat.is_eq(List.length(&2, X, xs), 1n+w),
    Bool.and(Nat.is_eq(List.length(&2, Y, ys), 1n+w), Bool.and(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H),
      Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))))), h))

def gq_shy(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {List.length(&2, Y, ys) == 1n+w : Nat}:
  Ar.ar_eq_true(List.length(&2, Y, ys), 1n+w, Ar.ar_and_l(Nat.is_eq(List.length(&2, Y, ys), 1n+w),
    Bool.and(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)))),
    gq_r1(~X, ~Y, H, w, xs, ys, c, h)))

def gq_drafted(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Nat.is_le(1n, w) == True{} : Bool}:
  +r2 = Ar.ar_and_r(Nat.is_eq(List.length(&2, Y, ys), 1n+w), Bool.and(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H),
    Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)))), gq_r1(~X, ~Y, H, w, xs, ys, c, h))
  Ar.ar_and_l(Nat.is_le(1n, w), Bool.and(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w))), r2)

def gq_fits(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Nat.is_le(w, H) == True{} : Bool}:
  Ar.ar_and_l(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)), gq_r3(~X, ~Y, H, w, xs, ys, c, h))

def gq_progress(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Nat.is_le(1n, c) == True{} : Bool}:
  Ar.ar_and_l(Nat.is_le(1n, c), Nat.is_le(c, 1n+w),
    Ar.ar_and_r(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)), gq_r3(~X, ~Y, H, w, xs, ys, c, h)))

def gq_bounded(~X: Data, ~Y: Data, +H: Nat, +w: Nat, +xs: List<&2, X>, +ys: List<&2, Y>, +c: Nat,
    +h: {Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}) == True{} : Bool})
  -> {Nat.is_le(c, 1n+w) == True{} : Bool}:
  Ar.ar_and_r(Nat.is_le(1n, c), Nat.is_le(c, 1n+w),
    Ar.ar_and_r(Nat.is_le(w, H), Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 1n+w)), gq_r3(~X, ~Y, H, w, xs, ys, c, h)))

# ---------------------------------------------------------------- scan lemmas

def gq_take_outputs(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    xs: List<&2, X>, +s0: S, +pre: List<&2, X>, +n: Nat)
  -> {List.take(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, xs, s0, pre), n) ==
      GS.outputs(~S, ~X, ~O, ~step, ~out, List.take(&2, X, xs, n), s0, pre) : List<&2, O>}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> rest 0n:
      {==}
    case +x <> rest 1n+m:
      +upto = List.append(&2, X, pre, [x])
      Equal.cong(List<&2, O>, List<&2, O>, t => out(GS.fold(~S, ~X, ~step, upto, s0), x) <> t,
        List.take(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto), m),
        GS.outputs(~S, ~X, ~O, ~step, ~out, List.take(&2, X, rest, m), s0, upto),
        gq_take_outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto, m))

def gq_outputs_append(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    +a: List<&2, X>, +b: List<&2, X>, +s0: S, +pre: List<&2, X>)
  -> {GS.outputs(~S, ~X, ~O, ~step, ~out, List.append(&2, X, a, b), s0, pre) ==
      List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, a, s0, pre),
        GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, List.append(&2, X, pre, a))) : List<&2, O>}:
  match a:
    case Nil{}:
      %GP.append_nil(~X, pre) : {GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, _) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, List.append(&2, X, pre, Nil{})) : List<&2, O>}
      {==}
    case +x <> rest:
      +upto = List.append(&2, X, pre, [x])
      +hd = out(GS.fold(~S, ~X, ~step, upto, s0), x)
      %Equal.sym(List<&2, O>, GS.outputs(~S, ~X, ~O, ~step, ~out, List.append(&2, X, rest, b), s0, upto),
        List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto),
          GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, List.append(&2, X, upto, rest))),
        gq_outputs_append(~S, ~X, ~O, ~step, ~out, rest, b, s0, upto)) :
        {hd <> _ == hd <> List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto),
          GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, List.append(&2, X, pre, x <> rest))) : List<&2, O>}
      %Equal.sym(List<&2, X>, List.append(&2, X, upto, rest), List.append(&2, X, pre, x <> rest),
        GP.append_assoc(~X, pre, [x], rest)) :
        {hd <> List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto),
          GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, _)) ==
         hd <> List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, upto),
          GS.outputs(~S, ~X, ~O, ~step, ~out, b, s0, List.append(&2, X, pre, x <> rest))) : List<&2, O>}
      {==}

# ---------------------------------------------------------------- C1 inductions

def gq_committed(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {GR.committed(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)) == True{} : Bool}:
  match rounds o:
    case Nil{} _:
      hc
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({GR.committed(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r})) == True{} : Bool},
        Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      gq_committed(~S, ~X, ~Y, ~step, K, H, rest,
        GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}}),
        GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), okt)

def gq_row0(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +pre: List<&2, X>, +s0: S,
    +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +hr: {GR.row0_of(~S, ~Y, o) == GS.fold(~S, ~X, ~step, pre, s0) : S},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)) ==
      GS.fold(~S, ~X, ~step, List.append(&2, X, pre, Spec.stream_x(~X, ~Y, rounds)), s0) : S}:
  match rounds o:
    case Nil{} _:
      %Equal.sym(List<&2, X>, List.append(&2, X, pre, Nil{}), pre, GP.append_nil(~X, pre)) :
        {GR.row0_of(~S, ~Y, o) == GS.fold(~S, ~X, ~step, _, s0) : S}
      hr
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r})) ==
        GS.fold(~S, ~X, ~step, List.append(&2, X, pre, Spec.stream_x(~X, ~Y, Impl.Round{w, xs, ys, c} <> rest)), s0) : S},
        Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +o1 = GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}})
      +tx = List.take(&2, X, xs, c)
      +hr1 = Equal.trans(S, GR.row0_of(~S, ~Y, o1), GS.fold(~S, ~X, ~step, tx, r), GS.fold(~S, ~X, ~step, List.append(&2, X, pre, tx), s0),
        GRL.commit_prefix(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)),
        Equal.trans(S, GS.fold(~S, ~X, ~step, tx, r), GS.fold(~S, ~X, ~step, tx, GS.fold(~S, ~X, ~step, pre, s0)),
          GS.fold(~S, ~X, ~step, List.append(&2, X, pre, tx), s0),
          Equal.cong(S, S, t => GS.fold(~S, ~X, ~step, tx, t), r, GS.fold(~S, ~X, ~step, pre, s0), hr),
          Equal.sym(S, GS.fold(~S, ~X, ~step, List.append(&2, X, pre, tx), s0), GS.fold(~S, ~X, ~step, tx, GS.fold(~S, ~X, ~step, pre, s0)),
            GP.fold_append(~S, ~X, ~step, pre, tx, s0))))
      %GP.append_assoc(~X, pre, tx, Spec.stream_x(~X, ~Y, rest)) :
        {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rest, o1)) == GS.fold(~S, ~X, ~step, _, s0) : S}
      gq_row0(~S, ~X, ~Y, ~step, K, H, rest, o1, List.append(&2, X, pre, tx), s0,
        GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), hr1, okt)

def gq_emit(~S: Data, ~X: Data, ~Y: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +pre: List<&2, X>, +s0: S,
    +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +hr: {GR.row0_of(~S, ~Y, o) == GS.fold(~S, ~X, ~step, pre, s0) : S},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds, o) ==
      GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rounds), s0, pre) : List<&2, O>}:
  match rounds o:
    case Nil{} _:
      {==}
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r}) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, Impl.Round{w, xs, ys, c} <> rest), s0, pre) : List<&2, O>},
        Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +hrr = hr
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +o1 = GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}})
      +tx = List.take(&2, X, xs, c)
      +pre1 = List.append(&2, X, pre, tx)
      +RHS = GS.outputs(~S, ~X, ~O, ~step, ~out, List.append(&2, X, tx, Spec.stream_x(~X, ~Y, rest)), s0, pre)
      +hr1 = Equal.trans(S, GR.row0_of(~S, ~Y, o1), GS.fold(~S, ~X, ~step, tx, r), GS.fold(~S, ~X, ~step, pre1, s0),
        GRL.commit_prefix(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)),
        Equal.trans(S, GS.fold(~S, ~X, ~step, tx, r), GS.fold(~S, ~X, ~step, tx, GS.fold(~S, ~X, ~step, pre, s0)),
          GS.fold(~S, ~X, ~step, pre1, s0),
          Equal.cong(S, S, t => GS.fold(~S, ~X, ~step, tx, t), r, GS.fold(~S, ~X, ~step, pre, s0), hrr),
          Equal.sym(S, GS.fold(~S, ~X, ~step, pre1, s0), GS.fold(~S, ~X, ~step, tx, GS.fold(~S, ~X, ~step, pre, s0)),
            GP.fold_append(~S, ~X, ~step, pre, tx, s0))))
      %Equal.sym(S, r, GS.fold(~S, ~X, ~step, pre, s0), hrr) :
        {List.append(&2, O, List.take(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, _), c),
          Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest, o1)) == RHS : List<&2, O>}
      %Equal.sym(List<&2, O>, GR.verify(~S, ~X, ~O, ~step, ~out, xs, GS.fold(~S, ~X, ~step, pre, s0)),
        GS.outputs(~S, ~X, ~O, ~step, ~out, xs, s0, pre), GP.verify_from(~S, ~X, ~O, ~step, ~out, xs, s0, pre)) :
        {List.append(&2, O, List.take(&2, O, _, c), Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest, o1)) == RHS : List<&2, O>}
      %Equal.sym(List<&2, O>, List.take(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, xs, s0, pre), c),
        GS.outputs(~S, ~X, ~O, ~step, ~out, tx, s0, pre), gq_take_outputs(~S, ~X, ~O, ~step, ~out, xs, s0, pre, c)) :
        {List.append(&2, O, _, Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest, o1)) == RHS : List<&2, O>}
      %Equal.sym(List<&2, O>, Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest, o1),
        GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rest), s0, pre1),
        gq_emit(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest, o1, pre1, s0,
          GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
            gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), hr1, okt)) :
        {List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, tx, s0, pre), _) == RHS : List<&2, O>}
      Equal.sym(List<&2, O>, RHS, List.append(&2, O, GS.outputs(~S, ~X, ~O, ~step, ~out, tx, s0, pre),
          GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rest), s0, pre1)),
        gq_outputs_append(~S, ~X, ~O, ~step, ~out, tx, Spec.stream_x(~X, ~Y, rest), s0, pre))

def gq_position(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)) ==
      Nat.add(GR.position_of(~S, ~Y, o), Spec.committed(~X, ~Y, rounds)) : Nat}:
  match rounds o:
    case Nil{} _:
      Equal.sym(Nat, Nat.add(GR.position_of(~S, ~Y, o), 0n), GR.position_of(~S, ~Y, o), Ar.ar_add_zero_r(GR.position_of(~S, ~Y, o)))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r})) ==
        Nat.add(GR.position_of(~S, ~Y, GR.Refused{r}), Spec.committed(~X, ~Y, Impl.Round{w, xs, ys, c} <> rest)) : Nat},
        Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +o1 = GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}})
      +n = Spec.committed(~X, ~Y, rest)
      +pa = Ar.ard_fst({GR.position_of(~S, ~Y, o1) == Nat.add(p, c) : Nat}, {GR.last_history_of(~S, ~Y, o1) == 0n : Nat},
        GRL.position_advance(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)))
      Equal.trans(Nat, GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rest, o1)), Nat.add(GR.position_of(~S, ~Y, o1), n),
        Nat.add(p, Nat.add(c, n)),
        gq_position(~S, ~X, ~Y, ~step, K, H, rest, o1,
          GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
            gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), okt),
        Equal.trans(Nat, Nat.add(GR.position_of(~S, ~Y, o1), n), Nat.add(Nat.add(p, c), n), Nat.add(p, Nat.add(c, n)),
          Equal.cong(Nat, Nat, t => Nat.add(t, n), GR.position_of(~S, ~Y, o1), Nat.add(p, c), pa),
          Ar.ar_add_assoc(p, c, n)))

def Laws.split_point_state(S, X, Y, O, step, out, K, H, s0, buf, position, lh, rounds, next, ok_):
  +ok = ok_
  +o = {GR.Committed{GR.Engine{s0, buf, position, lh}} : GR.Outcome<S, Y>}
  +row0 = gq_row0(~S, ~X, ~Y, ~step, K, H, rounds, o, Nil{}, s0, {==}, {==}, ok)
  (row0,
    gq_emit(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds, o, Nil{}, s0, {==}, {==}, ok),
    Equal.trans(List<&2, O>, GR.verify(~S, ~X, ~O, ~step, ~out, next, GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o))),
      GR.verify(~S, ~X, ~O, ~step, ~out, next, GS.fold(~S, ~X, ~step, Spec.stream_x(~X, ~Y, rounds), s0)),
      GS.outputs(~S, ~X, ~O, ~step, ~out, next, s0, Spec.stream_x(~X, ~Y, rounds)),
      Equal.cong(S, List<&2, O>, t => GR.verify(~S, ~X, ~O, ~step, ~out, next, t),
        GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)), GS.fold(~S, ~X, ~step, Spec.stream_x(~X, ~Y, rounds), s0), row0),
      GP.verify_from(~S, ~X, ~O, ~step, ~out, next, s0, Spec.stream_x(~X, ~Y, rounds))),
    gq_committed(~S, ~X, ~Y, ~step, K, H, rounds, o, {==}, ok),
    gq_position(~S, ~X, ~Y, ~step, K, H, rounds, o, {==}, ok))

# ---------------------------------------------------------------- C2 conv window

def gq_len_take_k(~Y: Data, +buf: List<&2, Y>, +K: Nat, +H: Nat, +h: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat})
  -> {List.length(&2, Y, List.take(&2, Y, buf, K)) == K : Nat}:
  GP.len_take(~Y, buf, K, GP.le_rw(K, List.length(&2, Y, buf), Nat.add(K, H), h, GP.le_add_right(K, H)))

# K <= length(take(cb, K) ++ b) for a K + H column buffer
def gq_le_len(~Y: Data, +K: Nat, +H: Nat, +cb: List<&2, Y>, +b: List<&2, Y>, +hl: {List.length(&2, Y, cb) == Nat.add(K, H) : Nat})
  -> {Nat.is_le(K, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, cb, K), b))) == True{} : Bool}:
  +t0 = List.take(&2, Y, cb, K)
  GP.le_rw(K, List.length(&2, Y, List.append(&2, Y, t0, b)), Nat.add(K, List.length(&2, Y, b)),
    Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, t0, b)), Nat.add(List.length(&2, Y, t0), List.length(&2, Y, b)),
      Nat.add(K, List.length(&2, Y, b)), GP.len_append(~Y, t0, b),
      Equal.cong(Nat, Nat, v => Nat.add(v, List.length(&2, Y, b)), List.length(&2, Y, t0), K, gq_len_take_k(~Y, cb, K, H, hl))),
    Ar.ar_le_add_r(K, List.length(&2, Y, b)))

# last(K, l) == l when l has exactly K entries
def gq_last_exact(~Y: Data, +K: Nat, +l: List<&2, Y>, +h: {List.length(&2, Y, l) == K : Nat})
  -> {GS.last(~Y, K, l) == l : List<&2, Y>}:
  %Equal.sym(Nat, List.length(&2, Y, l), K, h) : {List.drop(&2, Y, l, Nat.sub(_, K)) == l : List<&2, Y>}
  %Equal.sym(Nat, Nat.sub(K, K), 0n, GP.sub_self(K)) : {List.drop(&2, Y, l, _) == l : List<&2, Y>}
  GP.drop_zero(~Y, l)

def gq_convlen(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +hl: {List.length(&2, Y, GR.conv_of(~S, ~Y, o)) == Nat.add(K, H) : Nat},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {List.length(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o))) == Nat.add(K, H) : Nat}:
  match rounds o:
    case Nil{} _:
      hl
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({List.length(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r}))) ==
        Nat.add(K, H) : Nat}, Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +o1 = GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}})
      +snd = Ar.ard_snd({List.take(&2, Y, GR.conv_of(~S, ~Y, o1), K) ==
          GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, cb, K), List.take(&2, Y, ys, c))) : List<&2, Y>},
        {List.length(&2, Y, GR.conv_of(~S, ~Y, o1)) == Nat.add(K, H) : Nat},
        GRL.conv_window(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_shy(~X, ~Y, H, w, xs, ys, c, okr), hl, gq_drafted(~X, ~Y, H, w, xs, ys, c, okr), gq_fits(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)))
      gq_convlen(~S, ~X, ~Y, ~step, K, H, rest, o1,
        GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), snd, okt)

def gq_conv(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +hc: {GR.committed(~S, ~Y, o) == True{} : Bool},
    +hl: {List.length(&2, Y, GR.conv_of(~S, ~Y, o)) == Nat.add(K, H) : Nat},
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)), K) ==
      GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, o), K), Spec.stream_y(~X, ~Y, rounds))) : List<&2, Y>}:
  match rounds o:
    case Nil{} _:
      +t = List.take(&2, Y, GR.conv_of(~S, ~Y, o), K)
      %Equal.sym(List<&2, Y>, List.append(&2, Y, t, Nil{}), t, GP.append_nil(~Y, t)) : {t == GS.last(~Y, K, _) : List<&2, Y>}
      Equal.sym(List<&2, Y>, GS.last(~Y, K, t), t, gq_last_exact(~Y, K, t, gq_len_take_k(~Y, GR.conv_of(~S, ~Y, o), K, H, hl)))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Refused{r}:
      Empty.absurd({List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, Impl.Round{w, xs, ys, c} <> rest, GR.Refused{r})), K) ==
        GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, GR.Refused{r}), K),
          Spec.stream_y(~X, ~Y, Impl.Round{w, xs, ys, c} <> rest))) : List<&2, Y>}, Ar.ar_false_true(hc))
    case Impl.Round{+w, +xs, +ys, +c} <> rest GR.Committed{GR.Engine{+r, +cb, +p, +l}}:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +o1 = GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{r, cb, p, l}, w, xs, ys, Accept.Verdict{c, False{}})
      +t0 = List.take(&2, Y, cb, K)
      +ty = List.take(&2, Y, ys, c)
      +ry = Spec.stream_y(~X, ~Y, rest)
      +t1 = List.take(&2, Y, GR.conv_of(~S, ~Y, o1), K)
      +fst = Ar.ard_fst({t1 == GS.last(~Y, K, List.append(&2, Y, t0, ty)) : List<&2, Y>},
        {List.length(&2, Y, GR.conv_of(~S, ~Y, o1)) == Nat.add(K, H) : Nat},
        GRL.conv_window(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_shy(~X, ~Y, H, w, xs, ys, c, okr), hl, gq_drafted(~X, ~Y, H, w, xs, ys, c, okr), gq_fits(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)))
      +snd = Ar.ard_snd({t1 == GS.last(~Y, K, List.append(&2, Y, t0, ty)) : List<&2, Y>},
        {List.length(&2, Y, GR.conv_of(~S, ~Y, o1)) == Nat.add(K, H) : Nat},
        GRL.conv_window(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_shy(~X, ~Y, H, w, xs, ys, c, okr), hl, gq_drafted(~X, ~Y, H, w, xs, ys, c, okr), gq_fits(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)))
      +ih = gq_conv(~S, ~X, ~Y, ~step, K, H, rest, o1,
        GRL.commit_happens(~S, ~X, ~Y, ~step, K, H, r, cb, p, l, w, xs, ys, c, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
          gq_progress(~X, ~Y, H, w, xs, ys, c, okr), gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)), snd, okt)
      +A = List.append(&2, Y, t0, ty)
      Equal.trans(List<&2, Y>, List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rest, o1)), K),
        GS.last(~Y, K, List.append(&2, Y, t1, ry)), GS.last(~Y, K, List.append(&2, Y, t0, List.append(&2, Y, ty, ry))), ih,
      Equal.trans(List<&2, Y>, GS.last(~Y, K, List.append(&2, Y, t1, ry)), GS.last(~Y, K, List.append(&2, Y, GS.last(~Y, K, A), ry)),
        GS.last(~Y, K, List.append(&2, Y, t0, List.append(&2, Y, ty, ry))),
        Equal.cong(List<&2, Y>, List<&2, Y>, v => GS.last(~Y, K, List.append(&2, Y, v, ry)), t1, GS.last(~Y, K, A), fst),
      Equal.trans(List<&2, Y>, GS.last(~Y, K, List.append(&2, Y, GS.last(~Y, K, A), ry)), GS.last(~Y, K, List.append(&2, Y, A, ry)),
        GS.last(~Y, K, List.append(&2, Y, t0, List.append(&2, Y, ty, ry))),
        GP.last_last(~Y, K, A, ry, gq_le_len(~Y, K, H, cb, ty, hl)),
        Equal.cong(List<&2, Y>, List<&2, Y>, v => GS.last(~Y, K, v), List.append(&2, Y, A, ry), List.append(&2, Y, t0, List.append(&2, Y, ty, ry)),
          GP.append_assoc(~Y, t0, ty, ry)))))

def Laws.conv_window_rounds(S, X, Y, step, K, H, s0, buf, position, lh, rounds, next_y, j, shaped_buf_, ok_):
  +shaped_buf = shaped_buf_
  +ok = ok_
  +o = {GR.Committed{GR.Engine{s0, buf, position, lh}} : GR.Outcome<S, Y>}
  +run = Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, o)
  +B0 = List.append(&2, Y, List.take(&2, Y, buf, K), Spec.stream_y(~X, ~Y, rounds))
  +tj = List.take(&2, Y, next_y, j)
  +win = gq_conv(~S, ~X, ~Y, ~step, K, H, rounds, o, {==}, shaped_buf, ok)
  (win,
    gq_convlen(~S, ~X, ~Y, ~step, K, H, rounds, o, {==}, shaped_buf, ok),
    Equal.trans(List<&2, Y>, GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, run), K), tj)),
      GS.last(~Y, K, List.append(&2, Y, GS.last(~Y, K, B0), tj)), GS.last(~Y, K, List.append(&2, Y, B0, tj)),
      Equal.cong(List<&2, Y>, List<&2, Y>, v => GS.last(~Y, K, List.append(&2, Y, v, tj)),
        List.take(&2, Y, GR.conv_of(~S, ~Y, run), K), GS.last(~Y, K, B0), win),
      GP.last_last(~Y, K, B0, tj, gq_le_len(~Y, K, H, buf, Spec.stream_y(~X, ~Y, rounds), shaped_buf))))

# ---------------------------------------------------------------- C3 verify split point

# Dropping the first c verify rows is a verify of the dropped inputs from the replay of c inputs.
def gq_drop_verify(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    xs: List<&2, X>, +s: S, +c: Nat)
  -> {List.drop(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s), c) ==
      GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), GR.replay(~S, ~X, ~step, c, xs, s)) : List<&2, O>}:
  match xs c:
    case Nil{} _:
      {==}
    case x <> rest 0n:
      {==}
    case +x <> rest 1n+m:
      gq_drop_verify(~S, ~X, ~O, ~step, ~out, rest, step(s, x), m)

def gq_take_drop(~O: Data, l: List<&2, O>, +c: Nat)
  -> {List.append(&2, O, List.take(&2, O, l, c), List.drop(&2, O, l, c)) == l : List<&2, O>}:
  match l c:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      Equal.cong(List<&2, O>, List<&2, O>, v => h <> v,
        List.append(&2, O, List.take(&2, O, t, p), List.drop(&2, O, t, p)), t, gq_take_drop(~O, t, p))

# The first c verify rows followed by the fresh verify from the replayed state are the verify.
def gq_split_rows(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    +xs: List<&2, X>, +s: S, +c: Nat)
  -> {List.append(&2, O, List.take(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s), c),
      GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), GR.replay(~S, ~X, ~step, c, xs, s))) ==
      GR.verify(~S, ~X, ~O, ~step, ~out, xs, s) : List<&2, O>}:
  +V = GR.verify(~S, ~X, ~O, ~step, ~out, xs, s)
  +F = GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), GR.replay(~S, ~X, ~step, c, xs, s))
  Equal.trans(List<&2, O>, List.append(&2, O, List.take(&2, O, V, c), F),
    List.append(&2, O, List.take(&2, O, V, c), List.drop(&2, O, V, c)), V,
    Equal.cong(List<&2, O>, List<&2, O>, u => List.append(&2, O, List.take(&2, O, V, c), u), F, List.drop(&2, O, V, c),
      Equal.sym(List<&2, O>, List.drop(&2, O, V, c), F, gq_drop_verify(~S, ~X, ~O, ~step, ~out, xs, s, c))),
    gq_take_drop(~O, V, c))

def Laws.verify_split_point(S, X, O, step, out, xs, s, c):
  (gq_drop_verify(~S, ~X, ~O, ~step, ~out, xs, s, c),
    GP.replay_fold(~S, ~X, ~step, c, xs, s),
    gq_split_rows(~S, ~X, ~O, ~step, ~out, xs, s, c))

def Laws.verify_split_round(S, X, Y, O, step, out, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, bounded):
  +R = GR.row0_of(~S, ~Y, GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{s0, buf, position, lh}, window, xs, ys,
    Accept.Verdict{count, False{}}))
  +P = GR.replay(~S, ~X, ~step, count, xs, s0)
  +V = GR.verify(~S, ~X, ~O, ~step, ~out, xs, s0)
  +dx = List.drop(&2, X, xs, count)
  +rp = Equal.trans(S, R, GS.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0), P,
    GRL.commit_prefix(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, bounded),
    Equal.sym(S, P, GS.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0), GP.replay_fold(~S, ~X, ~step, count, xs, s0)))
  +pr = Equal.cong(S, List<&2, O>, t => GR.verify(~S, ~X, ~O, ~step, ~out, dx, t), P, R, Equal.sym(S, R, P, rp))
  (Equal.trans(List<&2, O>, List.drop(&2, O, V, count), GR.verify(~S, ~X, ~O, ~step, ~out, dx, P),
      GR.verify(~S, ~X, ~O, ~step, ~out, dx, R), gq_drop_verify(~S, ~X, ~O, ~step, ~out, xs, s0, count), pr),
    rp,
    Equal.trans(List<&2, O>, List.append(&2, O, List.take(&2, O, V, count), GR.verify(~S, ~X, ~O, ~step, ~out, dx, R)),
      List.append(&2, O, List.take(&2, O, V, count), GR.verify(~S, ~X, ~O, ~step, ~out, dx, P)), V,
      Equal.cong(List<&2, O>, List<&2, O>, u => List.append(&2, O, List.take(&2, O, V, count), u),
        GR.verify(~S, ~X, ~O, ~step, ~out, dx, R), GR.verify(~S, ~X, ~O, ~step, ~out, dx, P),
        Equal.sym(List<&2, O>, GR.verify(~S, ~X, ~O, ~step, ~out, dx, P), GR.verify(~S, ~X, ~O, ~step, ~out, dx, R), pr)),
      gq_split_rows(~S, ~X, ~O, ~step, ~out, xs, s0, count)))

# ---------------------------------------------------------------- C4 two schedules

# The committed count is the length of the committed rule-input stream.
def gq_committed_len(~X: Data, ~Y: Data, +H: Nat, +rounds: List<&2, Impl.Round<X, Y>>,
    +ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool})
  -> {Spec.committed(~X, ~Y, rounds) == List.length(&2, X, Spec.stream_x(~X, ~Y, rounds)) : Nat}:
  match rounds:
    case Nil{}:
      {==}
    case Impl.Round{+w, +xs, +ys, +c} <> rest:
      +okr = Ar.ar_and_l(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +okt = Ar.ar_and_r(Impl.round_ok(~X, ~Y, H, Impl.Round{w, xs, ys, c}), Impl.rounds_ok(~X, ~Y, H, rest), ok)
      +tx = List.take(&2, X, xs, c)
      +rx = Spec.stream_x(~X, ~Y, rest)
      +lt = GP.len_take(~X, xs, c, GP.le_rw(c, List.length(&2, X, xs), 1n+w, gq_shx(~X, ~Y, H, w, xs, ys, c, okr),
        gq_bounded(~X, ~Y, H, w, xs, ys, c, okr)))
      Equal.trans(Nat, Nat.add(c, Spec.committed(~X, ~Y, rest)), Nat.add(c, List.length(&2, X, rx)),
        List.length(&2, X, List.append(&2, X, tx, rx)),
        Equal.cong(Nat, Nat, t => Nat.add(c, t), Spec.committed(~X, ~Y, rest), List.length(&2, X, rx),
          gq_committed_len(~X, ~Y, H, rest, okt)),
        Equal.trans(Nat, Nat.add(c, List.length(&2, X, rx)), Nat.add(List.length(&2, X, tx), List.length(&2, X, rx)),
          List.length(&2, X, List.append(&2, X, tx, rx)),
          Equal.cong(Nat, Nat, t => Nat.add(t, List.length(&2, X, rx)), c, List.length(&2, X, tx),
            Equal.sym(Nat, List.length(&2, X, tx), c, lt)),
          Equal.sym(Nat, List.length(&2, X, List.append(&2, X, tx, rx)), Nat.add(List.length(&2, X, tx), List.length(&2, X, rx)),
            GP.len_append(~X, tx, rx))))

# C4 from two instances of C1 (c1, c2: split_point_state for each schedule from outcome o).
def gq_two_state(~S: Data, ~X: Data, ~Y: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O, +K: Nat, +H: Nat,
    +rounds1: List<&2, Impl.Round<X, Y>>, +rounds2: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>, +s0: S,
    +position: Nat, +next: List<&2, X>,
    +ok1: {Impl.rounds_ok(~X, ~Y, H, rounds1) == True{} : Bool},
    +ok2: {Impl.rounds_ok(~X, ~Y, H, rounds2) == True{} : Bool},
    +sx: {Spec.stream_x(~X, ~Y, rounds1) == Spec.stream_x(~X, ~Y, rounds2) : List<&2, X>},
    c1: {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)) == GS.fold(~S, ~X, ~step, Spec.stream_x(~X, ~Y, rounds1), s0) : S} &
      {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds1, o) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rounds1), s0, Nil{}) : List<&2, O>} &
      {GR.verify(~S, ~X, ~O, ~step, ~out, next, GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o))) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, next, s0, Spec.stream_x(~X, ~Y, rounds1)) : List<&2, O>} &
      {GR.committed(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)) == True{} : Bool} &
      {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)) == Nat.add(position, Spec.committed(~X, ~Y, rounds1)) : Nat},
    c2: {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)) == GS.fold(~S, ~X, ~step, Spec.stream_x(~X, ~Y, rounds2), s0) : S} &
      {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, o) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rounds2), s0, Nil{}) : List<&2, O>} &
      {GR.verify(~S, ~X, ~O, ~step, ~out, next, GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o))) ==
        GS.outputs(~S, ~X, ~O, ~step, ~out, next, s0, Spec.stream_x(~X, ~Y, rounds2)) : List<&2, O>} &
      {GR.committed(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)) == True{} : Bool} &
      {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)) == Nat.add(position, Spec.committed(~X, ~Y, rounds2)) : Nat})
  -> {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)) == GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)) : S} &
     {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds1, o) == Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, o) : List<&2, O>} &
     {GR.verify(~S, ~X, ~O, ~step, ~out, next, GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o))) ==
       GR.verify(~S, ~X, ~O, ~step, ~out, next, GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o))) : List<&2, O>} &
     {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)) == GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)) : Nat}:
  (r1, e1, v1, k1, p1) = c1
  (r2, e2, v2, k2, p2) = c2
  +run1 = Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)
  +run2 = Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)
  +x1 = Spec.stream_x(~X, ~Y, rounds1)
  +x2 = Spec.stream_x(~X, ~Y, rounds2)
  +n1 = Spec.committed(~X, ~Y, rounds1)
  +n2 = Spec.committed(~X, ~Y, rounds2)
  +row = Equal.trans(S, GR.row0_of(~S, ~Y, run1), GS.fold(~S, ~X, ~step, x1, s0), GR.row0_of(~S, ~Y, run2), r1,
    Equal.trans(S, GS.fold(~S, ~X, ~step, x1, s0), GS.fold(~S, ~X, ~step, x2, s0), GR.row0_of(~S, ~Y, run2),
      Equal.cong(List<&2, X>, S, t => GS.fold(~S, ~X, ~step, t, s0), x1, x2, sx),
      Equal.sym(S, GR.row0_of(~S, ~Y, run2), GS.fold(~S, ~X, ~step, x2, s0), r2)))
  +ln = Equal.trans(Nat, n1, List.length(&2, X, x1), n2, gq_committed_len(~X, ~Y, H, rounds1, ok1),
    Equal.trans(Nat, List.length(&2, X, x1), List.length(&2, X, x2), n2,
      Equal.cong(List<&2, X>, Nat, t => List.length(&2, X, t), x1, x2, sx),
      Equal.sym(Nat, n2, List.length(&2, X, x2), gq_committed_len(~X, ~Y, H, rounds2, ok2))))
  (row,
    Equal.trans(List<&2, O>, Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds1, o),
      GS.outputs(~S, ~X, ~O, ~step, ~out, x1, s0, Nil{}), Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, o), e1,
      Equal.trans(List<&2, O>, GS.outputs(~S, ~X, ~O, ~step, ~out, x1, s0, Nil{}), GS.outputs(~S, ~X, ~O, ~step, ~out, x2, s0, Nil{}),
        Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, o),
        Equal.cong(List<&2, X>, List<&2, O>, t => GS.outputs(~S, ~X, ~O, ~step, ~out, t, s0, Nil{}), x1, x2, sx),
        Equal.sym(List<&2, O>, Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, o),
          GS.outputs(~S, ~X, ~O, ~step, ~out, x2, s0, Nil{}), e2))),
    Equal.cong(S, List<&2, O>, t => GR.verify(~S, ~X, ~O, ~step, ~out, next, t), GR.row0_of(~S, ~Y, run1), GR.row0_of(~S, ~Y, run2), row),
    Equal.trans(Nat, GR.position_of(~S, ~Y, run1), Nat.add(position, n1), GR.position_of(~S, ~Y, run2), p1,
      Equal.trans(Nat, Nat.add(position, n1), Nat.add(position, n2), GR.position_of(~S, ~Y, run2),
        Equal.cong(Nat, Nat, t => Nat.add(position, t), n1, n2, ln),
        Equal.sym(Nat, GR.position_of(~S, ~Y, run2), Nat.add(position, n2), p2))))

def Laws.two_schedules(S, X, Y, O, step, out, K, H, s0, buf, position, lh, rounds1, rounds2, next, ok1_, ok2_, same_x):
  +ok1 = ok1_
  +ok2 = ok2_
  +o = {GR.Committed{GR.Engine{s0, buf, position, lh}} : GR.Outcome<S, Y>}
  gq_two_state(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds1, rounds2, o, s0, position, next, ok1, ok2, same_x,
    Laws.split_point_state(~S, ~X, ~Y, ~O, ~step, ~out, K, H, s0, buf, position, lh, rounds1, next, ok1),
    Laws.split_point_state(~S, ~X, ~Y, ~O, ~step, ~out, K, H, s0, buf, position, lh, rounds2, next, ok2))

# C4 conv from two instances of C2 (tb = the first K columns of the initial buffer).
def gq_two_conv(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +rounds1: List<&2, Impl.Round<X, Y>>, +rounds2: List<&2, Impl.Round<X, Y>>, +o: GR.Outcome<S, Y>,
    +tb: List<&2, Y>, +tj: List<&2, Y>,
    +sy: {Spec.stream_y(~X, ~Y, rounds1) == Spec.stream_y(~X, ~Y, rounds2) : List<&2, Y>},
    c1: {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)), K) ==
        GS.last(~Y, K, List.append(&2, Y, tb, Spec.stream_y(~X, ~Y, rounds1))) : List<&2, Y>} &
      {List.length(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o))) == Nat.add(K, H) : Nat} &
      {GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)), K), tj)) ==
        GS.last(~Y, K, List.append(&2, Y, List.append(&2, Y, tb, Spec.stream_y(~X, ~Y, rounds1)), tj)) : List<&2, Y>},
    c2: {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)), K) ==
        GS.last(~Y, K, List.append(&2, Y, tb, Spec.stream_y(~X, ~Y, rounds2))) : List<&2, Y>} &
      {List.length(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o))) == Nat.add(K, H) : Nat} &
      {GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)), K), tj)) ==
        GS.last(~Y, K, List.append(&2, Y, List.append(&2, Y, tb, Spec.stream_y(~X, ~Y, rounds2)), tj)) : List<&2, Y>})
  -> {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)), K) ==
       List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)), K) : List<&2, Y>} &
     {GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)), K), tj)) ==
       GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)), K), tj)) : List<&2, Y>}:
  (a1, b1, d1) = c1
  (a2, b2, d2) = c2
  +w1 = List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, o)), K)
  +w2 = List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, o)), K)
  +y1 = Spec.stream_y(~X, ~Y, rounds1)
  +y2 = Spec.stream_y(~X, ~Y, rounds2)
  +win = Equal.trans(List<&2, Y>, w1, GS.last(~Y, K, List.append(&2, Y, tb, y1)), w2, a1,
    Equal.trans(List<&2, Y>, GS.last(~Y, K, List.append(&2, Y, tb, y1)), GS.last(~Y, K, List.append(&2, Y, tb, y2)), w2,
      Equal.cong(List<&2, Y>, List<&2, Y>, t => GS.last(~Y, K, List.append(&2, Y, tb, t)), y1, y2, sy),
      Equal.sym(List<&2, Y>, w2, GS.last(~Y, K, List.append(&2, Y, tb, y2)), a2)))
  (win,
    Equal.cong(List<&2, Y>, List<&2, Y>, v => GS.last(~Y, K, List.append(&2, Y, v, tj)), w1, w2, win))

def Laws.two_schedules_conv(S, X, Y, step, K, H, s0, buf, position, lh, rounds1, rounds2, next_y, j, shaped_buf_, ok1, ok2, same_y):
  +shaped_buf = shaped_buf_
  +o = {GR.Committed{GR.Engine{s0, buf, position, lh}} : GR.Outcome<S, Y>}
  gq_two_conv(~S, ~X, ~Y, ~step, K, H, rounds1, rounds2, o, List.take(&2, Y, buf, K), List.take(&2, Y, next_y, j), same_y,
    Laws.conv_window_rounds(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, rounds1, next_y, j, shaped_buf, ok1),
    Laws.conv_window_rounds(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, rounds2, next_y, j, shaped_buf, ok2))

# ---------------------------------------------------------------- mutation witness

def gq_head_is3(l: List<&2, Nat>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case h <> t:
      Nat.is_eq(h, 3n)

def Laws.replay_step_mismatch_differs():
  ({==}, {==}, {==},
    e => Ar.ar_false_true(Equal.cong(List<&2, Nat>, Bool, l => gq_head_is3(l), [4n, 7n], [3n, 6n],
      Equal.sym(List<&2, Nat>, [3n, 6n], [4n, 7n], e))))
