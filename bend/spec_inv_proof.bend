# Proofs of bend/spec_inv_laws.bend. The round lemma (core) walks the acceptance facts position by
# position next to greedy decoding; the job laws follow by induction over the rounds with the
# invariant Inv. Acceptance facts are reused from exl3_accept_proof (decide_shift, accept_progress,
# accept_bounds via exl3_round_proof.usable), arithmetic from gemm_m16_partition_proof.
import Base
import ./spec_inv.bend as Impl
import ./spec_inv_spec.bend as Spec
import ./spec_inv_laws.bend as Laws
import ./exl3_accept_spec.bend as Accept
import ./exl3_accept_laws.bend as AcceptLaws
import ./exl3_accept_proof.bend as AcceptProof
import ./exl3_round.bend as Round
import ./exl3_round_spec.bend as RoundSpec
import ./exl3_round_proof.bend as RoundProof
import ./gemm_m16_partition_proof.bend as Ar

# ---------------------------------------------------------------- lists

def si_app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, U32>, List<&2, U32>, x => h <> x, List.append(&2, U32, t, Nil{}), t, si_app_nil(t))

def si_app_assoc(xs: List<&2, U32>, +ys: List<&2, U32>, +zs: List<&2, U32>)
  -> {List.append(&2, U32, List.append(&2, U32, xs, ys), zs) ==
      List.append(&2, U32, xs, List.append(&2, U32, ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, U32>, List<&2, U32>, x => h <> x,
        List.append(&2, U32, List.append(&2, U32, t, ys), zs), List.append(&2, U32, t, List.append(&2, U32, ys, zs)),
        si_app_assoc(t, ys, zs))

# (seq ++ [t]) ++ xs == seq ++ (t <> xs)
def si_app_snoc(+seq: List<&2, U32>, +t: U32, +xs: List<&2, U32>)
  -> {List.append(&2, U32, List.append(&2, U32, seq, [t]), xs) == List.append(&2, U32, seq, t <> xs) : List<&2, U32>}:
  si_app_assoc(seq, [t], xs)

def si_take_app(xs: List<&2, U32>, +ys: List<&2, U32>)
  -> {List.take(&2, U32, List.append(&2, U32, xs, ys), List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> r:
          {==}
    case +h <> t:
      Equal.cong(List<&2, U32>, List<&2, U32>, x => h <> x,
        List.take(&2, U32, List.append(&2, U32, t, ys), List.length(&2, U32, t)), t, si_take_app(t, ys))

def si_len_app(xs: List<&2, U32>, +ys: List<&2, U32>)
  -> {List.length(&2, U32, List.append(&2, U32, xs, ys)) == Nat.add(List.length(&2, U32, xs), List.length(&2, U32, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, List.append(&2, U32, t, ys)),
        Nat.add(List.length(&2, U32, t), List.length(&2, U32, ys)), si_len_app(t, ys))

def si_rows_len(~row: List<&2, U32> -> Nat -> U32, ds: List<&2, U32>, +seq: List<&2, U32>, +r: Nat)
  -> {List.length(&2, U32, Impl.rows_after(~row, ds, seq, r)) == List.length(&2, U32, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case +d <> rest:
      Equal.cong(Nat, Nat, x => 1n+x,
        List.length(&2, U32, Impl.rows_after(~row, rest, List.append(&2, U32, seq, [d]), 1n+r)),
        List.length(&2, U32, rest), si_rows_len(~row, rest, List.append(&2, U32, seq, [d]), 1n+r))

# A round's verify ids are k + 1 for k drafts (the acceptance laws' shape).
def si_shaped(~row: List<&2, U32> -> Nat -> U32, +ds: List<&2, U32>, +seq: List<&2, U32>, +r: Nat)
  -> {List.length(&2, U32, Impl.targets(~row, ds, seq, r)) == 1n+List.length(&2, U32, ds) : Nat}:
  Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, U32, Impl.rows_after(~row, ds, seq, r)),
    List.length(&2, U32, ds), si_rows_len(~row, ds, seq, r))

# ---------------------------------------------------------------- tokens and Bool / Nat facts

def si_bool_cmp_eq(+a: Bool, +b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      h
    case True{} False{}:
      Equal.sym(Bool, False{}, True{}, h)
    case True{} True{}:
      {==}

def si_fin_eq_t(+ab: Bool, +bb: Bool, t: Cmp, +h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool})
  -> {Cmp.is_eq(t) == True{} : Bool}:
  match t:
    case LT{}:
      h
    case EQ{}:
      {==}
    case GT{}:
      h

def si_fin_eq_b(+ab: Bool, +bb: Bool, t: Cmp, +h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool})
  -> {ab == bb : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ab == bb : Bool}, Ar.ar_false_true(h))
    case EQ{}:
      si_bool_cmp_eq(ab, bb, h)
    case GT{}:
      Empty.absurd({ab == bb : Bool}, Ar.ar_false_true(h))

# Word comparison reporting EQ means the words are equal.
def si_word_eq(+n: Nat, a: Word(n), b: Word(n), h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +hh = h
          %si_fin_eq_b(ab, bb, Word.cmp(p, at, bt), hh) : {WCon{ab, at} == WCon{_, bt} : Word.Con<p>}
          %si_word_eq(p, at, bt, si_fin_eq_t(ab, bb, Word.cmp(p, at, bt), hh)) : {WCon{ab, at} == WCon{ab, _} : Word.Con<p>}
          {==}

def si_not_false(+x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case False{}:
      Equal.sym(Bool, True{}, False{}, h)
    case True{}:
      {==}

# A draft the acceptance leaf does not reject equals the target (U32.is_ne is sound).
def si_u32_eq(a: U32, b: U32, h: {U32.is_ne(a, b) == False{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %si_word_eq(32n, x, y, si_not_false(Cmp.is_eq(Word.cmp(32n, x, y)), h)) : {U32{x} == U32{_} : U32}
      {==}

def si_or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      h

def si_member_is_stop(stops: List<&2, U32>, +t: U32) -> {Accept.member(stops, t) == Spec.is_stop(stops, t) : Bool}:
  match stops:
    case Nil{}:
      {==}
    case +s <> rest:
      Equal.cong(Bool, Bool, x => Bool.or(U32.is_eq(s, t), x), Accept.member(rest, t), Spec.is_stop(rest, t),
        si_member_is_stop(rest, t))

def si_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      m

def si_ck_shift(+i: Nat, ck: Nat) -> {Nat.is_eq(1n+(1n+i), ck) == Nat.is_eq(1n+i, si_pred(ck)) : Bool}:
  match ck:
    case 0n:
      {==}
    case 1n+c:
      {==}

# b < a gives 0 < a - b
def si_lt_sub_pos(+b: Nat, +a: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(a, b)) == True{} : Bool}:
  match b a:
    case 0n 0n:
      h
    case 0n 1n+ap:
      {==}
    case 1n+bp 0n:
      h
    case 1n+bp 1n+ap:
      si_lt_sub_pos(bp, ap, h)

def si_sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Ar.ar_le_refl(1n+ap)
    case 1n+ap 1n+bp:
      Ar.ar_le_trans(Nat.sub(ap, bp), ap, 1n+ap, si_sub_le(ap, bp), Ar.ar_h_le_succ(ap))

# ---------------------------------------------------------------- acceptance facts shift

# One committed token later with one more budget and the checkpoint one step closer: same facts.
def si_facts_shift(ts: List<&2, U32>, ds: List<&2, U32>, +stops: List<&2, U32>, +i: Nat, +b: Nat, +ck: Nat)
  -> {Accept.facts(ts, ds, stops, 1n+i, 1n+b, ck) == Accept.facts(ts, ds, stops, i, b, si_pred(ck)) : List<&2, Accept.Facts>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> rest:
      match ds:
        case Nil{}:
          {==}
        case +p <> more:
          +M = Accept.member(stops, t)
          +G = Nat.is_ge(1n+i, b)
          +NE = U32.is_ne(p, t)
          %Equal.sym(Bool, Nat.is_eq(1n+(1n+i), ck), Nat.is_eq(1n+i, si_pred(ck)), si_ck_shift(i, ck)) : {Accept.Facts{M, G, False{}, Bool.or(NE, _)} <> Accept.facts(rest, more, stops, 1n+(1n+i), 1n+b, ck) ==
            Accept.Facts{M, G, False{}, Bool.or(NE, Nat.is_eq(1n+i, si_pred(ck)))} <> Accept.facts(rest, more, stops, 1n+i, b, si_pred(ck)) : List<&2, Accept.Facts>}
          Equal.cong(List<&2, Accept.Facts>, List<&2, Accept.Facts>, x => Accept.Facts{M, G, False{}, Bool.or(NE, Nat.is_eq(1n+i, si_pred(ck)))} <> x,
            Accept.facts(rest, more, stops, 1n+(1n+i), 1n+b, ck), Accept.facts(rest, more, stops, 1n+i, b, si_pred(ck)),
            si_facts_shift(rest, more, stops, 1n+i, b, ck))

# The continuing position's decision equals the bumped decision of the shifted facts.
def si_dec(+ts: List<&2, U32>, +ds: List<&2, U32>, +stops: List<&2, U32>, +bq: Nat, +ck: Nat)
  -> {AcceptProof.bump(Accept.decide(Accept.facts(ts, ds, stops, 0n, 1n+bq, si_pred(ck)), 0n)) ==
      Accept.decide(Accept.facts(ts, ds, stops, 1n, 1n+(1n+bq), ck), 1n) : Accept.Verdict}:
  +F0 = Accept.facts(ts, ds, stops, 0n, 1n+bq, si_pred(ck))
  +F1 = Accept.facts(ts, ds, stops, 1n, 1n+(1n+bq), ck)
  Equal.trans(Accept.Verdict, AcceptProof.bump(Accept.decide(F0, 0n)), Accept.decide(F0, 1n), Accept.decide(F1, 1n),
    AcceptProof.decide_shift(F0, 0n),
    Equal.cong(List<&2, Accept.Facts>, Accept.Verdict, x => Accept.decide(x, 1n), F0, F1,
      Equal.sym(List<&2, Accept.Facts>, F1, F0, si_facts_shift(ts, ds, stops, 0n, 1n+bq, ck))))

# ---------------------------------------------------------------- the round lemma

# Verdict v on verify ids ts from prefix seq with remaining budget b explains lhs: its committed
# ids followed by what greedy decoding emits after them.
def Good(~row: List<&2, U32> -> Nat -> U32, lhs: List<&2, U32>, +stops: List<&2, U32>, +b: Nat,
    +seq: List<&2, U32>, +ts: List<&2, U32>, v: Accept.Verdict) -> Type:
  match v:
    case Accept.Verdict{+n, +e}:
      {lhs == List.append(&2, U32, List.take(&2, U32, ts, n),
        Spec.after(~row, e, Nat.sub(b, n), stops, List.append(&2, U32, seq, List.take(&2, U32, ts, n)))) : List<&2, U32>}

def si_good_bump(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +b: Nat, +seq: List<&2, U32>, +t: U32,
    +ts: List<&2, U32>, +lhs: List<&2, U32>, v: Accept.Verdict,
    ih: Good(~row, lhs, stops, b, List.append(&2, U32, seq, [t]), ts, v))
  -> Good(~row, t <> lhs, stops, 1n+b, seq, t <> ts, AcceptProof.bump(v)):
  match v:
    case Accept.Verdict{+n, +e}:
      +TK = List.take(&2, U32, ts, n)
      %si_app_snoc(seq, t, TK) :
        {t <> lhs == t <> List.append(&2, U32, TK, Spec.after(~row, e, Nat.sub(b, n), stops, _)) : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, x => t <> x, lhs,
        List.append(&2, U32, TK, Spec.after(~row, e, Nat.sub(b, n), stops, List.append(&2, U32, List.append(&2, U32, seq, [t]), TK))), ih)

def NilGoal(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32,
    s: Bool, s2: Bool, +bp: Nat) -> Type:
  Good(~row, row(seq, 0n) <> Spec.cont(s2, Spec.greedy(~row, bp, stops, List.append(&2, U32, seq, [row(seq, 0n)]))),
    stops, 1n+bp, seq, [t], Accept.decide([Accept.Facts{s, Nat.is_ge(1n, 1n+bp), True{}, False{}}], 0n))

# Last row (no draft left): the bonus token.
def si_nil(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32,
    s: Bool, s2: Bool, hss: {s == s2 : Bool}, +ht: {t == row(seq, 0n) : U32}, +bp: Nat)
  -> NilGoal(~row, stops, seq, t, s, s2, bp):
  match s s2:
    case True{} True{}:
      Equal.cong(U32, List<&2, U32>, x => x <> Nil{}, row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))
    case True{} False{}:
      Empty.absurd(NilGoal(~row, stops, seq, t, True{}, False{}, bp), Ar.ar_true_false(hss))
    case False{} True{}:
      Empty.absurd(NilGoal(~row, stops, seq, t, False{}, True{}, bp), Ar.ar_false_true(hss))
    case False{} False{}:
      match bp:
        case 0n:
          Equal.cong(U32, List<&2, U32>, x => x <> Nil{}, row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))
        case 1n+bq:
          Equal.cong(U32, List<&2, U32>, +x => x <> Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [x])),
            row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))

def ConsGoal(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32, +d: U32,
    +ds: List<&2, U32>, +r: Nat, +ck: Nat, s: Bool, s2: Bool, rej: Bool, +bp: Nat) -> Type:
  Good(~row, row(seq, 0n) <> Spec.cont(s2, Spec.greedy(~row, bp, stops, List.append(&2, U32, seq, [row(seq, 0n)]))),
    stops, 1n+bp, seq, t <> Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r),
    Accept.decide(Accept.Facts{s, Nat.is_ge(1n, 1n+bp), False{}, rej} <>
      Accept.facts(Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r), ds, stops, 1n, 1n+bp, ck), 0n))

# A drafted position with the budget spent at it: it commits and ends the job.
def si_cons_zero(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32, +d: U32,
    +ds: List<&2, U32>, +r: Nat, +ck: Nat, s: Bool, s2: Bool, hss: {s == s2 : Bool}, rej: Bool,
    +ht: {t == row(seq, 0n) : U32})
  -> ConsGoal(~row, stops, seq, t, d, ds, r, ck, s, s2, rej, 0n):
  match s s2:
    case True{} True{}:
      Equal.cong(U32, List<&2, U32>, x => x <> Nil{}, row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))
    case True{} False{}:
      Empty.absurd(ConsGoal(~row, stops, seq, t, d, ds, r, ck, True{}, False{}, rej, 0n), Ar.ar_true_false(hss))
    case False{} True{}:
      Empty.absurd(ConsGoal(~row, stops, seq, t, d, ds, r, ck, False{}, True{}, rej, 0n), Ar.ar_false_true(hss))
    case False{} False{}:
      Equal.cong(U32, List<&2, U32>, x => x <> Nil{}, row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))

# Carry the next position's round lemma from prefix seq ++ [d] to seq ++ [t] (d == t).
def si_move(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +d: U32, +t: U32, +bq: Nat,
    +ts: List<&2, U32>, +v: Accept.Verdict, hdt: {d == t : U32},
    ih: Good(~row, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [d])), stops, 1n+bq,
      List.append(&2, U32, seq, [d]), ts, v))
  -> Good(~row, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [t])), stops, 1n+bq,
      List.append(&2, U32, seq, [t]), ts, v):
  %hdt : Good(~row, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [_])), stops, 1n+bq,
    List.append(&2, U32, seq, [_]), ts, v)
  ih

# The accepted-and-continue position: the rest of the round is the round lemma one token later.
def si_continue(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32, +d: U32,
    +ds: List<&2, U32>, +r: Nat, +ck: Nat, +bq: Nat, +ht: {t == row(seq, 0n) : U32}, +hdt: {d == t : U32},
    ih: Good(~row, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [d])), stops, 1n+bq,
      List.append(&2, U32, seq, [d]), Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r),
      Accept.decide(Accept.facts(Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r), ds, stops, 0n, 1n+bq, si_pred(ck)), 0n)))
  -> Good(~row, row(seq, 0n) <> Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [row(seq, 0n)])),
      stops, 1n+(1n+bq), seq, t <> Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r),
      Accept.decide(Accept.facts(Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r), ds, stops, 1n, 1n+(1n+bq), ck), 1n)):
  +TS = Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r)
  +V0 = Accept.decide(Accept.facts(TS, ds, stops, 0n, 1n+bq, si_pred(ck)), 0n)
  %si_dec(TS, ds, stops, bq, ck) :
    Good(~row, row(seq, 0n) <> Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [row(seq, 0n)])),
      stops, 1n+(1n+bq), seq, t <> TS, _)
  %ht : Good(~row, _ <> Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [_])),
      stops, 1n+(1n+bq), seq, t <> TS, AcceptProof.bump(V0))
  si_good_bump(~row, stops, 1n+bq, seq, t, TS, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [t])), V0,
    si_move(~row, stops, seq, d, t, bq, TS, V0, hdt, ih))

# A drafted position with budget left after it.
def si_cons_succ(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +seq: List<&2, U32>, +t: U32, +d: U32,
    +ds: List<&2, U32>, +r: Nat, +ck: Nat, s: Bool, s2: Bool, hss: {s == s2 : Bool}, rej: Bool,
    hrej: {Bool.or(U32.is_ne(d, t), Nat.is_eq(1n, ck)) == rej : Bool}, +ht: {t == row(seq, 0n) : U32}, +bq: Nat,
    ih: Good(~row, Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [d])), stops, 1n+bq,
      List.append(&2, U32, seq, [d]), Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r),
      Accept.decide(Accept.facts(Impl.targets(~row, ds, List.append(&2, U32, seq, [d]), 1n+r), ds, stops, 0n, 1n+bq, si_pred(ck)), 0n)))
  -> ConsGoal(~row, stops, seq, t, d, ds, r, ck, s, s2, rej, 1n+bq):
  match s s2:
    case True{} True{}:
      Equal.cong(U32, List<&2, U32>, x => x <> Nil{}, row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))
    case True{} False{}:
      Empty.absurd(ConsGoal(~row, stops, seq, t, d, ds, r, ck, True{}, False{}, rej, 1n+bq), Ar.ar_true_false(hss))
    case False{} True{}:
      Empty.absurd(ConsGoal(~row, stops, seq, t, d, ds, r, ck, False{}, True{}, rej, 1n+bq), Ar.ar_false_true(hss))
    case False{} False{}:
      match rej:
        case True{}:
          Equal.cong(U32, List<&2, U32>, +x => x <> Spec.greedy(~row, 1n+bq, stops, List.append(&2, U32, seq, [x])),
            row(seq, 0n), t, Equal.sym(U32, t, row(seq, 0n), ht))
        case False{}:
          +hdt = si_u32_eq(d, t, si_or_false_l(U32.is_ne(d, t), Nat.is_eq(1n, ck), hrej))
          si_continue(~row, stops, seq, t, d, ds, r, ck, bq, ht, hdt, ih)

# The round lemma: from any prefix seq with budget 1 + bp, drafts ds and checkpoint ck, the
# verdict on the verify ids (rows r, r + 1, ...) explains greedy decoding.
def si_core(~row: List<&2, U32> -> Nat -> U32, ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32},
    +ds: List<&2, U32>, +seq: List<&2, U32>, +r: Nat, +stops: List<&2, U32>, +bp: Nat, +ck: Nat)
  -> Good(~row, Spec.greedy(~row, 1n+bp, stops, seq), stops, 1n+bp, seq, Impl.targets(~row, ds, seq, r),
      Accept.decide(Accept.facts(Impl.targets(~row, ds, seq, r), ds, stops, 0n, 1n+bp, ck), 0n)):
  match ds:
    case Nil{}:
      +t = row(seq, r)
      +t0 = row(seq, 0n)
      +hss = Equal.trans(Bool, Accept.member(stops, t), Spec.is_stop(stops, t), Spec.is_stop(stops, t0),
        si_member_is_stop(stops, t), Equal.cong(U32, Bool, x => Spec.is_stop(stops, x), t, t0, rinv(seq, r)))
      si_nil(~row, stops, seq, t, Accept.member(stops, t), Spec.is_stop(stops, t0), hss, rinv(seq, r), bp)
    case +d <> rest:
      match bp:
        case 0n:
          +t = row(seq, r)
          +t0 = row(seq, 0n)
          +hss = Equal.trans(Bool, Accept.member(stops, t), Spec.is_stop(stops, t), Spec.is_stop(stops, t0),
            si_member_is_stop(stops, t), Equal.cong(U32, Bool, x => Spec.is_stop(stops, x), t, t0, rinv(seq, r)))
          si_cons_zero(~row, stops, seq, t, d, rest, r, ck, Accept.member(stops, t), Spec.is_stop(stops, t0), hss,
            Bool.or(U32.is_ne(d, t), Nat.is_eq(1n, ck)), rinv(seq, r))
        case 1n+bq:
          +t = row(seq, r)
          +t0 = row(seq, 0n)
          +hss = Equal.trans(Bool, Accept.member(stops, t), Spec.is_stop(stops, t), Spec.is_stop(stops, t0),
            si_member_is_stop(stops, t), Equal.cong(U32, Bool, x => Spec.is_stop(stops, x), t, t0, rinv(seq, r)))
          si_cons_succ(~row, stops, seq, t, d, rest, r, ck, Accept.member(stops, t), Spec.is_stop(stops, t0), hss,
            Bool.or(U32.is_ne(d, t), Nat.is_eq(1n, ck)), {==}, rinv(seq, r), bq,
            si_core(~row, ~rinv, rest, List.append(&2, U32, seq, [d]), 1n+r, stops, bq, si_pred(ck)))

# ---------------------------------------------------------------- budget left by a live round

def Live(e: Bool, +n: Nat, +b: Nat) -> Type:
  match e:
    case True{}:
      Unit
    case False{}:
      {Nat.is_lt(n, b) == True{} : Bool}

def LiveV(v: Accept.Verdict, +b: Nat) -> Type:
  match v:
    case Accept.Verdict{+n, e}:
      Live(e, n, b)

def si_live_bump(v: Accept.Verdict, +b: Nat, h: LiveV(v, b)) -> LiveV(AcceptProof.bump(v), 1n+b):
  match v:
    case Accept.Verdict{+n, e}:
      match e:
        case True{}:
          Unit{}
        case False{}:
          h

def si_live_nil(s: Bool, +bp: Nat)
  -> LiveV(Accept.decide([Accept.Facts{s, Nat.is_ge(1n, 1n+bp), True{}, False{}}], 0n), 1n+bp):
  match s:
    case True{}:
      Unit{}
    case False{}:
      match bp:
        case 0n:
          Unit{}
        case 1n+bq:
          {==}

def si_live_zero(s: Bool, rej: Bool, -F1: List<&2, Accept.Facts>)
  -> LiveV(Accept.decide(Accept.Facts{s, Nat.is_ge(1n, 1n), False{}, rej} <> F1, 0n), 1n):
  match s:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def si_live_succ(s: Bool, rej: Bool, +ts: List<&2, U32>, +ds: List<&2, U32>, +stops: List<&2, U32>, +bq: Nat, +ck: Nat,
    ih: LiveV(Accept.decide(Accept.facts(ts, ds, stops, 0n, 1n+bq, si_pred(ck)), 0n), 1n+bq))
  -> LiveV(Accept.decide(Accept.Facts{s, Nat.is_ge(1n, 1n+(1n+bq)), False{}, rej} <>
      Accept.facts(ts, ds, stops, 1n, 1n+(1n+bq), ck), 0n), 1n+(1n+bq)):
  match s:
    case True{}:
      Unit{}
    case False{}:
      match rej:
        case True{}:
          {==}
        case False{}:
          %si_dec(ts, ds, stops, bq, ck) : LiveV(_, 1n+(1n+bq))
          si_live_bump(Accept.decide(Accept.facts(ts, ds, stops, 0n, 1n+bq, si_pred(ck)), 0n), 1n+bq, ih)

# A round that does not end the job commits fewer tokens than its budget (any verify ids).
def si_live(+ts: List<&2, U32>, +ds: List<&2, U32>, +stops: List<&2, U32>, +bp: Nat, +ck: Nat)
  -> LiveV(Accept.decide(Accept.facts(ts, ds, stops, 0n, 1n+bp, ck), 0n), 1n+bp):
  match ts:
    case Nil{}:
      {==}
    case +t <> rest:
      match ds:
        case Nil{}:
          si_live_nil(Accept.member(stops, t), bp)
        case +d <> more:
          match bp:
            case 0n:
              si_live_zero(Accept.member(stops, t), Bool.or(U32.is_ne(d, t), Nat.is_eq(1n, ck)),
                Accept.facts(rest, more, stops, 1n, 1n, ck))
            case 1n+bq:
              si_live_succ(Accept.member(stops, t), Bool.or(U32.is_ne(d, t), Nat.is_eq(1n, ck)), rest, more, stops, bq, ck,
                si_live(rest, more, stops, bq, si_pred(ck)))

def si_good_eq(~row: List<&2, U32> -> Nat -> U32, +lhs: List<&2, U32>, +stops: List<&2, U32>, +b: Nat,
    +seq: List<&2, U32>, +ts: List<&2, U32>, v: Accept.Verdict, g: Good(~row, lhs, stops, b, seq, ts, v))
  -> {lhs == List.append(&2, U32, List.take(&2, U32, ts, Accept.count(v)),
      Spec.after(~row, Accept.eos(v), Nat.sub(b, Accept.count(v)), stops,
        List.append(&2, U32, seq, List.take(&2, U32, ts, Accept.count(v))))) : List<&2, U32>}:
  match v:
    case Accept.Verdict{+n, +e}:
      g

def si_live_or(v: Accept.Verdict, +b: Nat, h: LiveV(v, b))
  -> {Bool.or(Accept.eos(v), Nat.is_lt(Accept.count(v), b)) == True{} : Bool}:
  match v:
    case Accept.Verdict{+n, e}:
      match e:
        case True{}:
          {==}
        case False{}:
          h

def Laws.round_commits_greedy(row, rinv, seq, ds, stops, bp, checkpoint):
  +TS = Impl.targets(~row, ds, seq, 0n)
  +V = Accept.accept(TS, ds, stops, 1n+bp, checkpoint)
  (si_good_eq(~row, Spec.greedy(~row, 1n+bp, stops, seq), stops, 1n+bp, seq, TS, V,
      si_core(~row, ~rinv, ds, seq, 0n, stops, bp, checkpoint)),
    si_live_or(V, 1n+bp, si_live(TS, ds, stops, bp, checkpoint)))

# ---------------------------------------------------------------- the job invariant

def Inv(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +prompt: List<&2, U32>, +B: Nat, r: Impl.Run) -> Type:
  match r:
    case Impl.Run{st, +o}:
      match st:
        case Round.State{position, +b, anchor, checkpoint, +stopped}:
          {Spec.greedy(~row, B, stops, prompt) ==
            List.append(&2, U32, o, Spec.after(~row, stopped, b, stops, List.append(&2, U32, prompt, o))) : List<&2, U32>} &
          Live(stopped, 0n, b)

def si_live_after(e: Bool, +n: Nat, +b: Nat, lv: Live(e, n, b)) -> Live(e, 0n, Nat.sub(b, n)):
  match e:
    case True{}:
      Unit{}
    case False{}:
      si_lt_sub_pos(n, b, lv)

def si_inv_eq(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +prompt: List<&2, U32>, +B: Nat,
    +o: List<&2, U32>, +TK: List<&2, U32>, +bp: Nat, +n: Nat, +e: Bool,
    g: {Spec.greedy(~row, 1n+bp, stops, List.append(&2, U32, prompt, o)) ==
      List.append(&2, U32, TK, Spec.after(~row, e, Nat.sub(1n+bp, n), stops,
        List.append(&2, U32, List.append(&2, U32, prompt, o), TK))) : List<&2, U32>},
    h: {Spec.greedy(~row, B, stops, prompt) ==
      List.append(&2, U32, o, Spec.greedy(~row, 1n+bp, stops, List.append(&2, U32, prompt, o))) : List<&2, U32>})
  -> {Spec.greedy(~row, B, stops, prompt) ==
      List.append(&2, U32, List.append(&2, U32, o, TK),
        Spec.after(~row, e, Nat.sub(1n+bp, n), stops, List.append(&2, U32, prompt, List.append(&2, U32, o, TK)))) : List<&2, U32>}:
  +G = Spec.greedy(~row, B, stops, prompt)
  +S = Nat.sub(1n+bp, n)
  +X = Spec.after(~row, e, S, stops, List.append(&2, U32, List.append(&2, U32, prompt, o), TK))
  %si_app_assoc(prompt, o, TK) : {G == List.append(&2, U32, List.append(&2, U32, o, TK), Spec.after(~row, e, S, stops, _)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, o, TK), X), List.append(&2, U32, o, List.append(&2, U32, TK, X)),
    si_app_assoc(o, TK, X)) : {G == _ : List<&2, U32>}
  %g : {G == List.append(&2, U32, o, _) : List<&2, U32>}
  h

def si_inv_verdict(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat,
    +interval: Nat, +B: Nat, +W: Nat, +position: Nat, +anchor: Nat, +ck: Nat, +o: List<&2, U32>, +bp: Nat,
    +TS: List<&2, U32>, v: Accept.Verdict,
    g: Good(~row, Spec.greedy(~row, 1n+bp, stops, List.append(&2, U32, prompt, o)), stops, 1n+bp,
      List.append(&2, U32, prompt, o), TS, v),
    lv: LiveV(v, 1n+bp), hw: {Round.writes(Accept.count(v), W) == True{} : Bool},
    h: {Spec.greedy(~row, B, stops, prompt) ==
      List.append(&2, U32, o, Spec.greedy(~row, 1n+bp, stops, List.append(&2, U32, prompt, o))) : List<&2, U32>})
  -> Inv(~row, stops, prompt, B, Impl.Run{Round.commit(Round.writes(Accept.count(v), W), Accept.count(v), Accept.eos(v), W,
      base, interval, position, 1n+bp, anchor, ck), List.append(&2, U32, o, List.take(&2, U32, TS, Accept.count(v)))}):
  match v:
    case Accept.Verdict{+n, +e}:
      %Equal.sym(Bool, Round.writes(n, W), True{}, hw) : Inv(~row, stops, prompt, B,
        Impl.Run{Round.commit(_, n, e, W, base, interval, position, 1n+bp, anchor, ck), List.append(&2, U32, o, List.take(&2, U32, TS, n))})
      (si_inv_eq(~row, stops, prompt, B, o, List.take(&2, U32, TS, n), bp, n, e, g, h), si_live_after(e, n, 1n+bp, lv))

def si_inv_live(~row: List<&2, U32> -> Nat -> U32, ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32},
    +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat, +interval: Nat, +B: Nat, +ds: List<&2, U32>,
    +position: Nat, +anchor: Nat, +ck: Nat, +o: List<&2, U32>, +b: Nat,
    h: {Spec.greedy(~row, B, stops, prompt) ==
      List.append(&2, U32, o, Spec.greedy(~row, b, stops, List.append(&2, U32, prompt, o))) : List<&2, U32>},
    lv: {Nat.is_lt(0n, b) == True{} : Bool})
  -> Inv(~row, stops, prompt, B, Impl.round(~row, prompt, stops, base, interval, ds,
      Impl.Run{Round.State{position, b, anchor, ck, False{}}, o})):
  match b:
    case 0n:
      Empty.absurd(Inv(~row, stops, prompt, B, Impl.round(~row, prompt, stops, base, interval, ds,
        Impl.Run{Round.State{position, 0n, anchor, ck, False{}}, o})), Ar.ar_false_true(lv))
    case 1n+bp:
      +seq = List.append(&2, U32, prompt, o)
      +TS = Impl.targets(~row, ds, seq, 0n)
      si_inv_verdict(~row, prompt, stops, base, interval, B, List.length(&2, U32, ds), position, anchor, ck, o, bp, TS,
        Accept.accept(TS, ds, stops, 1n+bp, ck), si_core(~row, ~rinv, ds, seq, 0n, stops, bp, ck),
        si_live(TS, ds, stops, bp, ck), RoundProof.usable(TS, ds, stops, 1n+bp, ck, si_shaped(~row, ds, seq, 0n)), h)

def si_inv_round(~row: List<&2, U32> -> Nat -> U32, ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32},
    +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat, +interval: Nat, +B: Nat, +ds: List<&2, U32>,
    r: Impl.Run, inv: Inv(~row, stops, prompt, B, r))
  -> Inv(~row, stops, prompt, B, Impl.round(~row, prompt, stops, base, interval, ds, r)):
  match r:
    case Impl.Run{st, +o}:
      match st:
        case Round.State{+position, +b, +anchor, +ck, stopped}:
          match stopped:
            case True{}:
              (h, u) = inv
              (Equal.trans(List<&2, U32>, Spec.greedy(~row, B, stops, prompt), List.append(&2, U32, o, Nil{}),
                List.append(&2, U32, List.append(&2, U32, o, Nil{}), Nil{}), h,
                Equal.cong(List<&2, U32>, List<&2, U32>, x => List.append(&2, U32, x, Nil{}), o, List.append(&2, U32, o, Nil{}),
                  Equal.sym(List<&2, U32>, List.append(&2, U32, o, Nil{}), o, si_app_nil(o)))), Unit{})
            case False{}:
              (h, lv) = inv
              si_inv_live(~row, ~rinv, prompt, stops, base, interval, B, ds, position, anchor, ck, o, b, h, lv)

def si_inv_run(~row: List<&2, U32> -> Nat -> U32, ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32},
    +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat, +interval: Nat, +B: Nat,
    drafts: List<&2, List<&2, U32>>, +r: Impl.Run, inv: Inv(~row, stops, prompt, B, r))
  -> Inv(~row, stops, prompt, B, Impl.run(~row, prompt, stops, base, interval, drafts, r)):
  match drafts:
    case Nil{}:
      inv
    case +ds <> rest:
      si_inv_run(~row, ~rinv, prompt, stops, base, interval, B, rest,
        Impl.round(~row, prompt, stops, base, interval, ds, r),
        si_inv_round(~row, ~rinv, prompt, stops, base, interval, B, ds, r, inv))

def si_inv_start(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +B: Nat,
    +position: Nat, +anchor: Nat, +ck: Nat, pos: {Nat.is_lt(0n, B) == True{} : Bool})
  -> Inv(~row, stops, prompt, B, Impl.Run{Round.State{position, B, anchor, ck, False{}}, Nil{}}):
  (Equal.cong(List<&2, U32>, List<&2, U32>, x => Spec.greedy(~row, B, stops, x), prompt, List.append(&2, U32, prompt, Nil{}),
    Equal.sym(List<&2, U32>, List.append(&2, U32, prompt, Nil{}), prompt, si_app_nil(prompt))), pos)

def si_job_inv(~row: List<&2, U32> -> Nat -> U32, ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32},
    +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat, +interval: Nat, +drafts: List<&2, List<&2, U32>>,
    +position: Nat, +budget: Nat, +anchor: Nat, +checkpoint: Nat, pos: {Nat.is_lt(0n, budget) == True{} : Bool})
  -> Inv(~row, stops, prompt, budget, Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)):
  si_inv_run(~row, ~rinv, prompt, stops, base, interval, budget, drafts,
    Impl.Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}},
    si_inv_start(~row, prompt, stops, budget, position, anchor, checkpoint, pos))

def si_prefix(+G: List<&2, U32>, +o: List<&2, U32>, +X: List<&2, U32>, h: {G == List.append(&2, U32, o, X) : List<&2, U32>})
  -> {List.take(&2, U32, G, List.length(&2, U32, o)) == o : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, G, List.append(&2, U32, o, X), h) : {List.take(&2, U32, _, List.length(&2, U32, o)) == o : List<&2, U32>}
  si_take_app(o, X)

def si_law1(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +prompt: List<&2, U32>, +B: Nat,
    r: Impl.Run, inv: Inv(~row, stops, prompt, B, r))
  -> {Spec.greedy(~row, B, stops, prompt) ==
      List.append(&2, U32, Impl.out(r), Spec.after(~row, Impl.stopped(r), Impl.budget(r), stops,
        List.append(&2, U32, prompt, Impl.out(r)))) : List<&2, U32>} &
    {List.take(&2, U32, Spec.greedy(~row, B, stops, prompt), List.length(&2, U32, Impl.out(r))) == Impl.out(r) : List<&2, U32>} &
    {Bool.or(Impl.stopped(r), Nat.is_lt(0n, Impl.budget(r))) == True{} : Bool}:
  match r:
    case Impl.Run{st, +o}:
      match st:
        case Round.State{position, +b, anchor, ck, stopped}:
          match stopped:
            case True{}:
              (h, u) = inv
              +hh = h
              (hh, si_prefix(Spec.greedy(~row, B, stops, prompt), o, Nil{}, hh), {==})
            case False{}:
              (h, lv) = inv
              +hh = h
              (hh, si_prefix(Spec.greedy(~row, B, stops, prompt), o,
                Spec.greedy(~row, b, stops, List.append(&2, U32, prompt, o)), hh), lv)

def Laws.prefix_of_greedy(row, rinv, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint, positive):
  si_law1(~row, stops, prompt, budget,
    Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint),
    si_job_inv(~row, ~rinv, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint, positive))

# ---------------------------------------------------------------- termination and progress

def Term(r: Impl.Run, +m: Nat) -> Type:
  match r:
    case Impl.Run{st, o}:
      match st:
        case Round.State{position, +b, anchor, checkpoint, stopped}:
          match stopped:
            case True{}:
              Unit
            case False{}:
              {Nat.is_le(b, m) == True{} : Bool} & {Nat.is_lt(0n, b) == True{} : Bool}

def si_le0_lt(+b: Nat, le: {Nat.is_le(b, 0n) == True{} : Bool}, lt: {Nat.is_lt(0n, b) == True{} : Bool}) -> Empty:
  match b:
    case 0n:
      Ar.ar_false_true(lt)
    case 1n+bp:
      Ar.ar_false_true(le)

def si_term_nil(r: Impl.Run, t: Term(r, 0n)) -> {Impl.stopped(r) == True{} : Bool}:
  match r:
    case Impl.Run{st, o}:
      match st:
        case Round.State{position, +b, anchor, checkpoint, stopped}:
          match stopped:
            case True{}:
              {==}
            case False{}:
              (le, lt) = t
              Empty.absurd({False{} == True{} : Bool}, si_le0_lt(b, le, lt))

# 0 < n and bp <= m give (1 + bp) - n <= m
def si_sub_step(+n: Nat, +bp: Nat, +m: Nat, prog: {Nat.is_lt(0n, n) == True{} : Bool}, le: {Nat.is_le(bp, m) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(1n+bp, n), m) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(1n+bp, m) == True{} : Bool}, Ar.ar_false_true(prog))
    case 1n+np:
      Ar.ar_le_trans(Nat.sub(bp, np), bp, m, si_sub_le(bp, np), le)

def si_term_tail(e: Bool, +n: Nat, +bp: Nat, +m: Nat, -P: Nat, -A: Nat, -C: Nat, -O: List<&2, U32>,
    lv: Live(e, n, 1n+bp), prog: {Nat.is_lt(0n, n) == True{} : Bool}, le: {Nat.is_le(bp, m) == True{} : Bool})
  -> Term(Impl.Run{Round.State{P, Nat.sub(1n+bp, n), A, C, e}, O}, m):
  match e:
    case True{}:
      Unit{}
    case False{}:
      +pr = prog
      (si_sub_step(n, bp, m, pr, le), si_lt_sub_pos(n, 1n+bp, lv))

def si_term_verdict(+W: Nat, +base: Nat, +interval: Nat, +position: Nat, +anchor: Nat, +ck: Nat, +o: List<&2, U32>,
    +bp: Nat, +m: Nat, +TS: List<&2, U32>, v: Accept.Verdict, hw: {Round.writes(Accept.count(v), W) == True{} : Bool},
    prog: {Nat.is_lt(0n, Accept.count(v)) == True{} : Bool}, lv: LiveV(v, 1n+bp), le: {Nat.is_le(bp, m) == True{} : Bool})
  -> Term(Impl.Run{Round.commit(Round.writes(Accept.count(v), W), Accept.count(v), Accept.eos(v), W, base, interval,
      position, 1n+bp, anchor, ck), List.append(&2, U32, o, List.take(&2, U32, TS, Accept.count(v)))}, m):
  match v:
    case Accept.Verdict{+n, +e}:
      %Equal.sym(Bool, Round.writes(n, W), True{}, hw) : Term(Impl.Run{Round.commit(_, n, e, W, base, interval,
        position, 1n+bp, anchor, ck), List.append(&2, U32, o, List.take(&2, U32, TS, n))}, m)
      si_term_tail(e, n, bp, m, Nat.add(position, n), Nat.sub(n, 1n), Round.checkpoint(Nat.add(position, n), base, interval, W),
        List.append(&2, U32, o, List.take(&2, U32, TS, n)), lv, prog, le)

def si_term_live(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat,
    +interval: Nat, +ds: List<&2, U32>, +position: Nat, +anchor: Nat, +ck: Nat, +o: List<&2, U32>, +b: Nat, +m: Nat,
    le: {Nat.is_le(b, 1n+m) == True{} : Bool}, lt: {Nat.is_lt(0n, b) == True{} : Bool})
  -> Term(Impl.round(~row, prompt, stops, base, interval, ds, Impl.Run{Round.State{position, b, anchor, ck, False{}}, o}), m):
  match b:
    case 0n:
      Empty.absurd(Term(Impl.round(~row, prompt, stops, base, interval, ds,
        Impl.Run{Round.State{position, 0n, anchor, ck, False{}}, o}), m), Ar.ar_false_true(lt))
    case 1n+bp:
      +seq = List.append(&2, U32, prompt, o)
      +TS = Impl.targets(~row, ds, seq, 0n)
      +sh = si_shaped(~row, ds, seq, 0n)
      si_term_verdict(List.length(&2, U32, ds), base, interval, position, anchor, ck, o, bp, m, TS,
        Accept.accept(TS, ds, stops, 1n+bp, ck), RoundProof.usable(TS, ds, stops, 1n+bp, ck, sh),
        AcceptLaws.accept_progress(TS, ds, stops, 1n+bp, ck, sh), si_live(TS, ds, stops, bp, ck), le)

def si_term_round(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat,
    +interval: Nat, +ds: List<&2, U32>, r: Impl.Run, +m: Nat, t: Term(r, 1n+m))
  -> Term(Impl.round(~row, prompt, stops, base, interval, ds, r), m):
  match r:
    case Impl.Run{st, +o}:
      match st:
        case Round.State{+position, +b, +anchor, +ck, stopped}:
          match stopped:
            case True{}:
              Unit{}
            case False{}:
              (le, lt) = t
              si_term_live(~row, prompt, stops, base, interval, ds, position, anchor, ck, o, b, m, le, lt)

def si_term_run(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +base: Nat,
    +interval: Nat, +drafts: List<&2, List<&2, U32>>, +r: Impl.Run, t: Term(r, List.length(&2, List<&2, U32>, drafts)))
  -> {Impl.stopped(Impl.run(~row, prompt, stops, base, interval, drafts, r)) == True{} : Bool}:
  match drafts:
    case Nil{}:
      si_term_nil(r, t)
    case +ds <> +rest:
      si_term_run(~row, prompt, stops, base, interval, rest, Impl.round(~row, prompt, stops, base, interval, ds, r),
        si_term_round(~row, prompt, stops, base, interval, ds, r, List.length(&2, List<&2, U32>, rest), t))

def Laws.terminates(row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint, positive, enough):
  si_term_run(~row, prompt, stops, base, interval, drafts,
    Impl.Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}}, (enough, positive))

def si_out_stopped(~row: List<&2, U32> -> Nat -> U32, +stops: List<&2, U32>, +prompt: List<&2, U32>, +B: Nat,
    r: Impl.Run, inv: Inv(~row, stops, prompt, B, r), hs: {Impl.stopped(r) == True{} : Bool})
  -> {Impl.out(r) == Spec.greedy(~row, B, stops, prompt) : List<&2, U32>}:
  match r:
    case Impl.Run{st, +o}:
      match st:
        case Round.State{position, +b, anchor, ck, stopped}:
          match stopped:
            case True{}:
              (h, u) = inv
              Equal.sym(List<&2, U32>, Spec.greedy(~row, B, stops, prompt), o,
                Equal.trans(List<&2, U32>, Spec.greedy(~row, B, stops, prompt), List.append(&2, U32, o, Nil{}), o, h, si_app_nil(o)))
            case False{}:
              Empty.absurd({o == Spec.greedy(~row, B, stops, prompt) : List<&2, U32>}, Ar.ar_false_true(hs))

def Laws.speculation_invariance(row, rinv, prompt, stops, base, interval, drafts1, drafts2, position, budget, anchor,
    checkpoint, positive_, enough1, enough2):
  +positive = positive_
  +J1 = Impl.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)
  +J2 = Impl.job(~row, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint)
  +s1 = si_term_run(~row, prompt, stops, base, interval, drafts1,
    Impl.Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}}, (enough1, positive))
  +s2 = si_term_run(~row, prompt, stops, base, interval, drafts2,
    Impl.Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}}, (enough2, positive))
  +o1 = si_out_stopped(~row, stops, prompt, budget, J1,
    si_job_inv(~row, ~rinv, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint, positive), s1)
  +o2 = si_out_stopped(~row, stops, prompt, budget, J2,
    si_job_inv(~row, ~rinv, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint, positive), s2)
  (s1, s2, o1, Equal.trans(List<&2, U32>, Impl.out(J1), Spec.greedy(~row, budget, stops, prompt), Impl.out(J2), o1,
    Equal.sym(List<&2, U32>, Impl.out(J2), Spec.greedy(~row, budget, stops, prompt), o2)))

# x < x + n for n >= 1
def si_lt_add_pos(+x: Nat, +n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(x, n)) == True{} : Bool}:
  match x:
    case 0n:
      pos
    case 1n+xp:
      si_lt_add_pos(xp, n, pos)

def si_prog(+o: List<&2, U32>, +TS: List<&2, U32>, v: Accept.Verdict, prog: {Nat.is_lt(0n, Accept.count(v)) == True{} : Bool},
    bound: {Nat.is_le(Accept.count(v), List.length(&2, U32, TS)) == True{} : Bool})
  -> {Nat.is_lt(List.length(&2, U32, o), List.length(&2, U32, List.append(&2, U32, o, List.take(&2, U32, TS, Accept.count(v))))) == True{} : Bool}:
  match v:
    case Accept.Verdict{+n, e}:
      +TK = List.take(&2, U32, TS, n)
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, o, TK)), Nat.add(List.length(&2, U32, o), List.length(&2, U32, TK)),
        si_len_app(o, TK)) : {Nat.is_lt(List.length(&2, U32, o), _) == True{} : Bool}
      %Equal.sym(Nat, List.length(&2, U32, TK), n, RoundProof.take_length(TS, n, bound)) :
        {Nat.is_lt(List.length(&2, U32, o), Nat.add(List.length(&2, U32, o), _)) == True{} : Bool}
      si_lt_add_pos(List.length(&2, U32, o), n, prog)

def Laws.round_progress(row, prompt, stops, base, interval, ds, position, budget, anchor, checkpoint, emitted):
  +TS = Impl.targets(~row, ds, List.append(&2, U32, prompt, emitted), 0n)
  +sh = si_shaped(~row, ds, List.append(&2, U32, prompt, emitted), 0n)
  si_prog(emitted, TS, Accept.accept(TS, ds, stops, budget, checkpoint),
    AcceptLaws.accept_progress(TS, ds, stops, budget, checkpoint, sh),
    RoundProof.count_le_targets(TS, ds, stops, budget, checkpoint, sh))

def Laws.row_index_leak_differs():
  ({==}, {==}, {==}, {==}, {==})
