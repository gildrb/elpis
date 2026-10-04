# Proofs of bend/rinv_laws.bend: the hypothesis `commit` closed by induction over the rounds, and
# the engine job identified with spec_inv's / spec_inv_tree's job for ref_row.
#
# Invariant LInv of an engine state (device state, emitted ids o, committed state cs): either the job
# has stopped, or there are a committed decode stream u and an anchor a with
#   prompt ++ o == pre ++ u ++ [a]     (pre: the n0 prefilled tokens),
#   position == n0 + |u|,
#   cs == rowinv_link_spec.committed(pf(pre), n0, u).
# Round step: rowinv_served_laws.served_chain_round / served_tree_round turn the served forward's
# verify ids into spec_inv's targets / spec_inv_tree's verify ids for ref_row (so acceptance, device
# state and emitted ids are spec_inv's, by computation); a stopped job emits nothing and keeps its
# state on both sides; a running job's decision is usable (exl3_accept_laws.accept_progress /
# accept_bounds), so its device position moves by count (exl3_round.advance) and the commit is the
# commit of the accepted rows, which rowinv_served_laws.served_commit turns into the 1-row-rounds
# state of u ++ stream(rows). The stream of the accepted rows is a ++ (the first count - 1 emitted
# ids): chain rounds by exl3_accept_laws.accept_explained (the first count - 1 drafts equal their
# targets); tree rounds by exl3_tree_accept_laws.path_matches (every path row after the root carries
# its parent's verify id), with the accepted rows P[0..count) shown equal to the tree path
# gdn_tree_spec.path(par, P[count - 1]) = rowinv_served.pth(tree_shape, last) (the walk follows parent
# links from the root; the path recursion is fuel-stable on legal trees). An eos round stops the job,
# so its commit (window + 1 replayed rows on chains) is never read again.
import Base
import ./rinv_engine.bend as Eng
import ./rinv_laws.bend as Laws
import ./rowinv_link.bend as Link
import ./rowinv_link_spec.bend as LSpec
import ./rowinv_link_laws.bend as LinkLaws
import ./rowinv_link_proof.bend as LinkProof
import ./rowinv_served.bend as Served
import ./rowinv_served_laws.bend as SL
import ./rowinv_served_proof.bend as ServedProof
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_proof.bend as Ar
import ./spec_inv.bend as SIC
import ./spec_inv_spec.bend as SIS
import ./spec_inv_laws.bend as SIL
import ./spec_inv_proof.bend as SIP
import ./spec_inv_tree.bend as SIT
import ./spec_inv_tree_laws.bend as SITL
import ./spec_inv_tree_proof.bend as SITP
import ./exl3_accept_spec.bend as Accept
import ./exl3_accept_laws.bend as AcceptLaws
import ./exl3_accept_proof.bend as AcceptProof
import ./exl3_tree_accept_spec.bend as Tree
import ./exl3_tree_accept_laws.bend as TreeLaws
import ./exl3_tree_path_proof.bend as TPath
import ./exl3_tree_accept_proof.bend as TreeProof
import ./exl3_tree_derive_proof.bend as TreeDerive
import ./exl3_round.bend as Round
import ./exl3_round_spec.bend as RoundSpec
import ./exl3_round_proof.bend as RoundProof
import ./gdn_tree_spec.bend as GtS
import ./attn_tree_spec.bend as AtS

def fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# ---------------------------------------------------------------- lists and numbers

def lt_go_snoc(xs: List<&2, U32>, -p: U32, +y: U32) -> {Eng.last_tok.go(List.append(&2, U32, xs, [y]), p) == y : U32}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      lt_go_snoc(rest, x, y)

def lt_snoc(xs: List<&2, U32>, +y: U32) -> {Eng.last_tok(List.append(&2, U32, xs, [y])) == y : U32}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      lt_go_snoc(rest, x, y)

# The anchor is the last token of pre ++ u ++ [a].
def lt_seq(+pre: List<&2, U32>, +u: List<&2, U32>, +a: U32)
  -> {Eng.last_tok(List.append(&2, U32, pre, List.append(&2, U32, u, [a]))) == a : U32}:
  %LinkProof.ri_app_assoc(~U32, pre, u, [a]) : {Eng.last_tok(_) == a : U32}
  lt_snoc(List.append(&2, U32, pre, u), a)

# p <> xs is its first |xs| tokens followed by its last one.
def split_go(+xs: List<&2, U32>, +p: U32, +n: Nat, h: {List.length(&2, U32, xs) == n : Nat})
  -> {p <> xs == List.append(&2, U32, List.take(&2, U32, p <> xs, n), [Eng.last_tok.go(xs, p)]) : List<&2, U32>}:
  match xs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({[p] == List.append(&2, U32, List.take(&2, U32, [p], 1n+m), [p]) : List<&2, U32>}, Ar.ar_zero_succ(m, h))
    case +y <> +rest:
      match n:
        case 0n:
          Empty.absurd({p <> y <> rest == List.append(&2, U32, List.take(&2, U32, p <> y <> rest, 0n), [Eng.last_tok.go(rest, y)]) : List<&2, U32>},
            Ar.ar_zero_succ(List.length(&2, U32, rest), Equal.sym(Nat, 1n+List.length(&2, U32, rest), 0n, h)))
        case 1n+m:
          Equal.cong(List<&2, U32>, List<&2, U32>, x => p <> x, y <> rest,
            List.append(&2, U32, List.take(&2, U32, y <> rest, m), [Eng.last_tok.go(rest, y)]),
            split_go(rest, y, m, Ar.ar_succ_inj(List.length(&2, U32, rest), m, h)))

# A prompt of n + 1 tokens is its first n tokens followed by its last one.
def split_last(+xs: List<&2, U32>, +n: Nat, h: {List.length(&2, U32, xs) == 1n+n : Nat})
  -> {xs == List.append(&2, U32, List.take(&2, U32, xs, n), [Eng.last_tok(xs)]) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({Nil{} == List.append(&2, U32, List.take(&2, U32, Nil{}, n), [0]) : List<&2, U32>}, Ar.ar_zero_succ(n, h))
    case +x <> +rest:
      split_go(rest, x, n, Ar.ar_succ_inj(List.length(&2, U32, rest), n, h))

def drop_app(~A: Data, xs: List<&2, A>, +ys: List<&2, A>)
  -> {List.drop(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == ys : List<&2, A>}:
  match xs:
    case Nil{}:
      LinkProof.ri_drop_zero(~A, ys)
    case h <> t:
      drop_app(~A, t, ys)

def add_cancel_l(+n: Nat, -x: Nat, -y: Nat, h: {Nat.add(n, x) == Nat.add(n, y) : Nat}) -> {x == y : Nat}:
  match n:
    case 0n:
      h
    case 1n+m:
      add_cancel_l(m, x, y, Ar.ar_succ_inj(Nat.add(m, x), Nat.add(m, y), h))

# Undecided Bool facts.
def not_or_l(+a: Bool, -b: Bool, h: {Bool.not(Bool.or(a, b)) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Ar.ar_false_true(h))
    case False{}:
      {==}

def u32_eq_t(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %SIP.si_word_eq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# The first n drafts of a passing prefix equal their targets (exl3_accept_spec.passes).
def passes_take(+n: Nat, +ts: List<&2, U32>, +ds: List<&2, U32>, +stops: List<&2, U32>, +k: Nat, +b: Nat, +ck: Nat,
    h: {Accept.passes(n, ts, ds, stops, k, b, ck) == True{} : Bool})
  -> {List.take(&2, U32, ds, n) == List.take(&2, U32, ts, n) : List<&2, U32>}:
  match n:
    case 0n:
      Equal.trans(List<&2, U32>, List.take(&2, U32, ds, 0n), Nil{}, List.take(&2, U32, ts, 0n), LinkProof.ri_take_nil(~U32, ds),
        Equal.sym(List<&2, U32>, List.take(&2, U32, ts, 0n), Nil{}, LinkProof.ri_take_nil(~U32, ts)))
    case 1n+m:
      match ts:
        case Nil{}:
          Empty.absurd({List.take(&2, U32, ds, 1n+m) == Nil{} : List<&2, U32>}, Ar.ar_false_true(h))
        case +t <> +rest:
          match ds:
            case Nil{}:
              Empty.absurd({Nil{} == t <> List.take(&2, U32, rest, m) : List<&2, U32>}, Ar.ar_false_true(h))
            case +d <> +more:
              +A1 = Bool.not(Accept.member(stops, t))
              +A2 = Bool.not(Nat.is_ge(1n+k, b))
              +A3 = Bool.not(Bool.or(U32.is_ne(d, t), Nat.is_eq(1n+k, ck)))
              +A4 = Accept.passes(m, rest, more, stops, 1n+k, b, ck)
              +h1 = Ar.ar_and_r(A1, Bool.and(A2, Bool.and(A3, A4)), h)
              +h2 = Ar.ar_and_r(A2, Bool.and(A3, A4), h1)
              +h3 = Ar.ar_and_l(A3, A4, h2)
              +h4 = Ar.ar_and_r(A3, A4, h2)
              LinkProof.ri_cong_cons(~U32, d, t, List.take(&2, U32, more, m), List.take(&2, U32, rest, m),
                SIP.si_u32_eq(d, t, not_or_l(U32.is_ne(d, t), Nat.is_eq(1n+k, ck), h3)),
                passes_take(m, rest, more, stops, 1n+k, b, ck, h4))

# s, s + 1, .. read from x <> xs is xs read from s - 1 ..
def stream_shift(+k: Nat, +x: U32, +xs: List<&2, U32>, +s: Nat)
  -> {Link.stream(x <> xs, Served.seqn(k, 1n+s)) == Link.stream(xs, Served.seqn(k, s)) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Link.at(~U32, ~0, xs, s) <> y,
        Link.stream(x <> xs, Served.seqn(k1, 1n+(1n+s))), Link.stream(xs, Served.seqn(k1, 1n+s)), stream_shift(k1, x, xs, 1n+s))

# The tokens along the chain path 0 .. k - 1 are the first k tokens.
def stream_take(+xs: List<&2, U32>, +k: Nat, h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool})
  -> {Link.stream(xs, Served.seqn(k, 0n)) == List.take(&2, U32, xs, k) : List<&2, U32>}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+k1:
          Empty.absurd({Link.stream(Nil{}, Served.seqn(1n+k1, 0n)) == Nil{} : List<&2, U32>}, Ar.ar_false_true(h))
    case +x <> +rest:
      match k:
        case 0n:
          {==}
        case 1n+k1:
          Equal.cong(List<&2, U32>, List<&2, U32>, y => x <> y, Link.stream(x <> rest, Served.seqn(k1, 1n)), List.take(&2, U32, rest, k1),
            Equal.trans(List<&2, U32>, Link.stream(x <> rest, Served.seqn(k1, 1n)), Link.stream(rest, Served.seqn(k1, 0n)),
              List.take(&2, U32, rest, k1), stream_shift(k1, x, rest, 0n), stream_take(rest, k1, h)))

def full_succ(b: Bool, +c: Nat, +w: Nat) -> {Round.full(b, 1n+c, 1n+w) == 1n+Round.full(b, c, w) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def steps_w0(+c1: Nat, h: {Nat.is_le(1n+c1, 1n) == True{} : Bool}) -> {Round.full(Nat.is_gt(1n+c1, 0n), 1n+c1, 0n) == 1n+c1 : Nat}:
  match c1:
    case 0n:
      {==}
    case 1n+c2:
      Empty.absurd({Round.full(Nat.is_gt(1n+(1n+c2), 0n), 1n+(1n+c2), 0n) == 1n+(1n+c2) : Nat}, Ar.ar_false_true(h))

# A usable live chain decision replays exactly count rows (exl3_round.steps).
def steps_ok(+c: Nat, +w: Nat, h: {Nat.is_le(c, 1n+w) == True{} : Bool}) -> {Round.full(Nat.is_gt(c, w), c, w) == c : Nat}:
  match c:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n+w1:
          {==}
    case 1n+c1:
      match w:
        case 0n:
          steps_w0(c1, h)
        case 1n+w1:
          Equal.trans(Nat, Round.full(Nat.is_gt(c1, w1), 1n+c1, 1n+w1), 1n+Round.full(Nat.is_gt(c1, w1), c1, w1), 1n+c1,
            full_succ(Nat.is_gt(c1, w1), c1, w1),
            Equal.cong(Nat, Nat, x => 1n+x, Round.full(Nat.is_gt(c1, w1), c1, w1), c1, steps_ok(c1, w1, h)))

# ---------------------------------------------------------------- the reference row function

def rr(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, p: List<&2, U32>, r: Nat)
  -> {Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, p, r) ==
      Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, p, 0n) : U32}:
  {==}

def isr(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, p: List<&2, U32>, r: Nat)
  -> {Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}:
  {==}

# ---------------------------------------------------------------- the invariant

def LiveU(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +pre: List<&2, U32>, +p: Nat, +o: List<&2, U32>, +cs: List<&2, C>) -> Type:
  &u: List<&2, U32> -> &a: U32 ->
    {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>} &
    {p == Nat.add(n0, List.length(&2, U32, u)) : Nat} &
    {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>}

def LInv(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +pre: List<&2, U32>, e: Eng.Eng<C>) -> Type:
  match e:
    case Eng.Eng{r, +cs}:
      match r:
        case SIC.Run{st, +o}:
          match st:
            case Round.State{+p, b, an, ck, s}:
              match s:
                case True{}:
                  Unit
                case False{}:
                  LiveU(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, p, o, cs)

# The next live state: count = 1 + c' committed ids of the verify ids ts, the accepted rows' stream
# being a followed by the first c' of them.
def next_seq(+prompt: List<&2, U32>, +o: List<&2, U32>, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +ts: List<&2, U32>,
    +c: Nat, +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hc: {Nat.is_lt(c, List.length(&2, U32, ts)) == True{} : Bool})
  -> {List.append(&2, U32, prompt, List.append(&2, U32, o, List.take(&2, U32, ts, 1n+c))) ==
      List.append(&2, U32, pre, List.append(&2, U32, List.append(&2, U32, u, a <> List.take(&2, U32, ts, c)), [Link.at(~U32, ~0, ts, c)])) : List<&2, U32>}:
  +X = List.take(&2, U32, ts, 1n+c)
  +T = List.take(&2, U32, ts, c)
  +L = Link.at(~U32, ~0, ts, c)
  +M = List.append(&2, U32, pre, List.append(&2, U32, u, a <> List.append(&2, U32, T, [L])))
  Equal.trans(List<&2, U32>, List.append(&2, U32, prompt, List.append(&2, U32, o, X)), M,
    List.append(&2, U32, pre, List.append(&2, U32, List.append(&2, U32, u, a <> T), [L])),
    Equal.trans(List<&2, U32>, List.append(&2, U32, prompt, List.append(&2, U32, o, X)), List.append(&2, U32, List.append(&2, U32, prompt, o), X), M,
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, prompt, o), X), List.append(&2, U32, prompt, List.append(&2, U32, o, X)),
        LinkProof.ri_app_assoc(~U32, prompt, o, X)),
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, prompt, o), X),
        List.append(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), X), M,
        Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, y, X), List.append(&2, U32, prompt, o),
          List.append(&2, U32, pre, List.append(&2, U32, u, [a])), hseq),
        Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), X),
          List.append(&2, U32, pre, List.append(&2, U32, List.append(&2, U32, u, [a]), X)), M,
          LinkProof.ri_app_assoc(~U32, pre, List.append(&2, U32, u, [a]), X),
          Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, pre, y), List.append(&2, U32, List.append(&2, U32, u, [a]), X),
            List.append(&2, U32, u, a <> List.append(&2, U32, T, [L])),
            Equal.trans(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, [a]), X), List.append(&2, U32, u, a <> X),
              List.append(&2, U32, u, a <> List.append(&2, U32, T, [L])),
              LinkProof.ri_app_assoc(~U32, u, [a], X),
              Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, u, a <> y), X, List.append(&2, U32, T, [L]),
                LinkProof.ri_take_snoc(~U32, ~0, ts, c, hc))))))),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, pre, y), List.append(&2, U32, u, a <> List.append(&2, U32, T, [L])),
      List.append(&2, U32, List.append(&2, U32, u, a <> T), [L]),
      Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, a <> T), [L]), List.append(&2, U32, u, a <> List.append(&2, U32, T, [L])),
        LinkProof.ri_app_assoc(~U32, u, a <> T, [L]))))

def next_pos(+n0: Nat, +p: Nat, +u: List<&2, U32>, +a: U32, +ts: List<&2, U32>, +c: Nat,
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat}, +hc: {Nat.is_le(c, List.length(&2, U32, ts)) == True{} : Bool})
  -> {Nat.add(p, 1n+c) == Nat.add(n0, List.length(&2, U32, List.append(&2, U32, u, a <> List.take(&2, U32, ts, c)))) : Nat}:
  +U = List.length(&2, U32, u)
  +T = List.take(&2, U32, ts, c)
  Equal.trans(Nat, Nat.add(p, 1n+c), Nat.add(Nat.add(n0, U), 1n+c), Nat.add(n0, List.length(&2, U32, List.append(&2, U32, u, a <> T))),
    Equal.cong(Nat, Nat, x => Nat.add(x, 1n+c), p, Nat.add(n0, U), hpos),
    Equal.trans(Nat, Nat.add(Nat.add(n0, U), 1n+c), Nat.add(n0, Nat.add(U, 1n+c)), Nat.add(n0, List.length(&2, U32, List.append(&2, U32, u, a <> T))),
      Ar.ar_add_assoc(n0, U, 1n+c),
      Equal.cong(Nat, Nat, x => Nat.add(n0, x), Nat.add(U, 1n+c), List.length(&2, U32, List.append(&2, U32, u, a <> T)),
        Equal.trans(Nat, Nat.add(U, 1n+c), Nat.add(U, 1n+List.length(&2, U32, T)), List.length(&2, U32, List.append(&2, U32, u, a <> T)),
          Equal.cong(Nat, Nat, x => Nat.add(U, 1n+x), c, List.length(&2, U32, T),
            Equal.sym(Nat, List.length(&2, U32, T), c, LinkProof.ri_len_take(~U32, ts, c, hc))),
          Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, u, a <> T)), Nat.add(U, 1n+List.length(&2, U32, T)),
            LinkProof.ri_len_app(~U32, u, a <> T))))))

# ---------------------------------------------------------------- chain rounds

# The live chain round once the verify ids are spec_inv's: the commit target.
def CMc(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +cs: List<&2, C>, +r: Nat, +base: Nat, +toks: List<&2, U32>) -> List<&2, C>:
  Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
    cs, 0n, Served.pth(Served.Chain{}, r), Served.Chain{}, base, List.length(&2, U32, toks), Link.embs(~V, ~emb, toks))

# The committed state after a live chain round committing 1 + c ids.
def c_commit(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, +stops: List<&2, U32>, +ds: List<&2, U32>, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat,
    +ck: Nat, +cs: List<&2, C>, +ts: List<&2, U32>, +c: Nat, +e: Bool,
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hbound: {Nat.is_le(1n+c, 1n+List.length(&2, U32, ds)) == True{} : Bool},
    +hexp: {Accept.explains(1n+c, e, ts, ds, stops, b, ck) == True{} : Bool})
  -> {CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs, c, p, a <> ds) ==
      LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
        List.append(&2, U32, u, a <> List.take(&2, U32, ts, c))) : List<&2, C>}:
  +hrow = Equal.trans(Bool, Nat.is_lt(c, 1n+List.length(&2, U32, ds)), Nat.is_le(1n+c, 1n+List.length(&2, U32, ds)), True{},
    Ar.ar_lt_succ_le(c, 1n+List.length(&2, U32, ds)), hbound)
  +hpass = Ar.ar_and_l(Accept.passes(c, ts, ds, stops, 0n, b, ck), Accept.halts(c, ts, ds, stops, 0n, b, ck, e), hexp)
  %Equal.sym(Nat, p, Nat.add(n0, List.length(&2, U32, u)), hpos) :
    {CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs, c, _, a <> ds) ==
      LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
        List.append(&2, U32, u, a <> List.take(&2, U32, ts, c))) : List<&2, C>}
  Equal.trans(List<&2, C>, CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs, c, Nat.add(n0, List.length(&2, U32, u)), a <> ds),
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
      List.append(&2, U32, u, Link.stream(a <> ds, Served.pth(Served.Chain{}, c)))),
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
      List.append(&2, U32, u, a <> List.take(&2, U32, ts, c))),
    SL.served_commit(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, pf(pre), n0, u, cs, a <> ds, Served.Chain{}, c,
      hcs, {==}, small, hrow),
    Equal.cong(List<&2, U32>, List<&2, C>,
      y => LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, y)),
      Link.stream(a <> ds, Served.pth(Served.Chain{}, c)), a <> List.take(&2, U32, ts, c),
      Equal.trans(List<&2, U32>, Link.stream(a <> ds, Served.seqn(1n+c, 0n)), a <> List.take(&2, U32, ds, c), a <> List.take(&2, U32, ts, c),
        stream_take(a <> ds, 1n+c, hbound),
        Equal.cong(List<&2, U32>, List<&2, U32>, y => a <> y, List.take(&2, U32, ds, c), List.take(&2, U32, ts, c),
          passes_take(c, ts, ds, stops, 0n, b, ck, hpass)))))

# GV: the invariant after the live chain round's verdict v on verify ids ts.
def GVc(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +cbase: Nat, +interval: Nat, +ds: List<&2, U32>, +pre: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat,
    +o: List<&2, U32>, +cs: List<&2, C>, +ts: List<&2, U32>, +wr: Bool, +c: Nat, +e: Bool) -> Type:
  LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
    Eng.Eng{SIC.Run{Round.commit(wr, c, e, List.length(&2, U32, ds), cbase, interval, p, b, an, ck),
        List.append(&2, U32, o, List.take(&2, U32, ts, c))},
      Eng.keep(~C, wr, CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs,
        Nat.sub(Round.steps(c, e, List.length(&2, U32, ds)), 1n), p, a <> ds), cs)})

# The usable live chain decision: eos stops the job; otherwise the invariant moves to u ++ a <> T.
def c_eos(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, e: Bool, +c: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +ds: List<&2, U32>,
    +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>, +cs: List<&2, C>,
    +ts: List<&2, U32>,
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hlen: {List.length(&2, U32, ts) == 1n+List.length(&2, U32, ds) : Nat},
    +hprog: {Nat.is_lt(0n, c) == True{} : Bool},
    +hbound: {Nat.is_le(c, 1n+List.length(&2, U32, ds)) == True{} : Bool},
    +hexp: {Accept.explains(c, e, ts, ds, stops, b, ck) == True{} : Bool})
  -> GVc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, ds, pre, a, p, b, an, ck, o, cs, ts,
      True{}, c, e):
  match e:
    case True{}:
      Unit{}
    case False{}:
      match c:
        case 0n:
          Empty.absurd(GVc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, ds, pre, a, p, b, an, ck,
            o, cs, ts, True{}, 0n, False{}), Ar.ar_false_true(hprog))
        case 1n+c1:
          +W = List.length(&2, U32, ds)
          +T = List.take(&2, U32, ts, c1)
          +hlt = Equal.trans(Bool, Nat.is_lt(c1, List.length(&2, U32, ts)), Nat.is_lt(c1, 1n+W), True{},
            Equal.cong(Nat, Bool, x => Nat.is_lt(c1, x), List.length(&2, U32, ts), 1n+W, hlen),
            Equal.trans(Bool, Nat.is_lt(c1, 1n+W), Nat.is_le(1n+c1, 1n+W), True{}, Ar.ar_lt_succ_le(c1, 1n+W), hbound))
          +hle = Ar.ar_lt_le(c1, List.length(&2, U32, ts), hlt)
          %Equal.sym(Nat, Round.full(Nat.is_gt(1n+c1, W), 1n+c1, W), 1n+c1, steps_ok(1n+c1, W, hbound)) :
            LiveU(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, Nat.add(p, 1n+c1),
              List.append(&2, U32, o, List.take(&2, U32, ts, 1n+c1)),
              CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs, Nat.sub(_, 1n), p, a <> ds))
          %Equal.sym(Nat, Nat.sub(c1, 0n), c1, Ar.ar_sub_zero_r(c1)) :
            LiveU(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, Nat.add(p, 1n+c1),
              List.append(&2, U32, o, List.take(&2, U32, ts, 1n+c1)),
              CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs, _, p, a <> ds))
          (List.append(&2, U32, u, a <> T), (Link.at(~U32, ~0, ts, c1),
            (next_seq(prompt, o, pre, u, a, ts, c1, hseq, hlt),
              (next_pos(n0, p, u, a, ts, c1, hpos, hle),
                c_commit(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, stops, ds, pre, u, a, p, b, ck, cs, ts, c1,
                  False{}, small, hpos, hcs, hbound, hexp)))))

def c_verdict(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, v: Accept.Verdict, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +ds: List<&2, U32>,
    +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>, +cs: List<&2, C>,
    +ts: List<&2, U32>,
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hlen: {List.length(&2, U32, ts) == 1n+List.length(&2, U32, ds) : Nat},
    +hprog: {Nat.is_lt(0n, Accept.count(v)) == True{} : Bool},
    +hbound: {Nat.is_le(Accept.count(v), 1n+List.length(&2, U32, ds)) == True{} : Bool},
    +hexp: {Accept.explains(Accept.count(v), Accept.eos(v), ts, ds, stops, b, ck) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.Eng{SIC.Run{Round.advance(Accept.count(v), Accept.eos(v), List.length(&2, U32, ds), cbase, interval, Round.State{p, b, an, ck, False{}}),
          List.append(&2, U32, o, RoundSpec.committed(ts, Accept.count(v), False{}))},
        Eng.keep(~C, Eng.live(False{}, Accept.count(v), List.length(&2, U32, ds)),
          CMc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, cs,
            Nat.sub(Round.steps(Accept.count(v), Accept.eos(v), List.length(&2, U32, ds)), 1n), p, a <> ds), cs)}):
  match v:
    case Accept.Verdict{+c, +e}:
      %Equal.sym(Bool, Round.writes(c, List.length(&2, U32, ds)), True{}, Ar.ar_and_intro(Nat.is_lt(0n, c), Nat.is_le(c, 1n+List.length(&2, U32, ds)), hprog, hbound)) :
        GVc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, ds, pre, a, p, b, an, ck, o, cs, ts, _, c, e)
      c_eos(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, e, c, prompt, stops, cbase, interval, ds, pre, u, a, p, b, an,
        ck, o, cs, ts, small, hseq, hpos, hcs, hlen, hprog, hbound, hexp)

# The round goal with the verify ids and rows abstracted.
def GAc(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +ds: List<&2, U32>,
    +pre: List<&2, U32>, +toks: List<&2, U32>, +ts: List<&2, U32>, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>,
    +cs: List<&2, C>) -> Type:
  {Eng.run(~C, Eng.chain_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, ds, toks, ts,
      Round.State{p, b, an, ck, False{}}, o, cs)) ==
    SIC.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, ds,
      SIC.Run{Round.State{p, b, an, ck, False{}}, o}) : SIC.Run} &
  LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
    Eng.chain_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, ds, toks, ts,
      Round.State{p, b, an, ck, False{}}, o, cs))

def c_live(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +ds: List<&2, U32>, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>,
    +cs: List<&2, C>,
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool},
    +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>})
  -> GAc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, ds, pre,
      Eng.last_tok(List.append(&2, U32, prompt, o)) <> ds,
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, p, Eng.last_tok(List.append(&2, U32, prompt, o)) <> ds, Served.Chain{}),
      p, b, an, ck, o, cs):
  +SEQ = List.append(&2, U32, prompt, o)
  +SEQ2 = List.append(&2, U32, pre, List.append(&2, U32, u, [a]))
  +LTK = Eng.last_tok(SEQ)
  +TS = SIC.targets(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), ds, SEQ, 0n)
  +hlt = Equal.trans(U32, a, Eng.last_tok(SEQ2), LTK, Equal.sym(U32, Eng.last_tok(SEQ2), a, lt_seq(pre, u, a)),
    Equal.cong(List<&2, U32>, U32, x => Eng.last_tok(x), SEQ2, SEQ, Equal.sym(List<&2, U32>, SEQ, SEQ2, hseq)))
  %hlt : GAc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, ds, pre, _ <> ds,
    Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
      ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, p, _ <> ds, Served.Chain{}), p, b, an, ck, o, cs)
  %Equal.sym(Nat, p, Nat.add(n0, List.length(&2, U32, u)), hpos) :
    GAc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, ds, pre, a <> ds,
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, _, a <> ds, Served.Chain{}), p, b, an, ck, o, cs)
  %Equal.trans(List<&2, U32>, TS,
      SIC.targets(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), ds, SEQ2, 0n),
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), a <> ds, Served.Chain{}),
      Equal.cong(List<&2, U32>, List<&2, U32>,
        x => SIC.targets(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), ds, x, 0n), SEQ, SEQ2, hseq),
      SL.served_chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0,
        ~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0),
        ~isr(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), pre, u, a, ds, cs, hpre, hcs, small)) :
    GAc(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, ds, pre, a <> ds, _,
      p, b, an, ck, o, cs)
  +hlen = SIP.si_shaped(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), ds, SEQ, 0n)
  ({==}, c_verdict(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, Accept.accept(TS, ds, stops, b, ck),
    prompt, stops, cbase, interval, ds, pre, u, a, p, b, an, ck, o, cs, TS, small, hseq, hpos, hcs, hlen,
    AcceptLaws.accept_progress(TS, ds, stops, b, ck, hlen),
    snd({Nat.is_le(Accept.count(Accept.accept(TS, ds, stops, b, ck)), List.length(&2, U32, TS)) == True{} : Bool},
      {Nat.is_le(Accept.count(Accept.accept(TS, ds, stops, b, ck)), 1n+List.length(&2, U32, ds)) == True{} : Bool},
      AcceptLaws.accept_bounds(TS, ds, stops, b, ck, hlen)),
    AcceptLaws.accept_explained(TS, ds, stops, b, ck, hlen)))

# One chain round from any state satisfying the invariant.
def c_round0(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, +ds: List<&2, U32>, e: Eng.Eng<C>,
    inv: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e),
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool})
  -> {Eng.run(~C, Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e)) ==
      SIC.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, ds,
        Eng.run(~C, e)) : SIC.Run} &
    LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e)):
  match e:
    case Eng.Eng{r, +cs}:
      match r:
        case SIC.Run{st, +o}:
          match st:
            case Round.State{+p, +b, +an, +ck, s}:
              match s:
                case True{}:
                  ({==}, Unit{})
                case False{}:
                  (u, i1) = inv
                  (a, i2) = i1
                  (hseq, i3) = i2
                  (hpos, hcs) = i3
                  c_live(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, ds, pre,
                    u, a, p, b, an, ck, o, cs, small, hpre, hseq, hpos, hcs)

# Reorder the round facts and chain the spec-side run state.
def swap_run(~C: Data, -E1: Eng.Eng<C>, -X: SIC.Run, -R: SIC.Run, -I1: Type, -F: SIC.Run -> SIC.Run,
    pr: {Eng.run(~C, E1) == F(X) : SIC.Run} & I1, heq: {X == R : SIC.Run})
  -> I1 & {Eng.run(~C, E1) == F(R) : SIC.Run}:
  (h1, i1) = pr
  (i1, Equal.trans(SIC.Run, Eng.run(~C, E1), F(X), F(R), h1, Equal.cong(SIC.Run, SIC.Run, F, X, R, heq)))

# One chain round: the invariant and the spec-side run state move together.
def c_round(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, +ds: List<&2, U32>, +e: Eng.Eng<C>, +R: SIC.Run,
    ji: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e) & {Eng.run(~C, e) == R : SIC.Run},
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e)) &
    {Eng.run(~C, Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e)) ==
      SIC.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, ds,
        R) : SIC.Run}:
  (inv, heq) = ji
  swap_run(~C, Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e),
    Eng.run(~C, e), R,
    LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e)),
    x => SIC.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, ds, x),
    c_round0(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, ds,
      e, inv, small), heq)

def c_run(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, drafts: List<&2, List<&2, U32>>, +e: Eng.Eng<C>, +R: SIC.Run,
    ji: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e) & {Eng.run(~C, e) == R : SIC.Run},
    +small: {Eng.all_small(drafts) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.chain_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, drafts, e)) &
    {Eng.run(~C, Eng.chain_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, drafts, e)) ==
      SIC.run(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, drafts,
        R) : SIC.Run}:
  match drafts:
    case Nil{}:
      ji
    case +ds <> +rest:
      c_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, rest,
        Eng.chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e),
        SIC.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, ds, R),
        c_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, ds,
          e, R, ji, Ar.ar_and_l(Nat.is_le(List.length(&2, U32, ds), 7n), Eng.all_small(rest), small)),
        Ar.ar_and_r(Nat.is_le(List.length(&2, U32, ds), 7n), Eng.all_small(rest), small))

# ---------------------------------------------------------------- the job start and the closed form

def pre_len(+prompt: List<&2, U32>, +n0: Nat, +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat})
  -> {List.length(&2, U32, List.take(&2, U32, prompt, n0)) == n0 : Nat}:
  LinkProof.ri_len_take(~U32, prompt, n0,
    Equal.trans(Bool, Nat.is_le(n0, List.length(&2, U32, prompt)), Nat.is_le(n0, 1n+n0), True{},
      Equal.cong(Nat, Bool, x => Nat.is_le(n0, x), List.length(&2, U32, prompt), 1n+n0, hlen), Ar.ar_h_le_succ(n0)))

# The job's first state satisfies the invariant: u = [], a = the last prompt token.
def start_inv(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +budget: Nat, +anchor: Nat, +checkpoint: Nat, +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.Eng{SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}}, pf(List.take(&2, U32, prompt, n0))}):
  +pre = List.take(&2, U32, prompt, n0)
  (Nil{}, (Eng.last_tok(prompt),
    (Equal.trans(List<&2, U32>, List.append(&2, U32, prompt, Nil{}), prompt, List.append(&2, U32, pre, [Eng.last_tok(prompt)]),
      LinkProof.ri_app_nil(~U32, prompt), split_last(prompt, n0, hlen)),
     (LinkProof.ri_zr(n0),
      Equal.sym(List<&2, C>, LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, Nil{}),
        pf(pre), LinkLaws.committed_prefill(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0))))))

# The closed form of a running state: its committed decode stream is the last prompt token followed by
# the emitted ids, without the last one.
def CL(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +e: Eng.Eng<C>) -> Type:
  {Eng.cs(~C, e) ==
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
      n0, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, Eng.out(~C, e)), n0), List.length(&2, U32, Eng.out(~C, e)))) : List<&2, C>} &
  {Eng.position(~C, e) == Nat.add(n0, List.length(&2, U32, Eng.out(~C, e))) : Nat}

def close_u(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +p: Nat, +o: List<&2, U32>, +cs: List<&2, C>, +u: List<&2, U32>, +a: U32,
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, List.take(&2, U32, prompt, n0), List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
      n0, u) : List<&2, C>})
  -> {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
        n0, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), List.length(&2, U32, o))) : List<&2, C>} &
    {p == Nat.add(n0, List.length(&2, U32, o)) : Nat}:
  +pre = List.take(&2, U32, prompt, n0)
  +hpre = pre_len(prompt, n0, hlen)
  +U = List.length(&2, U32, u)
  +O = List.length(&2, U32, o)
  # |prompt ++ o| == |pre ++ u ++ [a]|, so |o| == |u|
  +hl1 = Equal.cong(List<&2, U32>, Nat, x => List.length(&2, U32, x), List.append(&2, U32, prompt, o),
    List.append(&2, U32, pre, List.append(&2, U32, u, [a])), hseq)
  +hl2 = Equal.trans(Nat, 1n+Nat.add(n0, O), List.length(&2, U32, List.append(&2, U32, prompt, o)), Nat.add(n0, Nat.add(U, 1n)),
    Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, prompt, o)), 1n+Nat.add(n0, O),
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, prompt, o)), Nat.add(List.length(&2, U32, prompt), O), 1n+Nat.add(n0, O),
        LinkProof.ri_len_app(~U32, prompt, o),
        Equal.cong(Nat, Nat, x => Nat.add(x, O), List.length(&2, U32, prompt), 1n+n0, hlen))),
    Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, prompt, o)), List.length(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a]))),
      Nat.add(n0, Nat.add(U, 1n)), hl1,
      Equal.trans(Nat, List.length(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a]))),
        Nat.add(List.length(&2, U32, pre), List.length(&2, U32, List.append(&2, U32, u, [a]))), Nat.add(n0, Nat.add(U, 1n)),
        LinkProof.ri_len_app(~U32, pre, List.append(&2, U32, u, [a])),
        Equal.trans(Nat, Nat.add(List.length(&2, U32, pre), List.length(&2, U32, List.append(&2, U32, u, [a]))),
          Nat.add(n0, List.length(&2, U32, List.append(&2, U32, u, [a]))), Nat.add(n0, Nat.add(U, 1n)),
          Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, U32, List.append(&2, U32, u, [a]))), List.length(&2, U32, pre), n0, hpre),
          Equal.cong(Nat, Nat, x => Nat.add(n0, x), List.length(&2, U32, List.append(&2, U32, u, [a])), Nat.add(U, 1n),
            LinkProof.ri_len_app(~U32, u, [a]))))))
  +hl3 = Equal.trans(Nat, Nat.add(n0, Nat.add(U, 1n)), Nat.add(n0, 1n+U), 1n+Nat.add(n0, U),
    Equal.cong(Nat, Nat, x => Nat.add(n0, x), Nat.add(U, 1n), 1n+U,
      Equal.trans(Nat, Nat.add(U, 1n), 1n+Nat.add(U, 0n), 1n+U, Ar.ar_add_succ_r(U, 0n),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(U, 0n), U, Ar.ar_add_zero_r(U)))),
    Ar.ar_add_succ_r(n0, U))
  +hou = add_cancel_l(n0, O, U, Ar.ar_succ_inj(Nat.add(n0, O), Nat.add(n0, U),
    Equal.trans(Nat, 1n+Nat.add(n0, O), Nat.add(n0, Nat.add(U, 1n)), 1n+Nat.add(n0, U), hl2, hl3)))
  # drop(prompt ++ o, n0) == u ++ [a] and take(u ++ [a], |o|) == u
  +hdrop = Equal.trans(List<&2, U32>, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0),
    List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), List.length(&2, U32, pre)), List.append(&2, U32, u, [a]),
    Equal.trans(List<&2, U32>, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0),
      List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), n0),
      List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), List.length(&2, U32, pre)),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => List.drop(&2, U32, x, n0), List.append(&2, U32, prompt, o),
        List.append(&2, U32, pre, List.append(&2, U32, u, [a])), hseq),
      Equal.cong(Nat, List<&2, U32>, x => List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, u, [a])), x), n0,
        List.length(&2, U32, pre), Equal.sym(Nat, List.length(&2, U32, pre), n0, hpre))),
    drop_app(~U32, pre, List.append(&2, U32, u, [a])))
  +hstream = Equal.trans(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), O),
    List.take(&2, U32, List.append(&2, U32, u, [a]), U), u,
    Equal.trans(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), O),
      List.take(&2, U32, List.append(&2, U32, u, [a]), O), List.take(&2, U32, List.append(&2, U32, u, [a]), U),
      Equal.cong(List<&2, U32>, List<&2, U32>, x => List.take(&2, U32, x, O), List.drop(&2, U32, List.append(&2, U32, prompt, o), n0),
        List.append(&2, U32, u, [a]), hdrop),
      Equal.cong(Nat, List<&2, U32>, x => List.take(&2, U32, List.append(&2, U32, u, [a]), x), O, U, hou)),
    SIP.si_take_app(u, [a]))
  (Equal.trans(List<&2, C>, cs,
      LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u),
      LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
        List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), O)),
      hcs,
      Equal.cong(List<&2, U32>, List<&2, C>,
        x => LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, x), u,
        List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), O),
        Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), O), u, hstream))),
   Equal.trans(Nat, p, Nat.add(n0, U), Nat.add(n0, O), hpos,
     Equal.cong(Nat, Nat, x => Nat.add(n0, x), U, O, Equal.sym(Nat, O, U, hou))))

def close_live(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +p: Nat, +o: List<&2, U32>, +cs: List<&2, C>,
    lu: LiveU(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0), p, o, cs))
  -> {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
        n0, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, o), n0), List.length(&2, U32, o))) : List<&2, C>} &
    {p == Nat.add(n0, List.length(&2, U32, o)) : Nat}:
  (u, l1) = lu
  (a, l2) = l1
  (hseq, l3) = l2
  (hpos, hcs) = l3
  close_u(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, hlen, p, o, cs, u, a, hseq, hpos, hcs)

# A running state satisfying the invariant is in closed form.
def close_of(~V: Data, ~E: Data, ~C: Data, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, e: Eng.Eng<C>,
    inv: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0), e),
    running: {SIC.stopped(Eng.run(~C, e)) == False{} : Bool})
  -> CL(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, e):
  match e:
    case Eng.Eng{r, +cs}:
      match r:
        case SIC.Run{st, +o}:
          match st:
            case Round.State{+p, b, an, ck, s}:
              match s:
                case True{}:
                  Empty.absurd(CL(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt,
                    Eng.Eng{SIC.Run{Round.State{p, b, an, ck, True{}}, o}, cs}), Ar.ar_true_false(running))
                case False{}:
                  close_live(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, hlen, p, o, cs, inv)

# ---------------------------------------------------------------- chain laws

def c_job(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    drafts: List<&2, List<&2, U32>>, +budget: Nat, +anchor: Nat, +checkpoint: Nat,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, small: {Eng.all_small(drafts) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        drafts, budget, anchor, checkpoint)) &
    {Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        drafts, budget, anchor, checkpoint)) ==
      SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        drafts, n0, budget, anchor, checkpoint) : SIC.Run}:
  c_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval,
    List.take(&2, U32, prompt, n0), pre_len(prompt, n0, hlen), drafts,
    Eng.Eng{SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}}, pf(List.take(&2, U32, prompt, n0))},
    SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}},
    (start_inv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, budget, anchor, checkpoint, hlen), {==}), small)

def pair_out(-R1: SIC.Run, -R2: SIC.Run, +h: {R1 == R2 : SIC.Run})
  -> {R1 == R2 : SIC.Run} & {SIC.out(R1) == SIC.out(R2) : List<&2, U32>}:
  (h, Equal.cong(SIC.Run, List<&2, U32>, x => SIC.out(x), R1, R2, h))

def c_out(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +drafts: List<&2, List<&2, U32>>, +budget: Nat, +anchor: Nat, +checkpoint: Nat,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +small: {Eng.all_small(drafts) == True{} : Bool})
  -> {Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        drafts, budget, anchor, checkpoint)) ==
      SIC.out(SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        drafts, n0, budget, anchor, checkpoint)) : List<&2, U32>}:
  Equal.cong(SIC.Run, List<&2, U32>, x => SIC.out(x),
    Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint)),
    SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts, n0, budget, anchor, checkpoint),
    snd(LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
        Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)),
      {Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)) ==
        SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
          drafts, n0, budget, anchor, checkpoint) : SIC.Run},
      c_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts, budget,
        anchor, checkpoint, hlen, small)))

def Laws.served_chain_job(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, drafts, budget,
    anchor, checkpoint, hlen, small):
  pair_out(Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint)),
    SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts, n0, budget, anchor, checkpoint),
    snd(LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
        Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)),
      {Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)) ==
        SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
          drafts, n0, budget, anchor, checkpoint) : SIC.Run},
      c_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts, budget,
        anchor, checkpoint, hlen, small)))

def Laws.served_chain_commit(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, drafts, budget,
    anchor, checkpoint, hlen, small, running):
  close_of(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, hlen,
    Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint),
    fst(LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
        Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)),
      {Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
          drafts, budget, anchor, checkpoint)) ==
        SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
          drafts, n0, budget, anchor, checkpoint) : SIC.Run},
      c_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts, budget,
        anchor, checkpoint, hlen, small)),
    running)

# The components of spec_inv_laws.prefix_of_greedy / spec_inv_tree_laws.tree_prefix_of_greedy for a run J.
def gA(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run) -> Type:
  {SIS.greedy(~row, budget, stops, prompt) ==
    List.append(&2, U32, SIC.out(J), SIS.after(~row, SIC.stopped(J), SIC.budget(J), stops, List.append(&2, U32, prompt, SIC.out(J)))) : List<&2, U32>}

def gB(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run) -> Type:
  {List.take(&2, U32, SIS.greedy(~row, budget, stops, prompt), List.length(&2, U32, SIC.out(J))) == SIC.out(J) : List<&2, U32>}

def gC(+J: SIC.Run) -> Type:
  {Bool.or(SIC.stopped(J), Nat.is_lt(0n, SIC.budget(J))) == True{} : Bool}

# A prefix fact about a spec run carried to the engine's output (equal to the run's).
def prefix_carry(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run,
    -O: List<&2, U32>, eq: {O == SIC.out(J) : List<&2, U32>}, pg: gA(~row, prompt, stops, budget, J) & gB(~row, prompt, stops, budget, J) & gC(J))
  -> {List.take(&2, U32, SIS.greedy(~row, budget, stops, prompt), List.length(&2, U32, O)) == O : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, O, SIC.out(J), eq) :
    {List.take(&2, U32, SIS.greedy(~row, budget, stops, prompt), List.length(&2, U32, _)) == _ : List<&2, U32>}
  fst(gB(~row, prompt, stops, budget, J), gC(J), snd(gA(~row, prompt, stops, budget, J), gB(~row, prompt, stops, budget, J) & gC(J), pg))

def Laws.served_chain_greedy_prefix(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, drafts,
    budget, anchor, checkpoint, hlen, small, positive):
  prefix_carry(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, budget,
    SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts, n0, budget, anchor, checkpoint),
    Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint)),
    c_out(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts, budget,
      anchor, checkpoint, hlen, small),
    SIL.prefix_of_greedy(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0),
      ~rr(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, drafts, n0, budget,
      anchor, checkpoint, positive))

def sA(+J: SIC.Run) -> Type:
  {SIC.stopped(J) == True{} : Bool}

def sG(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run) -> Type:
  {SIC.out(J) == SIS.greedy(~row, budget, stops, prompt) : List<&2, U32>}

def sE(+J1: SIC.Run, +J2: SIC.Run) -> Type:
  {SIC.out(J1) == SIC.out(J2) : List<&2, U32>}

# speculation_invariance's two output facts carried to the engine's outputs.
def inv_carry(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J1: SIC.Run, +J2: SIC.Run,
    -O1: List<&2, U32>, -O2: List<&2, U32>, +eq1: {O1 == SIC.out(J1) : List<&2, U32>}, eq2: {O2 == SIC.out(J2) : List<&2, U32>},
    si: sA(J1) & sA(J2) & sG(~row, prompt, stops, budget, J1) & sE(J1, J2))
  -> {O1 == SIS.greedy(~row, budget, stops, prompt) : List<&2, U32>} & {O1 == O2 : List<&2, U32>}:
  (s1, r1) = si
  (s2, r2) = r1
  (g1, e12) = r2
  (Equal.trans(List<&2, U32>, O1, SIC.out(J1), SIS.greedy(~row, budget, stops, prompt), eq1, g1),
   Equal.trans(List<&2, U32>, O1, SIC.out(J1), O2, eq1,
     Equal.trans(List<&2, U32>, SIC.out(J1), SIC.out(J2), O2, e12, Equal.sym(List<&2, U32>, O2, SIC.out(J2), eq2))))

def Laws.served_chain_spec_invariance(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval,
    drafts1, drafts2, budget, anchor, checkpoint, hlen, small1, small2, positive, enough1, enough2):
  inv_carry(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, budget,
    SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts1, n0, budget, anchor, checkpoint),
    SIC.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts2, n0, budget, anchor, checkpoint),
    Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts1, budget, anchor, checkpoint)),
    Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts2, budget, anchor, checkpoint)),
    c_out(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts1, budget,
      anchor, checkpoint, hlen, small1),
    c_out(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, drafts2, budget,
      anchor, checkpoint, hlen, small2),
    SIL.speculation_invariance(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0),
      ~rr(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, drafts1, drafts2, n0,
      budget, anchor, checkpoint, positive, enough1, enough2))

# ---------------------------------------------------------------- tree rounds: the accepted path

def nsq(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32,
    +x6: U32, +x7: U32) -> List<&2, Tree.Node>:
  [Tree.Node{q1, x1}, Tree.Node{q2, x2}, Tree.Node{q3, x3}, Tree.Node{q4, x4}, Tree.Node{q5, x5}, Tree.Node{q6, x6}, Tree.Node{q7, x7}]

def parq(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat) -> List<&2, Nat>:
  [0n, q1, q2, q3, q4, q5, q6, q7]

# The served shape's parent array and the drafted nodes give every row the same parent (0 past row 7).
def pa_all(+c: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32,
    +x5: U32, +x6: U32, +x7: U32)
  -> {GtS.nth(parq(q1, q2, q3, q4, q5, q6, q7), c) ==
      Tree.parent_at(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, c) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+c1:
      match c1:
        case 0n:
          {==}
        case 1n+c2:
          match c2:
            case 0n:
              {==}
            case 1n+c3:
              match c3:
                case 0n:
                  {==}
                case 1n+c4:
                  match c4:
                    case 0n:
                      {==}
                    case 1n+c5:
                      match c5:
                        case 0n:
                          {==}
                        case 1n+c6:
                          match c6:
                            case 0n:
                              {==}
                            case 1n+c7:
                              match c7:
                                case 0n:
                                  {==}
                                case 1n+c8:
                                  {==}

def TKq(+c: Nat, +a: U32, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32,
    +x4: U32, +x5: U32, +x6: U32, +x7: U32) -> Type:
  {Link.at(~U32, ~0, [a, x1, x2, x3, x4, x5, x6, x7], c) ==
    Tree.token_at(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, c) : U32}

# Rows 1..7: the round's row token is the drafted node's token.
def tk_all(+c: Nat, +a: U32, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32,
    +x4: U32, +x5: U32, +x6: U32, +x7: U32, +hlo: {Nat.is_le(1n, c) == True{} : Bool}, +hhi: {Nat.is_le(c, 7n) == True{} : Bool})
  -> TKq(c, a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7):
  match c:
    case 0n:
      Empty.absurd(TKq(0n, a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), Ar.ar_false_true(hlo))
    case 1n+c1:
      match c1:
        case 0n:
          {==}
        case 1n+c2:
          match c2:
            case 0n:
              {==}
            case 1n+c3:
              match c3:
                case 0n:
                  {==}
                case 1n+c4:
                  match c4:
                    case 0n:
                      {==}
                    case 1n+c5:
                      match c5:
                        case 0n:
                          {==}
                        case 1n+c6:
                          match c6:
                            case 0n:
                              {==}
                            case 1n+c7:
                              match c7:
                                case 0n:
                                  {==}
                                case 1n+c8:
                                  Empty.absurd(TKq(1n+(1n+(1n+(1n+(1n+(1n+(1n+(1n+c8))))))), a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4,
                                    x5, x6, x7), Ar.ar_false_true(hhi))

# Legal parents point down: the parent of row 1 + q is below it (rows past 7 have parent 0).
def lt_par(+q: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool})
  -> {Nat.is_lt(GtS.nth(parq(q1, q2, q3, q4, q5, q6, q7), 1n+q), 1n+q) == True{} : Bool}:
  match q:
    case 0n:
      TPath.lt1(q1, q2, q3, q4, q5, q6, q7, legal)
    case 1n+r1:
      match r1:
        case 0n:
          TPath.lt2(q1, q2, q3, q4, q5, q6, q7, legal)
        case 1n+r2:
          match r2:
            case 0n:
              TPath.lt3(q1, q2, q3, q4, q5, q6, q7, legal)
            case 1n+r3:
              match r3:
                case 0n:
                  TPath.lt4(q1, q2, q3, q4, q5, q6, q7, legal)
                case 1n+r4:
                  match r4:
                    case 0n:
                      TPath.lt5(q1, q2, q3, q4, q5, q6, q7, legal)
                    case 1n+r5:
                      match r5:
                        case 0n:
                          TPath.lt6(q1, q2, q3, q4, q5, q6, q7, legal)
                        case 1n+r6:
                          match r6:
                            case 0n:
                              TPath.lt7(q1, q2, q3, q4, q5, q6, q7, legal)
                            case 1n+r7:
                              {==}

# gdn_tree_spec.path is fuel-stable on legal trees: any fuel above the row gives the same path.
def fuel_eq(+f: Nat, +g: Nat, +r: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}, +hf: {Nat.is_lt(r, f) == True{} : Bool},
    +hg: {Nat.is_lt(r, g) == True{} : Bool})
  -> {GtS.path.go(f, parq(q1, q2, q3, q4, q5, q6, q7), r) == GtS.path.go(g, parq(q1, q2, q3, q4, q5, q6, q7), r) : List<&2, Nat>}:
  match f:
    case 0n:
      Empty.absurd({GtS.path.go(0n, parq(q1, q2, q3, q4, q5, q6, q7), r) == GtS.path.go(g, parq(q1, q2, q3, q4, q5, q6, q7), r) : List<&2, Nat>},
        LinkProof.ri_lt_zero(r, hf))
    case 1n+f1:
      match g:
        case 0n:
          Empty.absurd({GtS.path.go(1n+f1, parq(q1, q2, q3, q4, q5, q6, q7), r) == GtS.path.go(0n, parq(q1, q2, q3, q4, q5, q6, q7), r) : List<&2, Nat>},
            LinkProof.ri_lt_zero(r, hg))
        case 1n+g1:
          match r:
            case 0n:
              {==}
            case 1n+q:
              +PQ = parq(q1, q2, q3, q4, q5, q6, q7)
              +N = GtS.nth(PQ, 1n+q)
              +hN = lt_par(q, q1, q2, q3, q4, q5, q6, q7, legal)
              +h1 = Ar.ar_lt_le_trans(N, 1n+q, f1, hN, Equal.trans(Bool, Nat.is_le(1n+q, f1), Nat.is_lt(q, f1), True{},
                Equal.sym(Bool, Nat.is_lt(q, f1), Nat.is_le(1n+q, f1), Ar.ar_lt_succ_le(q, f1)), hf))
              +h2 = Ar.ar_lt_le_trans(N, 1n+q, g1, hN, Equal.trans(Bool, Nat.is_le(1n+q, g1), Nat.is_lt(q, g1), True{},
                Equal.sym(Bool, Nat.is_lt(q, g1), Nat.is_le(1n+q, g1), Ar.ar_lt_succ_le(q, g1)), hg))
              Equal.cong(List<&2, Nat>, List<&2, Nat>, x => List.append(&2, Nat, x, [1n+q]), GtS.path.go(f1, PQ, N), GtS.path.go(g1, PQ, N),
                fuel_eq(f1, g1, N, q1, q2, q3, q4, q5, q6, q7, legal, h1, h2))

def PSq(+c: Nat, +cur: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat) -> Type:
  {GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), c) == List.append(&2, Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), [c]) : List<&2, Nat>}

# A row whose parent is cur: its tree path is cur's followed by the row.
def pstep_m(+c: Nat, +cur: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32,
    +x4: U32, +x5: U32, +x6: U32, +x7: U32, +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hlo: {Nat.is_le(1n, c) == True{} : Bool}, +hhi: {Nat.is_le(c, 7n) == True{} : Bool},
    +hpar: {Tree.parent_at(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, c) == cur : Nat})
  -> PSq(c, cur, q1, q2, q3, q4, q5, q6, q7):
  match c:
    case 0n:
      Empty.absurd(PSq(0n, cur, q1, q2, q3, q4, q5, q6, q7), Ar.ar_false_true(hlo))
    case 1n+q:
      +PQ = parq(q1, q2, q3, q4, q5, q6, q7)
      +N = GtS.nth(PQ, 1n+q)
      +hn = Equal.trans(Nat, N, Tree.parent_at(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, 1n+q), cur,
        pa_all(1n+q, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), hpar)
      +hc = Equal.trans(Bool, Nat.is_lt(cur, 1n+q), Nat.is_lt(N, 1n+q), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(y, 1n+q), cur, N, Equal.sym(Nat, N, cur, hn)), lt_par(q, q1, q2, q3, q4, q5, q6, q7, legal))
      +hc7 = Ar.ar_lt_le_trans(cur, 1n+q, 7n, hc, hhi)
      +hc8 = Ar.ar_lt_trans(cur, 7n, 8n, hc7, {==})
      Equal.trans(List<&2, Nat>, List.append(&2, Nat, GtS.path.go(7n, PQ, N), [1n+q]), List.append(&2, Nat, GtS.path.go(7n, PQ, cur), [1n+q]),
        List.append(&2, Nat, GtS.path.go(8n, PQ, cur), [1n+q]),
        Equal.cong(Nat, List<&2, Nat>, y => List.append(&2, Nat, GtS.path.go(7n, PQ, y), [1n+q]), N, cur, hn),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, y => List.append(&2, Nat, y, [1n+q]), GtS.path.go(7n, PQ, cur), GtS.path.go(8n, PQ, cur),
          fuel_eq(7n, 8n, cur, q1, q2, q3, q4, q5, q6, q7, legal, hc7, hc8)))

def EXq(+vs: List<&2, U32>, +cur: Nat, +c: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32,
    +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32) -> Bool:
  Tree.extends(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), vs, cur, c)

def PXq(+W: List<&2, Nat>, +vs: List<&2, U32>, +cur: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32) -> Bool:
  Tree.pext(W, nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), vs, cur)

# The facts of a row extending a matching path ending at cur (exl3_tree_accept_spec.extends).
def ex_lo(+vs: List<&2, U32>, +cur: Nat, +c: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32,
    +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +h: {EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool})
  -> {Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 7n)) == True{} : Bool}:
  +NS = nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
  Ar.ar_and_l(Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 7n)),
    Tree.hit(Tree.parent_at(NS, 1n, c), Tree.token_at(NS, 1n, c), cur, Tree.id_at(vs, cur)), h)

def ex_par(+vs: List<&2, U32>, +cur: Nat, +c: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32,
    +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +h: {EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool})
  -> {Tree.parent_at(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, c) == cur : Nat}:
  +NS = nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
  Ar.ar_eq_true(Tree.parent_at(NS, 1n, c), cur, Ar.ar_and_l(Nat.is_eq(Tree.parent_at(NS, 1n, c), cur),
    U32.is_eq(Tree.token_at(NS, 1n, c), Tree.id_at(vs, cur)),
    Ar.ar_and_r(Bool.and(Nat.is_le(1n, c), Nat.is_le(c, 7n)),
      Tree.hit(Tree.parent_at(NS, 1n, c), Tree.token_at(NS, 1n, c), cur, Tree.id_at(vs, cur)), h)))

# A row extending a matching path ending at cur: its tree path is cur's plus itself.
def pstep_g(+c: Nat, +cur: Nat, +vs: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32,
    +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hext: {EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool})
  -> PSq(c, cur, q1, q2, q3, q4, q5, q6, q7):
  +hA = ex_lo(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hext)
  pstep_m(c, cur, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, Ar.ar_and_l(Nat.is_le(1n, c), Nat.is_le(c, 7n), hA),
    Ar.ar_and_r(Nat.is_le(1n, c), Nat.is_le(c, 7n), hA), ex_par(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hext))

def WPq(+W: List<&2, Nat>, +cur: Nat, +n: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat) -> Type:
  {GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), Tree.row_at(cur <> W, n)) ==
    List.append(&2, Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), List.take(&2, Nat, W, n)) : List<&2, Nat>}

# Along a matching path W after cur, the tree path of its n-th row is cur's path followed by W's first n rows.
def wp(+W: List<&2, Nat>, +cur: Nat, +n: Nat, +vs: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hpx: {PXq(W, vs, cur, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hn: {Nat.is_le(n, List.length(&2, Nat, W)) == True{} : Bool})
  -> WPq(W, cur, n, q1, q2, q3, q4, q5, q6, q7):
  match W:
    case Nil{}:
      match n:
        case 0n:
          Equal.sym(List<&2, Nat>, List.append(&2, Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), Nil{}),
            GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), LinkProof.ri_app_nil(~Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur)))
        case 1n+m:
          Empty.absurd(WPq(Nil{}, cur, 1n+m, q1, q2, q3, q4, q5, q6, q7), Ar.ar_false_true(hn))
    case +c <> +W1:
      match n:
        case 0n:
          Equal.sym(List<&2, Nat>, List.append(&2, Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), Nil{}),
            GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur), LinkProof.ri_app_nil(~Nat, GtS.path(parq(q1, q2, q3, q4, q5, q6, q7), cur)))
        case 1n+m:
          +PQ = parq(q1, q2, q3, q4, q5, q6, q7)
          +E1 = EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +P1 = PXq(W1, vs, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +T = List.take(&2, Nat, W1, m)
          Equal.trans(List<&2, Nat>, GtS.path(PQ, Tree.row_at(c <> W1, m)), List.append(&2, Nat, GtS.path(PQ, c), T),
            List.append(&2, Nat, GtS.path(PQ, cur), c <> T),
            wp(W1, c, m, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, Ar.ar_and_r(E1, P1, hpx), hn),
            Equal.trans(List<&2, Nat>, List.append(&2, Nat, GtS.path(PQ, c), T), List.append(&2, Nat, List.append(&2, Nat, GtS.path(PQ, cur), [c]), T),
              List.append(&2, Nat, GtS.path(PQ, cur), c <> T),
              Equal.cong(List<&2, Nat>, List<&2, Nat>, y => List.append(&2, Nat, y, T), GtS.path(PQ, c), List.append(&2, Nat, GtS.path(PQ, cur), [c]),
                pstep_g(c, cur, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, Ar.ar_and_l(E1, P1, hpx))),
              LinkProof.ri_app_assoc(~Nat, GtS.path(PQ, cur), [c], T)))

def TSq(+W: List<&2, Nat>, +cur: Nat, +k: Nat, +vs: List<&2, U32>, +a: U32, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32,
    +x7: U32) -> Type:
  {Link.stream([a, x1, x2, x3, x4, x5, x6, x7], List.take(&2, Nat, W, k)) == List.take(&2, U32, Tree.targets(cur <> W, vs), k) : List<&2, U32>}

# Along a matching path W after cur, the round tokens of W's first k rows are the verify ids of the k rows
# before them (cur first): every path row's token is its parent's verify id.
def tsg(+W: List<&2, Nat>, +cur: Nat, +k: Nat, +vs: List<&2, U32>, +a: U32, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat,
    +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +hpx: {PXq(W, vs, cur, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hk: {Nat.is_le(k, List.length(&2, Nat, W)) == True{} : Bool})
  -> TSq(W, cur, k, vs, a, x1, x2, x3, x4, x5, x6, x7):
  match W:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd(TSq(Nil{}, cur, 1n+m, vs, a, x1, x2, x3, x4, x5, x6, x7), Ar.ar_false_true(hk))
    case +c <> +W1:
      match k:
        case 0n:
          {==}
        case 1n+m:
          +NS = nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +TOK = {[a, x1, x2, x3, x4, x5, x6, x7] : List<&2, U32>}
          +E1 = EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +P1 = PXq(W1, vs, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +he = Ar.ar_and_l(E1, P1, hpx)
          +hA = ex_lo(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, he)
          LinkProof.ri_cong_cons(~U32, Link.at(~U32, ~0, TOK, c), Tree.id_at(vs, cur), Link.stream(TOK, List.take(&2, Nat, W1, m)),
            List.take(&2, U32, Tree.targets(c <> W1, vs), m),
            Equal.trans(U32, Link.at(~U32, ~0, TOK, c), Tree.token_at(NS, 1n, c), Tree.id_at(vs, cur),
              tk_all(c, a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, Ar.ar_and_l(Nat.is_le(1n, c), Nat.is_le(c, 7n), hA),
                Ar.ar_and_r(Nat.is_le(1n, c), Nat.is_le(c, 7n), hA)),
              u32_eq_t(Tree.token_at(NS, 1n, c), Tree.id_at(vs, cur), TPath.tok_match(NS, vs, cur, c, he))),
            tsg(W1, c, m, vs, a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, Ar.ar_and_r(E1, P1, hpx), hk))

# Every row of a matching path is a row of the round (< 8).
def rb(+W: List<&2, Nat>, +cur: Nat, +k: Nat, +vs: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +hpx: {PXq(W, vs, cur, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hk: {Nat.is_lt(k, List.length(&2, Nat, W)) == True{} : Bool})
  -> {Nat.is_lt(Tree.row_at(W, k), 8n) == True{} : Bool}:
  match W:
    case Nil{}:
      Empty.absurd({Nat.is_lt(Tree.row_at(Nil{}, k), 8n) == True{} : Bool}, LinkProof.ri_lt_zero(k, hk))
    case +c <> +W1:
      match k:
        case 0n:
          +E1 = EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +P1 = PXq(W1, vs, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +hA = ex_lo(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, Ar.ar_and_l(E1, P1, hpx))
          Equal.trans(Bool, Nat.is_lt(c, 8n), Nat.is_le(1n+c, 8n), True{}, Ar.ar_lt_succ_le(c, 8n),
            Ar.ar_and_r(Nat.is_le(1n, c), Nat.is_le(c, 7n), hA))
        case 1n+m:
          +E1 = EXq(vs, cur, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          +P1 = PXq(W1, vs, c, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
          rb(W1, c, m, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, Ar.ar_and_r(E1, P1, hpx), hk)

# The accepted path's row at c (c <= |W|) is a row of the round.
def rbP(+W: List<&2, Nat>, +c: Nat, +vs: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +hpx: {PXq(W, vs, 0n, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +h: {Nat.is_le(c, List.length(&2, Nat, W)) == True{} : Bool})
  -> {Nat.is_lt(Tree.row_at(0n <> W, c), 8n) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+m:
      rb(W, 0n, m, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpx,
        Equal.trans(Bool, Nat.is_lt(m, List.length(&2, Nat, W)), Nat.is_le(1n+m, List.length(&2, Nat, W)), True{},
          Ar.ar_lt_succ_le(m, List.length(&2, Nat, W)), h))

# A legal tree is an admitted 8-row served round (rowinv_served.ok).
def ok_tree(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool})
  -> {Served.ok(Served.Tree{q1, q2, q3, q4, q5, q6, q7}, 8n) == True{} : Bool}:
  +B6 = Nat.is_lt(q7, 7n)
  +B5 = Bool.and(Nat.is_lt(q6, 6n), B6)
  +B4 = Bool.and(Nat.is_lt(q5, 5n), B5)
  +B3 = Bool.and(Nat.is_lt(q4, 4n), B4)
  +B2 = Bool.and(Nat.is_lt(q3, 3n), B3)
  +B1 = Bool.and(Nat.is_lt(q2, 2n), B2)
  Ar.ar_and_intro(Bool.and(Nat.is_lt(q1, 1n), B1), Nat.is_eq(8n, 8n),
    Ar.ar_and_intro(Nat.is_lt(q1, 1n), B1, TPath.lt1(q1, q2, q3, q4, q5, q6, q7, legal),
      Ar.ar_and_intro(Nat.is_lt(q2, 2n), B2, TPath.lt2(q1, q2, q3, q4, q5, q6, q7, legal),
        Ar.ar_and_intro(Nat.is_lt(q3, 3n), B3, TPath.lt3(q1, q2, q3, q4, q5, q6, q7, legal),
          Ar.ar_and_intro(Nat.is_lt(q4, 4n), B4, TPath.lt4(q1, q2, q3, q4, q5, q6, q7, legal),
            Ar.ar_and_intro(Nat.is_lt(q5, 5n), B5, TPath.lt5(q1, q2, q3, q4, q5, q6, q7, legal),
              Ar.ar_and_intro(Nat.is_lt(q6, 6n), B6, TPath.lt6(q1, q2, q3, q4, q5, q6, q7, legal),
                TPath.lt7(q1, q2, q3, q4, q5, q6, q7, legal))))))), {==})

# ---------------------------------------------------------------- tree rounds

# The commit of the accepted path rows P[0..count) = rowinv_served.pth(tree_shape, P[count - 1]) (count = 1 + c).
def t_commit(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +cs: List<&2, C>, +W: List<&2, Nat>, +vs: List<&2, U32>, +c: Nat,
    +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32,
    +x7: U32, +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hpx: {PXq(W, vs, 0n, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hc: {Nat.is_le(c, List.length(&2, Nat, W)) == True{} : Bool})
  -> {Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
        cs, 0n, List.take(&2, Nat, 0n <> W, 1n+c), Served.Tree{q1, q2, q3, q4, q5, q6, q7}, p,
        List.length(&2, U32, [a, x1, x2, x3, x4, x5, x6, x7]), Link.embs(~V, ~emb, [a, x1, x2, x3, x4, x5, x6, x7])) ==
      LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
        List.append(&2, U32, u, a <> List.take(&2, U32, Tree.targets(0n <> W, vs), c))) : List<&2, C>}:
  +TOK = {[a, x1, x2, x3, x4, x5, x6, x7] : List<&2, U32>}
  +SH = {Served.Tree{q1, q2, q3, q4, q5, q6, q7} : Served.Shape}
  +r = Tree.row_at(0n <> W, c)
  +RHS = LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
    List.append(&2, U32, u, a <> List.take(&2, U32, Tree.targets(0n <> W, vs), c)))
  +TR = {wp(W, 0n, c, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, hpx, hc) :
    {Served.pth(SH, r) == List.take(&2, Nat, 0n <> W, 1n+c) : List<&2, Nat>}}
  %TR : {Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
    cs, 0n, _, SH, p, List.length(&2, U32, TOK), Link.embs(~V, ~emb, TOK)) == RHS : List<&2, C>}
  %Equal.sym(Nat, p, Nat.add(n0, List.length(&2, U32, u)), hpos) :
    {Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, 0n, Served.pth(SH, r), SH, _, List.length(&2, U32, TOK), Link.embs(~V, ~emb, TOK)) == RHS : List<&2, C>}
  Equal.trans(List<&2, C>,
    Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, 0n, Served.pth(SH, r), SH, Nat.add(n0, List.length(&2, U32, u)), List.length(&2, U32, TOK), Link.embs(~V, ~emb, TOK)),
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0,
      List.append(&2, U32, u, Link.stream(TOK, Served.pth(SH, r)))), RHS,
    SL.served_commit(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, pf(pre), n0, u, cs, TOK, SH, r, hcs,
      ok_tree(q1, q2, q3, q4, q5, q6, q7, legal), {==}, rbP(W, c, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpx, hc)),
    Equal.cong(List<&2, U32>, List<&2, C>,
      y => LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, y)),
      Link.stream(TOK, Served.pth(SH, r)), a <> List.take(&2, U32, Tree.targets(0n <> W, vs), c),
      Equal.trans(List<&2, U32>, Link.stream(TOK, Served.pth(SH, r)), Link.stream(TOK, List.take(&2, Nat, 0n <> W, 1n+c)),
        a <> List.take(&2, U32, Tree.targets(0n <> W, vs), c),
        Equal.cong(List<&2, Nat>, List<&2, U32>, y => Link.stream(TOK, y), Served.pth(SH, r), List.take(&2, Nat, 0n <> W, 1n+c), TR),
        Equal.cong(List<&2, U32>, List<&2, U32>, y => a <> y, Link.stream(TOK, List.take(&2, Nat, W, c)),
          List.take(&2, U32, Tree.targets(0n <> W, vs), c), tsg(W, 0n, c, vs, a, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpx, hc)))))

# The invariant after the live tree round's decision (count c, eos e; usable when wr).
def GVt(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>, +n0: Nat, +prompt: List<&2, U32>, +cbase: Nat,
    +interval: Nat, +pre: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>, +cs: List<&2, C>,
    +W: List<&2, Nat>, +vs: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32,
    +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32, +wr: Bool, +c: Nat, +e: Bool) -> Type:
  LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
    Eng.Eng{SIC.Run{Round.commit(wr, c, e, 7n, cbase, interval, p, b, an, ck),
        List.append(&2, U32, o, List.take(&2, U32, Tree.targets(0n <> W, vs), c))},
      Eng.keep(~C, wr, Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth,
        ~Served.gat, cs, 0n, List.take(&2, Nat, 0n <> W, c), Served.Tree{q1, q2, q3, q4, q5, q6, q7}, p,
        List.length(&2, U32, [a, x1, x2, x3, x4, x5, x6, x7]), Link.embs(~V, ~emb, [a, x1, x2, x3, x4, x5, x6, x7])), cs)})

def tv_eos(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, e: Bool, +c: Nat, +prompt: List<&2, U32>, +cbase: Nat, +interval: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32,
    +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>, +cs: List<&2, C>, +W: List<&2, Nat>, +vs: List<&2, U32>,
    +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32,
    +x7: U32, +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hpx: {PXq(W, vs, 0n, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hprog: {Nat.is_lt(0n, c) == True{} : Bool},
    +hbound: {Nat.is_le(c, List.length(&2, U32, Tree.targets(0n <> W, vs))) == True{} : Bool})
  -> GVt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, pre, a, p, b, an, ck, o, cs, W, vs,
      q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, True{}, c, e):
  match e:
    case True{}:
      Unit{}
    case False{}:
      match c:
        case 0n:
          Empty.absurd(GVt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, pre, a, p, b, an, ck, o, cs,
            W, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, True{}, 0n, False{}), Ar.ar_false_true(hprog))
        case 1n+c1:
          +IDS = Tree.targets(0n <> W, vs)
          +LI = List.length(&2, U32, IDS)
          +LW = List.length(&2, Nat, W)
          +hlt = Equal.trans(Bool, Nat.is_lt(c1, LI), Nat.is_le(1n+c1, LI), True{}, Ar.ar_lt_succ_le(c1, LI), hbound)
          +hle = Ar.ar_lt_le(c1, LI, hlt)
          +hcW = {Equal.trans(Bool, Nat.is_le(1n+c1, 1n+LW), Nat.is_le(1n+c1, LI), True{},
            Equal.cong(Nat, Bool, y => Nat.is_le(1n+c1, y), 1n+LW, LI, Equal.sym(Nat, LI, 1n+LW, TPath.len_targets(0n <> W, vs))), hbound) :
            {Nat.is_le(c1, LW) == True{} : Bool}}
          (List.append(&2, U32, u, a <> List.take(&2, U32, IDS, c1)), (Link.at(~U32, ~0, IDS, c1),
            (next_seq(prompt, o, pre, u, a, IDS, c1, hseq, hlt),
              (next_pos(n0, p, u, a, IDS, c1, hpos, hle),
                t_commit(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, pre, u, a, p, cs, W, vs, c1,
                  q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, hpos, hcs, hpx, hcW)))))

# The live tree round's decision cv on the linearized matching path 0 <> W is usable.
def tv_verdict(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>,
    ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, cv: Accept.Verdict, +prompt: List<&2, U32>, +cbase: Nat, +interval: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32,
    +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>, +cs: List<&2, C>, +W: List<&2, Nat>, +vs: List<&2, U32>,
    +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32,
    +x7: U32, +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +hpx: {PXq(W, vs, 0n, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool},
    +hW: {Nat.is_le(List.length(&2, Nat, W), 7n) == True{} : Bool},
    +hprog: {Nat.is_lt(0n, Accept.count(cv)) == True{} : Bool},
    +hbound: {Nat.is_le(Accept.count(cv), List.length(&2, U32, Tree.targets(0n <> W, vs))) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.Eng{SIC.Run{Round.advance(Tree.count(Tree.finish(cv, 0n <> W)), Tree.eos(Tree.finish(cv, 0n <> W)), 7n, cbase, interval,
          Round.State{p, b, an, ck, False{}}),
          List.append(&2, U32, o, RoundSpec.committed(Tree.targets(0n <> W, vs), Tree.count(Tree.finish(cv, 0n <> W)), False{}))},
        Eng.keep(~C, Eng.live(False{}, Tree.count(Tree.finish(cv, 0n <> W)), 7n),
          Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
            cs, 0n, List.take(&2, Nat, 0n <> W, Tree.count(Tree.finish(cv, 0n <> W))), Served.Tree{q1, q2, q3, q4, q5, q6, q7}, p,
            List.length(&2, U32, [a, x1, x2, x3, x4, x5, x6, x7]), Link.embs(~V, ~emb, [a, x1, x2, x3, x4, x5, x6, x7])), cs)}):
  match cv:
    case Accept.Verdict{+c, +e}:
      +LI = List.length(&2, U32, Tree.targets(0n <> W, vs))
      +hw8 = Ar.ar_le_trans(c, LI, 8n, hbound, Equal.trans(Bool, Nat.is_le(LI, 8n), Nat.is_le(1n+List.length(&2, Nat, W), 8n), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, 8n), LI, 1n+List.length(&2, Nat, W), TPath.len_targets(0n <> W, vs)), hW))
      %Equal.sym(Bool, Round.writes(c, 7n), True{}, Ar.ar_and_intro(Nat.is_lt(0n, c), Nat.is_le(c, 8n), hprog, hw8)) :
        GVt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, cbase, interval, pre, a, p, b, an, ck, o, cs, W, vs,
          q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, _, c, e)
      tv_eos(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, e, c, prompt, cbase, interval, pre, u, a, p, b, an, ck,
        o, cs, W, vs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, hseq, hpos, hcs, hpx, hprog, hbound)

# exl3_tree_accept_laws.path_matches for the round's verify ids: the matching path after the root extends
# row by row and is maximal.
def pm_v(~row: List<&2, U32> -> Nat -> U32, +seq: List<&2, U32>, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +legal: {Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool})
  -> {PXq(Tree.walk(7n, Tree.child(nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), 1n, 0n,
        Tree.id_at(SIT.verify(~row, seq, nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)), 0n)),
        nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7), SIT.verify(~row, seq, nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7))),
      SIT.verify(~row, seq, nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)), 0n,
      q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) == True{} : Bool}:
  +NS = nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
  +VS = SIT.verify(~row, seq, NS)
  snd({Tree.row_at(Tree.path(NS, VS), 0n) == 0n : Nat}, {Tree.pext(List.tail(&2, Nat, Tree.path(NS, VS)), NS, VS, 0n) == True{} : Bool},
    TreeLaws.path_matches(row(SIT.prefix(seq, NS, 0n), 0n), row(SIT.prefix(seq, NS, 1n), 1n), row(SIT.prefix(seq, NS, 2n), 2n),
      row(SIT.prefix(seq, NS, 3n), 3n), row(SIT.prefix(seq, NS, 4n), 4n), row(SIT.prefix(seq, NS, 5n), 5n), row(SIT.prefix(seq, NS, 6n), 6n),
      row(SIT.prefix(seq, NS, 7n), 7n), x1, x2, x3, x4, x5, x6, x7, q1, q2, q3, q4, q5, q6, q7, legal))

# The tree round goal with the row tokens and verify ids abstracted.
def GAt(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +t: SIT.Draft,
    +pre: List<&2, U32>, +toks: List<&2, U32>, +vs: List<&2, U32>, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>,
    +cs: List<&2, C>) -> Type:
  {Eng.run(~C, Eng.tree_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, t, toks, vs,
      Round.State{p, b, an, ck, False{}}, o, cs)) ==
    SIT.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, t,
      SIC.Run{Round.State{p, b, an, ck, False{}}, o}) : SIC.Run} &
  LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
    Eng.tree_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, t, toks, vs,
      Round.State{p, b, an, ck, False{}}, o, cs))

def t_ver(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +t: SIT.Draft, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat,
    +interval: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>,
    +cs: List<&2, C>, +legal: {SIT.legal(t) == True{} : Bool},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>})
  -> GAt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, t, pre,
      Served.tree_toks(a, t),
      SIT.verify(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), List.append(&2, U32, prompt, o), SIT.nodes(t)),
      p, b, an, ck, o, cs):
  match t:
    case SIT.Draft{+q1, +q2, +q3, +q4, +q5, +q6, +q7, +x1, +x2, +x3, +x4, +x5, +x6, +x7}:
      +NS = nsq(q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7)
      +SEQ = List.append(&2, U32, prompt, o)
      +VS = SIT.verify(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), SEQ, NS)
      +W = Tree.walk(7n, Tree.child(NS, 1n, 0n, Tree.id_at(VS, 0n)), NS, VS)
      +TSH = TPath.shaped(W, NS, VS)
      +CV = Accept.accept(Tree.targets(0n <> W, VS), Tree.proposals(W, NS), stops, b, ck)
      ({==}, tv_verdict(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, CV, prompt, cbase, interval, pre, u, a, p, b, an,
        ck, o, cs, W, VS, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal, hseq, hpos, hcs,
        pm_v(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), SEQ,
          q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, legal),
        SITP.walk_len(7n, Tree.child(NS, 1n, 0n, Tree.id_at(VS, 0n)), NS, VS),
        AcceptLaws.accept_progress(Tree.targets(0n <> W, VS), Tree.proposals(W, NS), stops, b, ck, TSH),
        fst({Nat.is_le(Accept.count(CV), List.length(&2, U32, Tree.targets(0n <> W, VS))) == True{} : Bool},
          {Nat.is_le(Accept.count(CV), 1n+List.length(&2, U32, Tree.proposals(W, NS))) == True{} : Bool},
          AcceptLaws.accept_bounds(Tree.targets(0n <> W, VS), Tree.proposals(W, NS), stops, b, ck, TSH))))

def t_live(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +t: SIT.Draft, +pre: List<&2, U32>, +u: List<&2, U32>, +a: U32, +p: Nat, +b: Nat, +an: Nat, +ck: Nat, +o: List<&2, U32>,
    +cs: List<&2, C>, +legal: {SIT.legal(t) == True{} : Bool},
    +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +hseq: {List.append(&2, U32, prompt, o) == List.append(&2, U32, pre, List.append(&2, U32, u, [a])) : List<&2, U32>},
    +hpos: {p == Nat.add(n0, List.length(&2, U32, u)) : Nat},
    +hcs: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>})
  -> GAt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, t, pre,
      Served.tree_toks(Eng.last_tok(List.append(&2, U32, prompt, o)), t),
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, p, Served.tree_toks(Eng.last_tok(List.append(&2, U32, prompt, o)), t),
        Served.tree_shape(t)),
      p, b, an, ck, o, cs):
  +SEQ = List.append(&2, U32, prompt, o)
  +SEQ2 = List.append(&2, U32, pre, List.append(&2, U32, u, [a]))
  +LTK = Eng.last_tok(SEQ)
  +hlt = Equal.trans(U32, a, Eng.last_tok(SEQ2), LTK, Equal.sym(U32, Eng.last_tok(SEQ2), a, lt_seq(pre, u, a)),
    Equal.cong(List<&2, U32>, U32, x => Eng.last_tok(x), SEQ2, SEQ, Equal.sym(List<&2, U32>, SEQ, SEQ2, hseq)))
  %hlt : GAt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, t, pre,
    Served.tree_toks(_, t),
    Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
      ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, p, Served.tree_toks(_, t), Served.tree_shape(t)), p, b, an, ck, o, cs)
  %Equal.sym(Nat, p, Nat.add(n0, List.length(&2, U32, u)), hpos) :
    GAt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, t, pre, Served.tree_toks(a, t),
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, _, Served.tree_toks(a, t), Served.tree_shape(t)), p, b, an, ck, o, cs)
  %Equal.trans(List<&2, U32>,
      SIT.verify(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), SEQ, SIT.nodes(t)),
      SIT.verify(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), SEQ2, SIT.nodes(t)),
      Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
        ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), Served.tree_toks(a, t),
        Served.tree_shape(t)),
      Equal.cong(List<&2, U32>, List<&2, U32>,
        x => SIT.verify(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), x, SIT.nodes(t)), SEQ, SEQ2, hseq),
      SL.served_tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0,
        ~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0),
        ~isr(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), pre, u, a, t, cs, hpre, hcs, legal)) :
    GAt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, prompt, stops, cbase, interval, t, pre, Served.tree_toks(a, t), _,
      p, b, an, ck, o, cs)
  t_ver(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, t, prompt, stops, cbase, interval, pre, u, a, p, b, an,
    ck, o, cs, legal, hseq, hpos, hcs)

# One tree round from any state satisfying the invariant.
def t_round0(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, +t: SIT.Draft, e: Eng.Eng<C>,
    inv: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e),
    +legal: {SIT.legal(t) == True{} : Bool})
  -> {Eng.run(~C, Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e)) ==
      SIT.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, t,
        Eng.run(~C, e)) : SIC.Run} &
    LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e)):
  match e:
    case Eng.Eng{r, +cs}:
      match r:
        case SIC.Run{st, +o}:
          match st:
            case Round.State{+p, +b, +an, +ck, s}:
              match s:
                case True{}:
                  ({==}, Unit{})
                case False{}:
                  (u, i1) = inv
                  (a, i2) = i1
                  (hseq, i3) = i2
                  (hpos, hcs) = i3
                  t_live(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, t, pre,
                    u, a, p, b, an, ck, o, cs, legal, hpre, hseq, hpos, hcs)

def t_round(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, +t: SIT.Draft, +e: Eng.Eng<C>, +R: SIC.Run,
    ji: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e) & {Eng.run(~C, e) == R : SIC.Run},
    +legal: {SIT.legal(t) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e)) &
    {Eng.run(~C, Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e)) ==
      SIT.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, t,
        R) : SIC.Run}:
  (inv, heq) = ji
  swap_run(~C, Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e),
    Eng.run(~C, e), R,
    LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e)),
    x => SIT.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, t, x),
    t_round0(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, t,
      e, inv, legal), heq)

def t_run(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +pre: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat}, trees: List<&2, SIT.Draft>, +e: Eng.Eng<C>, +R: SIC.Run,
    ji: LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre, e) & {Eng.run(~C, e) == R : SIC.Run},
    +legal: {SIT.all_legal(trees) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, pre,
      Eng.tree_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, trees, e)) &
    {Eng.run(~C, Eng.tree_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, trees, e)) ==
      SIT.run(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, trees,
        R) : SIC.Run}:
  match trees:
    case Nil{}:
      ji
    case +t <> +rest:
      t_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, rest,
        Eng.tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e),
        SIT.round(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, t, R),
        t_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, pre, hpre, t,
          e, R, ji, Ar.ar_and_l(SIT.legal(t), SIT.all_legal(rest), legal)),
        Ar.ar_and_r(SIT.legal(t), SIT.all_legal(rest), legal))

def t_job(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    trees: List<&2, SIT.Draft>, +budget: Nat, +anchor: Nat, +checkpoint: Nat,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +legal: {SIT.all_legal(trees) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)) &
    {Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)) ==
      SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        trees, n0, budget, anchor, checkpoint) : SIC.Run}:
  t_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval,
    List.take(&2, U32, prompt, n0), pre_len(prompt, n0, hlen), trees,
    Eng.Eng{SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}}, pf(List.take(&2, U32, prompt, n0))},
    SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}},
    (start_inv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, budget, anchor, checkpoint, hlen), {==}), legal)

def t_eq(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +trees: List<&2, SIT.Draft>, +budget: Nat, +anchor: Nat, +checkpoint: Nat,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +legal: {SIT.all_legal(trees) == True{} : Bool})
  -> {Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)) ==
      SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        trees, n0, budget, anchor, checkpoint) : SIC.Run}:
  snd(LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)),
    {Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)) ==
      SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        trees, n0, budget, anchor, checkpoint) : SIC.Run},
    t_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, trees, budget,
      anchor, checkpoint, hlen, legal))

def t_inv(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    +trees: List<&2, SIT.Draft>, +budget: Nat, +anchor: Nat, +checkpoint: Nat,
    +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}, +legal: {SIT.all_legal(trees) == True{} : Bool})
  -> LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)):
  fst(LInv(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, List.take(&2, U32, prompt, n0),
      Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)),
    {Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)) ==
      SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        trees, n0, budget, anchor, checkpoint) : SIC.Run},
    t_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, trees, budget,
      anchor, checkpoint, hlen, legal))

def Laws.served_tree_job(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, trees, budget,
    anchor, checkpoint, hlen, legal):
  pair_out(Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      trees, budget, anchor, checkpoint)),
    SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      trees, n0, budget, anchor, checkpoint),
    t_eq(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, trees, budget,
      anchor, checkpoint, hlen, legal))

def Laws.served_tree_commit(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, trees, budget,
    anchor, checkpoint, hlen, legal, running):
  close_of(~V, ~E, ~C, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, hlen,
    Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      trees, budget, anchor, checkpoint),
    t_inv(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, trees, budget,
      anchor, checkpoint, hlen, legal),
    running)

def Laws.served_tree_greedy_prefix(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, prompt, stops, cbase, interval, trees,
    budget, anchor, checkpoint, hlen, legal, positive):
  prefix_carry(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, budget,
    SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      trees, n0, budget, anchor, checkpoint),
    Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      trees, budget, anchor, checkpoint)),
    Equal.cong(SIC.Run, List<&2, U32>, x => SIC.out(x),
      Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
        trees, budget, anchor, checkpoint)),
      SIT.job(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
        trees, n0, budget, anchor, checkpoint),
      t_eq(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, prompt, stops, cbase, interval, trees, budget,
        anchor, checkpoint, hlen, legal)),
    SITL.tree_prefix_of_greedy(~Laws.ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0),
      ~rr(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval, trees, n0, budget,
      anchor, checkpoint, positive, legal))
