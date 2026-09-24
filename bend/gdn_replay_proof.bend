# Proofs of the GDN replay laws (bend/gdn_replay_laws.bend). Structural
# evidence only: no unsafe definitions, axioms, holes or answer tables.
import Base
import ./gdn_replay.bend as Impl
import ./gdn_replay_spec.bend as Spec
import ./exl3_accept_spec.bend as Accept
import ./gdn_replay_laws.bend as Laws

# fold over a snoc is one more step.
def fold_snoc(~S: Data, ~X: Data, ~step: S -> X -> S, pre: List<&2, X>, +x: X,
    s: S) -> {Spec.fold(~S, ~X, ~step, List.append(&2, X, pre, [x]), s) ==
      step(Spec.fold(~S, ~X, ~step, pre, s), x) : S}:
  match pre:
    case Nil{}:
      {==}
    case p <> rest:
      fold_snoc(~S, ~X, ~step, rest, x, step(s, p))

# The verify kernel's running state is the fold of the rows before it.
def verify_from(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S,
    ~out: S -> X -> O, xs: List<&2, X>, +s0: S, +pre: List<&2, X>)
  -> {Impl.verify(~S, ~X, ~O, ~step, ~out, xs, Spec.fold(~S, ~X, ~step, pre, s0)) ==
    Spec.outputs(~S, ~X, ~O, ~step, ~out, xs, s0, pre) : List<&2, O>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %fold_snoc(~S, ~X, ~step, pre, x, s0) :
        {out(_, x) <> Impl.verify(~S, ~X, ~O, ~step, ~out, rest, _) ==
          out(Spec.fold(~S, ~X, ~step, List.append(&2, X, pre, [x]), s0), x) <>
          Spec.outputs(~S, ~X, ~O, ~step, ~out, rest, s0, List.append(&2, X, pre, [x]))
          : List<&2, O>}
      %verify_from(~S, ~X, ~O, ~step, ~out, rest, s0, List.append(&2, X, pre, [x])) :
        {out(Spec.fold(~S, ~X, ~step, List.append(&2, X, pre, [x]), s0), x) <>
          Impl.verify(~S, ~X, ~O, ~step, ~out, rest,
            Spec.fold(~S, ~X, ~step, List.append(&2, X, pre, [x]), s0)) ==
          out(Spec.fold(~S, ~X, ~step, List.append(&2, X, pre, [x]), s0), x) <> _
          : List<&2, O>}
      {==}

def Laws.verify_outputs(S, X, O, step, out, xs, s0):
  verify_from(~S, ~X, ~O, ~step, ~out, xs, s0, Nil{})

# The replay loop over steps tokens is the fold of the first steps tokens.
def replay_fold(~S: Data, ~X: Data, ~step: S -> X -> S, steps: Nat,
    xs: List<&2, X>, s: S) -> {Impl.replay(~S, ~X, ~step, steps, xs, s) ==
      Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, steps), s) : S}:
  match steps:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case x <> rest:
          {==}
    case 1n+more:
      match xs:
        case Nil{}:
          {==}
        case x <> rest:
          replay_fold(~S, ~X, ~step, more, rest, step(s, x))

# Every committed round is the replay of steps = window + 1 - num_rejected
# tokens, with the conv job and position of that num_rejected, once the two
# host checks (launch index in range, 1 <= steps <= seqlen) hold.
def master(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat, +eos: Bool,
    in_range: {True{} == Nat.is_le(Impl.num_rejected(window, count, eos), window)
      : Bool},
    checked: {True{} == Bool.and(
      Nat.is_le(1n, Nat.sub(1n+window, Impl.num_rejected(window, count, eos))),
      Nat.is_le(Nat.sub(1n+window, Impl.num_rejected(window, count, eos)),
        List.length(&2, X, xs))) : Bool})
  -> {Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh},
        window, xs, ys, Accept.Verdict{count, eos}) ==
      Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step,
          Nat.sub(1n+window, Impl.num_rejected(window, count, eos)), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H),
          Impl.num_rejected(window, count, eos),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, eos)),
        0n}} : Impl.Outcome<S, Y>}:
  %in_range : {Impl.launch(~S, ~X, ~Y, ~step, _, K, Nat.add(K, H), window,
      Impl.num_rejected(window, count, eos), xs, s0,
      Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys), Nat.add(position, 1n+window)) ==
      Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step,
          Nat.sub(1n+window, Impl.num_rejected(window, count, eos)), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H),
          Impl.num_rejected(window, count, eos),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, eos)),
        0n}} : Impl.Outcome<S, Y>}
  %checked : {Impl.replay_checked(~S, ~X, ~Y, ~step, _,
      Nat.sub(1n+window, Impl.num_rejected(window, count, eos)), xs, s0,
      Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H),
        Impl.num_rejected(window, count, eos),
        Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
      Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, eos))) ==
      Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step,
          Nat.sub(1n+window, Impl.num_rejected(window, count, eos)), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H),
          Impl.num_rejected(window, count, eos),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, eos)),
        0n}} : Impl.Outcome<S, Y>}
  {==}

# Order and subtraction facts on Nat.
def rp_truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

def rp_false_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : rp_truth(_)
  Unit{}

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_succ(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool})
  -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, rp_false_true(h))
    case 1n+p 1n+q:
      le_succ(p, q, h)

def sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_zero_left(n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      le_refl(p)
    case 1n+p 1n+q:
      le_succ(Nat.sub(p, q), p, sub_le(p, q))

def sub_succ_left(+p: Nat, +x: Nat, h: {Nat.is_le(x, p) == True{} : Bool})
  -> {Nat.sub(1n+p, x) == 1n+Nat.sub(p, x) : Nat}:
  match p x:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, sub_zero(p)) : {1n+p == 1n+_ : Nat}
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat},
        rp_false_true(h))
    case 1n+r 1n+q:
      sub_succ_left(r, q, h)

# num_rejected without eos is window + 1 - count, for every count.
def rejected_shift(b: Bool, +w: Nat, +c: Nat)
  -> {Impl.rejected_if(b, w, c) == Impl.rejected_if(b, 1n+w, 1n+c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rejected_sub(+c: Nat, +w: Nat)
  -> {Impl.num_rejected(w, c, False{}) == Nat.sub(1n+w, c) : Nat}:
  match c w:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Equal.sym(Nat, Nat.sub(0n, p), 0n, sub_zero_left(p))
    case 1n+p 1n+q:
      %rejected_shift(Nat.is_le(p, q), q, p) :
        {_ == Nat.sub(1n+q, p) : Nat}
      rejected_sub(p, q)

# a - (a - c) = c when c <= a.
def sub_sub(+a: Nat, +c: Nat, h: {Nat.is_le(c, a) == True{} : Bool})
  -> {Nat.sub(a, Nat.sub(a, c)) == c : Nat}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+q)) == 1n+q : Nat},
        rp_false_true(h))
    case 1n+p 0n:
      sub_self(p)
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.sub(1n+p, Nat.sub(p, q)),
        1n+Nat.sub(p, Nat.sub(p, q)), 1n+q,
        sub_succ_left(p, Nat.sub(p, q), sub_le(p, q)),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.sub(p, Nat.sub(p, q)), q,
          sub_sub(p, q, h)))

def add_succ_right(+x: Nat, +a: Nat) -> {Nat.add(x, 1n+a) == 1n+Nat.add(x, a) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+a), 1n+Nat.add(p, a),
        add_succ_right(p, a))

# (x + a) - d = x + (a - d) when d <= a.
def sub_add(+x: Nat, +a: Nat, +d: Nat, h: {Nat.is_le(d, a) == True{} : Bool})
  -> {Nat.sub(Nat.add(x, a), d) == Nat.add(x, Nat.sub(a, d)) : Nat}:
  match a d:
    case _ 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(x, a), 0n), Nat.add(x, a),
        Nat.add(x, Nat.sub(a, 0n)), sub_zero(Nat.add(x, a)),
        Equal.cong(Nat, Nat, n => Nat.add(x, n), a, Nat.sub(a, 0n),
          Equal.sym(Nat, Nat.sub(a, 0n), a, sub_zero(a))))
    case 0n 1n+q:
      Empty.absurd({Nat.sub(Nat.add(x, 0n), 1n+q) ==
        Nat.add(x, Nat.sub(0n, 1n+q)) : Nat}, rp_false_true(h))
    case 1n+r 1n+q:
      %Equal.sym(Nat, Nat.add(x, 1n+r), 1n+Nat.add(x, r), add_succ_right(x, r)) :
        {Nat.sub(_, 1n+q) == Nat.add(x, Nat.sub(r, q)) : Nat}
      sub_add(x, r, q, h)

def and_true(a: Bool, b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool})
  -> {True{} == Bool.and(a, b) : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {True{} == Bool.and(_, b) : Bool}
  Equal.sym(Bool, b, True{}, hb)

def le_one_sub(+w: Nat, +c: Nat, hp: {Nat.is_le(1n, c) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(1n+w, c), w) == True{} : Bool}:
  match c:
    case 0n:
      Empty.absurd({Nat.is_le(1n+w, w) == True{} : Bool}, rp_false_true(hp))
    case 1n+q:
      sub_le(w, q)

# Without eos, the replay runs exactly count steps.
def steps_eq(+window: Nat, +count: Nat,
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Nat.sub(1n+window, Impl.num_rejected(window, count, False{})) == count : Nat}:
  Equal.trans(Nat, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})),
    Nat.sub(1n+window, Nat.sub(1n+window, count)), count,
    Equal.cong(Nat, Nat, n => Nat.sub(1n+window, n), Impl.num_rejected(window, count, False{}),
      Nat.sub(1n+window, count), rejected_sub(count, window)),
    sub_sub(1n+window, count, bounded))

def steps_le_one(+window: Nat, +count: Nat,
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Nat.is_le(1n, Nat.sub(1n+window, Impl.num_rejected(window, count, False{}))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), count, steps_eq(window, count, bounded)) :
    {Nat.is_le(1n, _) == True{} : Bool}
  progress

def steps_le_len(~X: Data, +window: Nat, +count: Nat, +xs: List<&2, X>,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), List.length(&2, X, xs)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), count, steps_eq(window, count, bounded)) :
    {Nat.is_le(_, List.length(&2, X, xs)) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, X, xs), 1n+window, shaped_xs) :
    {Nat.is_le(count, _) == True{} : Bool}
  bounded

# Every non-eos round with 1 <= count <= window + 1 passes both host checks.
def master_ok(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}) ==
      Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})),
        0n}} : Impl.Outcome<S, Y>}:
  master(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count,
    False{},
    Equal.trans(Bool, True{}, Nat.is_le(Nat.sub(1n+window, count), window),
      Nat.is_le(Impl.num_rejected(window, count, False{}), window),
      Equal.sym(Bool, Nat.is_le(Nat.sub(1n+window, count), window), True{},
        le_one_sub(window, count, progress)),
      Equal.cong(Nat, Bool, n => Nat.is_le(n, window), Nat.sub(1n+window, count),
        Impl.num_rejected(window, count, False{}),
        Equal.sym(Nat, Impl.num_rejected(window, count, False{}), Nat.sub(1n+window, count),
          rejected_sub(count, window)))),
    and_true(Nat.is_le(1n, Nat.sub(1n+window, Impl.num_rejected(window, count, False{}))),
      Nat.is_le(Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), List.length(&2, X, xs)),
      steps_le_one(window, count, progress, bounded),
      steps_le_len(~X, window, count, xs, shaped_xs, bounded)))

def rp_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def rp_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_zero(-n: Nat, h: {1n+n == 0n : Nat}) -> Empty:
  %h : rp_disc(_)
  Unit{}

def take_all(~X: Data, xs: List<&2, X>, +n: Nat,
    h: {List.length(&2, X, xs) == n : Nat})
  -> {List.take(&2, X, xs, n) == xs : List<&2, X>}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> rest 0n:
      Empty.absurd({List.take(&2, X, x <> rest, 0n) == x <> rest : List<&2, X>},
        succ_zero(List.length(&2, X, rest), h))
    case x <> rest 1n+m:
      %Equal.sym(List<&2, X>, List.take(&2, X, rest, m), rest,
          take_all(~X, rest, m, Equal.cong(Nat, Nat, rp_pred,
            1n+List.length(&2, X, rest), 1n+m, h))) :
        {x <> _ == x <> rest : List<&2, X>}
      {==}

def eos_len(~X: Data, +window: Nat, +xs: List<&2, X>,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat})
  -> {Nat.is_le(1n+window, List.length(&2, X, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, X, xs), 1n+window, shaped_xs) :
    {Nat.is_le(1n+window, _) == True{} : Bool}
  le_refl(window)

# eos rounds reject nothing: the replay runs all window + 1 tokens.
def master_eos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat})
  -> {Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}) ==
      Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})),
        0n}} : Impl.Outcome<S, Y>}:
  master(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count,
    True{},
    Equal.sym(Bool, Nat.is_le(0n, window), True{}, le_zero(window)),
    and_true(Nat.is_le(1n, 1n+window), Nat.is_le(1n+window, List.length(&2, X, xs)),
      le_zero(window), eos_len(~X, window, xs, shaped_xs)))

def fold_take_zero(~S: Data, ~X: Data, ~step: S -> X -> S, xs: List<&2, X>,
    +s: S) -> {s == Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, 0n), s) : S}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def succ_not_le(n: Nat) -> {False{} == Nat.is_le(1n+n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      succ_not_le(p)

def Laws.commit_empty(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count):
  match window:
    case 0n:
      {==}
    case 1n+q:
      %succ_not_le(1n+q) :
        {Impl.launch(~S, ~X, ~Y, ~step, _, K, Nat.add(K, H), 1n+q, 2n+q, xs, s0,
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys), Nat.add(position, 2n+q)) ==
          Impl.Refused{s0} : Impl.Outcome<S, Y>}
      {==}

def prefix_pos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) ==
    Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0) : S}:
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})),
        0n}},
      master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)) :
    {Impl.row0_of(~S, ~Y, _) ==
      Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0) : S}
  %Equal.sym(Nat, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), count, steps_eq(window, count, bounded)) :
    {Impl.replay(~S, ~X, ~step, _, xs, s0) ==
      Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0) : S}
  replay_fold(~S, ~X, ~step, count, xs, s0)

def Laws.commit_prefix(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, bounded):
  match count:
    case 0n:
      %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{0n, False{}}), Impl.Refused{s0},
          Laws.commit_empty(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs,
            ys, 0n)) :
        {Impl.row0_of(~S, ~Y, _) ==
          Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, 0n), s0) : S}
      fold_take_zero(~S, ~X, ~step, xs, s0)
    case 1n+c:
      prefix_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys,
        1n+c, shaped_xs, le_zero(c), bounded)

def Laws.commit_eos(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped):
  +shaped_xs = shaped
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})),
        0n}}, master_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs)) :
    {Impl.row0_of(~S, ~Y, _) == Spec.fold(~S, ~X, ~step, xs, s0) : S}
  %Equal.sym(S, Impl.replay(~S, ~X, ~step, 1n+window, xs, s0),
      Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, 1n+window), s0),
      replay_fold(~S, ~X, ~step, 1n+window, xs, s0)) :
    {_ == Spec.fold(~S, ~X, ~step, xs, s0) : S}
  %Equal.sym(List<&2, X>, List.take(&2, X, xs, 1n+window), xs,
      take_all(~X, xs, 1n+window, shaped_xs)) :
    {Spec.fold(~S, ~X, ~step, _, s0) == Spec.fold(~S, ~X, ~step, xs, s0) : S}
  {==}

def Laws.commit_happens(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded):
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})),
        0n}},
      master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)) :
    {Impl.committed(~S, ~Y, _) == True{} : Bool}
  {==}

def Laws.commit_happens_eos(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs):
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})),
        0n}}, master_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs)) :
    {Impl.committed(~S, ~Y, _) == True{} : Bool}
  {==}

def position_pos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) == Nat.add(position, count) : Nat}:
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})),
        0n}},
      master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)) :
    {Impl.position_of(~S, ~Y, _) == Nat.add(position, count) : Nat}
  %Equal.sym(Nat, Impl.num_rejected(window, count, False{}), Nat.sub(1n+window, count), rejected_sub(count, window)) :
    {Nat.sub(Nat.add(position, 1n+window), _) == Nat.add(position, count) : Nat}
  Equal.trans(Nat, Nat.sub(Nat.add(position, 1n+window), Nat.sub(1n+window, count)),
    Nat.add(position, Nat.sub(1n+window, Nat.sub(1n+window, count))),
    Nat.add(position, count),
    sub_add(position, 1n+window, Nat.sub(1n+window, count), sub_le(1n+window, count)),
    Equal.cong(Nat, Nat, n => Nat.add(position, n),
      Nat.sub(1n+window, Nat.sub(1n+window, count)), count,
      sub_sub(1n+window, count, bounded)))

def lh_zero(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {Impl.last_history_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) == 0n : Nat}:
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})),
        0n}},
      master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)) :
    {Impl.last_history_of(~S, ~Y, _) == 0n : Nat}
  {==}

def lh_zero_eos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat})
  -> {Impl.last_history_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) == 0n : Nat}:
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})),
        0n}}, master_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs)) :
    {Impl.last_history_of(~S, ~Y, _) == 0n : Nat}
  {==}

def position_eos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat})
  -> {Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) == Nat.add(position, 1n+window) : Nat}:
  %Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}), Impl.Committed{Impl.Engine{
        Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0),
        Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}),
          Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)),
        Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})),
        0n}}, master_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs)) :
    {Impl.position_of(~S, ~Y, _) == Nat.add(position, 1n+window) : Nat}
  sub_zero(Nat.add(position, 1n+window))

def Laws.position_advance_eos(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs_):
  +shaped_xs = shaped_xs_
  (position_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs), lh_zero_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs))

def Laws.position_advance(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs_, progress_, bounded_):
  +shaped_xs = shaped_xs_
  +progress = progress_
  +bounded = bounded_
  (position_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded),
    lh_zero(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded))

# More Nat facts for the conv window.
def add_zero_r(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, add_zero_r(p))

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero_r(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, b), Nat.add(b, p), add_comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ_right(b, p)))

def add_sub_cancel(+K: Nat, +c: Nat) -> {Nat.sub(Nat.add(K, c), K) == c : Nat}:
  match K:
    case 0n:
      sub_zero(c)
    case 1n+p:
      add_sub_cancel(p, c)

def sub_add_cancel(+W: Nat, +x: Nat, h: {Nat.is_le(x, W) == True{} : Bool})
  -> {Nat.add(Nat.sub(W, x), x) == W : Nat}:
  match W x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, rp_false_true(h))
    case 1n+p 0n:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, add_zero_r(p))
    case 1n+p 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p,
        add_succ_right(Nat.sub(p, q), q),
        Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.sub(p, q), q), p,
          sub_add_cancel(p, q, h)))

def min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_l(p, q)

def min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      le_zero(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_r(p, q)

def le_min(+n: Nat, +a: Nat, +b: Nat, ha: {Nat.is_le(n, a) == True{} : Bool},
    hb: {Nat.is_le(n, b) == True{} : Bool})
  -> {Nat.is_le(n, Nat.min(a, b)) == True{} : Bool}:
  match n a b:
    case 0n _ _:
      le_zero(Nat.min(a, b))
    case 1n+m 0n _:
      Empty.absurd({Nat.is_le(1n+m, Nat.min(0n, b)) == True{} : Bool}, rp_false_true(ha))
    case 1n+m 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+m, Nat.min(1n+p, 0n)) == True{} : Bool},
        rp_false_true(hb))
    case 1n+m 1n+p 1n+q:
      le_min(m, p, q, ha, hb)

def le_trans(+a: Nat, +b: Nat, +c: Nat, hab: {Nat.is_le(a, b) == True{} : Bool},
    hbc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, rp_false_true(hab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, rp_false_true(hbc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, hab, hbc)

def sub_sub_add(+W: Nat, +n: Nat, +K: Nat)
  -> {Nat.sub(Nat.sub(W, n), K) == Nat.sub(W, Nat.add(n, K)) : Nat}:
  match W n:
    case _ 0n:
      Equal.cong(Nat, Nat, m => Nat.sub(m, K), Nat.sub(W, 0n), W, sub_zero(W))
    case 0n 1n+q:
      sub_zero_left(K)
    case 1n+p 1n+q:
      sub_sub_add(p, q, K)

# W - x <= W - n when n <= x.
def sub_antimono(+W: Nat, +n: Nat, +x: Nat, h: {Nat.is_le(n, x) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(W, x), Nat.sub(W, n)) == True{} : Bool}:
  match W n x:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(0n, n), 0n, sub_zero_left(n)) :
        {Nat.is_le(Nat.sub(0n, x), _) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(0n, x), 0n, sub_zero_left(x)) :
        {Nat.is_le(_, 0n) == True{} : Bool}
      {==}
    case 1n+p 0n _:
      sub_le(1n+p, x)
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+p, 0n), Nat.sub(1n+p, 1n+q)) == True{} : Bool},
        rp_false_true(h))
    case 1n+p 1n+q 1n+r:
      sub_antimono(p, q, r, h)

# (W - n) - (W - x) = x - n when n <= x <= W.
def sub_sub_both(+n: Nat, +x: Nat, +W: Nat, hnx: {Nat.is_le(n, x) == True{} : Bool},
    hxw: {Nat.is_le(x, W) == True{} : Bool})
  -> {Nat.sub(Nat.sub(W, n), Nat.sub(W, x)) == Nat.sub(x, n) : Nat}:
  match n x W:
    case 0n _ _:
      Equal.trans(Nat, Nat.sub(Nat.sub(W, 0n), Nat.sub(W, x)), Nat.sub(W, Nat.sub(W, x)),
        Nat.sub(x, 0n),
        Equal.cong(Nat, Nat, m => Nat.sub(m, Nat.sub(W, x)), Nat.sub(W, 0n), W, sub_zero(W)),
        Equal.trans(Nat, Nat.sub(W, Nat.sub(W, x)), x, Nat.sub(x, 0n), sub_sub(W, x, hxw),
          Equal.sym(Nat, Nat.sub(x, 0n), x, sub_zero(x))))
    case 1n+m 0n _:
      Empty.absurd({Nat.sub(Nat.sub(W, 1n+m), Nat.sub(W, 0n)) == Nat.sub(0n, 1n+m) : Nat},
        rp_false_true(hnx))
    case 1n+m 1n+q 0n:
      Empty.absurd({Nat.sub(Nat.sub(0n, 1n+m), Nat.sub(0n, 1n+q)) == Nat.sub(1n+q, 1n+m)
        : Nat}, rp_false_true(hxw))
    case 1n+m 1n+q 1n+p:
      sub_sub_both(m, q, p, hnx, hxw)

# (T - x) + (x - n) = T - n when n <= x <= T.
def add_sub_sub(+n: Nat, +x: Nat, +T: Nat, hnx: {Nat.is_le(n, x) == True{} : Bool},
    hxt: {Nat.is_le(x, T) == True{} : Bool})
  -> {Nat.add(Nat.sub(T, x), Nat.sub(x, n)) == Nat.sub(T, n) : Nat}:
  match n x T:
    case 0n _ _:
      Equal.trans(Nat, Nat.add(Nat.sub(T, x), Nat.sub(x, 0n)), Nat.add(Nat.sub(T, x), x),
        Nat.sub(T, 0n),
        Equal.cong(Nat, Nat, m => Nat.add(Nat.sub(T, x), m), Nat.sub(x, 0n), x, sub_zero(x)),
        Equal.trans(Nat, Nat.add(Nat.sub(T, x), x), T, Nat.sub(T, 0n),
          sub_add_cancel(T, x, hxt), Equal.sym(Nat, Nat.sub(T, 0n), T, sub_zero(T))))
    case 1n+m 0n _:
      Empty.absurd({Nat.add(Nat.sub(T, 0n), Nat.sub(0n, 1n+m)) == Nat.sub(T, 1n+m) : Nat},
        rp_false_true(hnx))
    case 1n+m 1n+q 0n:
      Empty.absurd({Nat.add(Nat.sub(0n, 1n+q), Nat.sub(1n+q, 1n+m)) == Nat.sub(0n, 1n+m)
        : Nat}, rp_false_true(hxt))
    case 1n+m 1n+q 1n+p:
      add_sub_sub(m, q, p, hnx, hxt)

# List facts for the conv window (Y is any element type).
def len_append(~Y: Data, a: List<&2, Y>, +b: List<&2, Y>)
  -> {List.length(&2, Y, List.append(&2, Y, a, b)) == Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Y, List.append(&2, Y, t, b)), Nat.add(List.length(&2, Y, t), List.length(&2, Y, b)),
        len_append(~Y, t, b))

def len_take(~Y: Data, xs: List<&2, Y>, +n: Nat, h: {Nat.is_le(n, List.length(&2, Y, xs)) == True{} : Bool})
  -> {List.length(&2, Y, List.take(&2, Y, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({List.length(&2, Y, List.take(&2, Y, Nil{}, 1n+m)) == 1n+m : Nat}, rp_false_true(h))
    case x <> t 0n:
      {==}
    case x <> t 1n+m:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Y, List.take(&2, Y, t, m)), m, len_take(~Y, t, m, h))

def len_drop(~Y: Data, xs: List<&2, Y>, +n: Nat)
  -> {List.length(&2, Y, List.drop(&2, Y, xs, n)) == Nat.sub(List.length(&2, Y, xs), n) : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+m:
      len_drop(~Y, t, m)

def drop_all(~Y: Data, xs: List<&2, Y>) -> {List.drop(&2, Y, xs, List.length(&2, Y, xs)) == Nil{} : List<&2, Y>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      drop_all(~Y, t)

def append_nil(~Y: Data, xs: List<&2, Y>) -> {List.append(&2, Y, xs, Nil{}) == xs : List<&2, Y>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, Y>, List<&2, Y>, r => x <> r, List.append(&2, Y, t, Nil{}), t, append_nil(~Y, t))

def drop_zero(~Y: Data, xs: List<&2, Y>) -> {List.drop(&2, Y, xs, 0n) == xs : List<&2, Y>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def take_all_y(~Y: Data, xs: List<&2, Y>, +n: Nat, h: {List.length(&2, Y, xs) == n : Nat})
  -> {List.take(&2, Y, xs, n) == xs : List<&2, Y>}:
  match xs n:
    case Nil{} _:
      {==}
    case x <> t 0n:
      Empty.absurd({List.take(&2, Y, x <> t, 0n) == x <> t : List<&2, Y>}, succ_zero(List.length(&2, Y, t), h))
    case +x <> t 1n+m:
      Equal.cong(List<&2, Y>, List<&2, Y>, r => x <> r, List.take(&2, Y, t, m), t,
        take_all_y(~Y, t, m, Equal.cong(Nat, Nat, rp_pred, 1n+List.length(&2, Y, t), 1n+m, h)))

# drop past an exact prefix of length d.
def drop_append_exact(~Y: Data, a: List<&2, Y>, +b: List<&2, Y>, +d: Nat, +m: Nat,
    ha: {List.length(&2, Y, a) == d : Nat}, hdm: {Nat.is_le(d, m) == True{} : Bool})
  -> {List.drop(&2, Y, List.append(&2, Y, a, b), m) == List.drop(&2, Y, b, Nat.sub(m, d)) : List<&2, Y>}:
  match a d m:
    case Nil{} 0n _:
      Equal.cong(Nat, List<&2, Y>, r => List.drop(&2, Y, b, r), m, Nat.sub(m, 0n),
        Equal.sym(Nat, Nat.sub(m, 0n), m, sub_zero(m)))
    case Nil{} 1n+q _:
      Empty.absurd({List.drop(&2, Y, List.append(&2, Y, Nil{}, b), m) == List.drop(&2, Y, b, Nat.sub(m, 1n+q)) : List<&2, Y>},
        succ_zero(q, Equal.sym(Nat, 0n, 1n+q, ha)))
    case x <> t 0n _:
      Empty.absurd({List.drop(&2, Y, List.append(&2, Y, x <> t, b), m) == List.drop(&2, Y, b, Nat.sub(m, 0n)) : List<&2, Y>},
        succ_zero(List.length(&2, Y, t), ha))
    case x <> t 1n+q 0n:
      Empty.absurd({List.drop(&2, Y, List.append(&2, Y, x <> t, b), 0n) == List.drop(&2, Y, b, Nat.sub(0n, 1n+q)) : List<&2, Y>},
        rp_false_true(hdm))
    case x <> t 1n+q 1n+r:
      drop_append_exact(~Y, t, b, q, r,
        Equal.cong(Nat, Nat, rp_pred, 1n+List.length(&2, Y, t), 1n+q, ha), hdm)

def drop_drop(~Y: Data, xs: List<&2, Y>, +a: Nat, +b: Nat)
  -> {List.drop(&2, Y, List.drop(&2, Y, xs, a), b) == List.drop(&2, Y, xs, Nat.add(a, b)) : List<&2, Y>}:
  match xs a:
    case Nil{} _:
      {==}
    case x <> t 0n:
      {==}
    case x <> t 1n+p:
      drop_drop(~Y, t, p, b)

def take_drop_shift(~Y: Data, xs: List<&2, Y>, +c: Nat, +K: Nat)
  -> {List.drop(&2, Y, List.take(&2, Y, xs, Nat.add(c, K)), c) == List.take(&2, Y, List.drop(&2, Y, xs, c), K) : List<&2, Y>}:
  match xs c:
    case Nil{} _:
      {==}
    case +x <> +t 0n:
      drop_zero(~Y, List.take(&2, Y, x <> t, K))
    case x <> t 1n+p:
      take_drop_shift(~Y, t, p, K)

def prefix_take(~Y: Data, w: List<&2, Y>, +ys: List<&2, Y>, +K: Nat, +c: Nat,
    h: {List.length(&2, Y, w) == K : Nat})
  -> {List.take(&2, Y, List.append(&2, Y, w, ys), Nat.add(K, c)) == List.append(&2, Y, w, List.take(&2, Y, ys, c)) : List<&2, Y>}:
  match w K:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      Empty.absurd({List.take(&2, Y, List.append(&2, Y, Nil{}, ys), Nat.add(1n+q, c)) == List.append(&2, Y, Nil{}, List.take(&2, Y, ys, c)) : List<&2, Y>},
        succ_zero(q, Equal.sym(Nat, 0n, 1n+q, h)))
    case x <> t 0n:
      Empty.absurd({List.take(&2, Y, List.append(&2, Y, x <> t, ys), Nat.add(0n, c)) == List.append(&2, Y, x <> t, List.take(&2, Y, ys, c)) : List<&2, Y>},
        succ_zero(List.length(&2, Y, t), h))
    case +x <> t 1n+q:
      Equal.cong(List<&2, Y>, List<&2, Y>, r => x <> r, List.take(&2, Y, List.append(&2, Y, t, ys), Nat.add(q, c)), List.append(&2, Y, t, List.take(&2, Y, ys, c)),
        prefix_take(~Y, t, ys, q, c, Equal.cong(Nat, Nat, rp_pred, 1n+List.length(&2, Y, t), 1n+q, h)))

def take_zero(~Y: Data, xs: List<&2, Y>) -> {List.take(&2, Y, xs, 0n) == Nil{} : List<&2, Y>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      {==}

def take_append_len(~Y: Data, a: List<&2, Y>, +b: List<&2, Y>, +n: Nat, h: {List.length(&2, Y, a) == n : Nat})
  -> {List.take(&2, Y, List.append(&2, Y, a, b), n) == a : List<&2, Y>}:
  match a n:
    case Nil{} 0n:
      take_zero(~Y, b)
    case Nil{} 1n+q:
      Empty.absurd({List.take(&2, Y, List.append(&2, Y, Nil{}, b), 1n+q) == Nil{} : List<&2, Y>},
        succ_zero(q, Equal.sym(Nat, 0n, 1n+q, h)))
    case x <> t 0n:
      Empty.absurd({List.take(&2, Y, List.append(&2, Y, x <> t, b), 0n) == x <> t : List<&2, Y>}, succ_zero(List.length(&2, Y, t), h))
    case +x <> t 1n+q:
      Equal.cong(List<&2, Y>, List<&2, Y>, r => x <> r, List.take(&2, Y, List.append(&2, Y, t, b), q), t,
        take_append_len(~Y, t, b, q, Equal.cong(Nat, Nat, rp_pred, 1n+List.length(&2, Y, t), 1n+q, h)))

def le_rw(+n: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, h: {Nat.is_le(n, b) == True{} : Bool})
  -> {Nat.is_le(n, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(n, _) == True{} : Bool}
  h

# The history write leaves [W - write, W) = the last write inputs of seq.
def cw_seq_len(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>,
    +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool})
  -> {List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)) == Nat.add(K, List.length(&2, Y, ys)) : Nat}:
  Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.add(List.length(&2, Y, List.take(&2, Y, buf, K)), List.length(&2, Y, ys)), Nat.add(K, List.length(&2, Y, ys)),
      len_append(~Y, List.take(&2, Y, buf, K), ys),
      Equal.cong(Nat, Nat, m => Nat.add(m, List.length(&2, Y, ys)), List.length(&2, Y, List.take(&2, Y, buf, K)), K, len_take(~Y, buf, K, le_rw(K, List.length(&2, Y, buf), W, hb, hK))))

def cw_tail(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>,
    +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool})
  -> {List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))) == List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nil{}), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), r), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nil{}, Equal.trans(List<&2, Y>, List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.drop(&2, Y, buf, W), Nil{},
      Equal.cong(Nat, List<&2, Y>, m => List.drop(&2, Y, buf, m), Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), W, sub_add_cancel(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), min_le_l(W, Nat.add(K, List.length(&2, Y, ys))))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, buf, W), List.drop(&2, Y, buf, List.length(&2, Y, buf)), Nil{},
      Equal.cong(Nat, List<&2, Y>, m => List.drop(&2, Y, buf, m), W, List.length(&2, Y, buf), Equal.sym(Nat, List.length(&2, Y, buf), W, hb)),
      drop_all(~Y, buf)))),
      Equal.trans(List<&2, Y>, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nil{}), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))),
      append_nil(~Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))),
      take_all_y(~Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), Equal.trans(Nat, List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))),
      len_drop(~Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))),
      Equal.trans(Nat, Nat.sub(List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))),
      Equal.cong(Nat, Nat, m => Nat.sub(m, Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.add(K, List.length(&2, Y, ys)), cw_seq_len(~Y, K, W, buf, ys, hb, hK)),
      sub_sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), min_le_r(W, Nat.add(K, List.length(&2, Y, ys)))))))))

def cw_drop_len(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool})
  -> {List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))) == Nat.min(W, Nat.add(K, List.length(&2, Y, ys))) : Nat}:
  Equal.trans(Nat, List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))),
      len_drop(~Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))),
      Equal.trans(Nat, Nat.sub(List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))),
      Equal.cong(Nat, Nat, m => Nat.sub(m, Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys)), Nat.add(K, List.length(&2, Y, ys)), cw_seq_len(~Y, K, W, buf, ys, hb, hK)),
      sub_sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), min_le_r(W, Nat.add(K, List.length(&2, Y, ys))))))

def cw_len(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool})
  -> {List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)) == W : Nat}:
  Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), Nat.add(List.length(&2, Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), W,
      len_append(~Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))))),
      Equal.trans(Nat, Nat.add(List.length(&2, Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), W,
      Equal.cong(Nat, Nat, m => Nat.add(m, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), List.length(&2, Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), len_take(~Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), le_rw(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, buf), W, hb, sub_le(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))))),
      Equal.trans(Nat, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))))), Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))))), W,
      Equal.cong(List<&2, Y>, Nat, r => Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, r)), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), cw_tail(~Y, K, W, buf, ys, hb, hK)),
      Equal.trans(Nat, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))))), Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), W,
      Equal.cong(Nat, Nat, m => Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), m), List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), cw_drop_len(~Y, K, W, buf, ys, hb, hK)),
      sub_add_cancel(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), min_le_l(W, Nat.add(K, List.length(&2, Y, ys))))))))

def cw_char(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +n: Nat, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool},
    +hnW: {Nat.is_le(n, W) == True{} : Bool}, +hnT: {Nat.is_le(n, Nat.add(K, List.length(&2, Y, ys))) == True{} : Bool})
  -> {List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(W, n)) == List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n)) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))))), Nat.sub(W, n)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(Nat.sub(W, n), Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n)),
      drop_append_exact(~Y, List.take(&2, Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.sub(W, n), len_take(~Y, buf, Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), le_rw(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.length(&2, Y, buf), W, hb, sub_le(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), sub_antimono(W, n, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), le_min(n, W, Nat.add(K, List.length(&2, Y, ys)), hnW, hnT))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(Nat.sub(W, n), Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n)),
      Equal.cong(Nat, List<&2, Y>, m => List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), m), Nat.sub(Nat.sub(W, n), Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n), sub_sub_both(n, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), W, le_min(n, W, Nat.add(K, List.length(&2, Y, ys)), hnW, hnT), min_le_l(W, Nat.add(K, List.length(&2, Y, ys))))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), List.drop(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n)),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => List.drop(&2, Y, r, Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), List.drop(&2, Y, buf, Nat.add(Nat.sub(W, Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), cw_tail(~Y, K, W, buf, ys, hb, hK)),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys))))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n)),
      drop_drop(~Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)),
      Equal.cong(Nat, List<&2, Y>, m => List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), m), Nat.add(Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.min(W, Nat.add(K, List.length(&2, Y, ys)))), Nat.sub(Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), n)), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), n), add_sub_sub(n, Nat.min(W, Nat.add(K, List.length(&2, Y, ys))), Nat.add(K, List.length(&2, Y, ys)), le_min(n, W, Nat.add(K, List.length(&2, Y, ys)), hnW, hnT), min_le_r(W, Nat.add(K, List.length(&2, Y, ys)))))))))

def le_add_left(+n: Nat, +K: Nat) -> {Nat.is_le(K, Nat.add(n, K)) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(K)
    case 1n+p:
      le_succ(K, Nat.add(p, K), le_add_left(p, K))

def rw_head_len(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +n: Nat, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool}, +hmW: {Nat.is_le(Nat.add(n, K), W) == True{} : Bool}, +hmT: {Nat.is_le(Nat.add(n, K), Nat.add(K, List.length(&2, Y, ys))) == True{} : Bool})
  -> {Nat.is_le(K, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)))) == True{} : Bool}:
  le_rw(K, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K))), Nat.add(n, K), Equal.trans(Nat, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K))), Nat.sub(List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), Nat.sub(Nat.sub(W, n), K)), Nat.add(n, K),
      len_drop(~Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)),
      Equal.trans(Nat, Nat.sub(List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), Nat.sub(Nat.sub(W, n), K)), Nat.sub(W, Nat.sub(Nat.sub(W, n), K)), Nat.add(n, K),
      Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.sub(Nat.sub(W, n), K)), List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), W, cw_len(~Y, K, W, buf, ys, hb, hK)),
      Equal.trans(Nat, Nat.sub(W, Nat.sub(Nat.sub(W, n), K)), Nat.sub(W, Nat.sub(W, Nat.add(n, K))), Nat.add(n, K),
      Equal.cong(Nat, Nat, x => Nat.sub(W, x), Nat.sub(Nat.sub(W, n), K), Nat.sub(W, Nat.add(n, K)), sub_sub_add(W, n, K)),
      sub_sub(W, Nat.add(n, K), hmW)))), le_add_left(n, K))

# The rewound conv window: the K inputs of seq that precede the last n.
def conv_head(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +n: Nat, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool}, +hmW: {Nat.is_le(Nat.add(n, K), W) == True{} : Bool}, +hmT: {Nat.is_le(Nat.add(n, K), Nat.add(K, List.length(&2, Y, ys))) == True{} : Bool})
  -> {List.take(&2, Y, Impl.conv_rewind(~Y, K, W, n, Impl.conv_write(~Y, K, W, buf, ys)), K) == List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(n, K))), K) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K)), K), List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(n, K))), K),
      take_append_len(~Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K), K, len_take(~Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K, rw_head_len(~Y, K, W, buf, ys, n, hb, hK, hmW, hmT))),
      Equal.trans(List<&2, Y>, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(W, Nat.add(n, K))), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(n, K))), K),
      Equal.cong(Nat, List<&2, Y>, x => List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), x), K), Nat.sub(Nat.sub(W, n), K), Nat.sub(W, Nat.add(n, K)), sub_sub_add(W, n, K)),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => List.take(&2, Y, r, K), List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(W, Nat.add(n, K))), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(n, K))), cw_char(~Y, K, W, buf, ys, Nat.add(n, K), hb, hK, hmW, hmT))))

def conv_len(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +n: Nat, +hb: {List.length(&2, Y, buf) == W : Nat}, +hK: {Nat.is_le(K, W) == True{} : Bool}, +hmW: {Nat.is_le(Nat.add(n, K), W) == True{} : Bool}, +hmT: {Nat.is_le(Nat.add(n, K), Nat.add(K, List.length(&2, Y, ys))) == True{} : Bool})
  -> {List.length(&2, Y, Impl.conv_rewind(~Y, K, W, n, Impl.conv_write(~Y, K, W, buf, ys))) == W : Nat}:
  Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), Nat.add(List.length(&2, Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K)), List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), W,
      len_append(~Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K), List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K)),
      Equal.trans(Nat, Nat.add(List.length(&2, Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K)), List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), Nat.add(K, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), W,
      Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), List.length(&2, Y, List.take(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K)), K, len_take(~Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), Nat.sub(Nat.sub(W, n), K)), K, rw_head_len(~Y, K, W, buf, ys, n, hb, hK, hmW, hmT))),
      Equal.trans(Nat, Nat.add(K, List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K))), Nat.add(K, Nat.sub(List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), K)), W,
      Equal.cong(Nat, Nat, x => Nat.add(K, x), List.length(&2, Y, List.drop(&2, Y, Impl.conv_write(~Y, K, W, buf, ys), K)), Nat.sub(List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), K), len_drop(~Y, Impl.conv_write(~Y, K, W, buf, ys), K)),
      Equal.trans(Nat, Nat.add(K, Nat.sub(List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), K)), Nat.add(K, Nat.sub(W, K)), W,
      Equal.cong(Nat, Nat, x => Nat.add(K, Nat.sub(x, K)), List.length(&2, Y, Impl.conv_write(~Y, K, W, buf, ys)), W, cw_len(~Y, K, W, buf, ys, hb, hK)),
      Equal.trans(Nat, Nat.add(K, Nat.sub(W, K)), Nat.add(Nat.sub(W, K), K), W,
      add_comm(K, Nat.sub(W, K)),
      sub_add_cancel(W, K, hK))))))

def le_rw_l(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(_, c) == True{} : Bool}
  h

def le_add_right(+K: Nat, +H: Nat) -> {Nat.is_le(K, Nat.add(K, H)) == True{} : Bool}:
  match K:
    case 0n:
      le_zero(H)
    case 1n+p:
      le_add_right(p, H)

def le_add_mono(+K: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(K, a), Nat.add(K, b)) == True{} : Bool}:
  match K:
    case 0n:
      h
    case 1n+p:
      le_add_mono(p, a, b, h)

def add_sub_add(+K: Nat, +a: Nat, +b: Nat)
  -> {Nat.sub(Nat.add(K, a), Nat.add(K, b)) == Nat.sub(a, b) : Nat}:
  match K:
    case 0n:
      {==}
    case 1n+p:
      add_sub_add(p, a, b)

def ne_zero(+w: Nat, h: {Nat.is_le(1n, w) == True{} : Bool})
  -> {Nat.is_eq(w, 0n) == False{} : Bool}:
  match w:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, rp_false_true(h))
    case 1n+p:
      {==}

# Reference side: the last K of the old window plus c inputs, as a window of seq.
def spec_last(~Y: Data, +K: Nat, +buf: List<&2, Y>, +ys: List<&2, Y>, +c: Nat,
    +hKb: {Nat.is_le(K, List.length(&2, Y, buf)) == True{} : Bool},
    +hc: {Nat.is_le(c, List.length(&2, Y, ys)) == True{} : Bool})
  -> {Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c))) == List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c), K) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), Nat.sub(List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c))), K)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), Nat.sub(Nat.add(K, c), K)), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c), K),
      Equal.cong(Nat, List<&2, Y>, x => List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), Nat.sub(x, K)), List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c))), Nat.add(K, c), Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c))), Nat.add(List.length(&2, Y, List.take(&2, Y, buf, K)), List.length(&2, Y, List.take(&2, Y, ys, c))), Nat.add(K, c),
      len_append(~Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)),
      Equal.trans(Nat, Nat.add(List.length(&2, Y, List.take(&2, Y, buf, K)), List.length(&2, Y, List.take(&2, Y, ys, c))), Nat.add(K, List.length(&2, Y, List.take(&2, Y, ys, c))), Nat.add(K, c),
      Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, Y, List.take(&2, Y, ys, c))), List.length(&2, Y, List.take(&2, Y, buf, K)), K, len_take(~Y, buf, K, hKb)),
      Equal.cong(Nat, Nat, x => Nat.add(K, x), List.length(&2, Y, List.take(&2, Y, ys, c)), c, len_take(~Y, ys, c, hc))))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), Nat.sub(Nat.add(K, c), K)), List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), c), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c), K),
      Equal.cong(Nat, List<&2, Y>, x => List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), x), Nat.sub(Nat.add(K, c), K), c, add_sub_cancel(K, c)),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), c), List.drop(&2, Y, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(K, c)), c), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c), K),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => List.drop(&2, Y, r, c), List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(K, c)), Equal.sym(List<&2, Y>, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(K, c)), List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, c)), prefix_take(~Y, List.take(&2, Y, buf, K), ys, K, c, len_take(~Y, buf, K, hKb)))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(K, c)), c), List.drop(&2, Y, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.add(c, K)), c), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c), K),
      Equal.cong(Nat, List<&2, Y>, x => List.drop(&2, Y, List.take(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), x), c), Nat.add(K, c), Nat.add(c, K), add_comm(K, c)),
      take_drop_shift(~Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), c, K)))))

def conv_head_pos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    +shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +shaped_ys: {List.length(&2, Y, ys) == 1n+window : Nat},
    +shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat},
    +drafted: {Nat.is_le(1n, window) == True{} : Bool},
    +fits: {Nat.is_le(window, H) == True{} : Bool},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})), K) == Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})), K), List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}}), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))),
      Equal.cong(Impl.Outcome<S, Y>, List<&2, Y>, o => List.take(&2, Y, Impl.conv_of(~S, ~Y, o), K), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}}), K), List.take(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))),
      Equal.cong(Bool, List<&2, Y>, b => List.take(&2, Y, Impl.conv_job(~Y, b, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Nat.is_eq(window, 0n), False{}, ne_zero(window, drafted)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), List.take(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), Nat.sub(1n+window, count), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))),
      Equal.cong(Nat, List<&2, Y>, x => List.take(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), x, Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Impl.num_rejected(window, count, False{}), Nat.sub(1n+window, count), rejected_sub(count, window)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), Nat.sub(1n+window, count), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(Nat.sub(1n+window, count), K))), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))),
      conv_head(~Y, K, Nat.add(K, H), buf, ys, Nat.sub(1n+window, count), shaped_buf, le_add_right(K, H), le_rw_l(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, Nat.sub(1n+window, count)), Nat.add(K, H), add_comm(Nat.sub(1n+window, count), K), le_add_mono(K, Nat.sub(1n+window, count), H, le_trans(Nat.sub(1n+window, count), window, H, le_one_sub(window, count, progress), fits))), le_rw(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, List.length(&2, Y, ys)), Nat.add(K, 1n+window), Equal.cong(Nat, Nat, x => Nat.add(K, x), List.length(&2, Y, ys), 1n+window, shaped_ys), le_rw_l(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, Nat.sub(1n+window, count)), Nat.add(K, 1n+window), add_comm(Nat.sub(1n+window, count), K), le_add_mono(K, Nat.sub(1n+window, count), 1n+window, sub_le(1n+window, count))))),
      Equal.trans(List<&2, Y>, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(Nat.sub(1n+window, count), K))), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), count), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))),
      Equal.cong(Nat, List<&2, Y>, x => List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), x), K), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(Nat.sub(1n+window, count), K)), count, Equal.trans(Nat, Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(Nat.sub(1n+window, count), K)), Nat.sub(Nat.add(K, 1n+window), Nat.add(Nat.sub(1n+window, count), K)), count,
      Equal.cong(Nat, Nat, x => Nat.sub(Nat.add(K, x), Nat.add(Nat.sub(1n+window, count), K)), List.length(&2, Y, ys), 1n+window, shaped_ys),
      Equal.trans(Nat, Nat.sub(Nat.add(K, 1n+window), Nat.add(Nat.sub(1n+window, count), K)), Nat.sub(Nat.add(K, 1n+window), Nat.add(K, Nat.sub(1n+window, count))), count,
      Equal.cong(Nat, Nat, x => Nat.sub(Nat.add(K, 1n+window), x), Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, Nat.sub(1n+window, count)), add_comm(Nat.sub(1n+window, count), K)),
      Equal.trans(Nat, Nat.sub(Nat.add(K, 1n+window), Nat.add(K, Nat.sub(1n+window, count))), Nat.sub(1n+window, Nat.sub(1n+window, count)), count,
      add_sub_add(K, 1n+window, Nat.sub(1n+window, count)),
      sub_sub(1n+window, count, bounded))))),
      Equal.sym(List<&2, Y>, Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, count))), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), count), K), spec_last(~Y, K, buf, ys, count, le_rw(K, List.length(&2, Y, buf), Nat.add(K, H), shaped_buf, le_add_right(K, H)), le_rw(count, List.length(&2, Y, ys), 1n+window, shaped_ys, bounded))))))))

def conv_len_pos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    +shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +shaped_ys: {List.length(&2, Y, ys) == 1n+window : Nat},
    +shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat},
    +drafted: {Nat.is_le(1n, window) == True{} : Bool},
    +fits: {Nat.is_le(window, H) == True{} : Bool},
    +progress: {Nat.is_le(1n, count) == True{} : Bool},
    +bounded: {Nat.is_le(count, 1n+window) == True{} : Bool})
  -> {List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}))) == Nat.add(K, H) : Nat}:
  Equal.trans(Nat, List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}))), List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}})), Nat.add(K, H),
      Equal.cong(Impl.Outcome<S, Y>, Nat, o => List.length(&2, Y, Impl.conv_of(~S, ~Y, o)), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, progress, bounded)),
      Equal.trans(Nat, List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, False{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, False{})), 0n}})), List.length(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys))), Nat.add(K, H),
      Equal.cong(Bool, Nat, b => List.length(&2, Y, Impl.conv_job(~Y, b, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys))), Nat.is_eq(window, 0n), False{}, ne_zero(window, drafted)),
      Equal.trans(Nat, List.length(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys))), List.length(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), Nat.sub(1n+window, count), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys))), Nat.add(K, H),
      Equal.cong(Nat, Nat, x => List.length(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), x, Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys))), Impl.num_rejected(window, count, False{}), Nat.sub(1n+window, count), rejected_sub(count, window)),
      conv_len(~Y, K, Nat.add(K, H), buf, ys, Nat.sub(1n+window, count), shaped_buf, le_add_right(K, H), le_rw_l(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, Nat.sub(1n+window, count)), Nat.add(K, H), add_comm(Nat.sub(1n+window, count), K), le_add_mono(K, Nat.sub(1n+window, count), H, le_trans(Nat.sub(1n+window, count), window, H, le_one_sub(window, count, progress), fits))), le_rw(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, List.length(&2, Y, ys)), Nat.add(K, 1n+window), Equal.cong(Nat, Nat, x => Nat.add(K, x), List.length(&2, Y, ys), 1n+window, shaped_ys), le_rw_l(Nat.add(Nat.sub(1n+window, count), K), Nat.add(K, Nat.sub(1n+window, count)), Nat.add(K, 1n+window), add_comm(Nat.sub(1n+window, count), K), le_add_mono(K, Nat.sub(1n+window, count), 1n+window, sub_le(1n+window, count))))))))

def Laws.conv_window(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs_, shaped_ys_, shaped_buf_, drafted_, fits_, progress_, bounded_):
  +shaped_xs = shaped_xs_
  +shaped_ys = shaped_ys_
  +shaped_buf = shaped_buf_
  +drafted = drafted_
  +fits = fits_
  +progress = progress_
  +bounded = bounded_
  (conv_head_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, shaped_ys, shaped_buf, drafted, fits, progress, bounded),
    conv_len_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, shaped_ys, shaped_buf, drafted, fits, progress, bounded))

def conv_head_eos(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +window: Nat,
    +xs: List<&2, X>, +ys: List<&2, Y>, +count: Nat,
    +shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat},
    +shaped_ys: {List.length(&2, Y, ys) == 1n+window : Nat},
    +shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat},
    +drafted: {Nat.is_le(1n, window) == True{} : Bool},
    +fits: {Nat.is_le(window, H) == True{} : Bool})
  -> {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})), K) == Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})), K), List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})), 0n}}), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      Equal.cong(Impl.Outcome<S, Y>, List<&2, Y>, o => List.take(&2, Y, Impl.conv_of(~S, ~Y, o), K), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})), 0n}}, master_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+window, Impl.num_rejected(window, count, True{})), xs, s0), Impl.conv_job(~Y, Nat.is_eq(window, 0n), K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), Nat.sub(Nat.add(position, 1n+window), Impl.num_rejected(window, count, True{})), 0n}}), K), List.take(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      Equal.cong(Bool, List<&2, Y>, b => List.take(&2, Y, Impl.conv_job(~Y, b, K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Nat.is_eq(window, 0n), False{}, ne_zero(window, drafted)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_job(~Y, False{}, K, Nat.add(K, H), Impl.num_rejected(window, count, True{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), List.take(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), 0n, Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      {==},
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_rewind(~Y, K, Nat.add(K, H), 0n, Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys)), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(0n, K))), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      conv_head(~Y, K, Nat.add(K, H), buf, ys, 0n, shaped_buf, le_add_right(K, H), le_add_right(K, H), le_add_right(K, List.length(&2, Y, ys))),
      Equal.trans(List<&2, Y>, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(0n, K))), K), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), List.length(&2, Y, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      Equal.cong(Nat, List<&2, Y>, x => List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), x), K), Nat.sub(Nat.add(K, List.length(&2, Y, ys)), Nat.add(0n, K)), List.length(&2, Y, ys), add_sub_cancel(K, List.length(&2, Y, ys))),
      Equal.trans(List<&2, Y>, List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), List.length(&2, Y, ys)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, List.length(&2, Y, ys)))), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys)),
      Equal.sym(List<&2, Y>, Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys, List.length(&2, Y, ys)))), List.take(&2, Y, List.drop(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), ys), List.length(&2, Y, ys)), K), spec_last(~Y, K, buf, ys, List.length(&2, Y, ys), le_rw(K, List.length(&2, Y, buf), Nat.add(K, H), shaped_buf, le_add_right(K, H)), le_refl(List.length(&2, Y, ys)))),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), r)), List.take(&2, Y, ys, List.length(&2, Y, ys)), ys, take_all_y(~Y, ys, List.length(&2, Y, ys), {==}))))))))

def Laws.conv_window_eos(S, X, Y, step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs_, shaped_ys_, shaped_buf_, drafted_, fits_):
  +shaped_xs = shaped_xs_
  +shaped_ys = shaped_ys_
  +shaped_buf = shaped_buf_
  +drafted = drafted_
  +fits = fits_
  conv_head_eos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, window, xs, ys, count, shaped_xs, shaped_ys, shaped_buf, drafted, fits)

def fold_append(~S: Data, ~X: Data, ~step: S -> X -> S, a: List<&2, X>, +b: List<&2, X>, s: S)
  -> {Spec.fold(~S, ~X, ~step, List.append(&2, X, a, b), s) == Spec.fold(~S, ~X, ~step, b, Spec.fold(~S, ~X, ~step, a, s)) : S}:
  match a:
    case Nil{}:
      {==}
    case x <> t:
      fold_append(~S, ~X, ~step, t, b, step(s, x))

def compose_row0(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +w1: Nat, +xs1: List<&2, X>,
    +ys1: List<&2, Y>, +c1: Nat, +w2: Nat, +xs2: List<&2, X>, +ys2: List<&2, Y>, +c2: Nat,
    +shaped_xs1: {List.length(&2, X, xs1) == 1n+w1 : Nat},
    +shaped_xs2: {List.length(&2, X, xs2) == 1n+w2 : Nat},
    +progress1: {Nat.is_le(1n, c1) == True{} : Bool},
    +bounded1: {Nat.is_le(c1, 1n+w1) == True{} : Bool},
    +progress2: {Nat.is_le(1n, c2) == True{} : Bool},
    +bounded2: {Nat.is_le(c2, 1n+w2) == True{} : Bool})
  -> {Impl.row0_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})) == Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2)), s0) : S}:
  Equal.trans(S, Impl.row0_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})), Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2)), s0),
      Equal.cong(Impl.Outcome<S, Y>, S, o => Impl.row0_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, o, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1)),
      Equal.trans(S, Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs2, c2), Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0)), Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2)), s0),
      prefix_pos(~S, ~X, ~Y, ~step, K, H, Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n, w2, xs2, ys2, c2, shaped_xs2, progress2, bounded2),
      Equal.trans(S, Spec.fold(~S, ~X, ~step, List.take(&2, X, xs2, c2), Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0)), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs2, c2), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs1, c1), s0)), Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2)), s0),
      Equal.cong(S, S, s => Spec.fold(~S, ~X, ~step, List.take(&2, X, xs2, c2), s), Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs1, c1), s0), Equal.trans(S, Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}})), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs1, c1), s0),
      Equal.cong(Impl.Outcome<S, Y>, S, o => Impl.row0_of(~S, ~Y, o), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      prefix_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      Equal.sym(S, Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2)), s0), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs2, c2), Spec.fold(~S, ~X, ~step, List.take(&2, X, xs1, c1), s0)), fold_append(~S, ~X, ~step, List.take(&2, X, xs1, c1), List.take(&2, X, xs2, c2), s0)))))

def add_assoc(+a: Nat, +b: Nat, +c: Nat)
  -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
        add_assoc(p, b, c))

def append_assoc(~Y: Data, a: List<&2, Y>, +b: List<&2, Y>, +c: List<&2, Y>)
  -> {List.append(&2, Y, List.append(&2, Y, a, b), c) == List.append(&2, Y, a, List.append(&2, Y, b, c)) : List<&2, Y>}:
  match a:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, Y>, List<&2, Y>, r => x <> r, List.append(&2, Y, List.append(&2, Y, t, b), c), List.append(&2, Y, t, List.append(&2, Y, b, c)),
        append_assoc(~Y, t, b, c))

def drop_append_le(~Y: Data, a: List<&2, Y>, +b: List<&2, Y>, +d: Nat, h: {Nat.is_le(d, List.length(&2, Y, a)) == True{} : Bool})
  -> {List.drop(&2, Y, List.append(&2, Y, a, b), d) == List.append(&2, Y, List.drop(&2, Y, a, d), b) : List<&2, Y>}:
  match a d:
    case Nil{} 0n:
      drop_zero(~Y, b)
    case Nil{} 1n+q:
      Empty.absurd({List.drop(&2, Y, List.append(&2, Y, Nil{}, b), 1n+q) == List.append(&2, Y, List.drop(&2, Y, Nil{}, 1n+q), b) : List<&2, Y>},
        rp_false_true(h))
    case x <> t 0n:
      {==}
    case x <> t 1n+q:
      drop_append_le(~Y, t, b, q, h)

# Keeping the last K twice equals keeping them once (a has at least K entries).
def last_last(~Y: Data, +K: Nat, +a: List<&2, Y>, +b: List<&2, Y>, +h: {Nat.is_le(K, List.length(&2, Y, a)) == True{} : Bool})
  -> {Spec.last(~Y, K, List.append(&2, Y, Spec.last(~Y, K, a), b)) == Spec.last(~Y, K, List.append(&2, Y, a, b)) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, Spec.last(~Y, K, List.append(&2, Y, List.drop(&2, Y, a, Nat.sub(List.length(&2, Y, a), K)), b)), Spec.last(~Y, K, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K))), List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K)),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => Spec.last(~Y, K, r), List.append(&2, Y, List.drop(&2, Y, a, Nat.sub(List.length(&2, Y, a), K)), b), List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K)), Equal.sym(List<&2, Y>, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K)), List.append(&2, Y, List.drop(&2, Y, a, Nat.sub(List.length(&2, Y, a), K)), b), drop_append_le(~Y, a, b, Nat.sub(List.length(&2, Y, a), K), sub_le(List.length(&2, Y, a), K)))),
      Equal.trans(List<&2, Y>, Spec.last(~Y, K, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K))), List.drop(&2, Y, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K)), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K)), List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K)),
      Equal.cong(Nat, List<&2, Y>, x => List.drop(&2, Y, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K)), Nat.sub(x, K)), List.length(&2, Y, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K))), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), len_drop(~Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K))),
      Equal.trans(List<&2, Y>, List.drop(&2, Y, List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K)), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K)), List.drop(&2, Y, List.append(&2, Y, a, b), Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K))), List.drop(&2, Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K)),
      drop_drop(~Y, List.append(&2, Y, a, b), Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K)),
      Equal.cong(Nat, List<&2, Y>, x => List.drop(&2, Y, List.append(&2, Y, a, b), x), Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K)), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K), Equal.trans(Nat, Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K)), Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.add(Nat.sub(List.length(&2, Y, a), K), K))), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.sub(List.length(&2, Y, a), K), x), Nat.sub(Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K)), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.add(Nat.sub(List.length(&2, Y, a), K), K)), sub_sub_add(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.sub(List.length(&2, Y, a), K), K)),
      Equal.trans(Nat, Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), Nat.add(Nat.sub(List.length(&2, Y, a), K), K))), Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), List.length(&2, Y, a))), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), x)), Nat.add(Nat.sub(List.length(&2, Y, a), K), K), List.length(&2, Y, a), sub_add_cancel(List.length(&2, Y, a), K, h)),
      Equal.trans(Nat, Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), List.length(&2, Y, a))), Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), List.length(&2, Y, a))), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(x, List.length(&2, Y, a))), List.length(&2, Y, List.append(&2, Y, a, b)), Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), len_append(~Y, a, b)),
      Equal.trans(Nat, Nat.add(Nat.sub(List.length(&2, Y, a), K), Nat.sub(Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), List.length(&2, Y, a))), Nat.add(Nat.sub(List.length(&2, Y, a), K), List.length(&2, Y, b)), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.sub(List.length(&2, Y, a), K), x), Nat.sub(Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), List.length(&2, Y, a)), List.length(&2, Y, b), add_sub_cancel(List.length(&2, Y, a), List.length(&2, Y, b))),
      Equal.trans(Nat, Nat.add(Nat.sub(List.length(&2, Y, a), K), List.length(&2, Y, b)), Nat.add(List.length(&2, Y, b), Nat.sub(List.length(&2, Y, a), K)), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      add_comm(Nat.sub(List.length(&2, Y, a), K), List.length(&2, Y, b)),
      Equal.trans(Nat, Nat.add(List.length(&2, Y, b), Nat.sub(List.length(&2, Y, a), K)), Nat.sub(Nat.add(List.length(&2, Y, b), List.length(&2, Y, a)), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.sym(Nat, Nat.sub(Nat.add(List.length(&2, Y, b), List.length(&2, Y, a)), K), Nat.add(List.length(&2, Y, b), Nat.sub(List.length(&2, Y, a), K)), sub_add(List.length(&2, Y, b), List.length(&2, Y, a), K, h)),
      Equal.trans(Nat, Nat.sub(Nat.add(List.length(&2, Y, b), List.length(&2, Y, a)), K), Nat.sub(Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), K), Nat.sub(List.length(&2, Y, List.append(&2, Y, a, b)), K),
      Equal.cong(Nat, Nat, x => Nat.sub(x, K), Nat.add(List.length(&2, Y, b), List.length(&2, Y, a)), Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), add_comm(List.length(&2, Y, b), List.length(&2, Y, a))),
      Equal.cong(Nat, Nat, x => Nat.sub(x, K), Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), List.length(&2, Y, List.append(&2, Y, a, b)), Equal.sym(Nat, List.length(&2, Y, List.append(&2, Y, a, b)), Nat.add(List.length(&2, Y, a), List.length(&2, Y, b)), len_append(~Y, a, b))))))))))))))

def compose_position(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +w1: Nat, +xs1: List<&2, X>,
    +ys1: List<&2, Y>, +c1: Nat, +w2: Nat, +xs2: List<&2, X>, +ys2: List<&2, Y>, +c2: Nat,
    +shaped_xs1: {List.length(&2, X, xs1) == 1n+w1 : Nat},
    +shaped_xs2: {List.length(&2, X, xs2) == 1n+w2 : Nat},
    +progress1: {Nat.is_le(1n, c1) == True{} : Bool},
    +bounded1: {Nat.is_le(c1, 1n+w1) == True{} : Bool},
    +progress2: {Nat.is_le(1n, c2) == True{} : Bool},
    +bounded2: {Nat.is_le(c2, 1n+w2) == True{} : Bool})
  -> {Impl.position_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})) == Nat.add(position, Nat.add(c1, c2)) : Nat}:
  Equal.trans(Nat, Impl.position_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})), Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Nat.add(position, Nat.add(c1, c2)),
      Equal.cong(Impl.Outcome<S, Y>, Nat, o => Impl.position_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, o, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1)),
      Equal.trans(Nat, Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), Nat.add(Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), c2), Nat.add(position, Nat.add(c1, c2)),
      position_pos(~S, ~X, ~Y, ~step, K, H, Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n, w2, xs2, ys2, c2, shaped_xs2, progress2, bounded2),
      Equal.trans(Nat, Nat.add(Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), c2), Nat.add(Nat.add(position, c1), c2), Nat.add(position, Nat.add(c1, c2)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c2), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), Nat.add(position, c1), Equal.trans(Nat, Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}})), Nat.add(position, c1),
      Equal.cong(Impl.Outcome<S, Y>, Nat, o => Impl.position_of(~S, ~Y, o), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      position_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      add_assoc(position, c1, c2))))

def compose_conv(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    +s0: S, +buf: List<&2, Y>, +position: Nat, +lh: Nat, +w1: Nat, +xs1: List<&2, X>,
    +ys1: List<&2, Y>, +c1: Nat, +w2: Nat, +xs2: List<&2, X>, +ys2: List<&2, Y>, +c2: Nat,
    +shaped_xs1: {List.length(&2, X, xs1) == 1n+w1 : Nat},
    +shaped_xs2: {List.length(&2, X, xs2) == 1n+w2 : Nat},
    +progress1: {Nat.is_le(1n, c1) == True{} : Bool},
    +bounded1: {Nat.is_le(c1, 1n+w1) == True{} : Bool},
    +progress2: {Nat.is_le(1n, c2) == True{} : Bool},
    +bounded2: {Nat.is_le(c2, 1n+w2) == True{} : Bool},
    +shaped_ys1: {List.length(&2, Y, ys1) == 1n+w1 : Nat},
    +shaped_ys2: {List.length(&2, Y, ys2) == 1n+w2 : Nat},
    +shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat},
    +drafted1: {Nat.is_le(1n, w1) == True{} : Bool},
    +fits1: {Nat.is_le(w1, H) == True{} : Bool},
    +drafted2: {Nat.is_le(1n, w2) == True{} : Bool},
    +fits2: {Nat.is_le(w2, H) == True{} : Bool})
  -> {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})), K) == Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))) : List<&2, Y>}:
  Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), w2, xs2, ys2, Accept.Verdict{c2, False{}})), K), List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))),
      Equal.cong(Impl.Outcome<S, Y>, List<&2, Y>, o => List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H, o, w2, xs2, ys2, Accept.Verdict{c2, False{}})), K), Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1)),
      Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}, w2, xs2, ys2, Accept.Verdict{c2, False{}})), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), K), List.take(&2, Y, ys2, c2))), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))),
      conv_head_pos(~S, ~X, ~Y, ~step, K, H, Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n, w2, xs2, ys2, c2, shaped_xs2, shaped_ys2, Equal.trans(Nat, List.length(&2, Y, Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1))), List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}))), Nat.add(K, H),
      Equal.cong(Impl.Outcome<S, Y>, Nat, o => List.length(&2, Y, Impl.conv_of(~S, ~Y, o)), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      conv_len_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, shaped_ys1, shaped_buf, drafted1, fits1, progress1, bounded1)), drafted2, fits2, progress2, bounded2),
      Equal.trans(List<&2, Y>, Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), K), List.take(&2, Y, ys2, c2))), Spec.last(~Y, K, List.append(&2, Y, Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))), List.take(&2, Y, ys2, c2))), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => Spec.last(~Y, K, List.append(&2, Y, r, List.take(&2, Y, ys2, c2))), List.take(&2, Y, Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))), Equal.trans(List<&2, Y>, List.take(&2, Y, Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), K), List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}})), K), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))),
      Equal.cong(Impl.Outcome<S, Y>, List<&2, Y>, o => List.take(&2, Y, Impl.conv_of(~S, ~Y, o), K), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Equal.sym(Impl.Outcome<S, Y>, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, w1, xs1, ys1, Accept.Verdict{c1, False{}}), Impl.Committed{Impl.Engine{Impl.replay(~S, ~X, ~step, Nat.sub(1n+w1, Impl.num_rejected(w1, c1, False{})), xs1, s0), Impl.conv_job(~Y, Nat.is_eq(w1, 0n), K, Nat.add(K, H), Impl.num_rejected(w1, c1, False{}), Impl.conv_write(~Y, K, Nat.add(K, H), buf, ys1)), Nat.sub(Nat.add(position, 1n+w1), Impl.num_rejected(w1, c1, False{})), 0n}}, master_ok(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, progress1, bounded1))),
      conv_head_pos(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, shaped_xs1, shaped_ys1, shaped_buf, drafted1, fits1, progress1, bounded1))),
      Equal.trans(List<&2, Y>, Spec.last(~Y, K, List.append(&2, Y, Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))), List.take(&2, Y, ys2, c2))), Spec.last(~Y, K, List.append(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1)), List.take(&2, Y, ys2, c2))), Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))),
      last_last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1)), List.take(&2, Y, ys2, c2), le_rw(K, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))), Nat.add(K, c1), Equal.trans(Nat, List.length(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1))), Nat.add(List.length(&2, Y, List.take(&2, Y, buf, K)), List.length(&2, Y, List.take(&2, Y, ys1, c1))), Nat.add(K, c1),
      len_append(~Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1)),
      Equal.trans(Nat, Nat.add(List.length(&2, Y, List.take(&2, Y, buf, K)), List.length(&2, Y, List.take(&2, Y, ys1, c1))), Nat.add(K, List.length(&2, Y, List.take(&2, Y, ys1, c1))), Nat.add(K, c1),
      Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, Y, List.take(&2, Y, ys1, c1))), List.length(&2, Y, List.take(&2, Y, buf, K)), K, len_take(~Y, buf, K, le_rw(K, List.length(&2, Y, buf), Nat.add(K, H), shaped_buf, le_add_right(K, H)))),
      Equal.cong(Nat, Nat, x => Nat.add(K, x), List.length(&2, Y, List.take(&2, Y, ys1, c1)), c1, len_take(~Y, ys1, c1, le_rw(c1, List.length(&2, Y, ys1), 1n+w1, shaped_ys1, bounded1))))), le_add_right(K, c1))),
      Equal.cong(List<&2, Y>, List<&2, Y>, r => Spec.last(~Y, K, r), List.append(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1)), List.take(&2, Y, ys2, c2)), List.append(&2, Y, List.take(&2, Y, buf, K), List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2))), append_assoc(~Y, List.take(&2, Y, buf, K), List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2)))))))

def Laws.compose(S, X, Y, step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, w2, xs2, ys2, c2, shaped_xs1_, shaped_xs2_, progress1_, bounded1_, progress2_, bounded2_, shaped_ys1_, shaped_ys2_, shaped_buf_, drafted1_, fits1_, drafted2_, fits2_):
  +shaped_xs1 = shaped_xs1_
  +shaped_xs2 = shaped_xs2_
  +progress1 = progress1_
  +bounded1 = bounded1_
  +progress2 = progress2_
  +bounded2 = bounded2_
  +shaped_ys1 = shaped_ys1_
  +shaped_ys2 = shaped_ys2_
  +shaped_buf = shaped_buf_
  +drafted1 = drafted1_
  +fits1 = fits1_
  +drafted2 = drafted2_
  +fits2 = fits2_
  (compose_row0(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, w2, xs2, ys2, c2, shaped_xs1, shaped_xs2, progress1, bounded1, progress2, bounded2),
    compose_conv(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, w2, xs2, ys2, c2, shaped_xs1, shaped_xs2, progress1, bounded1, progress2, bounded2, shaped_ys1, shaped_ys2, shaped_buf, drafted1, fits1, drafted2, fits2),
    compose_position(~S, ~X, ~Y, ~step, K, H, s0, buf, position, lh, w1, xs1, ys1, c1, w2, xs2, ys2, c2, shaped_xs1, shaped_xs2, progress1, bounded1, progress2, bounded2))
