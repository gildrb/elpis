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
