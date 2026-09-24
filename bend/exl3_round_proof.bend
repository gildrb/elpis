# Proofs of the device round-advance laws. Structural evidence only: no
# unsafe definitions, axioms, holes, foreign proof code or answer tables.
# The acceptance facts come from the proven exl3_accept laws.
import Base
import ./exl3_accept_spec.bend as Accept
import ./exl3_accept_laws.bend as AcceptLaws
import ./exl3_accept_proof.bend as AcceptProof
import ./exl3_round.bend as Impl
import ./exl3_round_spec.bend as Spec
import ./exl3_round_laws.bend as Laws

def Laws.stop_commits_nothing(targets, count):
  {==}

def Laws.advance_replay_eos(count, k):
  ({==}, {==})

def Laws.advance_error_stops(eos, window, base, interval, position, budget,
    anchor, checkpoint, stopped):
  match stopped:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.stop_absorbing(verdicts, window, base, interval, position, budget,
    anchor, checkpoint):
  match verdicts:
    case Nil{}:
      {==}
    case Accept.Verdict{count, eos} <> rest:
      Laws.stop_absorbing(rest, window, base, interval, position, budget,
        anchor, checkpoint)

def Laws.checkpoint_invariant(count, eos, window, base, interval, position,
    budget, anchor, stopped):
  match count:
    case 0n:
      match stopped:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+index:
      match stopped:
        case True{}:
          {==}
        case False{}:
          {==}

# List facts about the committed prefix.
def take_length(+xs: List<&2, U32>, +n: Nat,
    le: {Nat.is_le(n, List.length(&2, U32, xs)) == True{} : Bool})
  -> {List.length(&2, U32, List.take(&2, U32, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, AcceptProof.false_true(le))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %take_length(t, p, le)
        : {1n+List.length(&2, U32, List.take(&2, U32, t, p)) == 1n+_ : Nat}
      {==}

def drop_length(+xs: List<&2, U32>, +n: Nat)
  -> {List.length(&2, U32, List.drop(&2, U32, xs, n)) ==
    Nat.sub(List.length(&2, U32, xs), n) : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      drop_length(t, p)

# The last element of h <> take(xs, i) is (h <> xs)[i].
def last_take(+xs: List<&2, U32>, +i: Nat, +h: U32,
    le: {Nat.is_le(i, List.length(&2, U32, xs)) == True{} : Bool})
  -> {Some{List.last.go(&2, U32, List.take(&2, U32, xs, i), h)} ==
    List.get(&2, U32, h <> xs, i) : Maybe<&2, U32>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      Empty.absurd({Some{h} == List.get(&2, U32, [h], 1n+j) : Maybe<&2, U32>},
        AcceptProof.false_true(le))
    case x <> r 0n:
      {==}
    case x <> r 1n+j:
      last_take(r, j, x, le)

def get_last(+xs: List<&2, U32>, +i: Nat,
    le: {Nat.is_le(1n+i, List.length(&2, U32, xs)) == True{} : Bool})
  -> {List.last(&2, U32, List.take(&2, U32, xs, 1n+i)) ==
    List.get(&2, U32, xs, i) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      Empty.absurd({List.last(&2, U32, List.take(&2, U32, Nil{}, 1n+i)) ==
        List.get(&2, U32, Nil{}, i) : Maybe<&2, U32>},
        AcceptProof.false_true(le))
    case h <> t:
      last_take(t, i, h, le)

# Nat facts.
def sub_add(+b: Nat, +n: Nat, le: {Nat.is_le(n, b) == True{} : Bool})
  -> {Nat.add(Nat.sub(b, n), n) == b : Nat}:
  match b n:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      Empty.absurd({Nat.add(0n, 1n+p) == 0n : Nat}, AcceptProof.false_true(le))
    case 1n+q 0n:
      AcceptProof.add_zero(1n+q)
    case 1n+q 1n+p:
      %Equal.sym(Nat, Nat.add(Nat.sub(q, p), 1n+p),
          1n+Nat.add(Nat.sub(q, p), p),
          AcceptProof.add_succ(Nat.sub(q, p), p)) : {_ == 1n+q : Nat}
      %sub_add(q, p, le) : {1n+Nat.add(Nat.sub(q, p), p) == 1n+_ : Nat}
      {==}

def lt_sub(+b: Nat, +n: Nat, lt: {Nat.is_lt(n, b) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.sub(b, n)) == True{} : Bool}:
  match b n:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, AcceptProof.false_true(lt))
    case 0n 1n+p:
      Empty.absurd({False{} == True{} : Bool}, AcceptProof.false_true(lt))
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      lt_sub(q, p, lt)

def add_one(+c: Nat) -> {1n+c == Nat.add(c, 1n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      %add_one(p) : {2n+p == 1n+_ : Nat}
      {==}

# Consumer arithmetic on the served domain count <= k + 1.
def full_succ(+b: Bool, +p: Nat, +q: Nat)
  -> {Impl.full(b, 1n+p, 1n+q) == 1n+Impl.full(b, p, q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def full_eq(+n: Nat, +k: Nat, le: {Nat.is_le(n, 1n+k) == True{} : Bool})
  -> {Impl.full(Nat.is_gt(n, k), n, k) == n : Nat}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n 0n:
      {==}
    case 2n+r 0n:
      Empty.absurd({1n == 2n+r : Nat}, AcceptProof.false_true(le))
    case 1n+p 1n+q:
      %Equal.sym(Nat, Impl.full(Nat.is_gt(p, q), 1n+p, 1n+q),
          1n+Impl.full(Nat.is_gt(p, q), p, q),
          full_succ(Nat.is_gt(p, q), p, q)) : {_ == 1n+p : Nat}
      %full_eq(p, q, le) : {1n+Impl.full(Nat.is_gt(p, q), p, q) == 1n+_ : Nat}
      {==}

def keep_succ(+b: Bool, +p: Nat, +q: Nat)
  -> {Impl.keep(b, 1n+p, 1n+q) == Impl.keep(b, p, q) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def keep_eq(+n: Nat, +k: Nat, le: {Nat.is_le(n, 1n+k) == True{} : Bool})
  -> {Impl.keep(Nat.is_gt(n, k), n, k) == Nat.sub(1n+k, n) : Nat}:
  match n k:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n 0n:
      {==}
    case 2n+r 0n:
      {==}
    case 1n+p 1n+q:
      %Equal.sym(Nat, Impl.keep(Nat.is_gt(p, q), 1n+p, 1n+q),
          Impl.keep(Nat.is_gt(p, q), p, q),
          keep_succ(Nat.is_gt(p, q), p, q)) : {_ == Nat.sub(1n+q, p) : Nat}
      keep_eq(p, q, le)

# Budget exhaustion forces eos: the halting position of an explained verdict
# reports eos, or its count is still below the budget.
def halts0(+targets: List<&2, U32>, +proposals: List<&2, U32>,
    +stops: List<&2, U32>, +committed: Nat, +budget: Nat, +checkpoint: Nat,
    +flag: Bool,
    halting: {Accept.halts(0n, targets, proposals, stops, committed, budget,
      checkpoint, flag) == True{} : Bool})
  -> {Bool.or(flag, Nat.is_lt(1n+committed, budget)) == True{} : Bool}:
  match targets:
    case Nil{}:
      Empty.absurd(
        {Bool.or(flag, Nat.is_lt(1n+committed, budget)) == True{} : Bool},
        AcceptProof.false_true(halting))
    case t <> rest:
      match proposals:
        case Nil{}:
          match flag:
            case True{}:
              {==}
            case False{}:
              AcceptProof.cmp_ge_false(Nat.cmp(1n+committed, budget),
                AcceptProof.not_or_right(Accept.member(stops, t),
                  Nat.is_ge(1n+committed, budget), halting))
        case p <> more:
          match flag:
            case True{}:
              {==}
            case False{}:
              AcceptProof.cmp_ge_false(Nat.cmp(1n+committed, budget),
                AcceptProof.not_or_right(Accept.member(stops, t),
                  Nat.is_ge(1n+committed, budget),
                  AcceptProof.and_right(
                    Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint)),
                    Bool.not(Bool.or(Accept.member(stops, t),
                      Nat.is_ge(1n+committed, budget))),
                    halting)))

def halts_ends(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat, +flag: Bool,
    halting: {Accept.halts(passed, targets, proposals, stops, committed,
      budget, checkpoint, flag) == True{} : Bool})
  -> {Bool.or(flag, Nat.is_lt(Nat.add(committed, 1n+passed), budget)) ==
    True{} : Bool}:
  match passed:
    case 0n:
      %add_one(committed)
        : {Bool.or(flag, Nat.is_lt(_, budget)) == True{} : Bool}
      halts0(targets, proposals, stops, committed, budget, checkpoint, flag,
        halting)
    case 1n+more_passed:
      match targets:
        case Nil{}:
          Empty.absurd(
            {Bool.or(flag, Nat.is_lt(Nat.add(committed, 2n+more_passed), budget)) ==
              True{} : Bool},
            AcceptProof.false_true(halting))
        case t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd(
                {Bool.or(flag, Nat.is_lt(Nat.add(committed, 2n+more_passed), budget)) ==
              True{} : Bool},
                AcceptProof.false_true(halting))
            case p <> more:
              %Equal.sym(Nat, Nat.add(committed, 2n+more_passed),
                  1n+Nat.add(committed, 1n+more_passed),
                  AcceptProof.add_succ(committed, 1n+more_passed))
                : {Bool.or(flag, Nat.is_lt(_, budget)) == True{} : Bool}
              halts_ends(more_passed, rest, more, stops, 1n+committed, budget,
                checkpoint, flag, halting)

def explains_ends(+count: Nat, +flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat,
    explained: {Accept.explains(count, flag, targets, proposals, stops, budget,
      checkpoint) == True{} : Bool})
  -> {Bool.or(flag, Nat.is_lt(count, budget)) == True{} : Bool}:
  match count:
    case 0n:
      Empty.absurd({Bool.or(flag, Nat.is_lt(0n, budget)) == True{} : Bool},
        AcceptProof.false_true(explained))
    case 1n+passed:
      halts_ends(passed, targets, proposals, stops, 0n, budget, checkpoint,
        flag,
        AcceptProof.and_right(
          Accept.passes(passed, targets, proposals, stops, 0n, budget,
            checkpoint),
          Accept.halts(passed, targets, proposals, stops, 0n, budget,
            checkpoint, flag),
          explained))

# The advance on an arbitrary decision count n <= |targets|.
def position_gen(+n: Nat, -e: Bool, -k: Nat, -base: Nat, -interval: Nat,
    +position: Nat, -budget: Nat, -anchor: Nat, -ckpt: Nat, +stopped: Bool,
    +targets: List<&2, U32>,
    le: {Nat.is_le(n, List.length(&2, U32, targets)) == True{} : Bool})
  -> {Impl.position(Impl.advance(n, e, k, base, interval,
      Impl.State{position, budget, anchor, ckpt, stopped})) ==
    Nat.add(position, List.length(&2, U32, Spec.committed(targets, n,
      stopped))) : Nat}:
  match n:
    case 0n:
      match stopped:
        case True{}:
          Equal.sym(Nat, Nat.add(position, 0n), position,
            AcceptProof.add_zero(position))
        case False{}:
          %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, targets, 0n)),
              0n, take_length(targets, 0n, le))
            : {position == Nat.add(position, _) : Nat}
          Equal.sym(Nat, Nat.add(position, 0n), position,
            AcceptProof.add_zero(position))
    case 1n+i:
      match stopped:
        case True{}:
          Equal.sym(Nat, Nat.add(position, 0n), position,
            AcceptProof.add_zero(position))
        case False{}:
          %Equal.sym(Nat,
              List.length(&2, U32, List.take(&2, U32, targets, 1n+i)), 1n+i,
              take_length(targets, 1n+i, le))
            : {Nat.add(position, 1n+i) == Nat.add(position, _) : Nat}
          {==}

def budget_gen(+n: Nat, -e: Bool, -k: Nat, -base: Nat, -interval: Nat,
    -position: Nat, +budget: Nat, -anchor: Nat, -ckpt: Nat, +stopped: Bool,
    +targets: List<&2, U32>,
    le: {Nat.is_le(n, List.length(&2, U32, targets)) == True{} : Bool},
    fits: {Nat.is_le(n, budget) == True{} : Bool})
  -> {Nat.add(Impl.budget(Impl.advance(n, e, k, base, interval,
      Impl.State{position, budget, anchor, ckpt, stopped})),
    List.length(&2, U32, Spec.committed(targets, n, stopped))) == budget
    : Nat}:
  match n:
    case 0n:
      match stopped:
        case True{}:
          AcceptProof.add_zero(budget)
        case False{}:
          %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, targets, 0n)),
              0n, take_length(targets, 0n, le))
            : {Nat.add(budget, _) == budget : Nat}
          AcceptProof.add_zero(budget)
    case 1n+i:
      match stopped:
        case True{}:
          AcceptProof.add_zero(budget)
        case False{}:
          %Equal.sym(Nat,
              List.length(&2, U32, List.take(&2, U32, targets, 1n+i)), 1n+i,
              take_length(targets, 1n+i, le))
            : {Nat.add(Nat.sub(budget, 1n+i), _) == budget : Nat}
          sub_add(budget, 1n+i, fits)

def live_gen(+n: Nat, +stopped: Bool, +e: Bool, -k: Nat, -base: Nat,
    -interval: Nat, -position: Nat, +budget: Nat, -anchor: Nat, -ckpt: Nat,
    ends: {Bool.or(e, Nat.is_lt(n, budget)) == True{} : Bool})
  -> {Bool.or(Impl.stopped(Impl.advance(n, e, k, base, interval,
      Impl.State{position, budget, anchor, ckpt, stopped})),
    Nat.is_lt(0n, Impl.budget(Impl.advance(n, e, k, base, interval,
      Impl.State{position, budget, anchor, ckpt, stopped})))) == True{}
    : Bool}:
  match n:
    case 0n:
      match stopped:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+i:
      match stopped:
        case True{}:
          {==}
        case False{}:
          match e:
            case True{}:
              {==}
            case False{}:
              lt_sub(budget, 1n+i, ends)

def anchor_gen(+n: Nat, -e: Bool, -k: Nat, -base: Nat, -interval: Nat,
    -position: Nat, -budget: Nat, -anchor: Nat, -ckpt: Nat,
    +targets: List<&2, U32>,
    pos: {Nat.is_lt(0n, n) == True{} : Bool},
    le: {Nat.is_le(n, List.length(&2, U32, targets)) == True{} : Bool})
  -> {List.get(&2, U32, targets, Impl.anchor(Impl.advance(n, e, k, base,
      interval, Impl.State{position, budget, anchor, ckpt, False{}}))) ==
    List.last(&2, U32, Spec.committed(targets, n, False{})) : Maybe<&2, U32>}:
  match n:
    case 0n:
      Empty.absurd({List.get(&2, U32, targets, Impl.anchor(Impl.advance(0n, e,
          k, base, interval, Impl.State{position, budget, anchor, ckpt,
          False{}}))) ==
        List.last(&2, U32, Spec.committed(targets, 0n, False{}))
        : Maybe<&2, U32>}, AcceptProof.false_true(pos))
    case 1n+i:
      Equal.sym(Maybe<&2, U32>,
        List.last(&2, U32, List.take(&2, U32, targets, 1n+i)),
        List.get(&2, U32, targets, i), get_last(targets, i, le))

def refresh_gen(+n: Nat, -e: Bool, -k: Nat, -base: Nat, -interval: Nat,
    +position: Nat, -budget: Nat, -anchor: Nat, -ckpt: Nat)
  -> {Impl.refresh(position, n) == Impl.position(Impl.advance(n, e, k, base,
      interval, Impl.State{position, budget, anchor, ckpt, False{}})) : Nat}:
  match n:
    case 0n:
      AcceptProof.add_zero(position)
    case 1n+i:
      {==}

def eos_gen(+n: Nat, +stopped: Bool, +e: Bool, -k: Nat, -base: Nat,
    -interval: Nat, -position: Nat, -budget: Nat, -anchor: Nat, -ckpt: Nat,
    ended: {e == True{} : Bool})
  -> {Impl.stopped(Impl.advance(n, e, k, base, interval,
      Impl.State{position, budget, anchor, ckpt, stopped})) == True{} : Bool}:
  match n:
    case 0n:
      match stopped:
        case True{}:
          {==}
        case False{}:
          {==}
    case 1n+i:
      match stopped:
        case True{}:
          {==}
        case False{}:
          ended

def steps_gen(+n: Nat, +e: Bool, +k: Nat, +targets: List<&2, U32>,
    live: {e == False{} : Bool},
    le: {Nat.is_le(n, 1n+k) == True{} : Bool},
    bound: {Nat.is_le(n, List.length(&2, U32, targets)) == True{} : Bool})
  -> {Impl.steps(n, e, k) ==
    List.length(&2, U32, Spec.committed(targets, n, False{})) : Nat}:
  %Equal.sym(Bool, e, False{}, live)
    : {Impl.steps(n, _, k) ==
      List.length(&2, U32, Spec.committed(targets, n, False{})) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, targets, n)), n,
      take_length(targets, n, bound))
    : {Impl.steps(n, False{}, k) == _ : Nat}
  full_eq(n, k, le)

def offset_gen(+n: Nat, +e: Bool, +k: Nat, +targets: List<&2, U32>,
    live: {e == False{} : Bool},
    le: {Nat.is_le(n, 1n+k) == True{} : Bool},
    shaped: {List.length(&2, U32, targets) == 1n+k : Nat})
  -> {Impl.offset(n, e, k) ==
    List.length(&2, U32, Spec.uncommitted(targets, n)) : Nat}:
  %Equal.sym(Bool, e, False{}, live)
    : {Impl.offset(n, _, k) ==
      List.length(&2, U32, Spec.uncommitted(targets, n)) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.drop(&2, U32, targets, n)),
      Nat.sub(List.length(&2, U32, targets), n), drop_length(targets, n))
    : {Impl.offset(n, False{}, k) == _ : Nat}
  %Equal.sym(Nat, List.length(&2, U32, targets), 1n+k, shaped)
    : {Impl.offset(n, False{}, k) == Nat.sub(_, n) : Nat}
  keep_eq(n, k, le)

# The two halves of accept_bounds.
def count_le_targets(+targets: List<&2, U32>, +proposals: List<&2, U32>,
    +stops: List<&2, U32>, +budget: Nat, +checkpoint: Nat,
    shaped: {List.length(&2, U32, targets) ==
      1n+List.length(&2, U32, proposals) : Nat})
  -> {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, targets)) == True{}
    : Bool}:
  Pair.fst(
    {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, targets)) == True{}
      : Bool},
    {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), 1n+List.length(&2, U32, proposals)) ==
      True{} : Bool},
    AcceptLaws.accept_bounds(targets, proposals, stops, budget, checkpoint,
      shaped))

def count_le_window(+targets: List<&2, U32>, +proposals: List<&2, U32>,
    +stops: List<&2, U32>, +budget: Nat, +checkpoint: Nat,
    shaped: {List.length(&2, U32, targets) ==
      1n+List.length(&2, U32, proposals) : Nat})
  -> {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), 1n+List.length(&2, U32, proposals)) ==
    True{} : Bool}:
  Pair.snd(
    {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, targets)) == True{}
      : Bool},
    {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)), 1n+List.length(&2, U32, proposals)) ==
      True{} : Bool},
    AcceptLaws.accept_bounds(targets, proposals, stops, budget, checkpoint,
      shaped))

# The laws: instantiate at the verdict of Accept.accept, with the count's
# bounds, progress, budget and characterization from the exl3_accept laws.
def Laws.advance_position(targets, proposals, stops, budget, checkpoint, base,
    interval, position, anchor, stopped, shaped):
  position_gen(
    Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    List.length(&2, U32, proposals), base, interval, position, budget, anchor,
    checkpoint, stopped, targets, count_le_targets(targets, proposals, stops, budget, checkpoint, shaped))

def Laws.advance_replay(targets, proposals, stops, budget, checkpoint, shaped,
    live):
  (steps_gen(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), targets, live, count_le_window(targets, proposals, stops, budget, checkpoint, shaped), count_le_targets(targets, proposals, stops, budget, checkpoint, shaped)),
    offset_gen(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), targets, live, count_le_window(targets, proposals, stops, budget, checkpoint, shaped), shaped),
    AcceptLaws.accept_progress(targets, proposals, stops, budget, checkpoint,
      shaped))

def Laws.advance_refresh(targets, proposals, stops, budget, checkpoint, base,
    interval, position, anchor, shaped):
  (refresh_gen(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval, position, budget,
      anchor, checkpoint),
    count_le_window(targets, proposals, stops, budget, checkpoint, shaped))

def Laws.advance_anchor(targets, proposals, stops, budget, checkpoint, base,
    interval, position, anchor, shaped):
  anchor_gen(
    Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    List.length(&2, U32, proposals), base, interval, position, budget, anchor,
    checkpoint, targets,
    AcceptLaws.accept_progress(targets, proposals, stops, budget, checkpoint,
      shaped),
    count_le_targets(targets, proposals, stops, budget, checkpoint, shaped))

def Laws.advance_budget(targets, proposals, stops, budget, checkpoint, base,
    interval, position, anchor, stopped, shaped, positive):
  budget_gen(
    Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    List.length(&2, U32, proposals), base, interval, position, budget, anchor,
    checkpoint, stopped, targets, count_le_targets(targets, proposals, stops, budget, checkpoint, shaped),
    AcceptLaws.accept_budget(targets, proposals, stops, budget, checkpoint,
      shaped, positive))

def Laws.advance_budget_live(targets, proposals, stops, budget, checkpoint,
    base, interval, position, anchor, stopped, shaped):
  live_gen(
    Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    stopped,
    Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    List.length(&2, U32, proposals), base, interval, position, budget, anchor,
    checkpoint,
    explains_ends(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      targets, proposals, stops, budget, checkpoint,
      AcceptLaws.accept_explained(targets, proposals, stops, budget,
        checkpoint, shaped)))

def Laws.advance_eos_stops(targets, proposals, stops, budget, checkpoint,
    base, interval, position, anchor, stopped, ended):
  eos_gen(
    Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    stopped,
    Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
    List.length(&2, U32, proposals), base, interval, position, budget, anchor,
    checkpoint, ended)

# Remainders. Nat.mod(a, 1 + bp) runs Nat.divmod.go with the countdown m and
# the remainder r, m + r = bp; one more input step wraps 1 + r at 1 + bp.
def pick0(hit: Bool, x: Nat) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      x

def wrap(+x: Nat, +bp: Nat) -> Nat:
  pick0(Nat.is_eq(x, 1n+bp), x)

def eq_refl(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def ne_add(+r: Nat, +mp: Nat)
  -> {Nat.is_eq(r, 1n+Nat.add(mp, r)) == False{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      %Equal.sym(Nat, Nat.add(mp, 1n+q), 1n+Nat.add(mp, q),
          AcceptProof.add_succ(mp, q)) : {Nat.is_eq(q, _) == False{} : Bool}
      ne_add(q, mp)

def go_step(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat,
    inv: {Nat.add(m, r) == bp : Nat})
  -> {Nat.mod.fin(Nat.divmod.go(1n+n, m, d, r)) ==
    wrap(1n+Nat.mod.fin(Nat.divmod.go(n, m, d, r)), bp) : Nat}:
  match n m:
    case 0n 0n:
      %inv : {0n == wrap(1n+r, _) : Nat}
      %Equal.sym(Bool, Nat.is_eq(r, r), True{}, eq_refl(r))
        : {0n == pick0(_, 1n+r) : Nat}
      {==}
    case 0n 1n+mp:
      %inv : {1n+r == wrap(1n+r, _) : Nat}
      %Equal.sym(Bool, Nat.is_eq(r, 1n+Nat.add(mp, r)), False{}, ne_add(r, mp))
        : {1n+r == pick0(_, 1n+r) : Nat}
      {==}
    case 1n+np 0n:
      go_step(np, r, 1n+d, 0n, bp,
        Equal.trans(Nat, Nat.add(r, 0n), r, bp, AcceptProof.add_zero(r), inv))
    case 1n+np 1n+mp:
      go_step(np, mp, d, 1n+r, bp,
        Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp,
          AcceptProof.add_succ(mp, r), inv))

def mod_succ(+a: Nat, +bp: Nat)
  -> {Nat.mod(1n+a, 1n+bp) == wrap(1n+Nat.mod(a, 1n+bp), bp) : Nat}:
  go_step(a, bp, 0n, 0n, bp, AcceptProof.add_zero(bp))

def pick_shift(+b: Bool, -p: Nat, -q: Nat,
    h: {Nat.is_le(pick0(b, 1n+p), q) == True{} : Bool})
  -> {Nat.is_le(pick0(b, 2n+p), 1n+q) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

def wrap_le(+x: Nat, +bp: Nat, le: {Nat.is_le(x, bp) == True{} : Bool})
  -> {Nat.is_le(wrap(1n+x, bp), bp) == True{} : Bool}:
  match x bp:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      AcceptProof.le_zero(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(wrap(2n+p, 0n), 0n) == True{} : Bool},
        AcceptProof.false_true(le))
    case 1n+p 1n+q:
      pick_shift(Nat.is_eq(p, q), p, q, wrap_le(p, q, le))

def mod_le(+a: Nat, +bp: Nat)
  -> {Nat.is_le(Nat.mod(a, 1n+bp), bp) == True{} : Bool}:
  match a:
    case 0n:
      AcceptProof.le_zero(bp)
    case 1n+p:
      %Equal.sym(Nat, Nat.mod(1n+p, 1n+bp), wrap(1n+Nat.mod(p, 1n+bp), bp),
          mod_succ(p, bp)) : {Nat.is_le(_, bp) == True{} : Bool}
      wrap_le(Nat.mod(p, 1n+bp), bp, mod_le(p, bp))

def le_ne(+x: Nat, +bp: Nat, le: {Nat.is_le(1n+x, bp) == True{} : Bool})
  -> {Nat.is_eq(x, bp) == False{} : Bool}:
  match x bp:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool},
        AcceptProof.false_true(le))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      le_ne(p, q, le)

def wrap_id(+x: Nat, +bp: Nat, le: {Nat.is_le(1n+x, bp) == True{} : Bool})
  -> {wrap(1n+x, bp) == 1n+x : Nat}:
  %Equal.sym(Bool, Nat.is_eq(x, bp), False{}, le_ne(x, bp, le))
    : {pick0(_, 1n+x) == 1n+x : Nat}
  {==}

def le_pred(+x: Nat, +bp: Nat, h: {Nat.is_le(1n+x, bp) == True{} : Bool})
  -> {Nat.is_le(x, bp) == True{} : Bool}:
  match x bp:
    case 0n _:
      AcceptProof.le_zero(bp)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 1n+p 1n+q:
      le_pred(p, q, h)

def le_add_succ(+o: Nat, -q: Nat, -bp: Nat,
    fits: {Nat.is_le(Nat.add(o, 1n+q), bp) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.add(o, q), bp) == True{} : Bool}:
  %AcceptProof.add_succ(o, q) : {Nat.is_le(_, bp) == True{} : Bool}
  fits

# No wrap while the remainder stays below the interval.
def mod_add(+a: Nat, +j: Nat, +bp: Nat,
    fits: {Nat.is_le(Nat.add(Nat.mod(a, 1n+bp), j), bp) == True{} : Bool})
  -> {Nat.mod(Nat.add(a, j), 1n+bp) == Nat.add(Nat.mod(a, 1n+bp), j) : Nat}:
  match j:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, AcceptProof.add_zero(a))
        : {Nat.mod(_, 1n+bp) == Nat.add(Nat.mod(a, 1n+bp), 0n) : Nat}
      Equal.sym(Nat, Nat.add(Nat.mod(a, 1n+bp), 0n), Nat.mod(a, 1n+bp),
        AcceptProof.add_zero(Nat.mod(a, 1n+bp)))
    case 1n+q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q),
          AcceptProof.add_succ(a, q))
        : {Nat.mod(_, 1n+bp) == Nat.add(Nat.mod(a, 1n+bp), 1n+q) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(a, 1n+bp), 1n+q),
          1n+Nat.add(Nat.mod(a, 1n+bp), q),
          AcceptProof.add_succ(Nat.mod(a, 1n+bp), q))
        : {Nat.mod(1n+Nat.add(a, q), 1n+bp) == _ : Nat}
      %Equal.sym(Nat, Nat.mod(1n+Nat.add(a, q), 1n+bp),
          wrap(1n+Nat.mod(Nat.add(a, q), 1n+bp), bp),
          mod_succ(Nat.add(a, q), bp))
        : {_ == 1n+Nat.add(Nat.mod(a, 1n+bp), q) : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.add(a, q), 1n+bp),
          Nat.add(Nat.mod(a, 1n+bp), q),
          mod_add(a, q, bp,
            le_pred(Nat.add(Nat.mod(a, 1n+bp), q), bp,
              le_add_succ(Nat.mod(a, 1n+bp), q, bp, fits))))
        : {wrap(1n+_, bp) == 1n+Nat.add(Nat.mod(a, 1n+bp), q) : Nat}
      wrap_id(Nat.add(Nat.mod(a, 1n+bp), q), bp,
        le_add_succ(Nat.mod(a, 1n+bp), q, bp, fits))

def sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_add_comm(+position: Nat, +base: Nat, +j: Nat,
    above: {Nat.is_le(base, position) == True{} : Bool})
  -> {Nat.sub(Nat.add(position, j), base) ==
    Nat.add(Nat.sub(position, base), j) : Nat}:
  match position base:
    case 0n 0n:
      sub_zero(j)
    case 0n 1n+b:
      Empty.absurd({Nat.sub(j, 1n+b) == Nat.add(0n, j) : Nat},
        AcceptProof.false_true(above))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+b:
      sub_add_comm(p, b, j, above)

# Order facts for the distance to the next boundary.
def lt_le_succ(+j: Nat, +b: Nat, h: {Nat.is_lt(j, 1n+b) == True{} : Bool})
  -> {Nat.is_le(j, b) == True{} : Bool}:
  match j b:
    case 0n _:
      AcceptProof.le_zero(b)
    case 1n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 2n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 1n+p 1n+q:
      lt_le_succ(p, q, h)

def lt_pred(+r: Nat, +c: Nat, h: {Nat.is_lt(1n+r, c) == True{} : Bool})
  -> {Nat.is_lt(r, c) == True{} : Bool}:
  match r c:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 1n+p 1n+q:
      lt_pred(p, q, h)

def le_succ_lt(+r: Nat, +c: Nat, h: {Nat.is_le(1n+r, c) == True{} : Bool})
  -> {Nat.is_lt(r, c) == True{} : Bool}:
  match r c:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool},
        AcceptProof.false_true(h))
    case 1n+p 1n+q:
      le_succ_lt(p, q, h)

def not_le_succ(+c: Nat, +k: Nat, h: {Nat.is_le(c, k) == False{} : Bool})
  -> {Nat.is_le(1n+k, c) == True{} : Bool}:
  match c k:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool},
        AcceptProof.true_false(h))
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(2n+q, 0n) == True{} : Bool},
        AcceptProof.true_false(h))
    case 1n+p 0n:
      AcceptProof.le_zero(p)
    case 1n+p 1n+q:
      not_le_succ(p, q, h)

def le_trans(+a: Nat, +b: Nat, +c: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool},
    bc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      AcceptProof.le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool},
        AcceptProof.false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool},
        AcceptProof.false_true(bc))
    case 1n+p 1n+q 1n+r:
      le_trans(p, q, r, ab, bc)

def sub_pos(+o: Nat, +bp: Nat, le: {Nat.is_le(o, bp) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.sub(1n+bp, o)) == True{} : Bool}:
  match o bp:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.sub(1n, 1n+p)) == True{} : Bool},
        AcceptProof.false_true(le))
    case 1n+p 1n+q:
      sub_pos(p, q, le)

def room(+o: Nat, +bp: Nat, +j: Nat,
    lt: {Nat.is_lt(j, Nat.sub(1n+bp, o)) == True{} : Bool},
    le: {Nat.is_le(o, bp) == True{} : Bool})
  -> {Nat.is_le(Nat.add(o, j), bp) == True{} : Bool}:
  match o bp:
    case 0n _:
      lt_le_succ(j, bp, lt)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, j), 0n) == True{} : Bool},
        AcceptProof.false_true(le))
    case 1n+p 1n+q:
      room(p, q, j, lt, le)

# Positions position + 1 .. position + m are no boundary while m is below
# the distance 1 + bp - o to the next one.
def no_within(+m: Nat, +position: Nat, +base: Nat, +bp: Nat,
    +above: {Nat.is_le(base, position) == True{} : Bool},
    lt: {Nat.is_lt(m, Nat.sub(1n+bp,
      Nat.mod(Nat.sub(position, base), 1n+bp))) == True{} : Bool})
  -> {Spec.within(m, position, base, 1n+bp) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Nat,
          Nat.sub(Nat.add(position, 1n+r), base),
          Nat.add(Nat.sub(position, base), 1n+r),
          sub_add_comm(position, base, 1n+r, above))
        : {Bool.or(Nat.is_eq(Nat.mod(_, 1n+bp), 0n),
          Spec.within(r, position, base, 1n+bp)) == False{} : Bool}
      %Equal.sym(Nat,
          Nat.mod(Nat.add(Nat.sub(position, base), 1n+r), 1n+bp),
          Nat.add(Nat.mod(Nat.sub(position, base), 1n+bp), 1n+r),
          mod_add(Nat.sub(position, base), 1n+r, bp,
            room(Nat.mod(Nat.sub(position, base), 1n+bp), bp, 1n+r, lt,
              mod_le(Nat.sub(position, base), bp))))
        : {Bool.or(Nat.is_eq(_, 0n),
          Spec.within(r, position, base, 1n+bp)) == False{} : Bool}
      %Equal.sym(Nat,
          Nat.add(Nat.mod(Nat.sub(position, base), 1n+bp), 1n+r),
          1n+Nat.add(Nat.mod(Nat.sub(position, base), 1n+bp), r),
          AcceptProof.add_succ(Nat.mod(Nat.sub(position, base), 1n+bp), r))
        : {Bool.or(Nat.is_eq(_, 0n),
          Spec.within(r, position, base, 1n+bp)) == False{} : Bool}
      no_within(r, position, base, bp, above,
        lt_pred(r, Nat.sub(1n+bp, Nat.mod(Nat.sub(position, base), 1n+bp)),
          lt))

def crosses_gen(+count: Nat, +position: Nat, +base: Nat, +bp: Nat,
    above: {Nat.is_le(base, position) == True{} : Bool},
    le: {Nat.is_le(count, Nat.sub(1n+bp,
      Nat.mod(Nat.sub(position, base), 1n+bp))) == True{} : Bool})
  -> {Spec.crosses(count, position, base, 1n+bp) == False{} : Bool}:
  match count:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Nat, Nat.sub(r, 0n), r, sub_zero(r))
        : {Spec.within(_, position, base, 1n+bp) == False{} : Bool}
      no_within(r, position, base, bp, above,
        le_succ_lt(r, Nat.sub(1n+bp, Nat.mod(Nat.sub(position, base), 1n+bp)),
          le))

# The count never exceeds the distance c to the next boundary: with c in
# the window it is the accept checkpoint, else the window itself is below c.
def count_le_c(+targets: List<&2, U32>, +proposals: List<&2, U32>,
    +stops: List<&2, U32>, +budget: Nat, +fits: Bool, +c: Nat,
    +shaped: {List.length(&2, U32, targets) ==
      1n+List.length(&2, U32, proposals) : Nat},
    relation: {fits == Nat.is_le(c, List.length(&2, U32, proposals)) : Bool},
    positive: {Nat.is_lt(0n, c) == True{} : Bool})
  -> {Nat.is_le(Accept.count(Accept.accept(targets, proposals, stops, budget,
    Impl.fit(fits, c))), c) == True{} : Bool}:
  match fits:
    case True{}:
      AcceptLaws.accept_checkpoint(targets, proposals, stops, budget, c,
        shaped, positive)
    case False{}:
      le_trans(
        Accept.count(Accept.accept(targets, proposals, stops, budget, 0n)),
        1n+List.length(&2, U32, proposals), c,
        count_le_window(targets, proposals, stops, budget, 0n, shaped),
        not_le_succ(c, List.length(&2, U32, proposals),
          Equal.sym(Bool, False{}, Nat.is_le(c, List.length(&2, U32, proposals)),
            relation)))

def Laws.round_checkpoint(targets, proposals, stops, budget, base, interval,
    position, shaped, positive, above):
  match interval:
    case 0n:
      Empty.absurd({Spec.crosses(Accept.count(Accept.accept(targets, proposals,
          stops, budget, Impl.checkpoint(position, base, 0n,
            List.length(&2, U32, proposals)))), position, base, 0n) ==
        False{} : Bool}, AcceptProof.false_true(positive))
    case 1n+bp:
      crosses_gen(
        Accept.count(Accept.accept(targets, proposals, stops, budget,
          Impl.checkpoint(position, base, 1n+bp,
            List.length(&2, U32, proposals)))),
        position, base, bp, above,
        count_le_c(targets, proposals, stops, budget,
          Nat.is_le(Nat.sub(1n+bp, Nat.mod(Nat.sub(position, base), 1n+bp)),
            List.length(&2, U32, proposals)),
          Nat.sub(1n+bp, Nat.mod(Nat.sub(position, base), 1n+bp)),
          shaped, {==},
          sub_pos(Nat.mod(Nat.sub(position, base), 1n+bp), bp,
            mod_le(Nat.sub(position, base), bp))))
