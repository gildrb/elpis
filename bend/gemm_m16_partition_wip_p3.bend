# WIP proofs (part 3): warp-level laws warp_split, issue_matches_compute,
# segment_attribution, cursor_step, red_slots_disjoint. Merged into
# gemm_m16_partition_proof.bend (imports and `Arith.` prefixes stripped). Local defs: p3_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- small Nat/Bool facts ----

# 2 + q < 2 is absurd.
def p3_ge2(q: Nat, h: {Nat.is_lt(2n+q, 2n) == True{} : Bool}) -> Empty:
  match q:
    case 0n:
      Arith.ar_false_true(h)
    case 1n+r:
      Arith.ar_false_true(h)

def p3_ne_aux(+x: Nat, -y: Nat, same: {x == y : Nat}) -> {True{} == Nat.is_eq(x, y) : Bool}:
  %same : {True{} == Nat.is_eq(x, _) : Bool}
  Equal.sym(Bool, Nat.is_eq(x, x), True{}, Arith.ar_eq_refl(x))

# Equal Nats are is_eq.
def p3_ne(+x: Nat, -y: Nat, same: {x == y : Nat},
    diff: {Nat.is_eq(x, y) == False{} : Bool}) -> Empty:
  Arith.ar_true_false(Equal.trans(Bool, True{}, Nat.is_eq(x, y), False{},
    p3_ne_aux(x, y, same), diff))

def Laws.red_slots_disjoint(a, h, c, i, a2, h2, c2, i2, same):
  match a:
    case 0n:
      match h:
        case 0n:
          match c:
            case 0n:
              match i:
                case 0n:
                  ({==}, {==})
                case 1n+pi:
                  match pi:
                    case 0n:
                      Empty.absurd({0n == 0n : Nat} & {0n == 1n : Nat},
                        p3_ne(0n, 1n, same, {==}))
                    case 1n+qi:
                      Empty.absurd({0n == 0n : Nat} & {0n == 2n+qi : Nat},
                        p3_ge2(qi, i2))
            case 1n+pc:
              match pc:
                case 0n:
                  match i:
                    case 0n:
                      Empty.absurd({0n == 1n : Nat} & {0n == 0n : Nat},
                        p3_ne(0n, 2n, same, {==}))
                    case 1n+pi:
                      match pi:
                        case 0n:
                          Empty.absurd({0n == 1n : Nat} & {0n == 1n : Nat},
                            p3_ne(0n, 3n, same, {==}))
                        case 1n+qi:
                          Empty.absurd({0n == 1n : Nat} & {0n == 2n+qi : Nat},
                            p3_ge2(qi, i2))
                case 1n+qc:
                  Empty.absurd({0n == 2n+qc : Nat} & {0n == i : Nat},
                    p3_ge2(qc, c2))
        case 1n+ph:
          match ph:
            case 0n:
              match c:
                case 0n:
                  match i:
                    case 0n:
                      Empty.absurd({0n == 0n : Nat} & {1n == 0n : Nat},
                        p3_ne(1n, 0n, same, {==}))
                    case 1n+pi:
                      match pi:
                        case 0n:
                          ({==}, {==})
                        case 1n+qi:
                          Empty.absurd({0n == 0n : Nat} & {1n == 2n+qi : Nat},
                            p3_ge2(qi, i2))
                case 1n+pc:
                  match pc:
                    case 0n:
                      match i:
                        case 0n:
                          Empty.absurd({0n == 1n : Nat} & {1n == 0n : Nat},
                            p3_ne(1n, 2n, same, {==}))
                        case 1n+pi:
                          match pi:
                            case 0n:
                              Empty.absurd({0n == 1n : Nat} & {1n == 1n : Nat},
                                p3_ne(1n, 3n, same, {==}))
                            case 1n+qi:
                              Empty.absurd({0n == 1n : Nat} & {1n == 2n+qi : Nat},
                                p3_ge2(qi, i2))
                    case 1n+qc:
                      Empty.absurd({0n == 2n+qc : Nat} & {1n == i : Nat},
                        p3_ge2(qc, c2))
            case 1n+qh:
              Empty.absurd({0n == c : Nat} & {2n+qh == i : Nat},
                p3_ge2(qh, h2))
    case 1n+pa:
      match pa:
        case 0n:
          match h:
            case 0n:
              match c:
                case 0n:
                  match i:
                    case 0n:
                      Empty.absurd({1n == 0n : Nat} & {0n == 0n : Nat},
                        p3_ne(2n, 0n, same, {==}))
                    case 1n+pi:
                      match pi:
                        case 0n:
                          Empty.absurd({1n == 0n : Nat} & {0n == 1n : Nat},
                            p3_ne(2n, 1n, same, {==}))
                        case 1n+qi:
                          Empty.absurd({1n == 0n : Nat} & {0n == 2n+qi : Nat},
                            p3_ge2(qi, i2))
                case 1n+pc:
                  match pc:
                    case 0n:
                      match i:
                        case 0n:
                          ({==}, {==})
                        case 1n+pi:
                          match pi:
                            case 0n:
                              Empty.absurd({1n == 1n : Nat} & {0n == 1n : Nat},
                                p3_ne(2n, 3n, same, {==}))
                            case 1n+qi:
                              Empty.absurd({1n == 1n : Nat} & {0n == 2n+qi : Nat},
                                p3_ge2(qi, i2))
                    case 1n+qc:
                      Empty.absurd({1n == 2n+qc : Nat} & {0n == i : Nat},
                        p3_ge2(qc, c2))
            case 1n+ph:
              match ph:
                case 0n:
                  match c:
                    case 0n:
                      match i:
                        case 0n:
                          Empty.absurd({1n == 0n : Nat} & {1n == 0n : Nat},
                            p3_ne(3n, 0n, same, {==}))
                        case 1n+pi:
                          match pi:
                            case 0n:
                              Empty.absurd({1n == 0n : Nat} & {1n == 1n : Nat},
                                p3_ne(3n, 1n, same, {==}))
                            case 1n+qi:
                              Empty.absurd({1n == 0n : Nat} & {1n == 2n+qi : Nat},
                                p3_ge2(qi, i2))
                    case 1n+pc:
                      match pc:
                        case 0n:
                          match i:
                            case 0n:
                              Empty.absurd({1n == 1n : Nat} & {1n == 0n : Nat},
                                p3_ne(3n, 2n, same, {==}))
                            case 1n+pi:
                              match pi:
                                case 0n:
                                  ({==}, {==})
                                case 1n+qi:
                                  Empty.absurd({1n == 1n : Nat} & {1n == 2n+qi : Nat},
                                    p3_ge2(qi, i2))
                        case 1n+qc:
                          Empty.absurd({1n == 2n+qc : Nat} & {1n == i : Nat},
                            p3_ge2(qc, c2))
                case 1n+qh:
                  Empty.absurd({1n == c : Nat} & {2n+qh == i : Nat},
                    p3_ge2(qh, h2))
        case 1n+qa:
          Empty.absurd({2n+qa == c : Nat} & {h == i : Nat},
            p3_ge2(qa, a2))

def p3_not_t(-b: Bool, h: {b == True{} : Bool}) -> {Bool.not(b) == False{} : Bool}:
  %Equal.sym(Bool, b, True{}, h) : {Bool.not(_) == False{} : Bool}
  {==}

def p3_not_f(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Arith.ar_true_false(h))
    case True{}:
      {==}

def p3_lt_zero(j: Nat) -> {Nat.is_lt(j, 0n) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      {==}

def p3_lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      p3_lt_succ(p)

# ---- issue_matches_compute ----

# j < (span - kp + 3) / 4 iff kp + 4j < span
def p3_imc_l(+span: Nat, +kp: Nat, +j: Nat)
  -> {Nat.is_lt(j, Nat.div(Nat.add(Nat.sub(span, kp), 3n), 4n)) ==
    Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), span) : Bool}:
  %Equal.sym(Bool, Nat.is_lt(j, Nat.div(Nat.add(Nat.sub(span, kp), 3n), 4n)),
    Nat.is_le(1n+j, Nat.div(Nat.add(Nat.sub(span, kp), 3n), 4n)),
    Arith.ar_lt_succ_le(j, Nat.div(Nat.add(Nat.sub(span, kp), 3n), 4n)))
    : {_ == Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), span) : Bool}
  %Arith.ar_div_le(1n+j, Nat.add(Nat.sub(span, kp), 3n), 4n, {==})
    : {_ == Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), span) : Bool}
  %Arith.ar_add_comm(3n, Nat.sub(span, kp))
    : {Nat.is_le(Nat.mul(1n+j, 4n), _) == Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), span) : Bool}
  %Arith.ar_lt_succ_le(Nat.mul(j, 4n), Nat.sub(span, kp))
    : {_ == Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), span) : Bool}
  Arith.ar_lt_sub_iff(span, kp, Nat.mul(j, 4n))

# iter(s, kp, j) < e iff kp + 4j < e - s
def p3_imc_r(+s: Nat, +e: Nat, +kp: Nat, +j: Nat)
  -> {Nat.is_lt(Impl.iter(s, kp, j), e) ==
    Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)) : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(s, kp), Nat.mul(4n, j)),
    Nat.add(s, Nat.add(kp, Nat.mul(4n, j))), Arith.ar_add_assoc(s, kp, Nat.mul(4n, j)))
    : {Nat.is_lt(_, e) == Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)) : Bool}
  %Arith.ar_mul_comm(j, 4n)
    : {Nat.is_lt(Nat.add(s, Nat.add(kp, _)), e) ==
      Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)) : Bool}
  Equal.sym(Bool, Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)),
    Nat.is_lt(Nat.add(s, Nat.add(kp, Nat.mul(j, 4n))), e),
    Arith.ar_lt_sub_iff(e, s, Nat.add(kp, Nat.mul(j, 4n))))

def p3_imc_big(+s: Nat, +e: Nat, +kp: Nat, +j: Nat)
  -> {Nat.is_lt(j, Nat.div(Nat.add(Nat.sub(Nat.sub(e, s), kp), 3n), 4n)) ==
    Nat.is_lt(Impl.iter(s, kp, j), e) : Bool}:
  Equal.trans(Bool, Nat.is_lt(j, Nat.div(Nat.add(Nat.sub(Nat.sub(e, s), kp), 3n), 4n)),
    Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)),
    Nat.is_lt(Impl.iter(s, kp, j), e),
    p3_imc_l(Nat.sub(e, s), kp, j),
    Equal.sym(Bool, Nat.is_lt(Impl.iter(s, kp, j), e),
      Nat.is_lt(Nat.add(kp, Nat.mul(j, 4n)), Nat.sub(e, s)), p3_imc_r(s, e, kp, j)))

# e - s <= kp: every iteration of phase kp is at or past e.
def p3_imc_after(+s: Nat, +e: Nat, +kp: Nat, +j: Nat,
    small: {Nat.is_gt(Nat.sub(e, s), kp) == False{} : Bool})
  -> {Nat.is_lt(Impl.iter(s, kp, j), e) == False{} : Bool}:
  +le1 = p3_not_f(Nat.is_le(e, Nat.add(s, kp)),
    Equal.trans(Bool, Bool.not(Nat.is_le(e, Nat.add(s, kp))), Nat.is_lt(Nat.add(s, kp), e),
      False{},
      Equal.sym(Bool, Nat.is_lt(Nat.add(s, kp), e), Bool.not(Nat.is_le(e, Nat.add(s, kp))),
        Arith.ar_lt_not_le(Nat.add(s, kp), e)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(s, kp), e), Nat.is_lt(kp, Nat.sub(e, s)), False{},
        Equal.sym(Bool, Nat.is_lt(kp, Nat.sub(e, s)), Nat.is_lt(Nat.add(s, kp), e),
          Arith.ar_lt_sub_iff(e, s, kp)),
        Equal.trans(Bool, Nat.is_lt(kp, Nat.sub(e, s)), Nat.is_gt(Nat.sub(e, s), kp), False{},
          Equal.sym(Bool, Nat.is_gt(Nat.sub(e, s), kp), Nat.is_lt(kp, Nat.sub(e, s)),
            Arith.ar_gt_flip(Nat.sub(e, s), kp)),
          small))))
  +le3 = Arith.ar_le_trans(e, Nat.add(s, kp), Impl.iter(s, kp, j), le1,
    Arith.ar_le_add_r(Nat.add(s, kp), Nat.mul(4n, j)))
  Equal.trans(Bool, Nat.is_lt(Impl.iter(s, kp, j), e),
    Bool.not(Nat.is_le(e, Impl.iter(s, kp, j))), False{},
    Arith.ar_lt_not_le(Impl.iter(s, kp, j), e),
    p3_not_t(Nat.is_le(e, Impl.iter(s, kp, j)), le3))

def p3_imc_pick(big: Bool, +s: Nat, +e: Nat, +kp: Nat, +j: Nat,
    hb: {Nat.is_gt(Nat.sub(e, s), kp) == big : Bool})
  -> {Nat.is_lt(j, Impl.nj.pick(big, Nat.sub(e, s), kp)) ==
    Nat.is_lt(Impl.iter(s, kp, j), e) : Bool}:
  match big:
    case True{}:
      p3_imc_big(s, e, kp, j)
    case False{}:
      Equal.trans(Bool, Nat.is_lt(j, 0n), False{}, Nat.is_lt(Impl.iter(s, kp, j), e),
        p3_lt_zero(j),
        Equal.sym(Bool, Nat.is_lt(Impl.iter(s, kp, j), e), False{},
          p3_imc_after(s, e, kp, j, hb)))

def Laws.issue_matches_compute(s, e, kp, j, ordered):
  p3_imc_pick(Nat.is_gt(Nat.sub(e, s), kp), s, e, kp, j, {==})
