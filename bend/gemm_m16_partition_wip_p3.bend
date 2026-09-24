# WIP proofs: law issue_cursor (weight-issue cursor, K:140-155). v1 laws red_slots_disjoint /
# issue_matches_compute retired with kernel v1.
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p3_.
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


# ---- law issue_cursor ----

def p3_fst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

# a <= b and a != b give a < b.
def p3_le_ne_lt(a: Nat, b: Nat, le: {Nat.is_le(a, b) == True{} : Bool},
    ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, Arith.ar_true_false(ne))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, Arith.ar_false_true(le))
    case 1n+ap 1n+bp:
      p3_le_ne_lt(ap, bp, le, ne)

# decode(q * KT + r) == Cursor{q, r} for r < KT.
def p3_dec_qr(+q: Nat, +r: Nat, +KT: Nat, small: {Nat.is_lt(r, KT) == True{} : Bool})
  -> {Impl.decode(Nat.add(Nat.mul(q, KT), r), KT) == Impl.Cursor{q, r} : Impl.Cursor}:
  +dq = p3_fst({Nat.div(Nat.add(Nat.mul(q, KT), r), KT) == q : Nat},
    {Nat.mod(Nat.add(Nat.mul(q, KT), r), KT) == r : Nat},
    Arith.ar_div_unique(q, r, KT, small))
  %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(q, KT), r), KT), q, dq)
    : {Impl.Cursor{_, Nat.sub(Nat.add(Nat.mul(q, KT), r),
        Nat.mul(Nat.div(Nat.add(Nat.mul(q, KT), r), KT), KT))} == Impl.Cursor{q, r} : Impl.Cursor}
  %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(q, KT), r), KT), q, dq)
    : {Impl.Cursor{q, Nat.sub(Nat.add(Nat.mul(q, KT), r), Nat.mul(_, KT))} ==
      Impl.Cursor{q, r} : Impl.Cursor}
  %Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(q, KT), r), Nat.mul(q, KT)), r,
    Arith.ar_add_sub(Nat.mul(q, KT), r))
    : {Impl.Cursor{q, _} == Impl.Cursor{q, r} : Impl.Cursor}
  {==}

# One issue from Cursor{q, r} (r < KT) lands on decode(q * KT + r + 1).
def p3_step_pick(w: Bool, +q: Nat, +r: Nat, +KT: Nat,
    small: {Nat.is_lt(r, KT) == True{} : Bool}, pos: {Nat.is_lt(0n, KT) == True{} : Bool},
    hb: {Nat.is_eq(1n+r, KT) == w : Bool})
  -> {Impl.advance.pick(w, q, 1n+r) ==
    Impl.decode(1n+Nat.add(Nat.mul(q, KT), r), KT) : Impl.Cursor}:
  match w:
    case True{}:
      +eqk = Arith.ar_eq_true(1n+r, KT, hb)
      %Arith.ar_add_succ_r(Nat.mul(q, KT), r)
        : {Impl.Cursor{1n+q, 0n} == Impl.decode(_, KT) : Impl.Cursor}
      %Equal.sym(Nat, 1n+r, KT, eqk)
        : {Impl.Cursor{1n+q, 0n} == Impl.decode(Nat.add(Nat.mul(q, KT), _), KT) : Impl.Cursor}
      %Arith.ar_add_comm(KT, Nat.mul(q, KT))
        : {Impl.Cursor{1n+q, 0n} == Impl.decode(_, KT) : Impl.Cursor}
      %Arith.ar_add_zero_r(Nat.add(KT, Nat.mul(q, KT)))
        : {Impl.Cursor{1n+q, 0n} == Impl.decode(_, KT) : Impl.Cursor}
      Equal.sym(Impl.Cursor, Impl.decode(Nat.add(Nat.mul(1n+q, KT), 0n), KT),
        Impl.Cursor{1n+q, 0n}, p3_dec_qr(1n+q, 0n, KT, pos))
    case False{}:
      %Arith.ar_add_succ_r(Nat.mul(q, KT), r)
        : {Impl.Cursor{q, 1n+r} == Impl.decode(_, KT) : Impl.Cursor}
      Equal.sym(Impl.Cursor, Impl.decode(Nat.add(Nat.mul(q, KT), 1n+r), KT),
        Impl.Cursor{q, 1n+r},
        p3_dec_qr(q, 1n+r, KT,
          p3_le_ne_lt(1n+r, KT,
            Equal.trans(Bool, Nat.is_le(1n+r, KT), Nat.is_lt(r, KT), True{},
              Equal.sym(Bool, Nat.is_lt(r, KT), Nat.is_le(1n+r, KT), Arith.ar_lt_succ_le(r, KT)),
              small),
            hb)))

# The decoded remainder it - (it / KT) * KT is below KT.
def p3_rem_lt(+it: Nat, +KT: Nat, +pos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(it, Nat.mul(Nat.div(it, KT), KT)), KT) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(Nat.sub(it, Nat.mul(Nat.div(it, KT), KT)), KT),
    Nat.is_lt(it, Nat.add(Nat.mul(Nat.div(it, KT), KT), KT)),
    Arith.ar_sub_lt_iff(it, Nat.mul(Nat.div(it, KT), KT), KT, pos)) : {_ == True{} : Bool}
  %Arith.ar_add_comm(KT, Nat.mul(Nat.div(it, KT), KT)) : {Nat.is_lt(it, _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(it, Nat.mul(1n+Nat.div(it, KT), KT)),
    Nat.is_lt(Nat.div(it, KT), 1n+Nat.div(it, KT)), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.div(it, KT), 1n+Nat.div(it, KT)),
      Nat.is_lt(it, Nat.mul(1n+Nat.div(it, KT), KT)),
      Arith.ar_div_lt(1n+Nat.div(it, KT), it, KT, pos)),
    p3_lt_succ(Nat.div(it, KT)))

# One issue advances the decoded cursor of it to the decoded cursor of it + 1.
def p3_step(+it: Nat, +KT: Nat, +pos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Impl.advance(Impl.decode(it, KT), KT) == Impl.decode(1n+it, KT) : Impl.Cursor}:
  +le = Equal.trans(Bool, Nat.is_le(Nat.mul(Nat.div(it, KT), KT), it),
    Nat.is_le(Nat.div(it, KT), Nat.div(it, KT)), True{},
    Arith.ar_div_le(Nat.div(it, KT), it, KT, pos), Arith.ar_le_refl(Nat.div(it, KT)))
  %Arith.ar_sub_add(it, Nat.mul(Nat.div(it, KT), KT), le)
    : {Impl.advance(Impl.decode(it, KT), KT) == Impl.decode(1n+_, KT) : Impl.Cursor}
  p3_step_pick(Nat.is_eq(1n+Nat.sub(it, Nat.mul(Nat.div(it, KT), KT)), KT),
    Nat.div(it, KT), Nat.sub(it, Nat.mul(Nat.div(it, KT), KT)), KT,
    p3_rem_lt(it, KT, pos), pos, {==})

def p3_issue(+j: Nat, +s: Nat, +KT: Nat, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Impl.issued(j, s, KT) == Impl.decode(Nat.add(s, j), KT) : Impl.Cursor}:
  match j:
    case 0n:
      %Equal.sym(Nat, Nat.add(s, 0n), s, Arith.ar_add_zero_r(s))
        : {Impl.decode(s, KT) == Impl.decode(_, KT) : Impl.Cursor}
      {==}
    case 1n+i:
      %Equal.sym(Impl.Cursor, Impl.issued(i, s, KT), Impl.decode(Nat.add(s, i), KT),
        p3_issue(i, s, KT, tiles))
        : {Impl.advance(_, KT) == Impl.decode(Nat.add(s, 1n+i), KT) : Impl.Cursor}
      %Equal.sym(Nat, Nat.add(s, 1n+i), 1n+Nat.add(s, i), Arith.ar_add_succ_r(s, i))
        : {Impl.advance(Impl.decode(Nat.add(s, i), KT), KT) == Impl.decode(_, KT) : Impl.Cursor}
      p3_step(Nat.add(s, i), KT, tiles)

def Laws.issue_cursor(s, j, KT, tiles):
  +t = tiles
  p3_issue(j, s, KT, t)
