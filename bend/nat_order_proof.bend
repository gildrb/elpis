# Proofs of bend/nat_order_laws.bend: structural induction and rewriting only. No @unsafe
# definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./nat_order.bend as Nord
import ./nat_order_laws.bend as Laws

# ==== Bool ====

def Laws.false_true(e):
  %Equal.sym(Bool, False{}, True{}, e) : Nord.Truth(_)
  Unit{}

def Laws.and_l(a, b, h):
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Laws.false_true(h))
    case True{}:
      {==}

def Laws.and_r(a, b, h):
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, Laws.false_true(h))
    case True{}:
      h

def Laws.and_intro(a, b, ha, hb):
  match a:
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, Laws.false_true(ha))
    case True{}:
      hb

# ==== addition ====

def Laws.add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def Laws.add_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def Laws.add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Laws.add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Laws.add_succ_r(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %Laws.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def Laws.add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def Laws.add_swap(a, b, c):
  %Laws.add_assoc(b, a, c) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %Laws.add_comm(a, b) : {Nat.add(a, Nat.add(b, c)) == Nat.add(_, c) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Laws.add_assoc(a, b, c))

def Laws.add_swap4(a, b, c, d):
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))),
    Laws.add_assoc(a, c, Nat.add(b, d))) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == _ : Nat}
  %Laws.add_swap(b, c, d) : {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(a, _) : Nat}
  Laws.add_assoc(a, b, Nat.add(c, d))

# ==== multiplication ====

def Laws.mul_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.mul_zero_r(p)

def Laws.mul_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), Laws.mul_succ_r(p, b)) :
        {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %Laws.add_swap(b, p, Nat.mul(p, b)) : {1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def Laws.mul_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, Laws.mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), Laws.mul_succ_r(b, p)) :
        {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %Laws.mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

def Laws.mul_add_l(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), Laws.mul_add_l(p, b, c)) :
        {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
        Laws.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

def Laws.mul_add_r(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)), Laws.mul_add_r(p, b, c)) :
        {Nat.add(Nat.add(b, c), _) == Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))) : Nat}
      Laws.add_swap4(b, c, Nat.mul(p, b), Nat.mul(p, c))

def Laws.mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      Laws.mul_add_l(b, Nat.mul(p, b), c)

# ==== truncated subtraction ====

def Laws.sub_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.sub_self(p)

def Laws.sub_add(a, b, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(1n+q, Nat.sub(0n, 1n+q)) == 0n : Nat}, Laws.false_true(ba))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %Laws.sub_add(p, q, ba) : {1n+Nat.add(q, Nat.sub(p, q)) == 1n+_ : Nat}
      {==}

def Laws.add_sub(a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      Laws.add_sub(p, b)

def Laws.sub_add_add(a, b, c, d, ca, db):
  +u = Nat.sub(a, c)
  +v = Nat.sub(b, d)
  %Laws.sub_add(a, c, ca) : {Nat.sub(Nat.add(_, b), Nat.add(c, d)) == Nat.add(u, v) : Nat}
  %Laws.sub_add(b, d, db) : {Nat.sub(Nat.add(Nat.add(c, u), _), Nat.add(c, d)) == Nat.add(u, v) : Nat}
  %Laws.add_swap4(c, d, u, v) : {Nat.sub(_, Nat.add(c, d)) == Nat.add(u, v) : Nat}
  Laws.add_sub(Nat.add(c, d), Nat.add(u, v))

def Laws.sub_chain(a, b, c, ab, bc):
  +u = Nat.sub(b, a)
  +v = Nat.sub(c, b)
  %Laws.sub_add(c, b, bc) : {Nat.sub(_, a) == Nat.add(v, u) : Nat}
  %Laws.sub_add(b, a, ab) : {Nat.sub(Nat.add(_, v), a) == Nat.add(v, u) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, u), v), Nat.add(a, Nat.add(u, v)), Laws.add_assoc(a, u, v)) :
    {Nat.sub(_, a) == Nat.add(v, u) : Nat}
  %Laws.add_comm(u, v) : {Nat.sub(Nat.add(a, Nat.add(u, v)), a) == _ : Nat}
  Laws.add_sub(a, Nat.add(u, v))

# ==== order ====

def Laws.le_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.le_succ(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_succ(p)

def Laws.le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_refl(p)

def Laws.le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      Laws.le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, Laws.false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, Laws.false_true(bc))
    case 1n+p 1n+q 1n+r:
      Laws.le_trans(p, q, r, ab, bc)

def Laws.le_of_eq(a, b, e):
  %e : {Nat.is_le(a, _) == True{} : Bool}
  Laws.le_refl(a)

def Laws.le_add_r(a, b):
  match a:
    case 0n:
      Laws.le_zero(b)
    case 1n+p:
      Laws.le_add_r(p, b)

def Laws.le_add_l(a, b):
  match a:
    case 0n:
      Laws.le_refl(b)
    case 1n+p:
      Laws.le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), Laws.le_add_l(p, b), Laws.le_succ(Nat.add(p, b)))

def Laws.le_add_cancel(c, a, b):
  match c:
    case 0n:
      {==}
    case 1n+p:
      Laws.le_add_cancel(p, a, b)

# a <= b gives a + c <= b + c
def no_le_add_mono_r(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n _:
      Laws.le_add_l(b, c)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+p, c), c) == True{} : Bool}, Laws.false_true(ab))
    case 1n+p 1n+q:
      no_le_add_mono_r(p, q, c, ab)

def Laws.le_add_mono(a, b, c, d, ab, cd):
  Laws.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), no_le_add_mono_r(a, b, c, ab),
    Equal.trans(Bool, Nat.is_le(Nat.add(b, c), Nat.add(b, d)), Nat.is_le(c, d), True{},
      Laws.le_add_cancel(b, c, d), cd))

def Laws.le_mul_mono_l(a, b, c, ab):
  match a b:
    case 0n _:
      Laws.le_zero(Nat.mul(b, c))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+p, c), 0n) == True{} : Bool}, Laws.false_true(ab))
    case 1n+p 1n+q:
      Equal.trans(Bool, Nat.is_le(Nat.add(c, Nat.mul(p, c)), Nat.add(c, Nat.mul(q, c))),
        Nat.is_le(Nat.mul(p, c), Nat.mul(q, c)), True{},
        Laws.le_add_cancel(c, Nat.mul(p, c), Nat.mul(q, c)), Laws.le_mul_mono_l(p, q, c, ab))

def Laws.le_mul_mono_r(a, b, c, ab):
  match c:
    case 0n:
      {==}
    case 1n+p:
      +h = ab
      Laws.le_add_mono(a, b, Nat.mul(p, a), Nat.mul(p, b), h, Laws.le_mul_mono_r(a, b, p, h))
