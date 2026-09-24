# WIP shared Nat/Bool lemmas for the m16 partition proofs (merged into
# gemm_m16_partition_proof.bend at the end). Statements are a FIXED CONTRACT used by the
# p1..p4 WIP files: never change a statement; every body is a proof.
import Base

def ar_Truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

# False == True is absurd.
def ar_false_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : ar_Truth(_)
  Unit{}

law ar_add_zero_r:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

def ar_add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ar_add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law ar_add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def ar_add_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ar_add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law ar_add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def ar_add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, ar_add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), ar_add_succ_r(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %ar_add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

law ar_add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def ar_add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ar_add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

law ar_mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

def ar_mul_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      ar_mul_zero_r(p)

# a + (b + c) == b + (a + c).
def ar_h_add_swap(+a: Nat, +b: Nat, +c: Nat)
  -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %ar_add_assoc(b, a, c) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %ar_add_comm(a, b) : {Nat.add(a, Nat.add(b, c)) == Nat.add(_, c) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), ar_add_assoc(a, b, c))

law ar_mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

def ar_mul_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), ar_mul_succ_r(p, b)) : {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %ar_h_add_swap(b, p, Nat.mul(p, b)) : {1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

law ar_mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def ar_mul_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, ar_mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), ar_mul_succ_r(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %ar_mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

law ar_mul_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def ar_mul_add_l(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), ar_mul_add_l(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), ar_add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

law ar_mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def ar_mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ar_mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      ar_mul_add_l(b, Nat.mul(p, b), c)

law ar_le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

def ar_le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      ar_le_refl(p)

law ar_lt_not_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Bool.not(Nat.is_le(b, a)) : Bool}

def ar_lt_not_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_lt_not_le(p, q)

law ar_gt_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

def ar_gt_flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_gt_flip(p, q)

law ar_ge_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

def ar_ge_flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_ge_flip(p, q)

def ar_h_le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law ar_lt_succ_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

def ar_lt_succ_le(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, ar_h_le_zero(q))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_lt_succ_le(p, q)

law ar_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def ar_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      ar_h_le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, ar_false_true(bc))
    case 1n+p 1n+q 1n+r:
      ar_le_trans(p, q, r, ab, bc)

law ar_le_antisym:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def ar_le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, ar_false_true(ba))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, ar_false_true(ab))
    case 1n+p 1n+q:
      %ar_le_antisym(p, q, ab, ba) : {1n+p == 1n+_ : Nat}
      {==}

law ar_le_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}

def ar_le_add_cancel(c, a, b):
  match c:
    case 0n:
      {==}
    case 1n+p:
      ar_le_add_cancel(p, a, b)

law ar_lt_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}

def ar_lt_add_cancel(c, a, b):
  match c:
    case 0n:
      {==}
    case 1n+p:
      ar_lt_add_cancel(p, a, b)

law ar_le_add_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

def ar_le_add_r(a, b):
  match a:
    case 0n:
      ar_h_le_zero(b)
    case 1n+p:
      ar_le_add_r(p, b)

law ar_sub_add:
  for +a: Nat
  for +b: Nat
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}

def ar_sub_add(a, b, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(1n+q, Nat.sub(0n, 1n+q)) == 0n : Nat}, ar_false_true(ba))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %ar_sub_add(p, q, ba) : {1n+Nat.add(q, Nat.sub(p, q)) == 1n+_ : Nat}
      {==}

law ar_add_sub:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

def ar_add_sub(a, b):
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      ar_add_sub(p, b)

law ar_le_mul_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

def ar_le_mul_mono(a, b, c, ab):
  match a b:
    case 0n _:
      ar_h_le_zero(Nat.mul(b, c))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+p, c), 0n) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q:
      Equal.trans(Bool, Nat.is_le(Nat.add(c, Nat.mul(p, c)), Nat.add(c, Nat.mul(q, c))),
        Nat.is_le(Nat.mul(p, c), Nat.mul(q, c)), True{},
        ar_le_add_cancel(c, Nat.mul(p, c), Nat.mul(q, c)), ar_le_mul_mono(p, q, c, ab))

# ---- extra shared statements (contract) ----

def ar_true_false(equal: {True{} == False{} : Bool}) -> Empty:
  %equal : ar_Truth(_)
  Unit{}

def ar_h_Positive(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      Empty

def ar_h_pred(value: Nat) -> Nat:
  match value:
    case 0n:
      0n
    case 1n+p:
      p

def ar_h_succ(value: Nat) -> Nat:
  1n+value

def ar_zero_succ(-n: Nat, equal: {0n == 1n+n : Nat}) -> Empty:
  %equal : ar_h_Positive(_)
  Unit{}

def ar_succ_inj(-a: Nat, -b: Nat, equal: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, ar_h_pred, 1n+a, 1n+b, equal)

# Boolean extensionality from both implications.
def ar_bool_ext(a: Bool, b: Bool) -> ({a == True{} : Bool} -> {b == True{} : Bool}) ->
    ({b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      f => g => {==}
    case False{} True{}:
      f => g => Empty.absurd({False{} == True{} : Bool}, ar_false_true(g({==})))
    case True{} False{}:
      f => g => Empty.absurd({True{} == False{} : Bool}, ar_false_true(f({==})))
    case True{} True{}:
      f => g => {==}

def ar_and_l(a: Bool, -b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ar_false_true(both))
    case True{}:
      {==}

def ar_and_r(a: Bool, b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, ar_false_true(both))
    case True{}:
      both

def ar_and_intro(-a: Bool, -b: Bool, left: {a == True{} : Bool}, right: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, left) : {Bool.and(_, b) == True{} : Bool}
  right

def ar_false_ne(-a: Bool, no: {a == False{} : Bool}, yes: {a == True{} : Bool}) -> Empty:
  ar_false_true(Equal.trans(Bool, False{}, a, True{}, Equal.sym(Bool, a, False{}, no), yes))

# A Bool that is not True is False.
def ar_not_true(a: Bool, no: {a == True{} : Bool} -> Empty) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no({==}))

law ar_sub_zero_r:
  for +a: Nat
  {Nat.sub(a, 0n) == a : Nat}

def ar_sub_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

law ar_mul_one_l:
  for +a: Nat
  {Nat.mul(1n, a) == a : Nat}

def ar_mul_one_l(a):
  ar_add_zero_r(a)

law ar_lt_irrefl:
  for +a: Nat
  {Nat.is_lt(a, a) == False{} : Bool}

def ar_lt_irrefl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      ar_lt_irrefl(p)

law ar_eq_true:
  for +a: Nat
  for +b: Nat
  for equal: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def ar_eq_true(a, b, equal):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, ar_false_true(equal))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, ar_false_true(equal))
    case 1n+p 1n+q:
      %ar_eq_true(p, q, equal) : {1n+p == 1n+_ : Nat}
      {==}

law ar_eq_refl:
  for +a: Nat
  {Nat.is_eq(a, a) == True{} : Bool}

def ar_eq_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      ar_eq_refl(p)

# is_eq is False exactly when the values differ.
law ar_eq_false:
  for +a: Nat
  for +b: Nat
  for differ: {a == b : Nat} -> Empty
  {Nat.is_eq(a, b) == False{} : Bool}

def ar_eq_false(a, b, differ):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, differ({==}))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_eq_false(p, q, e => differ(Equal.cong(Nat, Nat, ar_h_succ, p, q, e)))

law ar_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_lt_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, ar_false_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ar_false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ar_false_true(bc))
    case 1n+p 1n+q 1n+r:
      ar_lt_trans(p, q, r, ab, bc)

law ar_le_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_le_lt_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ar_false_true(bc))
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ar_false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ar_false_true(bc))
    case 1n+p 1n+q 1n+r:
      ar_le_lt_trans(p, q, r, ab, bc)

law ar_lt_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_lt_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, ar_false_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ar_false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, ar_false_true(bc))
    case 1n+p 1n+q 1n+r:
      ar_lt_le_trans(p, q, r, ab, bc)

law ar_lt_le:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def ar_lt_le(a, b, ab):
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, ar_false_true(ab))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, ar_false_true(ab))
    case 1n+p 1n+q:
      ar_lt_le(p, q, ab)

def ar_h_le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ar_h_le_succ(p)

law ar_le_add_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}

def ar_le_add_l(a, b):
  match a:
    case 0n:
      ar_le_refl(b)
    case 1n+p:
      ar_le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), ar_le_add_l(p, b), ar_h_le_succ(Nat.add(p, b)))

def ar_h_lt_zero(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a - b < c iff a < b + c, for c >= 1 (false at c = 0 when a < b).
law ar_sub_lt_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for pos: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_lt(Nat.sub(a, b), c) == Nat.is_lt(a, Nat.add(b, c)) : Bool}

def ar_sub_lt_iff(a, b, c, pos):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pos
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_sub_lt_iff(p, q, c, pos)

# c < a - b iff b + c < a (no side condition on Nat).
law ar_lt_sub_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.is_lt(c, Nat.sub(a, b)) == Nat.is_lt(Nat.add(b, c), a) : Bool}

def ar_lt_sub_iff(a, b, c):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ar_h_lt_zero(c)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_lt_sub_iff(p, q, c)

law ar_le_sub_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.is_le(Nat.sub(a, b), c) == Nat.is_le(a, Nat.add(b, c)) : Bool}

def ar_le_sub_iff(a, b, c):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ar_h_le_zero(c)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ar_le_sub_iff(p, q, c)

law ar_mul_le_cancel:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for pos: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == Nat.is_le(a, b) : Bool}

def ar_mul_le_cancel(a, b, c, pos):
  match a b:
    case 0n _:
      Equal.trans(Bool, Nat.is_le(0n, Nat.mul(b, c)), True{}, Nat.is_le(0n, b),
        ar_h_le_zero(Nat.mul(b, c)), Equal.sym(Bool, Nat.is_le(0n, b), True{}, ar_h_le_zero(b)))
    case 1n+p 0n:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.mul(1n+p, 0n), 0n) == False{} : Bool}, ar_false_true(pos))
        case 1n+r:
          {==}
    case 1n+p 1n+q:
      Equal.trans(Bool, Nat.is_le(Nat.add(c, Nat.mul(p, c)), Nat.add(c, Nat.mul(q, c))),
        Nat.is_le(Nat.mul(p, c), Nat.mul(q, c)), Nat.is_le(p, q),
        ar_le_add_cancel(c, Nat.mul(p, c), Nat.mul(q, c)), ar_mul_le_cancel(p, q, c, pos))

law ar_mul_lt_cancel:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for pos: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_lt(Nat.mul(a, c), Nat.mul(b, c)) == Nat.is_lt(a, b) : Bool}

def ar_mul_lt_cancel(a, b, c, pos):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+q, 0n)) == True{} : Bool}, ar_false_true(pos))
        case 1n+r:
          {==}
    case 1n+p 0n:
      ar_h_lt_zero(Nat.mul(1n+p, c))
    case 1n+p 1n+q:
      Equal.trans(Bool, Nat.is_lt(Nat.add(c, Nat.mul(p, c)), Nat.add(c, Nat.mul(q, c))),
        Nat.is_lt(Nat.mul(p, c), Nat.mul(q, c)), Nat.is_lt(p, q),
        ar_lt_add_cancel(c, Nat.mul(p, c), Nat.mul(q, c)), ar_mul_lt_cancel(p, q, c, pos))

def ar_h_and_false_r(x: Bool) -> {False{} == Bool.and(x, False{}) : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

law ar_min_lt:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(c, Nat.min(a, b)) == Bool.and(Nat.is_lt(c, a), Nat.is_lt(c, b)) : Bool}

def ar_min_lt(c, a, b):
  match c a b:
    case 0n 0n _:
      {==}
    case 0n 1n+p 0n:
      {==}
    case 0n 1n+p 1n+q:
      {==}
    case 1n+r 0n _:
      {==}
    case 1n+r 1n+p 0n:
      ar_h_and_false_r(Nat.is_lt(r, p))
    case 1n+r 1n+p 1n+q:
      ar_min_lt(r, p, q)

law ar_min_left:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.min(a, b) == a : Nat}

def ar_min_left(a, b, ab):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({0n == 1n+p : Nat}, ar_false_true(ab))
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.min(p, q), p, ar_min_left(p, q, ab)) : {1n+_ == 1n+p : Nat}
      {==}

# STUB-BEGIN (proven in gemm_m16_partition_wip_arithd.bend)
# Galois connection of floor division: q * b <= a iff q <= a / b (b >= 1).
law ar_div_le:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(q, b), a) == Nat.is_le(q, Nat.div(a, b)) : Bool}

def ar_div_le(q, a, b, pos):
  ?TODO

law ar_divmod:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat} &
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

def ar_divmod(a, b, pos):
  ?TODO

law ar_div_unique:
  for +q: Nat
  for +r: Nat
  for +b: Nat
  for small: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat} &
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}

def ar_div_unique(q, r, b, small):
  ?TODO

# Dual Galois connection of floor division: a / b < q iff a < q * b (b >= 1).
law ar_div_lt:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.div(a, b), q) == Nat.is_lt(a, Nat.mul(q, b)) : Bool}

def ar_div_lt(q, a, b, pos):
  ?TODO

law ar_div_add_self:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.div(Nat.add(a, b), b) == 1n+Nat.div(a, b) : Nat}

def ar_div_add_self(a, b, pos):
  ?TODO

law ar_div_mono:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  for ac: {Nat.is_le(a, c) == True{} : Bool}
  {Nat.is_le(Nat.div(a, b), Nat.div(c, b)) == True{} : Bool}

def ar_div_mono(a, c, b, pos, ac):
  ?TODO

# q1 * m + r1 == q2 * m + r2 with r1, r2 < m forces q1 == q2 and r1 == r2.
law ar_divmod_inj:
  for +q1: Nat
  for +r1: Nat
  for +q2: Nat
  for +r2: Nat
  for +m: Nat
  for small1: {Nat.is_lt(r1, m) == True{} : Bool}
  for small2: {Nat.is_lt(r2, m) == True{} : Bool}
  for same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat}
  {q1 == q2 : Nat} & {r1 == r2 : Nat}

def ar_divmod_inj(q1, r1, q2, r2, m, small1, small2, same):
  ?TODO
# STUB-END
