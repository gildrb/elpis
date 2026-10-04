# Helpers of dec_p2 (bend/err_attn_dec_p2.bend): ceil-division bounds, min / sub bounds, the elpis-side
# bound e_rt(L) <= 38 + 2 e_n0(L) for every L and e_n0(L) * 1280 <= 1279 + L. Structural proofs only.
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./attn_stride_proof.bend as SP
import ./err_attn_dec_tree.bend as Tr

# ==== Bool / order helpers ====

# not(x) == False gives x == True
def p2_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Ar.ar_true_false(h))
    case True{}:
      {==}

# is_lt(p, c) == False gives c <= p
def p2_ge(+p: Nat, +c: Nat, e: {Nat.is_lt(p, c) == False{} : Bool}) -> {Nat.is_le(c, p) == True{} : Bool}:
  p2_not_false(Nat.is_le(c, p), Equal.trans(Bool, Bool.not(Nat.is_le(c, p)), Nat.is_lt(p, c), False{},
    Equal.sym(Bool, Nat.is_lt(p, c), Bool.not(Nat.is_le(c, p)), Ar.ar_lt_not_le(p, c)), e))

# is_le(p, c) == False gives c < p
def p2_gt(+p: Nat, +c: Nat, e: {Nat.is_le(p, c) == False{} : Bool}) -> {Nat.is_lt(c, p) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(c, p), Bool.not(Nat.is_le(p, c)), Ar.ar_lt_not_le(c, p),
    Equal.cong(Bool, Bool, x => Bool.not(x), Nat.is_le(p, c), False{}, e))

# a < b gives 1 + a <= b
def p2_lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  Ar.ard_rt(Nat.is_lt(a, b), Nat.is_le(1n+a, b), Ar.ar_lt_succ_le(a, b), h)

# 1 + a <= b gives a < b
def p2_le_lt(+a: Nat, +b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(a, b), Nat.is_le(1n+a, b), Ar.ar_lt_succ_le(a, b), h)

# x - y <= x
def p2_sub_le(+x: Nat, +y: Nat) -> {Nat.is_le(Nat.sub(x, y), x) == True{} : Bool}:
  Ar.ard_tr(Nat.is_le(Nat.sub(x, y), x), Nat.is_le(x, Nat.add(y, x)), Ar.ar_le_sub_iff(x, y, x), Ar.ar_le_add_l(y, x))

# n < c gives n <= c - 1
def p2_le_pred(+n: Nat, +c: Nat, h: {Nat.is_lt(n, c) == True{} : Bool}) -> {Nat.is_le(n, Nat.sub(c, 1n)) == True{} : Bool}:
  match c:
    case 0n:
      Empty.absurd({Nat.is_le(n, Nat.sub(0n, 1n)) == True{} : Bool},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(n, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, Ar.ar_h_lt_zero(n)), h)))
    case 1n+cp:
      %Equal.sym(Nat, Nat.sub(cp, 0n), cp, Ar.ar_sub_zero_r(cp)) : {Nat.is_le(n, _) == True{} : Bool}
      Ar.ard_rt(Nat.is_lt(n, 1n+cp), Nat.is_le(1n+n, 1n+cp), Ar.ar_lt_succ_le(n, 1n+cp), h)

# 0 < x gives x - 1 < x
def p2_pred_lt(+x: Nat, h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(x, 1n), x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, Ar.ar_false_true(h))
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, Ar.ar_sub_zero_r(p)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      Ar.ard_tr(Nat.is_lt(p, 1n+p), Nat.is_le(1n+p, 1n+p), Ar.ar_lt_succ_le(p, 1n+p), Ar.ar_le_refl(1n+p))

# ==== min ====

def p2_min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      p2_min_le_l(ap, bp)

def p2_min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      Ar.ar_h_le_zero(b)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      p2_min_le_r(ap, bp)

# b <= a gives min(a, b) == b
def p2_min_right(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.min(0n, 1n+bp) == 1n+bp : Nat}, Ar.ar_false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(ap, bp), bp, p2_min_right(ap, bp, h))

# ==== ceil division (b >= 1) ====

# a <= c * b gives ceil(a / b) <= c
def p2_cd_le(+a: Nat, +b: Nat, +c: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_le(a, Nat.mul(c, b)) == True{} : Bool}) -> {Nat.is_le(St.cdiv(a, b), c) == True{} : Bool}:
  +cd = St.cdiv(a, b)
  +e1 = Equal.trans(Bool, Nat.is_lt(c, cd), Bool.not(Nat.is_le(a, Nat.mul(c, b))), False{}, SP.sp_live(c, a, b, pos),
    Equal.cong(Bool, Bool, x => Bool.not(x), Nat.is_le(a, Nat.mul(c, b)), True{}, h))
  p2_not_false(Nat.is_le(cd, c), Equal.trans(Bool, Bool.not(Nat.is_le(cd, c)), Nat.is_lt(c, cd), False{},
    Equal.sym(Bool, Nat.is_lt(c, cd), Bool.not(Nat.is_le(cd, c)), Ar.ar_lt_not_le(c, cd)), e1))

# a <= ceil(a / b) * b
def p2_cd_ub(+a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_le(a, Nat.mul(St.cdiv(a, b), b)) == True{} : Bool}:
  +cd = St.cdiv(a, b)
  p2_not_false(Nat.is_le(a, Nat.mul(cd, b)), Equal.trans(Bool, Bool.not(Nat.is_le(a, Nat.mul(cd, b))), Nat.is_lt(cd, cd), False{},
    Equal.sym(Bool, Nat.is_lt(cd, cd), Bool.not(Nat.is_le(a, Nat.mul(cd, b))), SP.sp_live(cd, a, b, pos)), Ar.ar_lt_irrefl(cd)))

# ceil(a / b) * b < b + a
def p2_cd_lb(+a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(Nat.mul(St.cdiv(a, b), b), Nat.add(b, a)) == True{} : Bool}:
  %Ar.ar_add_comm(a, b) : {Nat.is_lt(Nat.mul(St.cdiv(a, b), b), _) == True{} : Bool}
  +s = Nat.sub(Nat.add(a, b), 1n)
  Ar.ar_le_lt_trans(Nat.mul(St.cdiv(a, b), b), s, Nat.add(a, b), Ar.ard_le_mul_div(s, b, pos),
    p2_pred_lt(Nat.add(a, b), Ar.ar_lt_le_trans(0n, b, Nat.add(a, b), pos, Ar.ar_le_add_l(a, b))))


# n < 1 + n
def p2_lt_succ(+n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(n, 1n+n), Nat.is_le(1n+n, 1n+n), Ar.ar_lt_succ_le(n, 1n+n), Ar.ar_le_refl(1n+n))

# ceil(q * b / b) == q (b = 1 + bp)
def p2_cd_mul(+q: Nat, +bp: Nat) -> {St.cdiv(Nat.mul(q, 1n+bp), 1n+bp) == q : Nat}:
  +X = Nat.mul(q, 1n+bp)
  %Equal.sym(Nat, Nat.sub(Nat.add(X, 1n+bp), 1n), Nat.add(X, bp), SP.sp_pred(X, bp)) : {Nat.div(_, 1n+bp) == q : Nat}
  Ar.ard_fst({Nat.div(Nat.add(X, bp), 1n+bp) == q : Nat}, {Nat.mod(Nat.add(X, bp), 1n+bp) == bp : Nat},
    Ar.ar_div_unique(q, bp, 1n+bp, p2_lt_succ(bp)))
# ==== the elpis side ====

def p2_e_mono(+o: Nat, +n: Nat, +d: Nat, +t: Nat, ho: {Nat.is_le(o, 4n) == True{} : Bool},
    hd: {Nat.is_le(d, 5n) == True{} : Bool}, ht: {Nat.is_le(t, 6n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(o, 16n), Nat.add(Nat.add(n, d), Nat.add(2n, Nat.add(t, Nat.add(n, d))))),
       Nat.add(Nat.add(4n, 16n), Nat.add(Nat.add(n, 5n), Nat.add(2n, Nat.add(6n, Nat.add(n, 5n)))))) == True{} : Bool}:
  +a2 = NO.le_add_mono(n, n, d, 5n, Ar.ar_le_refl(n), hd)
  +a3 = NO.le_add_mono(t, 6n, Nat.add(n, d), Nat.add(n, 5n), ht, a2)
  +a4 = NO.le_add_mono(2n, 2n, Nat.add(t, Nat.add(n, d)), Nat.add(6n, Nat.add(n, 5n)), Ar.ar_le_refl(2n), a3)
  +a5 = NO.le_add_mono(Nat.add(n, d), Nat.add(n, 5n), Nat.add(2n, Nat.add(t, Nat.add(n, d))),
    Nat.add(2n, Nat.add(6n, Nat.add(n, 5n))), a2, a4)
  NO.le_add_mono(Nat.add(o, 16n), Nat.add(4n, 16n), Nat.add(Nat.add(n, d), Nat.add(2n, Nat.add(t, Nat.add(n, d)))),
    Nat.add(Nat.add(n, 5n), Nat.add(2n, Nat.add(6n, Nat.add(n, 5n)))),
    NO.le_add_mono(o, 4n, 16n, 16n, ho, Ar.ar_le_refl(16n)), a5)

def p2_e_norm(+n: Nat)
  -> {Nat.add(Nat.add(4n, 16n), Nat.add(Nat.add(n, 5n), Nat.add(2n, Nat.add(6n, Nat.add(n, 5n))))) == Nat.add(38n, Nat.add(n, n)) : Nat}:
  %Ar.ar_add_comm(5n, n) : {Nat.add(Nat.add(4n, 16n), Nat.add(_, Nat.add(2n, Nat.add(6n, _)))) == Nat.add(38n, Nat.add(n, n)) : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(25n, z), Nat.add(n, Nat.add(13n, n)), Nat.add(13n, Nat.add(n, n)), NO.add_swap(n, 13n, n))

# e_OE(L) <= 4
def p2_oe_le(+L: Nat) -> {Nat.is_le(Dec.e_OE(L), 4n) == True{} : Bool}:
  +m = Nat.min(4n, St.cdiv(L, 16n))
  Ar.ar_le_trans(Dec.e_OE(L), m, 4n, p2_sub_le(m, St.bit(Nat.is_eq(L, 1n))), p2_min_le_l(4n, St.cdiv(L, 16n)))

# e_rt(L) <= 38 + 2 e_n0(L)
def p2_e_le(+L: Nat) -> {Nat.is_le(Dec.e_rt(L), Nat.add(38n, Nat.add(Dec.e_n0(L), Dec.e_n0(L)))) == True{} : Bool}:
  +n = Dec.e_n0(L)
  hd : {Nat.is_le(Dec.e_D(L), 5n) == True{} : Bool} = Tr.tr_tbound_mono(9n, Dec.e_nsl(L), 20n, p2_min_le_r(Dec.e_T(L), 20n))
  Ar.ar_le_trans(Dec.e_rt(L), Nat.add(Nat.add(4n, 16n), Nat.add(Nat.add(n, 5n), Nat.add(2n, Nat.add(6n, Nat.add(n, 5n))))),
    Nat.add(38n, Nat.add(n, n)),
    p2_e_mono(Dec.e_OE(L), n, Dec.e_D(L), Dec.e_TE(L), p2_oe_le(L), hd, Tr.tr_tbound_le(6n, L)),
    NO.le_of_eq(Nat.add(Nat.add(4n, 16n), Nat.add(Nat.add(n, 5n), Nat.add(2n, Nat.add(6n, Nat.add(n, 5n))))),
      Nat.add(38n, Nat.add(n, n)), p2_e_norm(n)))

# e_n0(L) * 20 < 20 + e_T(L)
def p2_n0_t(+L: Nat) -> {Nat.is_lt(Nat.mul(Dec.e_n0(L), 20n), Nat.add(20n, Dec.e_T(L))) == True{} : Bool}:
  %Ar.ar_sub_zero_r(Dec.e_T(L)) : {Nat.is_lt(Nat.mul(Dec.e_n0(L), 20n), Nat.add(20n, _)) == True{} : Bool}
  p2_cd_lb(Nat.sub(Dec.e_T(L), 0n), 20n, {==})

# e_n0(L) * 1280 <= 1279 + L
def p2_n0_bound(+L: Nat) -> {Nat.is_le(Nat.mul(Dec.e_n0(L), 1280n), Nat.add(1279n, L)) == True{} : Bool}:
  +n = Dec.e_n0(L)
  +T = Dec.e_T(L)
  +X = Nat.mul(n, 20n)
  h3 : {Nat.is_le(Nat.add(64n, Nat.mul(X, 64n)), Nat.add(1280n, Nat.mul(T, 64n))) == True{} : Bool} =
    Ar.ar_le_mul_mono(1n+X, Nat.add(20n, T), 64n, p2_lt_le(X, Nat.add(20n, T), p2_n0_t(L)))
  h4 : {Nat.is_le(Nat.add(1280n, Nat.mul(T, 64n)), Nat.add(1343n, L)) == True{} : Bool} =
    p2_lt_le(Nat.mul(T, 64n), Nat.add(64n, L), p2_cd_lb(L, 64n, {==}))
  h5 : {Nat.is_le(Nat.mul(X, 64n), Nat.add(1279n, L)) == True{} : Bool} =
    Ar.ar_le_trans(Nat.add(64n, Nat.mul(X, 64n)), Nat.add(1280n, Nat.mul(T, 64n)), Nat.add(1343n, L), h3, h4)
  %Ar.ar_mul_assoc(n, 20n, 64n) : {Nat.is_le(_, Nat.add(1279n, L)) == True{} : Bool}
  h5
