# dec_p2 (bend/err_attn_dec_p2.bend) for L > 4096, the final arithmetic: with stock's split_len 32 m,
# m = 7 + mq, and nl live splits, stock key 0's total is 51 + 2 (2 mq + (nl - 1)) (p2_d_tail), and
# e_n0(L) <= 6 + 2 mq + (nl - 1) both when nl >= 3 (L <= 1312 m) and when nl <= 2 (L <= 64 m).
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./err_attn_dec_p2_lib.bend as Lb
import ./err_attn_dec_p2_s.bend as Ps

# mq * 2 == mq + mq
def p2_d_two(+mq: Nat) -> {Nat.mul(mq, 2n) == Nat.add(mq, mq) : Nat}:
  Equal.trans(Nat, Nat.mul(mq, 2n), Nat.mul(2n, mq), Nat.add(mq, mq), Ar.ar_mul_comm(mq, 2n),
    Equal.cong(Nat, Nat, z => Nat.add(mq, z), Nat.add(mq, 0n), mq, Ar.ar_add_zero_r(mq)))

# (6 + J) + (6 + J) <= 13 + (J + J)
def p2_d_dbl(+J: Nat) -> {Nat.is_le(Nat.add(Nat.add(6n, J), Nat.add(6n, J)), Nat.add(13n, Nat.add(J, J))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(J, Nat.add(6n, J)), Nat.add(6n, Nat.add(J, J)), NO.add_swap(J, 6n, J)) : {Nat.is_le(Nat.add(6n, _), Nat.add(13n, Nat.add(J, J))) == True{} : Bool}
  Ar.ar_h_le_succ(Nat.add(J, J))

# n <= 6 + J gives 38 + 2 n <= 51 + 2 J
def p2_d_fin2(+n: Nat, +J: Nat, hn: {Nat.is_le(n, Nat.add(6n, J)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(38n, Nat.add(n, n)), Nat.add(51n, Nat.add(J, J))) == True{} : Bool}:
  +h = hn
  Ar.ar_le_trans(Nat.add(n, n), Nat.add(Nat.add(6n, J), Nat.add(6n, J)), Nat.add(13n, Nat.add(J, J)),
    NO.le_add_mono(n, Nat.add(6n, J), n, Nat.add(6n, J), h, h), p2_d_dbl(J))

# Stock key 0's total at split_len 32 (7 + mq) and nl live splits is 51 + 2 (mq + (mq + (nl - 1)))
def p2_d_tail(+n: Nat, +mq: Nat, +nl: Nat, +Lp: Nat,
    hn: {Nat.is_le(n, Nat.add(6n, Nat.add(mq, Nat.add(mq, Nat.sub(nl, 1n))))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(38n, Nat.add(n, n)), Ps.p2_srt2(Nat.add(129n, Lp), Nat.mul(Nat.add(7n, mq), 2n), Nat.add(7n, mq), nl)) == True{} : Bool}:
  +a = Nat.sub(nl, 1n)
  +X = Nat.mul(mq, 2n)
  +Q = Nat.add(mq, 1n+a)
  +M = Nat.add(mq, a)
  +XL = Nat.add(38n, Nat.add(n, n))
  %Ar.ar_add_comm(16n, X) : {Nat.is_le(XL, Nat.add(14n, Nat.add(_, Nat.add(6n, Nat.add(Q, Nat.add(13n, Q)))))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Q, Nat.add(13n, Q)), Nat.add(13n, Nat.add(Q, Q)), NO.add_swap(Q, 13n, Q)) : {Nat.is_le(XL, Nat.add(30n, Nat.add(X, Nat.add(6n, _)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(X, Nat.add(19n, Nat.add(Q, Q))), Nat.add(19n, Nat.add(X, Nat.add(Q, Q))), NO.add_swap(X, 19n, Nat.add(Q, Q))) : {Nat.is_le(XL, Nat.add(30n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(mq, 1n+a), 1n+Nat.add(mq, a), Ar.ar_add_succ_r(mq, a)) : {Nat.is_le(XL, Nat.add(49n, Nat.add(X, Nat.add(_, _)))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(X, 1n+Nat.add(M, 1n+M)), 1n+Nat.add(X, Nat.add(M, 1n+M)), Ar.ar_add_succ_r(X, Nat.add(M, 1n+M))) : {Nat.is_le(XL, Nat.add(49n, _)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(M, 1n+M), 1n+Nat.add(M, M), Ar.ar_add_succ_r(M, M)) : {Nat.is_le(XL, Nat.add(50n, Nat.add(X, _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(X, 1n+Nat.add(M, M)), 1n+Nat.add(X, Nat.add(M, M)), Ar.ar_add_succ_r(X, Nat.add(M, M))) : {Nat.is_le(XL, Nat.add(50n, _)) == True{} : Bool}
  %Equal.sym(Nat, X, Nat.add(mq, mq), p2_d_two(mq)) : {Nat.is_le(XL, Nat.add(51n, Nat.add(_, Nat.add(M, M)))) == True{} : Bool}
  %NO.add_swap4(mq, M, mq, M) : {Nat.is_le(XL, Nat.add(51n, _)) == True{} : Bool}
  p2_d_fin2(n, Nat.add(mq, M), hn)

# 2 <= a: 8 + 2 mq <= 6 + (mq + (mq + a))
def p2_d_k6(+mq: Nat, +a: Nat, ha: {Nat.is_le(2n, a) == True{} : Bool})
  -> {Nat.is_le(Nat.add(8n, Nat.mul(mq, 2n)), Nat.add(6n, Nat.add(mq, Nat.add(mq, a)))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(mq, 2n), Nat.add(mq, mq), p2_d_two(mq)) : {Nat.is_le(Nat.add(2n, _), Nat.add(mq, Nat.add(mq, a))) == True{} : Bool}
  +MM = Nat.add(mq, mq)
  Ar.ar_le_trans(Nat.add(2n, MM), Nat.add(mq, Nat.add(mq, 2n)), Nat.add(mq, Nat.add(mq, a)),
    NO.le_of_eq(Nat.add(2n, MM), Nat.add(mq, Nat.add(mq, 2n)),
      Equal.trans(Nat, Nat.add(2n, MM), Nat.add(MM, 2n), Nat.add(mq, Nat.add(mq, 2n)), Ar.ar_add_comm(2n, MM), Ar.ar_add_assoc(mq, mq, 2n))),
    NO.le_add_mono(mq, mq, Nat.add(mq, 2n), Nat.add(mq, a), Ar.ar_le_refl(mq),
      NO.le_add_mono(mq, mq, 2n, a, Ar.ar_le_refl(mq), ha)))

# nl >= 3 (a = nl - 1 >= 2), L <= 1312 (7 + mq): e_n0 <= 6 + (mq + (mq + a))
def p2_d_big(+n: Nat, +mq: Nat, +a: Nat, +L: Nat, h1: {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1279n, L)) == True{} : Bool},
    h2: {Nat.is_le(L, Nat.mul(Nat.add(7n, mq), 1312n)) == True{} : Bool}, ha: {Nat.is_le(2n, a) == True{} : Bool})
  -> {Nat.is_le(n, Nat.add(6n, Nat.add(mq, Nat.add(mq, a)))) == True{} : Bool}:
  +X = Nat.mul(mq, 2n)
  +Y = Nat.mul(X, 1280n)
  k1 : {Nat.is_le(Nat.mul(n, 1280n), Nat.add(10463n, Nat.mul(mq, 1312n))) == True{} : Bool} =
    Ar.ar_le_trans(Nat.mul(n, 1280n), Nat.add(1279n, L), Nat.add(1279n, Nat.mul(Nat.add(7n, mq), 1312n)), h1,
      NO.le_add_mono(1279n, 1279n, L, Nat.mul(Nat.add(7n, mq), 1312n), Ar.ar_le_refl(1279n), h2))
  +k2 = Ar.ar_le_trans(Nat.mul(mq, 1312n), Nat.mul(mq, 2560n), Y, NO.le_mul_mono_r(1312n, 2560n, mq, {==}),
    NO.le_of_eq(Nat.mul(mq, 2560n), Y, Equal.sym(Nat, Y, Nat.mul(mq, 2560n), Ar.ar_mul_assoc(mq, 2n, 1280n))))
  lt2 : {Nat.is_lt(Y, Nat.add(1057n, Y)) == True{} : Bool} = Lb.p2_le_lt(Y, Nat.add(1057n, Y), Ar.ar_le_add_l(1056n, Y))
  lt1 : {Nat.is_lt(Nat.add(10463n, Nat.mul(mq, 1312n)), Nat.add(11520n, Y)) == True{} : Bool} =
    Ar.ar_le_lt_trans(Nat.mul(mq, 1312n), Y, Nat.add(1057n, Y), k2, lt2)
  k3 : {Nat.is_lt(Nat.mul(n, 1280n), Nat.mul(Nat.add(9n, X), 1280n)) == True{} : Bool} =
    Ar.ar_le_lt_trans(Nat.mul(n, 1280n), Nat.add(10463n, Nat.mul(mq, 1312n)), Nat.add(11520n, Y), k1, lt1)
  +k4 = Ar.ard_rt(Nat.is_lt(Nat.mul(n, 1280n), Nat.mul(Nat.add(9n, X), 1280n)), Nat.is_lt(n, Nat.add(9n, X)),
    Ar.ar_mul_lt_cancel(n, Nat.add(9n, X), 1280n, {==}), k3)
  k5 : {Nat.is_le(n, Nat.add(8n, X)) == True{} : Bool} = Lb.p2_lt_le(n, Nat.add(9n, X), k4)
  Ar.ar_le_trans(n, Nat.add(8n, X), Nat.add(6n, Nat.add(mq, Nat.add(mq, a))), k5, p2_d_k6(mq, a, ha))

# nl <= 2, L <= nl * 32 (7 + mq): e_n0 <= 6 + (mq + (mq + (nl - 1)))
def p2_d_small(+n: Nat, +mq: Nat, +nl: Nat, +L: Nat, h1: {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1279n, L)) == True{} : Bool},
    h3: {Nat.is_le(L, Nat.mul(nl, Nat.mul(Nat.add(7n, mq), 32n))) == True{} : Bool}, hnl: {Nat.is_le(nl, 2n) == True{} : Bool})
  -> {Nat.is_le(n, Nat.add(6n, Nat.add(mq, Nat.add(mq, Nat.sub(nl, 1n))))) == True{} : Bool}:
  +m = Nat.add(7n, mq)
  +v = Nat.mul(m, 32n)
  +J = Nat.add(mq, Nat.add(mq, Nat.sub(nl, 1n)))
  +j2 = Equal.trans(Nat, Nat.mul(2n, v), Nat.mul(v, 2n), Nat.mul(m, 64n), Ar.ar_mul_comm(2n, v), Ar.ar_mul_assoc(m, 32n, 2n))
  +j3 = Ar.ar_le_trans(L, Nat.mul(nl, v), Nat.mul(m, 64n), h3,
    Ar.ar_le_trans(Nat.mul(nl, v), Nat.mul(2n, v), Nat.mul(m, 64n), Ar.ar_le_mul_mono(nl, 2n, v, hnl),
      NO.le_of_eq(Nat.mul(2n, v), Nat.mul(m, 64n), j2)))
  j4 : {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1727n, Nat.mul(mq, 64n))) == True{} : Bool} =
    Ar.ar_le_trans(Nat.mul(n, 1280n), Nat.add(1279n, L), Nat.add(1279n, Nat.mul(m, 64n)), h1,
      NO.le_add_mono(1279n, 1279n, L, Nat.mul(m, 64n), Ar.ar_le_refl(1279n), j3))
  +Z = Nat.mul(mq, 1280n)
  lt1 : {Nat.is_lt(Nat.add(1727n, Nat.mul(mq, 64n)), Nat.add(2560n, Z)) == True{} : Bool} =
    Ar.ar_le_lt_trans(Nat.mul(mq, 64n), Z, Nat.add(833n, Z), NO.le_mul_mono_r(64n, 1280n, mq, {==}),
      Lb.p2_le_lt(Z, Nat.add(833n, Z), Ar.ar_le_add_l(832n, Z)))
  j5 : {Nat.is_lt(Nat.mul(n, 1280n), Nat.mul(Nat.add(2n, mq), 1280n)) == True{} : Bool} =
    Ar.ar_le_lt_trans(Nat.mul(n, 1280n), Nat.add(1727n, Nat.mul(mq, 64n)), Nat.add(2560n, Z), j4, lt1)
  +j6 = Ar.ard_rt(Nat.is_lt(Nat.mul(n, 1280n), Nat.mul(Nat.add(2n, mq), 1280n)), Nat.is_lt(n, Nat.add(2n, mq)),
    Ar.ar_mul_lt_cancel(n, Nat.add(2n, mq), 1280n, {==}), j5)
  j7 : {Nat.is_le(n, Nat.add(1n, mq)) == True{} : Bool} = Lb.p2_lt_le(n, Nat.add(2n, mq), j6)
  j8 : {Nat.is_le(Nat.add(1n, mq), Nat.add(6n, J)) == True{} : Bool} =
    Ar.ar_le_trans(mq, J, Nat.add(5n, J), Ar.ar_le_add_r(mq, Nat.add(mq, Nat.sub(nl, 1n))), Ar.ar_le_add_l(5n, J))
  Ar.ar_le_trans(n, Nat.add(1n, mq), Nat.add(6n, J), j7, j8)

def p2_d_case(+n: Nat, +mq: Nat, +nl: Nat, +L: Nat, b: Bool, e: {Nat.is_le(3n, nl) == b : Bool},
    h1: {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1279n, L)) == True{} : Bool},
    h2: {Nat.is_le(L, Nat.mul(Nat.add(7n, mq), 1312n)) == True{} : Bool},
    h3: {Nat.is_le(L, Nat.mul(nl, Nat.mul(Nat.add(7n, mq), 32n))) == True{} : Bool})
  -> {Nat.is_le(n, Nat.add(6n, Nat.add(mq, Nat.add(mq, Nat.sub(nl, 1n))))) == True{} : Bool}:
  match b:
    case True{}:
      p2_d_big(n, mq, Nat.sub(nl, 1n), L, h1, h2, Lb.p2_le_pred(2n, nl, Lb.p2_le_lt(2n, nl, e)))
    case False{}:
      hnl : {Nat.is_le(nl, 2n) == True{} : Bool} = Lb.p2_lt_le(nl, 3n, Lb.p2_gt(3n, nl, e))
      p2_d_small(n, mq, nl, L, h1, h3, hnl)

# The case-D conclusion at split_len 32 (7 + mq) with nl live splits
def p2_d_fin(+n: Nat, +mq: Nat, +nl: Nat, +L: Nat, +Lp: Nat,
    h1: {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1279n, L)) == True{} : Bool},
    h2: {Nat.is_le(L, Nat.mul(Nat.add(7n, mq), 1312n)) == True{} : Bool},
    h3: {Nat.is_le(L, Nat.mul(nl, Nat.mul(Nat.add(7n, mq), 32n))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(38n, Nat.add(n, n)), Ps.p2_srt2(Nat.add(129n, Lp), Nat.mul(Nat.add(7n, mq), 2n), Nat.add(7n, mq), nl)) == True{} : Bool}:
  p2_d_tail(n, mq, nl, Lp, p2_d_case(n, mq, nl, L, Nat.is_le(3n, nl), {==}, h1, h2, h3))
