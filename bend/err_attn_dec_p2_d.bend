# dec_p2 (bend/err_attn_dec_p2.bend) for L >= 4097: the block-table width g = ceil(ceil(L / 256) / 16) >= 2,
# stock's bound B = 4096 g + 1 >= 8193, num_splits 41, split_len 32 m with m = ceil(ceil(B / 41) / 32) >= 7;
# 32 m <= L (split 0 is full: 2 m groups, m tiles), L <= 1312 m and L <= nl * 32 m (nl live splits); the
# arithmetic is bend/err_attn_dec_p2_d2.bend's.
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./attn_stride_proof.bend as SP
import ./err_attn_dec_p2_lib.bend as Lb
import ./err_attn_dec_p2_s.bend as Ps
import ./err_attn_dec_p2_d2.bend as D2

# The stock quantities of a row of length L
def p2_c1(+L: Nat) -> Nat:
  St.cdiv(L, 256n)

def p2_g(+L: Nat) -> Nat:
  St.cdiv(p2_c1(L), 16n)

def p2_bx(+L: Nat) -> Nat:
  Nat.mul(Nat.mul(p2_g(L), 16n), 256n)

def p2_c3(+L: Nat) -> Nat:
  St.cdiv(Nat.add(p2_bx(L), 1n), 41n)

def p2_m(+L: Nat) -> Nat:
  St.cdiv(p2_c3(L), 32n)

# 8192 <= 4096 g
def p2_d_bx(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Nat.is_le(8192n, p2_bx(L)) == True{} : Bool}:
  +f1 = SP.sp_lt_cdiv(16n, L, 256n, {==}, Lb.p2_le_lt(4096n, L, lo))
  +f2 = SP.sp_lt_cdiv(1n, p2_c1(L), 16n, {==}, f1)
  Ar.ar_le_mul_mono(Nat.mul(2n, 16n), Nat.mul(p2_g(L), 16n), 256n, Ar.ar_le_mul_mono(2n, p2_g(L), 16n, Lb.p2_lt_le(1n, p2_g(L), f2)))

# 8192 <= B
def p2_d_bb(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Nat.is_le(8192n, Nat.add(p2_bx(L), 1n)) == True{} : Bool}:
  Ar.ar_le_trans(8192n, p2_bx(L), Nat.add(p2_bx(L), 1n), p2_d_bx(L, lo), Ar.ar_le_add_r(p2_bx(L), 1n))

# num_splits == 41
def p2_d_ns(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Dec.s_nsB(Dec.s_bound(L)) == 41n : Nat}:
  +B = Nat.add(p2_bx(L), 1n)
  +c = St.cdiv(B, 128n)
  +h41 = Lb.p2_lt_le(40n, c, SP.sp_lt_cdiv(40n, B, 128n, {==}, Ar.ar_lt_le_trans(5120n, 8192n, B, {==}, p2_d_bb(L, lo))))
  Equal.cong(Nat, Nat, z => Nat.max(1n, z), Nat.min(41n, c), 41n, Ar.ar_min_left(41n, c, h41))

# split_len == 32 m
def p2_d_sl(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Dec.s_sl(L) == Nat.mul(p2_m(L), 32n) : Nat}:
  +B = Nat.add(p2_bx(L), 1n)
  Equal.cong(Nat, Nat, z => Nat.mul(St.cdiv(St.cdiv(B, z), 32n), 32n), Dec.s_nsB(B), 41n, p2_d_ns(L, lo))

# 7 <= m
def p2_d_m7(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Nat.is_le(7n, p2_m(L)) == True{} : Bool}:
  +B = Nat.add(p2_bx(L), 1n)
  +f7 = SP.sp_lt_cdiv(199n, B, 41n, {==}, Ar.ar_lt_le_trans(8159n, 8192n, B, {==}, p2_d_bb(L, lo)))
  Lb.p2_lt_le(6n, p2_m(L), SP.sp_lt_cdiv(6n, p2_c3(L), 32n, {==}, Ar.ar_lt_trans(192n, 199n, p2_c3(L), {==}, f7)))

# L <= 1312 m
def p2_d_h2(+L: Nat) -> {Nat.is_le(L, Nat.mul(p2_m(L), 1312n)) == True{} : Bool}:
  +c1 = p2_c1(L)
  +bx = p2_bx(L)
  +B = Nat.add(bx, 1n)
  +c3 = p2_c3(L)
  +m = p2_m(L)
  +s1 = Ar.ar_le_trans(L, Nat.mul(c1, 256n), bx, Lb.p2_cd_ub(L, 256n, {==}),
    Ar.ar_le_mul_mono(c1, Nat.mul(p2_g(L), 16n), 256n, Lb.p2_cd_ub(c1, 16n, {==})))
  +s2 = Ar.ar_le_trans(L, bx, B, s1, Ar.ar_le_add_r(bx, 1n))
  +s3 = Ar.ar_le_trans(L, B, Nat.mul(c3, 41n), s2, Lb.p2_cd_ub(B, 41n, {==}))
  +s4 = Ar.ar_le_trans(L, Nat.mul(c3, 41n), Nat.mul(Nat.mul(m, 32n), 41n), s3,
    Ar.ar_le_mul_mono(c3, Nat.mul(m, 32n), 41n, Lb.p2_cd_ub(c3, 32n, {==})))
  Ar.ar_le_trans(L, Nat.mul(Nat.mul(m, 32n), 41n), Nat.mul(m, 1312n), s4,
    NO.le_of_eq(Nat.mul(Nat.mul(m, 32n), 41n), Nat.mul(m, 1312n), Ar.ar_mul_assoc(m, 32n, 41n)))

# B <= 4096 + L
def p2_d_b5(+L: Nat) -> {Nat.is_le(Nat.add(p2_bx(L), 1n), Nat.add(4096n, L)) == True{} : Bool}:
  +c1 = p2_c1(L)
  +bx = p2_bx(L)
  %Ar.ar_add_comm(1n, bx) : {Nat.is_le(_, Nat.add(4096n, L)) == True{} : Bool}
  b2 : {Nat.is_le(Nat.add(256n, bx), Nat.add(4096n, Nat.mul(c1, 256n))) == True{} : Bool} =
    Ar.ar_le_mul_mono(1n+Nat.mul(p2_g(L), 16n), Nat.add(16n, c1), 256n,
      Lb.p2_lt_le(Nat.mul(p2_g(L), 16n), Nat.add(16n, c1), Lb.p2_cd_lb(c1, 16n, {==})))
  b3 : {Nat.is_le(Nat.add(4096n, Nat.mul(c1, 256n)), Nat.add(4351n, L)) == True{} : Bool} =
    Lb.p2_lt_le(Nat.mul(c1, 256n), Nat.add(256n, L), Lb.p2_cd_lb(L, 256n, {==}))
  Ar.ar_le_trans(Nat.add(256n, bx), Nat.add(4096n, Nat.mul(c1, 256n)), Nat.add(4351n, L), b2, b3)

# 5407 + L <= 41 L
def p2_d_a6(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Nat.is_le(Nat.add(5407n, L), Nat.mul(L, 41n)) == True{} : Bool}:
  +c2 = Ar.ar_le_trans(5407n, 5440n, Nat.mul(L, 40n), {==},
    Ar.ar_le_mul_mono(136n, L, 40n, Ar.ar_le_trans(136n, 4097n, L, {==}, lo)))
  Ar.ar_le_trans(Nat.add(5407n, L), Nat.add(Nat.mul(L, 40n), L), Nat.mul(L, 41n),
    NO.le_add_mono(5407n, Nat.mul(L, 40n), L, L, c2, Ar.ar_le_refl(L)),
    NO.le_of_eq(Nat.add(Nat.mul(L, 40n), L), Nat.mul(L, 41n),
      Equal.trans(Nat, Nat.add(Nat.mul(L, 40n), L), Nat.add(L, Nat.mul(L, 40n)), Nat.mul(L, 41n),
        Ar.ar_add_comm(Nat.mul(L, 40n), L), Equal.sym(Nat, Nat.mul(L, 41n), Nat.add(L, Nat.mul(L, 40n)), Ar.ar_mul_succ_r(L, 40n)))))

# 32 m <= L: split 0 is full
def p2_d_hv(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool}) -> {Nat.is_le(Nat.mul(p2_m(L), 32n), L) == True{} : Bool}:
  +B = Nat.add(p2_bx(L), 1n)
  +c3 = p2_c3(L)
  +v = Nat.mul(p2_m(L), 32n)
  a1 : {Nat.is_le(v, Nat.add(31n, c3)) == True{} : Bool} = Lb.p2_lt_le(v, Nat.add(32n, c3), Lb.p2_cd_lb(c3, 32n, {==}))
  a2 : {Nat.is_le(Nat.mul(v, 41n), Nat.add(1271n, Nat.mul(c3, 41n))) == True{} : Bool} = Ar.ar_le_mul_mono(v, Nat.add(31n, c3), 41n, a1)
  a3 : {Nat.is_le(Nat.add(1271n, Nat.mul(c3, 41n)), Nat.add(1311n, B)) == True{} : Bool} =
    Lb.p2_lt_le(Nat.mul(c3, 41n), Nat.add(41n, B), Lb.p2_cd_lb(B, 41n, {==}))
  b5 : {Nat.is_le(Nat.add(1311n, B), Nat.add(5407n, L)) == True{} : Bool} = p2_d_b5(L)
  +a5 = Ar.ar_le_trans(Nat.mul(v, 41n), Nat.add(1271n, Nat.mul(c3, 41n)), Nat.add(5407n, L), a2,
    Ar.ar_le_trans(Nat.add(1271n, Nat.mul(c3, 41n)), Nat.add(1311n, B), Nat.add(5407n, L), a3, b5))
  +a7 = Ar.ar_le_trans(Nat.mul(v, 41n), Nat.add(5407n, L), Nat.mul(L, 41n), a5, p2_d_a6(L, lo))
  Ar.ard_rt(Nat.is_le(Nat.mul(v, 41n), Nat.mul(L, 41n)), Nat.is_le(v, L), Ar.ar_mul_le_cancel(v, L, 41n, {==}), a7)

# L <= nl * 32 m
def p2_d_h3(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool})
  -> {Nat.is_le(L, Nat.mul(St.cdiv(L, Nat.mul(p2_m(L), 32n)), Nat.mul(p2_m(L), 32n))) == True{} : Bool}:
  +v = Nat.mul(p2_m(L), 32n)
  pos : {Nat.is_lt(0n, v) == True{} : Bool} =
    Ar.ar_lt_le_trans(0n, 224n, v, {==}, Ar.ar_le_mul_mono(7n, p2_m(L), 32n, p2_d_m7(L, lo)))
  Lb.p2_cd_ub(L, v, pos)

# ceil(32 m / 16) == 2 m
def p2_d_cd16(+m: Nat) -> {St.cdiv(Nat.mul(m, 32n), 16n) == Nat.mul(m, 2n) : Nat}:
  %Ar.ar_mul_assoc(m, 2n, 16n) : {St.cdiv(_, 16n) == Nat.mul(m, 2n) : Nat}
  Lb.p2_cd_mul(Nat.mul(m, 2n), 15n)

# The stock side at split_len 32 m, m = 7 + mq
def p2_d_t1(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool})
  -> {Nat.is_le(Nat.add(38n, Nat.add(Dec.e_n0(L), Dec.e_n0(L))),
       Ps.p2_srt2(L, St.cdiv(Nat.mul(p2_m(L), 32n), 16n), St.cdiv(Nat.mul(p2_m(L), 32n), 32n),
         St.cdiv(L, Nat.mul(p2_m(L), 32n)))) == True{} : Bool}:
  +m = p2_m(L)
  +mq = Nat.sub(m, 7n)
  +v = Nat.mul(m, 32n)
  +nl = St.cdiv(L, v)
  +n = Dec.e_n0(L)
  +X = Nat.add(38n, Nat.add(n, n))
  +l = lo
  +em = Ar.ar_sub_add(m, 7n, p2_d_m7(L, l))
  +h2 = Ar.ard_rt(Nat.is_le(L, Nat.mul(m, 1312n)), Nat.is_le(L, Nat.mul(Nat.add(7n, mq), 1312n)),
    Equal.cong(Nat, Bool, z => Nat.is_le(L, Nat.mul(z, 1312n)), m, Nat.add(7n, mq), Equal.sym(Nat, Nat.add(7n, mq), m, em)),
    p2_d_h2(L))
  +h3 = Ar.ard_rt(Nat.is_le(L, Nat.mul(nl, v)), Nat.is_le(L, Nat.mul(nl, Nat.mul(Nat.add(7n, mq), 32n))),
    Equal.cong(Nat, Bool, z => Nat.is_le(L, Nat.mul(nl, Nat.mul(z, 32n))), m, Nat.add(7n, mq), Equal.sym(Nat, Nat.add(7n, mq), m, em)),
    p2_d_h3(L, l))
  %Equal.sym(Nat, St.cdiv(v, 16n), Nat.mul(m, 2n), p2_d_cd16(m)) : {Nat.is_le(X, Ps.p2_srt2(L, _, St.cdiv(v, 32n), nl)) == True{} : Bool}
  %Equal.sym(Nat, St.cdiv(v, 32n), m, Lb.p2_cd_mul(m, 31n)) : {Nat.is_le(X, Ps.p2_srt2(L, Nat.mul(m, 2n), _, nl)) == True{} : Bool}
  %em : {Nat.is_le(X, Ps.p2_srt2(L, Nat.mul(_, 2n), _, nl)) == True{} : Bool}
  Ps.p2_s_sh(L, Nat.mul(Nat.add(7n, mq), 2n), Nat.add(7n, mq), nl, X, Ar.ar_le_trans(129n, 4097n, L, {==}, l),
    D2.p2_d_fin(n, mq, nl, L, Nat.sub(L, 129n), Lb.p2_n0_bound(L), h2, h3))

# own0 + laterk0 >= 4 at split_len 32 m
def p2_d_t0(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool})
  -> {Nat.is_le(4n, Ps.p2_sok(L, St.cdiv(Nat.mul(p2_m(L), 32n), 16n))) == True{} : Bool}:
  +m = p2_m(L)
  +mq = Nat.sub(m, 7n)
  +l = lo
  %Equal.sym(Nat, St.cdiv(Nat.mul(m, 32n), 16n), Nat.mul(m, 2n), p2_d_cd16(m)) : {Nat.is_le(4n, Ps.p2_sok(L, _)) == True{} : Bool}
  %Ar.ar_sub_add(m, 7n, p2_d_m7(L, l)) : {Nat.is_le(4n, Ps.p2_sok(L, Nat.mul(_, 2n))) == True{} : Bool}
  Ps.p2_ok_sh(L, Nat.mul(Nat.add(7n, mq), 2n), 4n, Ar.ar_le_trans(129n, 4097n, L, {==}, l), {==})

def p2_d(+L: Nat, lo: {Nat.is_le(4097n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  +l = lo
  +v = Nat.mul(p2_m(L), 32n)
  +slq = p2_d_sl(L, l)
  +hv = p2_d_hv(L, l)
  +n = Dec.e_n0(L)
  +X = Nat.add(38n, Nat.add(n, n))
  (Ar.ar_le_trans(Dec.e_OE(L), 4n, Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), Lb.p2_oe_le(L),
     Ps.p2_ok_rw(L, v, slq, hv, 4n, p2_d_t0(L, l))),
   Ar.ar_le_trans(Dec.e_rt(L), X, Dec.s_rt(L), Lb.p2_e_le(L),
     Ps.p2_s_rw(L, v, slq, hv, X, p2_d_t1(L, l))))
