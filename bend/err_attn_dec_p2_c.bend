# dec_p2 (bend/err_attn_dec_p2.bend) for 129 <= L <= 4096: the block table is one 4096-key width, so
# stock's bound is 4097, num_splits 33, split_len 128: split 0 holds 128 keys (4 tiles, 8 groups) and the
# live splits are ceil(L / 128) > e_n0(L).
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./attn_stride_proof.bend as SP
import ./err_attn_dec_p2_lib.bend as Lb
import ./err_attn_dec_p2_s.bend as Ps

# n * 1280 <= 1279 + L and 129 <= L give n * 128 < L
def p2_c_n0(+n: Nat, +L: Nat, h: {Nat.is_le(Nat.mul(n, 1280n), Nat.add(1279n, L)) == True{} : Bool},
    lo: {Nat.is_le(129n, L) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(n, 128n), L) == True{} : Bool}:
  match n:
    case 0n:
      Ar.ar_lt_le_trans(0n, 129n, L, {==}, lo)
    case 1n+p:
      match p:
        case 0n:
          Ar.ar_lt_le_trans(128n, 129n, L, {==}, lo)
        case 1n+pp:
          hh : {Nat.is_le(Nat.add(1281n, Nat.mul(pp, 1280n)), L) == True{} : Bool} = h
          Ar.ar_le_lt_trans(Nat.add(256n, Nat.mul(pp, 128n)), Nat.add(1280n, Nat.mul(pp, 1280n)), L,
            NO.le_add_mono(256n, 1280n, Nat.mul(pp, 128n), Nat.mul(pp, 1280n), {==}, NO.le_mul_mono_r(128n, 1280n, pp, {==})),
            Lb.p2_le_lt(Nat.add(1280n, Nat.mul(pp, 1280n)), L, hh))

# n <= a: 38 + 2 n <= 28 + (a + (11 + a))
def p2_c_fin(+n: Nat, +a: Nat, h: {Nat.is_le(n, a) == True{} : Bool})
  -> {Nat.is_le(Nat.add(38n, Nat.add(n, n)), Nat.add(28n, Nat.add(a, Nat.add(11n, a)))) == True{} : Bool}:
  +hh = h
  %Equal.sym(Nat, Nat.add(a, Nat.add(11n, a)), Nat.add(11n, Nat.add(a, a)), NO.add_swap(a, 11n, a)) : {Nat.is_le(Nat.add(38n, Nat.add(n, n)), Nat.add(28n, _)) == True{} : Bool}
  Ar.ar_le_trans(Nat.add(n, n), Nat.add(a, a), 1n+Nat.add(a, a), NO.le_add_mono(n, a, n, a, hh, hh), Ar.ar_h_le_succ(Nat.add(a, a)))

# s_sl(L) == 128 for 129 <= L <= 4096
def p2_c_sl(+L: Nat, lo: {Nat.is_le(129n, L) == True{} : Bool}, hi: {Nat.is_le(L, 4096n) == True{} : Bool})
  -> {Dec.s_sl(L) == 128n : Nat}:
  +c1 = St.cdiv(L, 256n)
  +g = St.cdiv(c1, 16n)
  +c1hi = Lb.p2_cd_le(L, 256n, 16n, {==}, hi)
  +c1lo = SP.sp_lt_cdiv(0n, L, 256n, {==}, Ar.ar_lt_le_trans(0n, 129n, L, {==}, lo))
  +geq = Ar.ar_le_antisym(g, 1n, Lb.p2_cd_le(c1, 16n, 1n, {==}, c1hi),
    Lb.p2_lt_le(0n, g, SP.sp_lt_cdiv(0n, c1, 16n, {==}, c1lo)))
  bnd : {Dec.s_bound(L) == 4097n : Nat} = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.mul(z, 16n), 256n), 1n), g, 1n, geq)
  Equal.cong(Nat, Nat, z => Dec.s_slB(z), Dec.s_bound(L), 4097n, bnd)

def p2_c(+L: Nat, lo: {Nat.is_le(129n, L) == True{} : Bool}, hi: {Nat.is_le(L, 4096n) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  +l = lo
  +slq = p2_c_sl(L, l, hi)
  +hv = Ar.ar_le_trans(128n, 129n, L, {==}, l)
  +n = Dec.e_n0(L)
  +X = Nat.add(38n, Nat.add(n, n))
  +a = Nat.sub(St.cdiv(L, 128n), 1n)
  +hna = Lb.p2_le_pred(n, St.cdiv(L, 128n), SP.sp_lt_cdiv(n, L, 128n, {==}, p2_c_n0(n, L, Lb.p2_n0_bound(L), l)))
  (Ar.ar_le_trans(Dec.e_OE(L), 4n, Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), Lb.p2_oe_le(L),
     Ps.p2_ok_rw(L, 128n, slq, hv, 4n, Ps.p2_ok_sh(L, St.cdiv(128n, 16n), 4n, l, {==}))),
   Ar.ar_le_trans(Dec.e_rt(L), X, Dec.s_rt(L), Lb.p2_e_le(L),
     Ps.p2_s_rw(L, 128n, slq, hv, X, Ps.p2_s_sh(L, St.cdiv(128n, 16n), St.cdiv(128n, 32n), St.cdiv(L, 128n), X, l,
       p2_c_fin(n, a, hna)))))
