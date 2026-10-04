# Per-key bounds of the 3030 decode-attention model (bend/err_attn_dec.bend): for every live key of a row
# at position L - 1, its own-group MMA steps, folds, combine-tree adds and tile-tree adds stay within
# e_OE, e_n0, e_D, e_TE. Structural induction and the proven Nat libraries only: no @unsafe definitions,
# axioms, holes or foreign code; every def precedes its uses.
import Base
import ./attn_stride.bend as St
import ./attn_stride_proof.bend as SP
import ./err_attn_dec.bend as Dec
import ./err_attn_dec_tree.bend as Tr
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP

# ==== Nat helpers ====

# a - b <= a
def k_sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          NO.le_refl(1n+ap)
        case 1n+bp:
          NO.le_trans(Nat.sub(ap, bp), ap, 1n+ap, k_sub_le(ap, bp), NO.le_succ(ap))

# a <= c gives a - k <= c - k
def k_sub_mono(+a: Nat, +c: Nat, +k: Nat, h: {Nat.is_le(a, c) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(a, k), Nat.sub(c, k)) == True{} : Bool}:
  match a:
    case 0n:
      NO.le_zero(Nat.sub(c, k))
    case 1n+ap:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.sub(1n+ap, k), Nat.sub(0n, k)) == True{} : Bool}, Ar.ar_false_true(h))
        case 1n+cp:
          match k:
            case 0n:
              h
            case 1n+kp:
              k_sub_mono(ap, cp, kp, h)

# min(a, b) <= a and min(a, b) <= b
def k_min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          k_min_le_l(ap, bp)

def k_min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a:
    case 0n:
      NO.le_zero(b)
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          k_min_le_r(ap, bp)

# a <= b and a <= c give a <= min(b, c)
def k_le_min(+a: Nat, +b: Nat, +c: Nat, hb: {Nat.is_le(a, b) == True{} : Bool}, hc: {Nat.is_le(a, c) == True{} : Bool})
  -> {Nat.is_le(a, Nat.min(b, c)) == True{} : Bool}:
  match a:
    case 0n:
      NO.le_zero(Nat.min(b, c))
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, Nat.min(0n, c)) == True{} : Bool}, Ar.ar_false_true(hb))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, Nat.min(1n+bp, 0n)) == True{} : Bool}, Ar.ar_false_true(hc))
            case 1n+cp:
              k_le_min(ap, bp, cp, hb, hc)

# n < 1 gives n == 0
def k_lt1(+n: Nat, h: {Nat.is_lt(n, 1n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Tr.tr_lt0({1n+p == 0n : Nat}, p, h)

# a + b == 0 gives a == 0 and b == 0
def k_add_eq0_l(+a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat},
        Ar.ar_zero_succ(Nat.add(p, b), Equal.sym(Nat, 1n+Nat.add(p, b), 0n, h)))

def k_add_eq0_r(+a: Nat, -b: Nat, h: {Nat.add(a, b) == 0n : Nat}) -> {b == 0n : Nat}:
  match a:
    case 0n:
      h
    case 1n+p:
      Empty.absurd({b == 0n : Nat},
        Ar.ar_zero_succ(Nat.add(p, b), Equal.sym(Nat, 1n+Nat.add(p, b), 0n, h)))

# t * (1 + bp) == 0 gives t == 0
def k_mul_eq0(+t: Nat, +bp: Nat, h: {Nat.mul(t, 1n+bp) == 0n : Nat}) -> {t == 0n : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat},
        Ar.ar_zero_succ(Nat.add(bp, Nat.mul(p, 1n+bp)), Equal.sym(Nat, 1n+Nat.add(bp, Nat.mul(p, 1n+bp)), 0n, h)))

# ==== ceil division (St.cdiv) ====

def k_cdiv(+a: Nat, +bp: Nat) -> {St.cdiv(a, 1n+bp) == Nat.div(Nat.add(a, bp), 1n+bp) : Nat}:
  Equal.cong(Nat, Nat, t => Nat.div(t, 1n+bp), Nat.sub(Nat.add(a, 1n+bp), 1n), Nat.add(a, bp), SP.sp_pred(a, bp))

def k_cdiv_mono(+a: Nat, +c: Nat, +bp: Nat, h: {Nat.is_le(a, c) == True{} : Bool})
  -> {Nat.is_le(St.cdiv(a, 1n+bp), St.cdiv(c, 1n+bp)) == True{} : Bool}:
  %Equal.sym(Nat, St.cdiv(a, 1n+bp), Nat.div(Nat.add(a, bp), 1n+bp), k_cdiv(a, bp)) :
    {Nat.is_le(_, St.cdiv(c, 1n+bp)) == True{} : Bool}
  %Equal.sym(Nat, St.cdiv(c, 1n+bp), Nat.div(Nat.add(c, bp), 1n+bp), k_cdiv(c, bp)) :
    {Nat.is_le(Nat.div(Nat.add(a, bp), 1n+bp), _) == True{} : Bool}
  Ar.ar_div_mono(Nat.add(a, bp), Nat.add(c, bp), 1n+bp, {==},
    NO.le_add_mono(a, c, bp, bp, h, NO.le_refl(bp)))

def k_cdiv_pos(+a: Nat, +bp: Nat, h: {Nat.is_le(1n, a) == True{} : Bool})
  -> {Nat.is_le(1n, St.cdiv(a, 1n+bp)) == True{} : Bool}:
  Ar.ard_rt(Nat.is_lt(0n, St.cdiv(a, 1n+bp)), Nat.is_le(1n, St.cdiv(a, 1n+bp)), Ar.ar_lt_succ_le(0n, St.cdiv(a, 1n+bp)),
    SP.sp_lt_cdiv(0n, a, 1n+bp, {==},
      Ar.ard_tr(Nat.is_lt(0n, a), Nat.is_le(1n, a), Ar.ar_lt_succ_le(0n, a), h)))

# ==== the key predicate ====

def k_ok_x(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_lt(x, 20n) == True{} : Bool}:
  NO.and_l(Nat.is_lt(x, 20n), Bool.and(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L))), ok)

def k_ok_rest(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L))) == True{} : Bool}:
  NO.and_r(Nat.is_lt(x, 20n), Bool.and(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L))), ok)

def k_ok_g(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_lt(g, 4n) == True{} : Bool}:
  NO.and_l(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L)), k_ok_rest(L, x, q, g, r, ok))

def k_ok_rest2(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L)) == True{} : Bool}:
  NO.and_r(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L)), k_ok_rest(L, x, q, g, r, ok))

def k_ok_r(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_lt(r, 16n) == True{} : Bool}:
  NO.and_l(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L), k_ok_rest2(L, x, q, g, r, ok))

def k_ok_pos(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_lt(Dec.key_pos(x, q, g, r), L) == True{} : Bool}:
  NO.and_r(Nat.is_lt(r, 16n), Nat.is_lt(Dec.key_pos(x, q, g, r), L), k_ok_rest2(L, x, q, g, r, ok))

# x * 64 <= key_pos(x, q, g, r)
def k_x64_le(+x: Nat, +q: Nat, +g: Nat, +r: Nat) -> {Nat.is_le(Nat.mul(x, 64n), Dec.key_pos(x, q, g, r)) == True{} : Bool}:
  +mq = Nat.mul(q, 20n)
  +u = Nat.add(Nat.mul(g, 16n), r)
  NO.le_trans(Nat.mul(x, 64n), Nat.mul(Dec.tile_of(x, q), 64n), Dec.key_pos(x, q, g, r),
    Equal.trans(Bool, Nat.is_le(Nat.mul(x, 64n), Nat.mul(Nat.add(x, mq), 64n)),
      Nat.is_le(Nat.mul(x, 64n), Nat.add(Nat.mul(x, 64n), Nat.mul(mq, 64n))), True{},
      Equal.cong(Nat, Bool, t => Nat.is_le(Nat.mul(x, 64n), t), Nat.mul(Nat.add(x, mq), 64n),
        Nat.add(Nat.mul(x, 64n), Nat.mul(mq, 64n)), Ar.ar_mul_add_l(x, mq, 64n)),
      NO.le_add_r(Nat.mul(x, 64n), Nat.mul(mq, 64n))),
    NO.le_add_r(Nat.mul(Dec.tile_of(x, q), 64n), u))

# The key's in-tile position 16 g + r is below 64 and below the tile's live keys
def k_u64(+g: Nat, +r: Nat, hg: {Nat.is_lt(g, 4n) == True{} : Bool}, hr: {Nat.is_lt(r, 16n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(g, 16n), r), 64n) == True{} : Bool}:
  +g3 = Ar.ard_rt(Nat.is_lt(g, 4n), Nat.is_le(1n+g, 4n), Ar.ar_lt_succ_le(g, 4n), hg)
  +r15 = Ar.ard_rt(Nat.is_lt(r, 16n), Nat.is_le(1n+r, 16n), Ar.ar_lt_succ_le(r, 16n), hr)
  Ar.ard_tr(Nat.is_lt(Nat.add(Nat.mul(g, 16n), r), 64n), Nat.is_le(1n+Nat.add(Nat.mul(g, 16n), r), 64n),
    Ar.ar_lt_succ_le(Nat.add(Nat.mul(g, 16n), r), 64n),
    %Ar.ar_add_succ_r(Nat.mul(g, 16n), r) : {Nat.is_le(_, 64n) == True{} : Bool}
    NO.le_add_mono(Nat.mul(g, 16n), 48n, 1n+r, 16n, NO.le_mul_mono_l(g, 3n, 16n, g3), r15))

def k_u_nt(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(g, 16n), r), Dec.e_nt(L, x, q)) == True{} : Bool}:
  +u = Nat.add(Nat.mul(g, 16n), r)
  +t64 = Nat.mul(Dec.tile_of(x, q), 64n)
  +hl = Ar.ard_tr(Nat.is_lt(u, Nat.sub(L, t64)), Nat.is_lt(Nat.add(t64, u), L), Ar.ar_lt_sub_iff(L, t64, u),
    k_ok_pos(L, x, q, g, r, ok))
  Ar.ard_tr(Nat.is_lt(u, Nat.min(64n, Nat.sub(L, t64))), Bool.and(Nat.is_lt(u, 64n), Nat.is_lt(u, Nat.sub(L, t64))),
    Ar.ar_min_lt(u, 64n, Nat.sub(L, t64)),
    NO.and_intro(Nat.is_lt(u, 64n), Nat.is_lt(u, Nat.sub(L, t64)), k_u64(g, r, k_ok_g(L, x, q, g, r, ok), k_ok_r(L, x, q, g, r, ok)), hl))

# The tile's live keys are at most L
def k_nt_le(+L: Nat, +x: Nat, +q: Nat) -> {Nat.is_le(Dec.e_nt(L, x, q), L) == True{} : Bool}:
  NO.le_trans(Dec.e_nt(L, x, q), Nat.sub(L, Nat.mul(Dec.tile_of(x, q), 64n)), L,
    k_min_le_r(64n, Nat.sub(L, Nat.mul(Dec.tile_of(x, q), 64n))), k_sub_le(L, Nat.mul(Dec.tile_of(x, q), 64n)))

# ==== P1: the per-key bounds ====

# combine tree: the key's slot x < min(live tiles, 20)
def k_depth(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_le(Dec.e_depth(L, x), Dec.e_D(L)) == True{} : Bool}:
  +x64 = NO.le_trans(Nat.mul(x, 64n), Dec.key_pos(x, q, g, r), L, k_x64_le(x, q, g, r),
    Ar.ar_lt_le(Dec.key_pos(x, q, g, r), L, k_ok_pos(L, x, q, g, r, ok)))
  +xlt = Ar.ar_le_lt_trans(Nat.mul(x, 64n), Dec.key_pos(x, q, g, r), L, k_x64_le(x, q, g, r), k_ok_pos(L, x, q, g, r, ok))
  +xT = SP.sp_lt_cdiv(x, L, 64n, {==}, xlt)
  +xs = Ar.ard_tr(Nat.is_lt(x, Nat.min(Dec.e_T(L), 20n)), Bool.and(Nat.is_lt(x, Dec.e_T(L)), Nat.is_lt(x, 20n)),
    Ar.ar_min_lt(x, Dec.e_T(L), 20n), NO.and_intro(Nat.is_lt(x, Dec.e_T(L)), Nat.is_lt(x, 20n), xT, k_ok_x(L, x, q, g, r, ok)))
  Tr.tr_tdepth_le(9n, x, Dec.e_nsl(L), xs)

# tile tree: the key's in-tile position is below the tile's live keys, and those are at most L
def k_tsum(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_le(Dec.e_tsum(L, x, q, g, r), Dec.e_TE(L)) == True{} : Bool}:
  NO.le_trans(Dec.e_tsum(L, x, q, g, r), Dec.tbound(6n, Dec.e_nt(L, x, q)), Dec.e_TE(L),
    Tr.tr_tdepth_le(6n, Nat.add(Nat.mul(g, 16n), r), Dec.e_nt(L, x, q), k_u_nt(L, x, q, g, r, ok)),
    Tr.tr_tbound_mono(6n, Dec.e_nt(L, x, q), L, k_nt_le(L, x, q)))

# folds: 1 + ((a - 1) - q) <= N when 1 <= N and a <= N
def k_fold_core(+a: Nat, +q: Nat, +N: Nat, h1: {Nat.is_le(1n, N) == True{} : Bool}, h2: {Nat.is_le(a, N) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.sub(Nat.sub(a, 1n), q), N) == True{} : Bool}:
  match a:
    case 0n:
      h1
    case 1n+ap:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, Ar.ar_sub_zero_r(ap)) : {Nat.is_le(1n+Nat.sub(_, q), N) == True{} : Bool}
      NO.le_trans(1n+Nat.sub(ap, q), 1n+ap, N, k_sub_le(ap, q), h2)

def k_fold(+L: Nat, +x: Nat, +q: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_fold(L, x, q), Dec.e_n0(L)) == True{} : Bool}:
  +T = Dec.e_T(L)
  +T1 = k_cdiv_pos(L, 63n, pos)
  +n0e = Equal.cong(Nat, Nat, t => St.cdiv(t, 20n), Nat.sub(T, 0n), T, Ar.ar_sub_zero_r(T))
  %Equal.sym(Nat, St.cdiv(Nat.sub(T, 0n), 20n), St.cdiv(T, 20n), n0e) : {Nat.is_le(Dec.e_fold(L, x, q), _) == True{} : Bool}
  k_fold_core(St.cta_tiles(T, x, 20n), q, St.cdiv(T, 20n), k_cdiv_pos(T, 19n, T1),
    k_cdiv_mono(Nat.sub(T, x), T, 19n, k_sub_le(T, x)))

# own groups: bit(b) + ((lg - g) - 1) <= M when 1 <= M and lg <= M
def k_own_core(+b: Bool, +lg: Nat, +g: Nat, +M: Nat, h1: {Nat.is_le(1n, M) == True{} : Bool}, h2: {Nat.is_le(lg, M) == True{} : Bool})
  -> {Nat.is_le(Nat.add(St.bit(b), Nat.sub(Nat.sub(lg, g), 1n)), M) == True{} : Bool}:
  match b:
    case False{}:
      NO.le_trans(Nat.sub(Nat.sub(lg, g), 1n), lg, M,
        NO.le_trans(Nat.sub(Nat.sub(lg, g), 1n), Nat.sub(lg, g), lg, k_sub_le(Nat.sub(lg, g), 1n), k_sub_le(lg, g)), h2)
    case True{}:
      match lg:
        case 0n:
          h1
        case 1n+lp:
          +s1 = NO.le_trans(Nat.sub(Nat.sub(1n+lp, g), 1n), Nat.sub(1n+lp, 1n), lp,
            k_sub_mono(Nat.sub(1n+lp, g), 1n+lp, 1n, k_sub_le(1n+lp, g)),
            NO.le_of_eq(Nat.sub(1n+lp, 1n), lp, Ar.ar_sub_zero_r(lp)))
          NO.le_trans(1n+Nat.sub(Nat.sub(1n+lp, g), 1n), 1n+lp, M, s1, h2)

# lg <= min(4, ceil(L / 16)) and 1 <= min(4, ceil(L / 16))
def k_lg_le(+L: Nat, +x: Nat, +q: Nat) -> {Nat.is_le(Dec.e_lg(L, x, q), Nat.min(4n, St.cdiv(L, 16n))) == True{} : Bool}:
  k_le_min(Dec.e_lg(L, x, q), 4n, St.cdiv(L, 16n),
    k_cdiv_mono(Dec.e_nt(L, x, q), 64n, 15n, k_min_le_l(64n, Nat.sub(L, Nat.mul(Dec.tile_of(x, q), 64n)))),
    k_cdiv_mono(Dec.e_nt(L, x, q), L, 15n, k_nt_le(L, x, q)))

def k_own_big(+L: Nat, +x: Nat, +q: Nat, +g: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_own(L, x, q, g), Nat.min(4n, St.cdiv(L, 16n))) == True{} : Bool}:
  k_own_core(Dec.e_shared(L, x, q, g), Dec.e_lg(L, x, q), g, Nat.min(4n, St.cdiv(L, 16n)),
    k_le_min(1n, 4n, St.cdiv(L, 16n), {==}, k_cdiv_pos(L, 15n, pos)), k_lg_le(L, x, q))

# L = 1: the only key is key 0
def k_own_one(+x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(1n, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_le(Dec.e_own(1n, x, q, g), Dec.e_OE(1n)) == True{} : Bool}:
  +kp0 = k_lt1(Dec.key_pos(x, q, g, r), k_ok_pos(1n, x, q, g, r, ok))
  +t64 = Nat.mul(Dec.tile_of(x, q), 64n)
  +u = Nat.add(Nat.mul(g, 16n), r)
  +t0 = k_mul_eq0(Dec.tile_of(x, q), 63n, k_add_eq0_l(t64, u, kp0))
  +x0 = k_add_eq0_l(x, Nat.mul(q, 20n), t0)
  +q0 = k_mul_eq0(q, 19n, k_add_eq0_r(x, Nat.mul(q, 20n), t0))
  +g0 = k_mul_eq0(g, 15n, k_add_eq0_l(Nat.mul(g, 16n), r, k_add_eq0_r(t64, u, kp0)))
  %Equal.sym(Nat, x, 0n, x0) : {Nat.is_le(Dec.e_own(1n, _, q, g), Dec.e_OE(1n)) == True{} : Bool}
  %Equal.sym(Nat, q, 0n, q0) : {Nat.is_le(Dec.e_own(1n, 0n, _, g), Dec.e_OE(1n)) == True{} : Bool}
  %Equal.sym(Nat, g, 0n, g0) : {Nat.is_le(Dec.e_own(1n, 0n, 0n, _), Dec.e_OE(1n)) == True{} : Bool}
  {==}

def k_own(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Nat.is_le(Dec.e_own(L, x, q, g), Dec.e_OE(L)) == True{} : Bool}:
  match L:
    case 0n:
      Tr.tr_lt0({Nat.is_le(Dec.e_own(0n, x, q, g), Dec.e_OE(0n)) == True{} : Bool}, Dec.key_pos(x, q, g, r),
        k_ok_pos(0n, x, q, g, r, ok))
    case 1n+lp:
      match lp:
        case 0n:
          k_own_one(x, q, g, r, ok)
        case 1n+lq:
          %Equal.sym(Nat, Nat.sub(Nat.min(4n, St.cdiv(2n+lq, 16n)), 0n), Nat.min(4n, St.cdiv(2n+lq, 16n)),
            Ar.ar_sub_zero_r(Nat.min(4n, St.cdiv(2n+lq, 16n)))) :
            {Nat.is_le(Dec.e_own(2n+lq, x, q, g), _) == True{} : Bool}
          k_own_big(2n+lq, x, q, g, {==})
