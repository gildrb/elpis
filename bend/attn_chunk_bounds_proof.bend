# Proofs of the ext patch 3003 buffer bounds laws (attn_chunk_bounds_laws.bend) about the Nat model
# attn_chunk_bounds.bend against attn_chunk_bounds_spec.bend. Structural evidence only: no unsafe
# definitions, axioms, holes, foreign proof code or answer tables. Nat arithmetic lemmas come from
# the proven m16 partition library, the ceil-division lemmas from attn_split_proof.bend and the
# row-major block bound from attn_bounds_proof.bend.
import Base
import ./attn_chunk.bend as Chunk
import ./attn_chunk_bounds.bend as Impl
import ./attn_chunk_bounds_spec.bend as Spec
import ./attn_chunk_bounds_laws.bend as Laws
import ./attn_bounds.bend as Bounds
import ./gemm_m16_partition_proof.bend as Ar
import ./attn_split_proof.bend as AS
import ./attn_bounds_proof.bend as ABP

# (a + r) + s == (a + s) + r
def ab_swap_tail(+a: Nat, +r: Nat, +s: Nat)
  -> {Nat.add(Nat.add(a, r), s) == Nat.add(Nat.add(a, s), r) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, r), s), Nat.add(a, Nat.add(r, s)), Nat.add(Nat.add(a, s), r),
    Ar.ar_add_assoc(a, r, s),
    Equal.trans(Nat, Nat.add(a, Nat.add(r, s)), Nat.add(a, Nat.add(s, r)), Nat.add(Nat.add(a, s), r),
      Equal.cong(Nat, Nat, t => Nat.add(a, t), Nat.add(r, s), Nat.add(s, r), Ar.ar_add_comm(r, s)),
      Equal.sym(Nat, Nat.add(Nat.add(a, s), r), Nat.add(a, Nat.add(s, r)), Ar.ar_add_assoc(a, s, r))))

# The combine's cidx(b, kvh, r, s) == ((b * n_kv + kvh) * mc + s) * 48 + r
def ab_cidx(+b: Nat, +kvh: Nat, +r: Nat, +s: Nat, +n_kv: Nat, +mc: Nat)
  -> {Impl.cidx(b, kvh, r, s, n_kv, mc) ==
      Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), mc), s), 48n), r) : Nat}:
  +M = Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), mc)
  %Equal.sym(Nat, Nat.mul(Nat.add(M, s), 48n), Nat.add(Nat.mul(M, 48n), Nat.mul(s, 48n)), Ar.ar_mul_add_l(M, s, 48n)) :
    {Impl.cidx(b, kvh, r, s, n_kv, mc) == Nat.add(_, r) : Nat}
  ab_swap_tail(Nat.mul(M, 48n), r, Nat.mul(s, 48n))

# (((a * b) * c) * d) * e == a * (b * (c * (d * e)))
def ab_mul5(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat)
  -> {Nat.mul(Nat.mul(Nat.mul(Nat.mul(a, b), c), d), e) == Nat.mul(a, Nat.mul(b, Nat.mul(c, Nat.mul(d, e)))) : Nat}:
  +ab = Nat.mul(a, b)
  +de = Nat.mul(d, e)
  Equal.trans(Nat, Nat.mul(Nat.mul(Nat.mul(ab, c), d), e), Nat.mul(Nat.mul(ab, c), de),
    Nat.mul(a, Nat.mul(b, Nat.mul(c, de))),
    Ar.ar_mul_assoc(Nat.mul(ab, c), d, e),
    Equal.trans(Nat, Nat.mul(Nat.mul(ab, c), de), Nat.mul(ab, Nat.mul(c, de)), Nat.mul(a, Nat.mul(b, Nat.mul(c, de))),
      Ar.ar_mul_assoc(ab, c, de), Ar.ar_mul_assoc(a, b, Nat.mul(c, de))))

# ((a * b) * c) * d == a * (b * (c * d))
def ab_mul4(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {Nat.mul(Nat.mul(Nat.mul(a, b), c), d) == Nat.mul(a, Nat.mul(b, Nat.mul(c, d))) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(Nat.mul(a, b), c), d), Nat.mul(Nat.mul(a, b), Nat.mul(c, d)),
    Nat.mul(a, Nat.mul(b, Nat.mul(c, d))),
    Ar.ar_mul_assoc(Nat.mul(a, b), c, d), Ar.ar_mul_assoc(a, b, Nat.mul(c, d)))

def Laws.store_in_bounds(bsz, n_kv, mc, L, chunk, b, kvh, c, row, col, k, bb, kb, cb, notrap, rb, colb, eb):
  +BH = Nat.add(Nat.mul(b, n_kv), kvh)
  +BHC = Nat.add(Nat.mul(BH, mc), c)
  +R = Nat.add(Nat.mul(BHC, 48n), row)
  +B48 = Nat.mul(Nat.mul(Nat.mul(bsz, n_kv), mc), 48n)
  +hbh = ABP.ab_blk(b, bsz, kvh, n_kv, bb, kb)
  +hc = Ar.ar_lt_le_trans(c, Chunk.live(L, chunk), mc, cb, notrap)
  +hbhc = ABP.ab_blk(BH, Nat.mul(bsz, n_kv), c, mc, hbh, hc)
  +hr = ABP.ab_blk(BHC, Nat.mul(Nat.mul(bsz, n_kv), mc), row, 48n, hbhc, rb)
  ({==},
    Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 256n), col), Impl.cidx(b, kvh, row, c, n_kv, mc), R,
      ab_cidx(b, kvh, row, c, n_kv, mc)),
    {==},
    Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 2n), k), Impl.cidx(b, kvh, row, c, n_kv, mc), R,
      ab_cidx(b, kvh, row, c, n_kv, mc)),
    ab_mul5(bsz, n_kv, mc, 48n, 256n),
    ab_mul5(bsz, n_kv, mc, 48n, 2n),
    ABP.ab_blk(R, B48, col, 256n, hr, colb),
    ABP.ab_blk(R, B48, k, 2n, hr, eb))

def Laws.out_in_bounds(bsz, q_len, n_q, n_kv, b, q_pos, kvh, hl, d, bb, qb, kb, hb, db):
  +kb2 = kb
  +G = Nat.div(n_q, n_kv)
  +KG = Nat.mul(kvh, G)
  +H = Nat.add(KG, hl)
  +RQ = Nat.add(Nat.mul(b, q_len), q_pos)
  +X = Nat.mul(RQ, n_q)
  +C = Nat.mul(Nat.mul(Nat.mul(bsz, q_len), n_q), 256n)
  +eq = Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 256n), d), Nat.add(Nat.add(X, KG), hl), Nat.add(X, H),
    Ar.ar_add_assoc(X, KG, hl))
  +pos = Ar.ard_pos(kvh, n_kv, kb2)
  # kvh * group + hl < n_kv * group <= n_q
  +h1 = ABP.ab_blk(kvh, n_kv, hl, G, kb2, hb)
  +h2 = Ar.ard_rt(Nat.is_le(Nat.mul(G, n_kv), n_q), Nat.is_le(Nat.mul(n_kv, G), n_q),
    Equal.cong(Nat, Bool, t => Nat.is_le(t, n_q), Nat.mul(G, n_kv), Nat.mul(n_kv, G), Ar.ar_mul_comm(G, n_kv)),
    Ar.ard_le_mul_div(n_q, n_kv, pos))
  +hh = Ar.ar_lt_le_trans(H, Nat.mul(n_kv, G), n_q, h1, h2)
  +hrq = ABP.ab_blk(b, bsz, q_pos, q_len, bb, qb)
  +hx = ABP.ab_blk(RQ, Nat.mul(bsz, q_len), H, n_q, hrq, hh)
  +hcell = ABP.ab_blk(Nat.add(X, H), Nat.mul(Nat.mul(bsz, q_len), n_q), d, 256n, hx, db)
  +old = Nat.add(Nat.mul(Nat.add(Nat.add(X, KG), hl), 256n), d)
  +new = Nat.add(Nat.mul(Nat.add(X, H), 256n), d)
  (eq,
    Ar.ard_rt(Nat.is_lt(new, C), Nat.is_lt(old, C),
      Equal.cong(Nat, Bool, t => Nat.is_lt(t, C), new, old, Equal.sym(Nat, old, new, eq)), hcell),
    ab_mul4(bsz, q_len, n_q, 256n))

def Laws.no_trap(L, chunk, mc, num_pages, cpos, spans, checked):
  +C = Chunk.live(L, chunk)
  +hL = Ar.ar_le_trans(L, Nat.mul(num_pages, 256n), Nat.mul(mc, chunk), spans, checked)
  +e = Equal.trans(Bool, Bool.not(Nat.is_le(C, mc)), Nat.is_lt(mc, C), False{},
    Equal.sym(Bool, Nat.is_lt(mc, C), Bool.not(Nat.is_le(C, mc)), Ar.ar_lt_not_le(mc, C)),
    Equal.trans(Bool, Nat.is_lt(mc, C), Bool.not(Nat.is_le(L, Nat.mul(mc, chunk))), False{},
      AS.as_live(mc, L, chunk, cpos),
      Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(L, Nat.mul(mc, chunk)), True{}, hL)))
  AS.as_not_false(Nat.is_le(C, mc), e)

def Laws.host_no_trap(max_pages, num_pages, chunk, cpos, width):
  +MP = Nat.mul(max_pages, 256n)
  Ar.ar_le_trans(Nat.mul(num_pages, 256n), MP, Nat.mul(Impl.host_max_chunks(max_pages, chunk), chunk),
    Ar.ar_le_mul_mono(num_pages, max_pages, 256n, width), AS.as_up(MP, chunk, cpos))

# a <= max(a, b)
def ab_max_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  Ar.ard_rt(Nat.is_ge(Nat.max(a, b), a), Nat.is_le(a, Nat.max(a, b)), Ar.ar_ge_flip(Nat.max(a, b), a),
    Nat.max_ge_l(a, b))

# b <= max(a, b)
def ab_max_r(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  Ar.ard_rt(Nat.is_ge(Nat.max(a, b), b), Nat.is_le(b, Nat.max(a, b)), Ar.ar_ge_flip(Nat.max(a, b), b),
    Nat.max_ge_r(a, b))

def Laws.host_fits(bsz, kvh, splits, nsub, rows, hd_pad, max_pages, chunk, sms):
  +M = Impl.host_max_chunks(max_pages, chunk)
  +BKM48 = Nat.mul(Nat.mul(Nat.mul(bsz, kvh), M), 48n)
  +DO = Impl.dense_o(bsz, kvh, splits, nsub, rows, hd_pad)
  +DM = Impl.dense_ml(bsz, kvh, splits, nsub, rows)
  +z = Nat.div(sms, Nat.mul(bsz, kvh))
  (ab_max_r(DO, Nat.mul(BKM48, 256n)),
    ab_max_r(DM, Nat.mul(BKM48, 2n)),
    ab_max_l(DO, Nat.mul(BKM48, 256n)),
    ab_max_l(DM, Nat.mul(BKM48, 2n)),
    Ar.ard_tr(Nat.is_lt(0n, Nat.max(1n, z)), Nat.is_le(1n, Nat.max(1n, z)), Ar.ar_lt_succ_le(0n, Nat.max(1n, z)),
      ABP.ab_max1(z)))

# (q * 64) mod 256 + 64 <= 256: q * 64 = (q / 4) * 256 + (q mod 4) * 64 with (q mod 4) * 64 <= 192
def ab_slot(+q: Nat) -> {Nat.is_le(Nat.add(Nat.mod(Nat.mul(q, 64n), 256n), 64n), 256n) == True{} : Bool}:
  +Q = Nat.div(q, 4n)
  +r = Nat.mod(q, 4n)
  +r64 = Nat.mul(r, 64n)
  +rlt = Ar.ard_dm_lt(q, 4n, {==})
  +small = Ar.ard_rt(Nat.is_lt(r, 4n), Nat.is_lt(r64, Nat.mul(4n, 64n)),
    Equal.sym(Bool, Nat.is_lt(r64, Nat.mul(4n, 64n)), Nat.is_lt(r, 4n), Ar.ar_mul_lt_cancel(r, 4n, 64n, {==})), rlt)
  +md = Ar.ard_snd({Nat.div(Nat.add(Nat.mul(Q, 256n), r64), 256n) == Q : Nat},
    {Nat.mod(Nat.add(Nat.mul(Q, 256n), r64), 256n) == r64 : Nat}, Ar.ar_div_unique(Q, r64, 256n, small))
  +Q4 = Nat.add(Nat.mul(Q, 4n), r)
  +eq = Equal.trans(Nat, Nat.mul(q, 64n), Nat.mul(Q4, 64n), Nat.add(Nat.mul(Q, 256n), r64),
    Equal.cong(Nat, Nat, t => Nat.mul(t, 64n), q, Q4, Equal.sym(Nat, Q4, q, Ar.ard_dm_eq(q, 4n, {==}))),
    Equal.trans(Nat, Nat.mul(Q4, 64n), Nat.add(Nat.mul(Nat.mul(Q, 4n), 64n), r64), Nat.add(Nat.mul(Q, 256n), r64),
      Ar.ar_mul_add_l(Nat.mul(Q, 4n), r, 64n),
      Equal.cong(Nat, Nat, t => Nat.add(t, r64), Nat.mul(Nat.mul(Q, 4n), 64n), Nat.mul(Q, 256n),
        Ar.ar_mul_assoc(Q, 4n, 64n))))
  +r1 = Ar.ard_rt(Nat.is_lt(r, 4n), Nat.is_le(1n+r, 4n), Ar.ar_lt_succ_le(r, 4n), rlt)
  %Equal.sym(Nat, Nat.mul(q, 64n), Nat.add(Nat.mul(Q, 256n), r64), eq) :
    {Nat.is_le(Nat.add(Nat.mod(_, 256n), 64n), 256n) == True{} : Bool}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Q, 256n), r64), 256n), r64, md) :
    {Nat.is_le(Nat.add(_, 64n), 256n) == True{} : Bool}
  %Ar.ar_add_comm(64n, r64) : {Nat.is_le(_, 256n) == True{} : Bool}
  Ar.ar_le_mul_mono(1n+r, 4n, 64n, r1)

def Laws.tile_in_page(m, c, it):
  +q = Nat.add(Nat.mul(c, m), it)
  +e = Equal.trans(Nat, Nat.mul(q, 64n), Nat.add(Nat.mul(Nat.mul(c, m), 64n), Nat.mul(it, 64n)),
    Nat.add(Nat.mul(c, Nat.mul(m, 64n)), Nat.mul(it, 64n)),
    Ar.ar_mul_add_l(Nat.mul(c, m), it, 64n),
    Equal.cong(Nat, Nat, t => Nat.add(t, Nat.mul(it, 64n)), Nat.mul(Nat.mul(c, m), 64n), Nat.mul(c, Nat.mul(m, 64n)),
      Ar.ar_mul_assoc(c, m, 64n)))
  %e : {Nat.is_le(Impl.tile_slot_end(_), 256n) == True{} : Bool}
  ab_slot(q)

def Laws.tile_in_table(L, chunk, num_pages, c, it, cb, tb, spans):
  +ns = Chunk.n_start(c, chunk)
  +ne = Chunk.n_end(c, L, chunk)
  +D = Nat.sub(ne, ns)
  +i64 = Nat.mul(it, 64n)
  +n0 = Nat.add(ns, i64)
  +P = Nat.mul(num_pages, 256n)
  # it < ceil(D / 64) gives it * 64 < D
  +h1 = Ar.ard_rt(Nat.is_lt(it, Chunk.ntiles(c, L, chunk)), Bool.not(Nat.is_le(D, i64)),
    AS.as_live(it, D, 64n, {==}), tb)
  +h2 = Ar.ard_tr(Nat.is_lt(i64, D), Bool.not(Nat.is_le(D, i64)), Ar.ar_lt_not_le(i64, D), h1)
  # n0 < n_end = min(n_start + chunk, L) <= L
  +h3 = Ar.ard_rt(Nat.is_lt(i64, D), Nat.is_lt(n0, ne), Ar.ar_lt_sub_iff(ne, ns, i64), h2)
  +h4 = Ar.ar_and_r(Nat.is_lt(n0, Nat.add(ns, chunk)), Nat.is_lt(n0, L),
    Ar.ard_rt(Nat.is_lt(n0, ne), Bool.and(Nat.is_lt(n0, Nat.add(ns, chunk)), Nat.is_lt(n0, L)),
      Ar.ar_min_lt(n0, Nat.add(ns, chunk), L), h3))
  +h5 = Ar.ar_lt_le_trans(n0, L, P, h4, spans)
  Ar.ard_tr(Nat.is_lt(Nat.div(n0, 256n), num_pages), Nat.is_lt(n0, P), Ar.ar_div_lt(num_pages, n0, 256n, {==}), h5)

def Laws.unaligned_chunk_straddles():
  ({==}, {==}, {==})
