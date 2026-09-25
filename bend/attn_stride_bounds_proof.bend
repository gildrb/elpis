# Proofs of the ext patch 3006 buffer bounds laws (attn_stride_bounds_laws.bend) about the Nat model
# attn_stride_bounds.bend (+ attn_stride.bend) against attn_stride_bounds_spec.bend. Structural
# evidence only: no unsafe definitions, axioms, holes, foreign proof code or answer tables. Nat
# arithmetic lemmas come from the proven m16 partition library, the ceil-division lemma from
# attn_split_proof.bend, the row-major block bound from attn_bounds_proof.bend and the generic
# product / max / page-slot lemmas from attn_chunk_bounds_proof.bend.
import Base
import ./attn_stride.bend as Stride
import ./attn_stride_bounds.bend as Impl
import ./attn_stride_bounds_spec.bend as Spec
import ./attn_stride_bounds_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar
import ./attn_split_proof.bend as AS
import ./attn_bounds_proof.bend as ABP
import ./attn_chunk_bounds_proof.bend as CBP

# The combine's cidx(b, kvh, r, s) == ((b * n_kv + kvh) * S + s) * 48 + r
def sb_cidx(+b: Nat, +kvh: Nat, +r: Nat, +s: Nat, +n_kv: Nat, +S: Nat)
  -> {Impl.cidx(b, kvh, r, s, n_kv, S) ==
      Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), s), 48n), r) : Nat}:
  +M = Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S)
  %Equal.sym(Nat, Nat.mul(Nat.add(M, s), 48n), Nat.add(Nat.mul(M, 48n), Nat.mul(s, 48n)), Ar.ar_mul_add_l(M, s, 48n)) :
    {Impl.cidx(b, kvh, r, s, n_kv, S) == Nat.add(_, r) : Nat}
  CBP.ab_swap_tail(Nat.mul(M, 48n), r, Nat.mul(s, 48n))

# Row y = ((b * n_kv + kvh) * S + slot) * 48 + row of a slot < S lies below (bsz * n_kv * S) * 48
def sb_row(+bsz: Nat, +n_kv: Nat, +S: Nat, +b: Nat, +kvh: Nat, +slot: Nat, +row: Nat,
    bb: {Nat.is_lt(b, bsz) == True{} : Bool}, kb: {Nat.is_lt(kvh, n_kv) == True{} : Bool},
    xb: {Nat.is_lt(slot, S) == True{} : Bool}, rb: {Nat.is_lt(row, 48n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), slot), 48n), row),
      Nat.mul(Nat.mul(Nat.mul(bsz, n_kv), S), 48n)) == True{} : Bool}:
  +BH = Nat.add(Nat.mul(b, n_kv), kvh)
  +BHX = Nat.add(Nat.mul(BH, S), slot)
  +hbh = ABP.ab_blk(b, bsz, kvh, n_kv, bb, kb)
  +hbhx = ABP.ab_blk(BH, Nat.mul(bsz, n_kv), slot, S, hbh, xb)
  ABP.ab_blk(BHX, Nat.mul(Nat.mul(bsz, n_kv), S), row, 48n, hbhx, rb)

def Laws.store_in_bounds(bsz, n_kv, S, L, b, kvh, x, s, row, col, k, bb, kb, xb, sb, rb, colb, eb):
  +bb2 = bb
  +kb2 = kb
  +rb2 = rb
  +colb2 = colb
  +eb2 = eb
  +n = Stride.live_tiles(L)
  +B48 = Nat.mul(Nat.mul(Nat.mul(bsz, n_kv), S), 48n)
  # s < min(n_tiles, S) gives s < S
  +hs = Ar.ar_and_r(Nat.is_lt(s, n), Nat.is_lt(s, S),
    Ar.ard_rt(Nat.is_lt(s, Nat.min(n, S)), Bool.and(Nat.is_lt(s, n), Nat.is_lt(s, S)), Ar.ar_min_lt(s, n, S), sb))
  +RX = Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), x), 48n), row)
  +RS = Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), s), 48n), row)
  +hx = sb_row(bsz, n_kv, S, b, kvh, x, row, bb2, kb2, xb, rb2)
  +hsr = sb_row(bsz, n_kv, S, b, kvh, s, row, bb2, kb2, hs, rb2)
  +C = Impl.cidx(b, kvh, row, s, n_kv, S)
  +eo = Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 256n), col), C, RS, sb_cidx(b, kvh, row, s, n_kv, S))
  +em = Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(t, 2n), k), C, RS, sb_cidx(b, kvh, row, s, n_kv, S))
  +CO = Nat.mul(B48, 256n)
  +CM = Nat.mul(B48, 2n)
  +co = Impl.co_index(b, kvh, row, s, col, n_kv, S)
  +cm = Impl.cml_index(b, kvh, row, s, k, n_kv, S)
  +ro = Nat.add(Nat.mul(RS, 256n), col)
  +rm = Nat.add(Nat.mul(RS, 2n), k)
  ({==},
    {==},
    eo,
    em,
    CBP.ab_mul5(bsz, n_kv, S, 48n, 256n),
    CBP.ab_mul5(bsz, n_kv, S, 48n, 2n),
    ABP.ab_blk(RX, B48, col, 256n, hx, colb2),
    ABP.ab_blk(RX, B48, k, 2n, hx, eb2),
    Ar.ard_rt(Nat.is_lt(ro, CO), Nat.is_lt(co, CO),
      Equal.cong(Nat, Bool, t => Nat.is_lt(t, CO), ro, co, Equal.sym(Nat, co, ro, eo)),
      ABP.ab_blk(RS, B48, col, 256n, hsr, colb2)),
    Ar.ard_rt(Nat.is_lt(rm, CM), Nat.is_lt(cm, CM),
      Equal.cong(Nat, Bool, t => Nat.is_lt(t, CM), rm, cm, Equal.sym(Nat, cm, rm, em)),
      ABP.ab_blk(RS, B48, k, 2n, hsr, eb2)))

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
    CBP.ab_mul4(bsz, q_len, n_q, 256n))

def Laws.host_fits(bsz, kvh, splits, nsub, rows, hd_pad, sms):
  +BKS48 = Nat.mul(Nat.mul(Nat.mul(bsz, kvh), Impl.host_splits(sms, kvh)), 48n)
  +DO = Impl.dense_o(bsz, kvh, splits, nsub, rows, hd_pad)
  +DM = Impl.dense_ml(bsz, kvh, splits, nsub, rows)
  +z = Nat.div(sms, kvh)
  (CBP.ab_max_r(DO, Nat.mul(BKS48, 256n)),
    CBP.ab_max_r(DM, Nat.mul(BKS48, 2n)),
    CBP.ab_max_l(DO, Nat.mul(BKS48, 256n)),
    CBP.ab_max_l(DM, Nat.mul(BKS48, 2n)),
    Ar.ard_tr(Nat.is_lt(0n, Nat.max(1n, z)), Nat.is_le(1n, Nat.max(1n, z)), Ar.ar_lt_succ_le(0n, Nat.max(1n, z)),
      ABP.ab_max1(z)))

# tile_n0(x, it, S) = (x + it S) * 64: a multiple of 64, so its page slot ends by 256
def Laws.tile_in_page(x, it, S):
  CBP.ab_slot(Nat.add(x, Nat.mul(it, S)))

# A CTA with a tile (it < ceil(D / S)) has a nonempty grid (S > 0)
def sb_spos(+D: Nat, +it: Nat, +S: Nat, tb: {Nat.is_lt(it, Stride.cdiv(D, S)) == True{} : Bool})
  -> {Nat.is_lt(0n, S) == True{} : Bool}:
  match S:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(it, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(it, 0n), False{}, Ar.ar_h_lt_zero(it)), tb)))
    case 1n+sp:
      {==}

def Laws.tile_in_table(L, S, num_pages, x, it, xb, tb, ok):
  +tb2 = tb
  +n = Stride.live_tiles(L)
  +D = Nat.sub(n, x)
  +iS = Nat.mul(it, S)
  +q = Nat.add(x, iS)
  +n0 = Nat.mul(q, 64n)
  +P = Nat.mul(num_pages, 256n)
  +spos = sb_spos(D, it, S, tb2)
  # it < ceil((n_tiles - x) / S) gives it * S < n_tiles - x, so the tile x + it S < n_tiles
  +h1 = Ar.ard_rt(Nat.is_lt(it, Stride.cta_tiles(n, x, S)), Bool.not(Nat.is_le(D, iS)),
    AS.as_live(it, D, S, spos), tb2)
  +h2 = Ar.ard_tr(Nat.is_lt(iS, D), Bool.not(Nat.is_le(D, iS)), Ar.ar_lt_not_le(iS, D), h1)
  +h3 = Ar.ard_rt(Nat.is_lt(iS, D), Nat.is_lt(q, n), Ar.ar_lt_sub_iff(n, x, iS), h2)
  # tile q < ceil(L / 64) gives q * 64 < L
  +h4 = Ar.ard_rt(Nat.is_lt(q, n), Bool.not(Nat.is_le(L, n0)), AS.as_live(q, L, 64n, {==}), h3)
  +h5 = Ar.ard_tr(Nat.is_lt(n0, L), Bool.not(Nat.is_le(L, n0)), Ar.ar_lt_not_le(n0, L), h4)
  # the kernel runs past the trap only when L <= num_pages * 256
  +h6 = Ar.ar_lt_le_trans(n0, L, P, h5, ok)
  (h5,
    Ar.ard_tr(Nat.is_lt(Nat.div(n0, 256n), num_pages), Nat.is_lt(n0, P), Ar.ar_div_lt(num_pages, n0, 256n, {==}), h6))

def Laws.trap_needed():
  ({==}, {==}, {==}, {==})

# live = min(n_tiles, S) <= S <= 256 once attn_verify_gr accepted S
def Laws.combine_no_trap(L, S, checked):
  +n = Stride.live_tiles(L)
  Ar.ar_le_trans(Nat.min(n, S), S, 256n, Ar.p5_min_le_r(n, S),
    Ar.ar_and_r(Nat.is_lt(0n, S), Nat.is_le(S, 256n), checked))

def Laws.host_gr_ok():
  {==}
