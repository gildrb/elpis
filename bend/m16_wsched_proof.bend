# Proofs of ext 8205's slot-weighted 8201 / 8202 schedule laws (m16_wsched_laws.bend) about the Bend
# model m16_wsched.bend. Structural evidence only: no unsafe definitions, axioms, holes or foreign proof
# code. The event-list lemmas are ext 8201's (mlp_m16_sched_proof.bend) and ext 8204's
# (mlp_m16_defer_proof.bend), the arithmetic ones gemm_m16_partition_proof's, the host-guard and
# equal-weight lemmas m16_wsched_tables_proof.bend's; the per-block and grid
# lemmas are re-instantiated over the weighted slices, and the partition facts come from the proven
# gemm_m16_wpart laws.
# Every def precedes its uses.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_laws.bend as PLaws
import ./gemm_m16_partition_proof.bend as PP
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./gemm_m16_wpart_laws.bend as WLaws
import ./gemm_m16_wpart_proof.bend as WPP
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_sched_laws.bend as MLaws
import ./mlp_m16_sched_proof.bend as MP
import ./tail_m16_sched.bend as Tail
import ./mlp_m16_defer.bend as Defer
import ./mlp_m16_defer_spec.bend as DSpec
import ./mlp_m16_defer_proof.bend as DP
import ./m16_wsched.bend as Impl
import ./m16_wsched_laws.bend as Laws
import ./m16_wsched_tables_proof.bend as TBP

# ==== (5) ext 8204's program order ====

def Laws.wprogram(G, nsm, H, I, a1, b1, a2, b2, b):
  +ML = Impl.mainloop1(G, nsm, H, I, a1, b1, b)
  +EV = Impl.events(G, nsm, H, I, a1, b1, a2, b2, b)
  +R = {Defer.tag_sync(EV, Nil{}) : List<&2, DSpec.Ev>}
  +np = Mlp.pairs(I)
  +p = Impl.fin_pair(G, nsm, H, I, a2, b2, b)
  +ws = Impl.waits(G, nsm, H, I, a2, b2, b)
  +F = Mlp.finish(np, p, Mlp.waits2(ws))
  +S = DP.acc(ML, Nil{})
  (%DP.sy_work(ML, R) : {_ == EV : List<&2, MSpec.Ev>}
    DP.sy_sync(EV),
    DP.wk_work(ML, R, DP.wk_sync(EV, Nil{})),
    %DP.pw_work(ML, Defer.tag_sync(Mlp.sigs1(ML, F), Nil{}), Nil{}) : {_ == True{} : Bool}
    %DP.pw_sigs(ML, F, S, DP.acc_covers(ML, Nil{})) : {_ == True{} : Bool}
    DP.pw_finish(np, p, ws, S))

# ==== (4) levels: 8201's lemmas over any block's (main loop, finish pair, wait list) ====

def lv_ordered(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>)
  -> {MSpec.ordered(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), 0n) == True{} : Bool}:
  %MP.ord_sigs1_sym(ml, Mlp.finish(np, fp, Mlp.waits2(ws))) : {_ == True{} : Bool}
  MP.ord_waits2(ws, 1n, {==})

def lv_sig(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +c: MSpec.Ctr)
  -> {MSpec.sigs_below(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), c, MLaws.gate_level(c)) ==
    True{} : Bool}:
  match c:
    case MSpec.C1{g}:
      %MP.sb_sigs1_sym(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C1{g}, 0n) : {_ == True{} : Bool}
      MP.sb_waits2(ws, MSpec.C1{g}, 1n)
    case MSpec.C2{p}:
      %MP.sb_sigs1_sym(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C2{p}, 1n) : {_ == True{} : Bool}
      %MP.or_true_r(Bool.not(Nat.is_eq(fp, p)))
        : {Bool.and(_, MSpec.sigs_below(Mlp.waits2(ws), MSpec.C2{p}, 2n)) == True{} : Bool}
      MP.sb_waits2(ws, MSpec.C2{p}, 2n)

def lv_wait(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +c: MSpec.Ctr)
  -> {MSpec.waits_from(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), c, MLaws.gate_level(c)) ==
    True{} : Bool}:
  match c:
    case MSpec.C1{g}:
      %MP.wf_sigs1_sym(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C1{g}, 1n) : {_ == True{} : Bool}
      %MP.or_true_r(Bool.not(Nat.is_eq(fp, g)))
        : {Bool.and(_, Bool.and(Bool.or(Bool.not(Nat.is_eq(Nat.add(np, fp), g)), True{}),
          MSpec.waits_from(Mlp.waits2(ws), MSpec.C1{g}, 1n))) == True{} : Bool}
      %MP.or_true_r(Bool.not(Nat.is_eq(Nat.add(np, fp), g)))
        : {Bool.and(_, MSpec.waits_from(Mlp.waits2(ws), MSpec.C1{g}, 1n)) == True{} : Bool}
      MP.wf_waits2(ws, MSpec.C1{g}, 1n, {==})
    case MSpec.C2{p}:
      %MP.wf_sigs1_sym(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C2{p}, 2n) : {_ == True{} : Bool}
      MP.wf_waits2(ws, MSpec.C2{p}, 2n, {==})

def Laws.wlevels(G, nsm, H, I, a1, b1, a2, b2, b, d, c):
  +np = Mlp.pairs(I)
  (lv_ordered(Impl.mainloop1(G, nsm, H, I, a1, b1, b), np, Impl.fin_pair(G, nsm, H, I, a2, b2, b),
      Impl.waits(G, nsm, H, I, a2, b2, b)),
    lv_sig(Impl.mainloop1(G, nsm, H, I, a1, b1, d), np, Impl.fin_pair(G, nsm, H, I, a2, b2, d),
      Impl.waits(G, nsm, H, I, a2, b2, d), c),
    lv_wait(Impl.mainloop1(G, nsm, H, I, a1, b1, b), np, Impl.fin_pair(G, nsm, H, I, a2, b2, b),
      Impl.waits(G, nsm, H, I, a2, b2, b), c))

# ==== (6) wait lists ====

def Laws.wwaits_nodup(G, nsm, H, I, a2, b2, b):
  MP.nodup_go(I, Impl.n2(G, nsm, H, I, a2, b2, b), Impl.s2(G, nsm, H, I, a2, b2, b), Nil{})

def Laws.wwaits_cover(G, nsm, H, I, a2, b2, b, x, lo, hi):
  +l = lo
  +s = Impl.s2(G, nsm, H, I, a2, b2, b)
  +n = Impl.n2(G, nsm, H, I, a2, b2, b)
  +j = Nat.sub(x, s)
  %PP.ar_sub_add(x, s, l)
    : {MSpec.member(Impl.waits(G, nsm, H, I, a2, b2, b), Mlp.pair_of(I, _)) == True{} : Bool}
  MP.cover_go(I, n, s, Nil{}, j,
    (%PP.ar_lt_add_cancel(s, j, n) : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.add(s, j), x, PP.ar_sub_add(x, s, l))
        : {Nat.is_lt(_, Nat.add(s, n)) == True{} : Bool}
      hi))

# ==== (3) counters: one block's amounts, over any (main loop, finish pair, wait list) ====

def blk_sig_c2(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +p: Nat)
  -> {Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n) ==
    MSpec.sig_amount(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), MSpec.C2{p}) : Nat}:
  +M = Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n)
  %MP.sa_sigs1_c2(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), p) : {M == _ : Nat}
  %MP.sa_waits2(ws, MSpec.C2{p}) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def blk_wait_c1(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +p: Nat,
    lt: {Nat.is_lt(p, np) == True{} : Bool})
  -> {Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n) ==
    MSpec.wait_amount(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), MSpec.C1{p}) : Nat}:
  +M = Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n)
  %MP.wa_sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C1{p}) : {M == _ : Nat}
  %MP.eq_add_lt(np, fp, p, lt)
    : {M == Nat.add(M, Nat.add(Nat.mul(MSpec.bit(_), 8n),
      MSpec.wait_amount(Mlp.waits2(ws), MSpec.C1{p}))) : Nat}
  %MP.wa_waits2_c1(ws, p) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def blk_wait_up(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +p: Nat,
    fplt: {Nat.is_lt(fp, np) == True{} : Bool})
  -> {Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n) ==
    MSpec.wait_amount(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), MSpec.C1{Nat.add(np, p)})
    : Nat}:
  +M = Nat.mul(MSpec.bit(Nat.is_eq(fp, p)), 8n)
  %MP.wa_sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C1{Nat.add(np, p)}) : {M == _ : Nat}
  %MP.eq_lt_add(fp, np, p, fplt)
    : {M == Nat.add(Nat.mul(MSpec.bit(_), 8n),
      Nat.add(Nat.mul(MSpec.bit(Nat.is_eq(Nat.add(np, fp), Nat.add(np, p))), 8n),
        MSpec.wait_amount(Mlp.waits2(ws), MSpec.C1{Nat.add(np, p)}))) : Nat}
  %MP.eq_add_cancel(np, fp, p)
    : {M == Nat.add(Nat.mul(MSpec.bit(_), 8n),
      MSpec.wait_amount(Mlp.waits2(ws), MSpec.C1{Nat.add(np, p)})) : Nat}
  %MP.wa_waits2_c1(ws, Nat.add(np, p)) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def blk_wait_c2(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +p: Nat,
    nd: {MSpec.nodup(ws) == True{} : Bool})
  -> {MSpec.bit(MSpec.member(ws, p)) ==
    MSpec.wait_amount(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), MSpec.C2{p}) : Nat}:
  %MP.wa_sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), MSpec.C2{p})
    : {MSpec.bit(MSpec.member(ws, p)) == _ : Nat}
  %MP.wa_waits2_occ(ws, p) : {MSpec.bit(MSpec.member(ws, p)) == _ : Nat}
  MP.occ_member(ws, p, nd)

# ==== (3) grid totals over the weighted blocks ====

def st_c2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +p: Nat)
  -> {Nat.mul(Impl.fin_count(G, nsm, H, I, a2, b2, n, p), 8n) ==
    Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, n, MSpec.C2{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = MSpec.bit(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, m), p))
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, m, p)
      %st_c2(G, nsm, H, I, a1, b1, a2, b2, m, p)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, MSpec.sig_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, m), MSpec.C2{p})) : Nat}
      %blk_sig_c2(Impl.mainloop1(G, nsm, H, I, a1, b1, m), Mlp.pairs(I),
          Impl.fin_pair(G, nsm, H, I, a2, b2, m), Impl.waits(G, nsm, H, I, a2, b2, m), p)
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.wfinish_signals(G, nsm, H, I, a1, b1, a2, b2, p):
  +C = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
  Equal.trans(Nat, Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C2{p}), Nat.mul(C, 8n),
    Nat.mul(8n, C),
    Equal.sym(Nat, Nat.mul(C, 8n), Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C2{p}),
      st_c2(G, nsm, H, I, a1, b1, a2, b2, G, p)),
    PP.ar_mul_comm(C, 8n))

def wt_c1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +p: Nat, +lt: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool})
  -> {Nat.mul(Impl.fin_count(G, nsm, H, I, a2, b2, n, p), 8n) ==
    Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, n, MSpec.C1{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = MSpec.bit(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, m), p))
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, m, p)
      %wt_c1(G, nsm, H, I, a1, b1, a2, b2, m, p, lt)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, MSpec.wait_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, m), MSpec.C1{p})) : Nat}
      %blk_wait_c1(Impl.mainloop1(G, nsm, H, I, a1, b1, m), Mlp.pairs(I),
          Impl.fin_pair(G, nsm, H, I, a2, b2, m), Impl.waits(G, nsm, H, I, a2, b2, m), p, lt)
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.wgate_waiters(G, nsm, H, I, a1, b1, a2, b2, p, pair):
  +C = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
  Equal.trans(Nat, Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{p}), Nat.mul(C, 8n),
    Nat.mul(8n, C),
    Equal.sym(Nat, Nat.mul(C, 8n), Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{p}),
      wt_c1(G, nsm, H, I, a1, b1, a2, b2, G, p, pair)),
    PP.ar_mul_comm(C, 8n))

# Every down pair of an iteration is a real pair: pair_of(I, s) < NP (I >= 128, I = 0 mod 512).
def pair_lt(+I: Nat, +s: Nat, shaped: {Nat.is_le(128n, I) == True{} : Bool},
    grp: {Nat.mod(I, 512n) == 0n : Nat})
  -> {Nat.is_lt(Mlp.pair_of(I, s), Mlp.pairs(I)) == True{} : Bool}:
  +y = Nat.mod(s, Mlp.kt2(I))
  %Equal.sym(Bool, Nat.is_lt(Nat.div(y, 32n), Mlp.pairs(I)),
      Nat.is_lt(y, Nat.mul(Mlp.pairs(I), 32n)), PP.ar_div_lt(Mlp.pairs(I), y, 32n, {==}))
    : {_ == True{} : Bool}
  %MP.kt2_pairs(I, grp) : {Nat.is_lt(y, _) == True{} : Bool}
  PP.ard_dm_lt(s, Mlp.kt2(I), PP.p2_kt_pos(I, shaped))

def wt_up(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +p: Nat, +shaped: {Nat.is_le(128n, I) == True{} : Bool}, +grp: {Nat.mod(I, 512n) == 0n : Nat})
  -> {Nat.mul(Impl.fin_count(G, nsm, H, I, a2, b2, n, p), 8n) ==
    Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, n, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = MSpec.bit(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, m), p))
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, m, p)
      %wt_up(G, nsm, H, I, a1, b1, a2, b2, m, p, shaped, grp)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, MSpec.wait_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, m),
            MSpec.C1{Nat.add(Mlp.pairs(I), p)})) : Nat}
      %blk_wait_up(Impl.mainloop1(G, nsm, H, I, a1, b1, m), Mlp.pairs(I),
          Impl.fin_pair(G, nsm, H, I, a2, b2, m), Impl.waits(G, nsm, H, I, a2, b2, m), p,
          pair_lt(I, Impl.s2(G, nsm, H, I, a2, b2, m), shaped, grp))
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.wup_waiters(G, nsm, H, I, a1, b1, a2, b2, p, shaped, groups):
  +C = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
  Equal.trans(Nat, Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}),
    Nat.mul(C, 8n), Nat.mul(8n, C),
    Equal.sym(Nat, Nat.mul(C, 8n),
      Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}),
      wt_up(G, nsm, H, I, a1, b1, a2, b2, G, p, shaped, groups)),
    PP.ar_mul_comm(C, 8n))

def wt_c2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +p: Nat)
  -> {Impl.wait_blocks(G, nsm, H, I, a2, b2, n, p) ==
    Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, n, MSpec.C2{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +W = Impl.wait_blocks(G, nsm, H, I, a2, b2, m, p)
      +ws = Impl.waits(G, nsm, H, I, a2, b2, m)
      %wt_c2(G, nsm, H, I, a1, b1, a2, b2, m, p)
        : {Nat.add(W, MSpec.bit(MSpec.member(ws, p))) ==
          Nat.add(_, MSpec.wait_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, m), MSpec.C2{p})) : Nat}
      %blk_wait_c2(Impl.mainloop1(G, nsm, H, I, a1, b1, m), Mlp.pairs(I),
          Impl.fin_pair(G, nsm, H, I, a2, b2, m), ws, p, Laws.wwaits_nodup(G, nsm, H, I, a2, b2, m))
        : {Nat.add(W, MSpec.bit(MSpec.member(ws, p))) == Nat.add(W, _) : Nat}
      {==}

def Laws.wpair_waiters(G, nsm, H, I, a1, b1, a2, b2, p):
  Equal.sym(Nat, Impl.wait2(G, nsm, H, I, a2, b2, p),
    Laws.wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C2{p}),
    wt_c2(G, nsm, H, I, a1, b1, a2, b2, G, p))

# ==== (6) finish jobs and ranks over the weighted finish pairs ====

def fh_step(v: Bool, +G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat, +p: Nat,
    +x: Nat, +m: Nat,
    ev: {Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, b), p) == v : Bool},
    ih: {Impl.finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m) ==
      Part.job_hits(Impl.fin_count(G, nsm, H, I, a2, b2, b, p), x,
        Impl.fin_count(G, nsm, H, I, a2, b2, G, p), Nat.mul(4n, m)) : Nat})
  -> {Nat.add(Impl.finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m),
      Nat.mul(MSpec.bit(v), Part.warp_hits(8n, Impl.fin_rank(G, nsm, H, I, a2, b2, b), x,
        Impl.fin_cnt(G, nsm, H, I, a2, b2, b), Nat.mul(4n, m)))) ==
    Part.job_hits(Nat.add(Impl.fin_count(G, nsm, H, I, a2, b2, b, p), MSpec.bit(v)), x,
      Impl.fin_count(G, nsm, H, I, a2, b2, G, p), Nat.mul(4n, m)) : Nat}:
  match v:
    case True{}:
      +J = Nat.mul(4n, m)
      +K = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, b, p)
      +JH = Part.job_hits(C, x, K, J)
      %Equal.sym(Nat, Impl.fin_pair(G, nsm, H, I, a2, b2, b), p,
          PP.ar_eq_true(Impl.fin_pair(G, nsm, H, I, a2, b2, b), p, ev))
        : {Nat.add(Impl.finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m),
            Nat.mul(1n, Part.warp_hits(8n, Impl.fin_count(G, nsm, H, I, a2, b2, b, _), x,
              Impl.fin_count(G, nsm, H, I, a2, b2, G, _), J))) ==
          Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %Equal.sym(Nat, Impl.finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m), JH, ih)
        : {Nat.add(_, Nat.mul(1n, Part.warp_hits(8n, C, x, K, J))) ==
          Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.mul(1n, Part.warp_hits(8n, C, x, K, J)), Part.warp_hits(8n, C, x, K, J),
          PP.ar_mul_one_l(Part.warp_hits(8n, C, x, K, J)))
        : {Nat.add(JH, _) == Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %MP.add_one(C) : {Nat.add(JH, Part.warp_hits(8n, C, x, K, J)) == Part.job_hits(_, x, K, J) : Nat}
      {==}
    case False{}:
      +J = Nat.mul(4n, m)
      +K = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, b, p)
      +JH = Part.job_hits(C, x, K, J)
      %Equal.sym(Nat, Impl.finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m), JH, ih)
        : {Nat.add(_, 0n) == Part.job_hits(Nat.add(C, 0n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.add(JH, 0n), JH, PP.ar_add_zero_r(JH))
        : {_ == Part.job_hits(Nat.add(C, 0n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.add(C, 0n), C, PP.ar_add_zero_r(C))
        : {JH == Part.job_hits(_, x, K, J) : Nat}
      {==}

# The finisher warps of pair p's blocks b < n are the v2 finish loop's (block, warp) pairs of the
# ranks 0 .. fin_count(n, p) - 1 over a k_p-block grid.
def fh_re(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +n: Nat, +p: Nat, +x: Nat,
    +m: Nat)
  -> {Impl.finisher_hits(G, nsm, H, I, a2, b2, n, p, x, m) ==
    Part.job_hits(Impl.fin_count(G, nsm, H, I, a2, b2, n, p), x,
      Impl.fin_count(G, nsm, H, I, a2, b2, G, p), Nat.mul(4n, m)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      fh_step(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, b), p), G, nsm, H, I, a2, b2, b, p, x, m,
        {==}, fh_re(G, nsm, H, I, a2, b2, b, p, x, m))

def Laws.wfinish_jobs_once(G, nsm, H, I, a2, b2, p, m, x, finished):
  +K = Impl.fin_count(G, nsm, H, I, a2, b2, G, p)
  Equal.trans(Nat, Impl.finisher_hits(G, nsm, H, I, a2, b2, G, p, x, m),
    Part.job_hits(K, x, K, Nat.mul(4n, m)), PSpec.bit(Nat.is_lt(x, Nat.mul(4n, m))),
    fh_re(G, nsm, H, I, a2, b2, G, p, x, m),
    PLaws.finish_jobs_once(x, K, Nat.mul(4n, m), finished))

def fc_mono(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat, +k: Nat, +q: Nat)
  -> {Nat.is_le(Impl.fin_count(G, nsm, H, I, a2, b2, b, q),
    Impl.fin_count(G, nsm, H, I, a2, b2, Nat.add(b, k), q)) == True{} : Bool}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(b, 0n), b, PP.ar_add_zero_r(b))
        : {Nat.is_le(Impl.fin_count(G, nsm, H, I, a2, b2, b, q),
          Impl.fin_count(G, nsm, H, I, a2, b2, _, q)) == True{} : Bool}
      PP.ar_le_refl(Impl.fin_count(G, nsm, H, I, a2, b2, b, q))
    case 1n+j:
      +C = Impl.fin_count(G, nsm, H, I, a2, b2, Nat.add(b, j), q)
      %Equal.sym(Nat, Nat.add(b, 1n+j), 1n+Nat.add(b, j), PP.ar_add_succ_r(b, j))
        : {Nat.is_le(Impl.fin_count(G, nsm, H, I, a2, b2, b, q),
          Impl.fin_count(G, nsm, H, I, a2, b2, _, q)) == True{} : Bool}
      PP.ar_le_trans(Impl.fin_count(G, nsm, H, I, a2, b2, b, q), C,
        Nat.add(C, MSpec.bit(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, Nat.add(b, j)), q))),
        fc_mono(G, nsm, H, I, a2, b2, b, j, q),
        PP.ar_le_add_r(C, MSpec.bit(Nat.is_eq(Impl.fin_pair(G, nsm, H, I, a2, b2, Nat.add(b, j)), q))))

# Block b's rank is below the count of its finish pair among blocks < n, for b < n.
def rank_below(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat, +n: Nat,
    lt: {Nat.is_lt(b, n) == True{} : Bool})
  -> {Nat.is_lt(Impl.fin_count(G, nsm, H, I, a2, b2, b, Impl.fin_pair(G, nsm, H, I, a2, b2, b)),
    Impl.fin_count(G, nsm, H, I, a2, b2, n, Impl.fin_pair(G, nsm, H, I, a2, b2, b))) == True{} : Bool}:
  +q = Impl.fin_pair(G, nsm, H, I, a2, b2, b)
  +c = Impl.fin_count(G, nsm, H, I, a2, b2, b, q)
  +K = Impl.fin_count(G, nsm, H, I, a2, b2, n, q)
  +le1b = Equal.trans(Bool, Nat.is_le(1n+b, n), Nat.is_lt(b, n), True{},
    Equal.sym(Bool, Nat.is_lt(b, n), Nat.is_le(1n+b, n), PP.ar_lt_succ_le(b, n)), lt)
  %Equal.sym(Bool, Nat.is_lt(c, K), Nat.is_le(1n+c, K), PP.ar_lt_succ_le(c, K))
    : {_ == True{} : Bool}
  PP.ar_le_trans(1n+c, Impl.fin_count(G, nsm, H, I, a2, b2, 1n+b, q), K,
    (%Equal.sym(Bool, Nat.is_eq(q, q), True{}, PP.ar_eq_refl(q))
        : {Nat.is_le(1n+c, Nat.add(c, MSpec.bit(_))) == True{} : Bool}
      %MP.add_one(c) : {Nat.is_le(1n+c, _) == True{} : Bool}
      PP.ar_le_refl(1n+c)),
    (%PP.ar_sub_add(n, 1n+b, le1b)
        : {Nat.is_le(Impl.fin_count(G, nsm, H, I, a2, b2, 1n+b, q),
          Impl.fin_count(G, nsm, H, I, a2, b2, _, q)) == True{} : Bool}
      fc_mono(G, nsm, H, I, a2, b2, 1n+b, Nat.sub(n, 1n+b), q)))

def Laws.wfin_rank_bound(G, nsm, H, I, a2, b2, b, inside):
  rank_below(G, nsm, H, I, a2, b2, b, G, inside)

def rank_lt(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat, +c: Nat,
    lt: {Nat.is_lt(b, c) == True{} : Bool},
    pair: {Impl.fin_pair(G, nsm, H, I, a2, b2, b) == Impl.fin_pair(G, nsm, H, I, a2, b2, c) : Nat})
  -> {Nat.is_lt(Impl.fin_rank(G, nsm, H, I, a2, b2, b), Impl.fin_rank(G, nsm, H, I, a2, b2, c)) ==
    True{} : Bool}:
  %pair
    : {Nat.is_lt(Impl.fin_count(G, nsm, H, I, a2, b2, b, Impl.fin_pair(G, nsm, H, I, a2, b2, b)),
      Impl.fin_count(G, nsm, H, I, a2, b2, c, _)) == True{} : Bool}
  rank_below(G, nsm, H, I, a2, b2, b, c, lt)

def unique_tri(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat, +c: Nat, v: Bool,
    ev: {Nat.is_lt(b, c) == v : Bool}, w: Bool, ew: {Nat.is_lt(c, b) == w : Bool},
    pair: {Impl.fin_pair(G, nsm, H, I, a2, b2, b) == Impl.fin_pair(G, nsm, H, I, a2, b2, c) : Nat},
    rank: {Impl.fin_rank(G, nsm, H, I, a2, b2, b) == Impl.fin_rank(G, nsm, H, I, a2, b2, c) : Nat})
  -> {b == c : Nat}:
  match v:
    case True{}:
      Empty.absurd({b == c : Nat}, MP.lt_self_of(Impl.fin_rank(G, nsm, H, I, a2, b2, b),
        Impl.fin_rank(G, nsm, H, I, a2, b2, c), rank, rank_lt(G, nsm, H, I, a2, b2, b, c, ev, pair)))
    case False{}:
      match w:
        case True{}:
          Empty.absurd({b == c : Nat},
            MP.lt_self_of(Impl.fin_rank(G, nsm, H, I, a2, b2, c), Impl.fin_rank(G, nsm, H, I, a2, b2, b),
              Equal.sym(Nat, Impl.fin_rank(G, nsm, H, I, a2, b2, b), Impl.fin_rank(G, nsm, H, I, a2, b2, c),
                rank),
              rank_lt(G, nsm, H, I, a2, b2, c, b, ew,
                Equal.sym(Nat, Impl.fin_pair(G, nsm, H, I, a2, b2, b), Impl.fin_pair(G, nsm, H, I, a2, b2, c),
                  pair))))
        case False{}:
          PP.ar_le_antisym(b, c,
            PP.p2_not_false(Nat.is_le(b, c), Equal.trans(Bool, Bool.not(Nat.is_le(b, c)),
              Nat.is_lt(c, b), False{},
              Equal.sym(Bool, Nat.is_lt(c, b), Bool.not(Nat.is_le(b, c)), PP.ar_lt_not_le(c, b)),
              ew)),
            PP.p2_not_false(Nat.is_le(c, b), Equal.trans(Bool, Bool.not(Nat.is_le(c, b)),
              Nat.is_lt(b, c), False{},
              Equal.sym(Bool, Nat.is_lt(b, c), Bool.not(Nat.is_le(c, b)), PP.ar_lt_not_le(b, c)),
              ev)))

def Laws.wfin_rank_unique(G, nsm, H, I, a2, b2, b, c, pair, rank):
  unique_tri(G, nsm, H, I, a2, b2, b, c, Nat.is_lt(b, c), {==}, Nat.is_lt(c, b), {==}, pair, rank)

# ==== (1) slices are the weighted partition's owned ranges ====

# s + (e - s) == e for the slice [s, e) = [start(c), start(c + 1)).
def w_end(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +c: Nat,
    +valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.add(Wp.start(c, T, G, nsm, w0, w1),
      Nat.sub(Wp.start(1n+c, T, G, nsm, w0, w1), Wp.start(c, T, G, nsm, w0, w1))) ==
    Wp.start(1n+c, T, G, nsm, w0, w1) : Nat}:
  PP.ar_sub_add(Wp.start(1n+c, T, G, nsm, w0, w1), Wp.start(c, T, G, nsm, w0, w1),
    WLaws.start_mono(T, G, nsm, w0, w1, c, 1n+c, TBP.tv_w0(T, G, nsm, w0, w1, valid),
      TBP.tv_w1(T, G, nsm, w0, w1, valid), TBP.tv_g(T, G, nsm, w0, w1, valid), PP.ar_h_le_succ(c)))

def w_slice_owned(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +c: Nat, +x: Nat,
    +valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool})
  -> {Bool.and(Nat.is_le(Wp.start(c, T, G, nsm, w0, w1), x),
      Nat.is_lt(x, Nat.add(Wp.start(c, T, G, nsm, w0, w1),
        Nat.sub(Wp.start(1n+c, T, G, nsm, w0, w1), Wp.start(c, T, G, nsm, w0, w1))))) ==
    WSpec.owns(c, x, T, G, nsm, w0, w1) : Bool}:
  +s = Wp.start(c, T, G, nsm, w0, w1)
  +e = Wp.start(1n+c, T, G, nsm, w0, w1)
  %Equal.sym(Nat, Nat.add(s, Nat.sub(e, s)), e, w_end(T, G, nsm, w0, w1, c, valid))
    : {Bool.and(Nat.is_le(s, x), Nat.is_lt(x, _)) == WSpec.owns(c, x, T, G, nsm, w0, w1) : Bool}
  WLaws.range_is_owned(T, G, nsm, w0, w1, c, x, TBP.tv_w0(T, G, nsm, w0, w1, valid),
    TBP.tv_w1(T, G, nsm, w0, w1, valid), TBP.tv_g(T, G, nsm, w0, w1, valid))

def w_once(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +x: Nat,
    +valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool},
    inside: {Nat.is_lt(x, T) == True{} : Bool})
  -> {WSpec.owners(G, x, T, G, nsm, w0, w1) == 1n : Nat}:
  WLaws.owners_exactly_one(T, G, nsm, w0, w1, x, TBP.tv_w0(T, G, nsm, w0, w1, valid),
    TBP.tv_w1(T, G, nsm, w0, w1, valid), TBP.tv_g(T, G, nsm, w0, w1, valid), inside)

def Laws.wphase1_slice_owned(G, nsm, H, I, a1, b1, b, x, valid):
  w_slice_owned(Mlp.total1(H, I), G, nsm, a1, b1, b, x, valid)

def Laws.wphase1_exactly_once(G, nsm, H, I, a1, b1, x, valid, inside):
  w_once(Mlp.total1(H, I), G, nsm, a1, b1, x, valid, inside)

def Laws.wphase2_slice_owned(G, nsm, H, I, a2, b2, b, x, valid):
  w_slice_owned(Mlp.total2(H, I), G, nsm, a2, b2, b, x, valid)

def Laws.wphase2_exactly_once(G, nsm, H, I, a2, b2, x, valid, inside):
  w_once(Mlp.total2(H, I), G, nsm, a2, b2, x, valid, inside)

def Laws.wphase0_slice_owned(G, nsm, A, H, a0, b0, b, x, valid):
  w_slice_owned(Tail.total0(A, H), G, nsm, a0, b0, b, x, valid)

def Laws.wphase0_exactly_once(G, nsm, A, H, a0, b0, x, valid, inside):
  w_once(Tail.total0(A, H), G, nsm, a0, b0, x, valid, inside)

# ==== (2) split-K slots ====

def w_slots(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +b: Nat,
    +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool},
    +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +contributor: {WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b) == True{} : Bool} &
    {Nat.is_lt(Nat.sub(b, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
      Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
    {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
      Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  +T = Nat.mul(groups, KT)
  +lo = Wp.first_contrib(g, KT, T, G, nsm, w0, w1)
  +hi = Wp.last_contrib(g, KT, T, G, nsm, w0, w1)
  +n = Wp.nc(g, KT, T, G, nsm, w0, w1)
  +mc = Wp.max_contrib(groups, KT, G, nsm, w0, w1)
  +w0p = TBP.tv_w0(T, G, nsm, w0, w1, valid)
  +w1p = TBP.tv_w1(T, G, nsm, w0, w1, valid)
  +gp = TBP.tv_g(T, G, nsm, w0, w1, valid)
  -A = {Nat.is_le(lo, b) == True{} : Bool}
  -B = {Nat.is_lt(Nat.sub(b, lo), n) == True{} : Bool}
  -C = {Nat.is_lt(Nat.sub(b, lo), mc) == True{} : Bool}
  -D = {Nat.is_lt(Wp.address(g, mc, b, lo), Nat.mul(groups, mc)) == True{} : Bool}
  -A2 = {Nat.is_le(lo, hi) == True{} : Bool}
  -B2 = {Nat.is_lt(hi, G) == True{} : Bool}
  -C2 = {Nat.is_le(1n, n) == True{} : Bool}
  -D2 = {Nat.is_le(n, mc) == True{} : Bool}
  (PP.ard_fst(A, B & C & D,
      WLaws.slot_in_range(groups, KT, G, nsm, w0, w1, g, b, w0p, w1p, gp, tiles, group, contributor)),
    PP.ard_fst(B, C & D, PP.ard_snd(A, B & C & D,
      WLaws.slot_in_range(groups, KT, G, nsm, w0, w1, g, b, w0p, w1p, gp, tiles, group, contributor))),
    PP.ard_snd(C2, D2, PP.ard_snd(B2, C2 & D2, PP.ard_snd(A2, B2 & C2 & D2,
      WLaws.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0p, w1p, gp, tiles, group)))))

def Laws.wphase1_slots(G, nsm, H, I, a1, b1, g, b, valid, shaped, group, contributor):
  w_slots(Part.groups(2n, I), Mlp.kt1(H), G, nsm, a1, b1, g, b, valid, PP.p2_kt_pos(H, shaped), group,
    contributor)

def Laws.wphase2_slots(G, nsm, H, I, a2, b2, g, b, valid, shaped, group, contributor):
  w_slots(Part.groups(1n, H), Mlp.kt2(I), G, nsm, a2, b2, g, b, valid, PP.p2_kt_pos(I, shaped), group,
    contributor)

def Laws.wphase0_slots(G, nsm, A, H, a0, b0, g, b, valid, shaped, group, contributor):
  w_slots(Part.groups(1n, H), Tail.kt0(A), G, nsm, a0, b0, g, b, valid, PP.p2_kt_pos(A, shaped), group,
    contributor)

# ==== (3) cnt1 signals: a block flushes group g once iff it touches g; nc(g) blocks touch it ====

# owns_some over the weighted ownership is the range scan p1t_os over [start(b), start(b + 1)).
def wos_eq(left: Nat, +x: Nat, +b: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0p: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1p: {Nat.is_lt(0n, w1) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {WSpec.owns_some(left, x, b, T, G, nsm, w0, w1) ==
    PP.p1t_os(left, x, Wp.start(b, T, G, nsm, w0, w1), Wp.start(1n+b, T, G, nsm, w0, w1)) : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      +s = Wp.start(b, T, G, nsm, w0, w1)
      +e = Wp.start(1n+b, T, G, nsm, w0, w1)
      %wos_eq(r, 1n+x, b, T, G, nsm, w0, w1, w0p, w1p, gp)
        : {Bool.or(WSpec.owns(b, x, T, G, nsm, w0, w1), WSpec.owns_some(r, 1n+x, b, T, G, nsm, w0, w1)) ==
          Bool.or(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e)), _) : Bool}
      %WLaws.range_is_owned(T, G, nsm, w0, w1, b, x, w0p, w1p, gp)
        : {Bool.or(_, WSpec.owns_some(r, 1n+x, b, T, G, nsm, w0, w1)) ==
          Bool.or(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e)), WSpec.owns_some(r, 1n+x, b, T, G, nsm, w0, w1))
          : Bool}
      {==}

# Block b touches group g iff its range is non-empty and meets [g KT, (g + 1) KT).
def wtouch_range(+b: Nat, +g: Nat, +KT: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0p: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1p: {Nat.is_lt(0n, w1) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {WSpec.touches(b, g, KT, T, G, nsm, w0, w1) ==
    PP.p6_P(Wp.start(b, T, G, nsm, w0, w1), Wp.start(1n+b, T, G, nsm, w0, w1), KT, g) : Bool}:
  match KT:
    case 0n:
      +s = Wp.start(b, T, G, nsm, w0, w1)
      +e = Wp.start(1n+b, T, G, nsm, w0, w1)
      %Equal.sym(Nat, Nat.mul(g, 0n), 0n, PP.ar_mul_zero_r(g))
        : {False{} == Bool.and(Nat.is_lt(s, e), Bool.and(Nat.is_lt(s, _), Nat.is_lt(_, e))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(s, 0n), False{}, PP.p1t_lt0(s))
        : {False{} == Bool.and(Nat.is_lt(s, e), Bool.and(_, Nat.is_lt(0n, e))) : Bool}
      PP.p1t_and_false_r(Nat.is_lt(s, e))
    case 1n+k:
      +s = Wp.start(b, T, G, nsm, w0, w1)
      +e = Wp.start(1n+b, T, G, nsm, w0, w1)
      %PP.ar_add_comm(Nat.mul(g, 1n+k), 1n+k)
        : {WSpec.touches(b, g, 1n+k, T, G, nsm, w0, w1) ==
          Bool.and(Nat.is_lt(s, e), Bool.and(Nat.is_lt(s, _), Nat.is_lt(Nat.mul(g, 1n+k), e))) : Bool}
      Equal.trans(Bool, WSpec.owns_some(1n+k, Nat.mul(g, 1n+k), b, T, G, nsm, w0, w1),
        PP.p1t_os(1n+k, Nat.mul(g, 1n+k), s, e), PP.p1t_rng(k, Nat.mul(g, 1n+k), s, e),
        wos_eq(1n+k, Nat.mul(g, 1n+k), b, T, G, nsm, w0, w1, w0p, w1p, gp),
        PP.p1t_main(s, e, Nat.mul(g, 1n+k), k))

# The weighted slice [start(b), start(b + 1)) flushes group g once iff b touches g.
def wflush(+b: Nat, +g: Nat, +KT: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0p: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1p: {Nat.is_lt(0n, w1) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {PSpec.flushes(Part.mainloop(Wp.start(b, T, G, nsm, w0, w1), Wp.start(1n+b, T, G, nsm, w0, w1), KT),
      g) == PSpec.bit(WSpec.touches(b, g, KT, T, G, nsm, w0, w1)) : Nat}:
  +s = Wp.start(b, T, G, nsm, w0, w1)
  +e = Wp.start(1n+b, T, G, nsm, w0, w1)
  +ord = WLaws.start_mono(T, G, nsm, w0, w1, b, 1n+b, w0p, w1p, gp, PP.ar_h_le_succ(b))
  %Equal.sym(List<&2, PSpec.Ev>, Part.mainloop(s, e, KT), PSpec.trace(Nat.sub(e, s), s, e, KT),
      PLaws.mainloop_trace(s, e, KT, ord, kpos))
    : {PSpec.flushes(_, g) == PSpec.bit(WSpec.touches(b, g, KT, T, G, nsm, w0, w1)) : Nat}
  %Equal.sym(Bool, WSpec.touches(b, g, KT, T, G, nsm, w0, w1), PP.p6_P(s, e, KT, g),
      wtouch_range(b, g, KT, T, G, nsm, w0, w1, w0p, w1p, gp))
    : {PSpec.flushes(PSpec.trace(Nat.sub(e, s), s, e, KT), g) == PSpec.bit(_) : Nat}
  PP.p6_core(Nat.sub(e, s), s, e, KT, g, kpos,
    Equal.trans(Nat, Nat.add(Nat.sub(e, s), s), Nat.add(s, Nat.sub(e, s)), e,
      PP.ar_add_comm(Nat.sub(e, s), s), PP.ar_sub_add(e, s, ord)))

# A block signals cnt1[g] 8 times per flush of g in its phase-1 loop.
def blk_sig_c1(+ml: List<&2, PSpec.Ev>, +np: Nat, +fp: Nat, +ws: List<&2, Nat>, +g: Nat)
  -> {Nat.mul(PSpec.flushes(ml, g), 8n) ==
    MSpec.sig_amount(Mlp.sigs1(ml, Mlp.finish(np, fp, Mlp.waits2(ws))), MSpec.C1{g}) : Nat}:
  +M = Nat.mul(PSpec.flushes(ml, g), 8n)
  %MP.sa_sigs1_c1(ml, Mlp.finish(np, fp, Mlp.waits2(ws)), g) : {M == _ : Nat}
  %MP.sa_waits2(ws, MSpec.C1{g}) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def st_c1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +g: Nat, +w0p: {Nat.is_lt(0n, a1) == True{} : Bool}, +w1p: {Nat.is_lt(0n, b1) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool}, +kpos: {Nat.is_lt(0n, Mlp.kt1(H)) == True{} : Bool})
  -> {Nat.mul(WSpec.touch_count(n, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1), 8n) ==
    Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, n, MSpec.C1{g}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +T = PSpec.bit(WSpec.touches(m, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1))
      +C = WSpec.touch_count(m, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1)
      +ML = Impl.mainloop1(G, nsm, H, I, a1, b1, m)
      +F = PSpec.flushes(ML, g)
      +SA = MSpec.sig_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, m), MSpec.C1{g})
      %st_c1(G, nsm, H, I, a1, b1, a2, b2, m, g, w0p, w1p, gp, kpos)
        : {Nat.mul(Nat.add(C, T), 8n) == Nat.add(_, SA) : Nat}
      %Equal.trans(Nat, Nat.mul(T, 8n), Nat.mul(F, 8n), SA,
          Equal.cong(Nat, Nat, t => Nat.mul(t, 8n), T, F,
            Equal.sym(Nat, F, T, wflush(m, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1, w0p, w1p, gp,
              kpos))),
          blk_sig_c1(ML, Mlp.pairs(I), Impl.fin_pair(G, nsm, H, I, a2, b2, m),
            Impl.waits(G, nsm, H, I, a2, b2, m), g))
        : {Nat.mul(Nat.add(C, T), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, T, 8n)

def sig_c1_nc(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +g: Nat,
    +valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{g}) ==
    Nat.mul(8n, Wp.nc(g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1)) : Nat}:
  +T1 = Mlp.total1(H, I)
  +kpos = PP.p2_kt_pos(H, shaped)
  +C = WSpec.touch_count(G, g, Mlp.kt1(H), T1, G, nsm, a1, b1)
  +N = Wp.nc(g, Mlp.kt1(H), T1, G, nsm, a1, b1)
  Equal.trans(Nat, Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{g}), Nat.mul(C, 8n),
    Nat.mul(8n, N),
    Equal.sym(Nat, Nat.mul(C, 8n), Laws.sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{g}),
      st_c1(G, nsm, H, I, a1, b1, a2, b2, G, g, TBP.tv_w0(T1, G, nsm, a1, b1, valid),
        TBP.tv_w1(T1, G, nsm, a1, b1, valid), TBP.tv_g(T1, G, nsm, a1, b1, valid), kpos)),
    Equal.trans(Nat, Nat.mul(C, 8n), Nat.mul(N, 8n), Nat.mul(8n, N),
      Equal.cong(Nat, Nat, t => Nat.mul(t, 8n), C, N,
        WLaws.touch_count_is_nc(Part.groups(2n, I), Mlp.kt1(H), G, nsm, a1, b1, g, valid, kpos, group)),
      PP.ar_mul_comm(N, 8n)))

def Laws.wgate_signals(G, nsm, H, I, a1, b1, a2, b2, p, valid, shaped, pair):
  +np = Mlp.pairs(I)
  sig_c1_nc(G, nsm, H, I, a1, b1, a2, b2, p, valid, shaped,
    PP.ar_lt_le_trans(p, np, Part.groups(2n, I), pair, PP.ar_le_add_r(np, Nat.add(np, 0n))))

def Laws.wup_signals(G, nsm, H, I, a1, b1, a2, b2, p, valid, shaped, pair):
  +np = Mlp.pairs(I)
  sig_c1_nc(G, nsm, H, I, a1, b1, a2, b2, Nat.add(np, p), valid, shaped,
    (%Equal.sym(Bool, Nat.is_lt(Nat.add(np, p), Nat.add(np, Nat.add(np, 0n))),
        Nat.is_lt(p, Nat.add(np, 0n)), PP.ar_lt_add_cancel(np, p, Nat.add(np, 0n)))
        : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.add(np, 0n), np, PP.ar_add_zero_r(np)) : {Nat.is_lt(p, _) == True{} : Bool}
      pair))

# ==== (7) equal weights are the uniform model (lemmas t_*: m16_wsched_tables_proof.bend) ====

def Laws.wuniform(G, nsm, A, H, I, u, w, v, b, g, upos, wpos, vpos, grid, shaped_a, shaped_h, shaped_i):
  +up = upos
  +wp = wpos
  +vp = vpos
  +gp = grid
  (TBP.t_start(b, Tail.total0(A, H), G, nsm, u, up, gp),
    TBP.t_start(b, Mlp.total1(H, I), G, nsm, w, wp, gp),
    TBP.t_start(b, Mlp.total2(H, I), G, nsm, v, vp, gp),
    TBP.t_events(G, nsm, H, I, w, v, b, wp, vp, gp),
    TBP.t_owner(Nat.mul(g, Mlp.kt1(H)), Mlp.total1(H, I), G, nsm, w, wp, gp),
    TBP.t_nc(g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, w, wp, gp),
    TBP.t_nc(g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, v, vp, gp),
    TBP.t_nc(g, Tail.kt0(A), Tail.total0(A, H), G, nsm, u, up, gp))
