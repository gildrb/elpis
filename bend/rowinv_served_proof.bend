# Proofs of bend/rowinv_served_laws.bend. The discharge laws: grid_pos (Nat.max(1, _) >= 1);
# contributors_seqn (the touching blocks below first_contrib, inside [first, last] and above last_contrib,
# from gemm_m16_wpart_laws.contributors_contiguous / contrib_bounds / valid_domain); arrivals_exact and
# perm_reach_step (insertion lemmas: an insertion keeps every element and adds one); barrier_sees_all
# (nc arrivals of 8 counter adds reach 8 nc exactly at the last); splitk_group (those, then
# splitk_finish_asc from gemm_m16_partition_proof's finisher lemmas). The served plan satisfies O_plan
# and O_head fieldwise (attn_stride row_invariant_rounds over grid_S, splitk_group, m16_wsched_tables
# wtail_rows, gdn_ba_ksplit task_value, lmhead o_head_served); the served shapes satisfy the guarded
# path and gather obligations (chain: generically; tree: the 5040 legal shapes decided once by
# evaluation plus attn_tree_laws.path_prefix and gdn_tree_laws.tree_all_shapes); then
# rowinv_link_laws.compose / commit_path give the served ~rinv, its commit step, and the adapters to
# spec_inv / spec_inv_tree. exl3_tree_accept_proof / exl3_tree_derive_proof are imported because
# spec_inv_tree_proof's import of exl3_tree_path_proof leaves the other exl3_tree_accept_laws open.
import Base
import ./rowinv_served_laws.bend as Laws
import ./rowinv_served.bend as Served
import ./rowinv_link.bend as Link
import ./rowinv_link_spec.bend as LSpec
import ./rowinv_link_laws.bend as LinkLaws
import ./rowinv_link_proof.bend as LinkProof
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_proof.bend as GP
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./gemm_m16_wpart_laws.bend as WpL
import ./gemm_m16_wpart_proof.bend as WpP
import ./m16_wsched.bend as Ws
import ./m16_wsched_tables_laws.bend as WsTL
import ./tail_m16_sched_spec.bend as TSpec
import ./tail_m16_sched.bend as Tail
import ./mlp_m16_sched_spec.bend as MSpec
import ./attn_stride.bend as Stride
import ./attn_stride_laws.bend as StrideLaws
import ./gdn_ba_ksplit.bend as Ba
import ./gdn_ba_ksplit_spec.bend as BaS
import ./gdn_ba_ksplit_laws.bend as BaL
import ./attn_tree.bend as AtI
import ./attn_tree_spec.bend as AtS
import ./attn_tree_laws.bend as AtL
import ./attn_tree_proof.bend as AtP
import ./gdn_tree.bend as GtI
import ./gdn_tree_spec.bend as GtS
import ./gdn_tree_laws.bend as GtL
import ./gdn_tree_proof.bend as GtP
import ./exl3_tree_accept_spec.bend as TAS
import ./spec_inv_tree.bend as SIT
import ./spec_inv_tree_laws.bend as SITL
import ./spec_inv_tree_proof.bend as SITP
import ./spec_inv_spec.bend as SIS
import ./spec_inv.bend as SIC
import ./spec_inv_laws.bend as SIL
import ./spec_inv_proof.bend as SIP
import ./gdn_ba_ksplit_proof.bend as BaP
import ./attn_stride_proof.bend as StrideP
import ./m16_wsched_tables_proof.bend as WsTP
import ./lmhead.bend as Lm
import ./lmhead_laws.bend as LmL
import ./lmhead_proof.bend as LmP
import ./exl3_tree_accept_proof.bend as TAP
import ./exl3_tree_derive_proof.bend as TDP

# ---------------------------------------------------------------- conjunction projections

def fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# ---------------------------------------------------------------- the split-K finisher (new law)

def sv_only_ge(order: List<&2, Nat>, +lo: Nat) -> {Served.arr_only(order, lo) == GP.p4_all_ge(order, lo) : Bool}:
  match order:
    case Nil{}:
      {==}
    case +a <> rest:
      Equal.cong(Bool, Bool, y => Bool.and(Nat.is_le(lo, a), y), Served.arr_only(rest, lo), GP.p4_all_ge(rest, lo), sv_only_ge(rest, lo))

def sv_all_arr(k: Nat, +b: Nat, +order: List<&2, Nat>) -> {Served.arr_all(k, b, order) == GP.p4_all_arr(k, b, order) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      Equal.cong(Bool, Bool, y => Bool.and(PSpec.arrived(order, b), y), Served.arr_all(k1, 1n+b, order), GP.p4_all_arr(k1, 1n+b, order),
        sv_all_arr(k1, 1n+b, order))

def sv_asc(k: Nat, +b: Nat, +v: PSpec.Sum) -> {Served.asc.go(k, b, v) == GP.p4_asc(k, b, v) : PSpec.Sum}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      sv_asc(k1, 1n+b, PSpec.Add{v, PSpec.Part{b}})

def Laws.splitk_finish_asc(order, ws, lo, nc, only, all, room, pos):
  match nc:
    case 0n:
      Empty.absurd({Part.finish(Part.arrive(order, ws, lo), 0n) == Served.asc(0n, lo) : PSpec.Sum}, GP.ar_false_true(pos))
    case 1n+k:
      +k = k
      +all2 = all
      +room2 = room
      +hall = Equal.trans(Bool, GP.p4_all_ge(order, lo), Served.arr_only(order, lo), True{},
        Equal.sym(Bool, Served.arr_only(order, lo), GP.p4_all_ge(order, lo), sv_only_ge(order, lo)), only)
      +harr0 = GP.ar_and_l(PSpec.arrived(order, lo), Served.arr_all(k, 1n+lo, order), all2)
      +harr1 = Equal.trans(Bool, GP.p4_all_arr(k, 1n+lo, order), Served.arr_all(k, 1n+lo, order), True{},
        Equal.sym(Bool, Served.arr_all(k, 1n+lo, order), GP.p4_all_arr(k, 1n+lo, order), sv_all_arr(k, 1n+lo, order)),
        GP.ar_and_r(PSpec.arrived(order, lo), Served.arr_all(k, 1n+lo, order), all2))
      +hlen0 = GP.ar_lt_le_trans(0n, 1n+k, List.length(&2, PSpec.Sum, ws), {==}, room2)
      +hlenk = Equal.trans(Bool, Nat.is_le(Nat.add(k, 1n), List.length(&2, PSpec.Sum, ws)),
        Nat.is_le(1n+k, List.length(&2, PSpec.Sum, ws)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_le(z, List.length(&2, PSpec.Sum, ws)), Nat.add(k, 1n), 1n+k,
          Equal.trans(Nat, Nat.add(k, 1n), 1n+Nat.add(k, 0n), 1n+k, GP.ar_add_succ_r(k, 0n),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, 0n), k, GP.ar_add_zero_r(k)))),
        room2)
      +s0 = GP.p4_slot_c(0n, order, ws, lo, hall, harr0, hlen0)
      +fin = GP.p4_fin(k, 1n, PSpec.Part{lo}, order, ws, lo, hall, harr1, hlenk)
      %Equal.sym(Nat, Nat.sub(k, 0n), k, GP.ar_sub_zero_r(k)) : {Part.finish.go(_, 1n, Part.slot_at(Part.arrive(order, ws, lo), 0n), Part.arrive(order, ws, lo)) ==
        Served.asc.go(_, 1n+lo, PSpec.Part{lo}) : PSpec.Sum}
      %Equal.sym(PSpec.Sum, Part.slot_at(Part.arrive(order, ws, lo), 0n), PSpec.Part{lo}, s0) :
        {Part.finish.go(k, 1n, _, Part.arrive(order, ws, lo)) == Served.asc.go(k, 1n+lo, PSpec.Part{lo}) : PSpec.Sum}
      Equal.trans(PSpec.Sum, Part.finish.go(k, 1n, PSpec.Part{lo}, Part.arrive(order, ws, lo)), GP.p4_asc(k, 1n+lo, PSpec.Part{lo}),
        Served.asc.go(k, 1n+lo, PSpec.Part{lo}), fin,
        Equal.sym(PSpec.Sum, Served.asc.go(k, 1n+lo, PSpec.Part{lo}), GP.p4_asc(k, 1n+lo, PSpec.Part{lo}), sv_asc(k, 1n+lo, PSpec.Part{lo})))

# ---------------------------------------------------------------- 5106: relabelling the row's operands

def sv_chain_el(c: Bool, +j: Nat, +s: Nat, +row: Nat, +k2: Nat, +acc: Ba.Ex)
  -> {Served.unshift(BaS.chain_el(c, j, s, row, k2, acc), Nat.mul(s, k2)) == BaS.chain_el(c, j, 0n, row, k2, Served.unshift(acc, Nat.mul(s, k2))) : Ba.Ex}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(s, k2), j), Nat.mul(s, k2)), j, GP.ar_add_sub(Nat.mul(s, k2), j)) :
        {Ba.Fma{_, Nat.add(Nat.mul(row, k2), j), 1n, Ba.Fma{_, Nat.add(Nat.mul(row, k2), j), 0n, Served.unshift(acc, Nat.mul(s, k2))}} ==
          Ba.Fma{j, Nat.add(Nat.mul(row, k2), j), 1n, Ba.Fma{j, Nat.add(Nat.mul(row, k2), j), 0n, Served.unshift(acc, Nat.mul(s, k2))}} : Ba.Ex}
      {==}
    case False{}:
      {==}

def sv_chain_go(fuel: Nat, +j: Nat, +s: Nat, +row: Nat, +k2: Nat, +acc: Ba.Ex)
  -> {Served.unshift(BaS.chain_go(fuel, j, s, row, k2, acc), Nat.mul(s, k2)) == BaS.chain_go(fuel, j, 0n, row, k2, Served.unshift(acc, Nat.mul(s, k2))) : Ba.Ex}:
  match fuel:
    case 0n:
      {==}
    case 1n+more:
      Equal.trans(Ba.Ex, Served.unshift(BaS.chain_go(more, Nat.add(j, 512n), s, row, k2, BaS.chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc)), Nat.mul(s, k2)),
        BaS.chain_go(more, Nat.add(j, 512n), 0n, row, k2, Served.unshift(BaS.chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc), Nat.mul(s, k2))),
        BaS.chain_go(more, Nat.add(j, 512n), 0n, row, k2, BaS.chain_el(Nat.is_lt(j, k2), j, 0n, row, k2, Served.unshift(acc, Nat.mul(s, k2)))),
        sv_chain_go(more, Nat.add(j, 512n), s, row, k2, BaS.chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc)),
        Equal.cong(Ba.Ex, Ba.Ex, y => BaS.chain_go(more, Nat.add(j, 512n), 0n, row, k2, y),
          Served.unshift(BaS.chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc), Nat.mul(s, k2)),
          BaS.chain_el(Nat.is_lt(j, k2), j, 0n, row, k2, Served.unshift(acc, Nat.mul(s, k2))),
          sv_chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc)))

def sv_wtree(n: Nat, +l: Nat, +w: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat)
  -> {Served.unshift(BaS.wtree(n, l, w, s, ab, k2, h, H), Nat.mul(s, k2)) == BaS.wtree(n, l, w, 0n, ab, k2, h, H) : Ba.Ex}:
  match n:
    case 0n:
      sv_chain_go(5n, Nat.add(Nat.mul(w, 32n), l), s, BaS.wrow(ab, h, H), k2, Ba.ZeroF{})
    case 1n+m:
      +m = m
      %Equal.sym(Ba.Ex, Served.unshift(BaS.wtree(m, l, w, s, ab, k2, h, H), Nat.mul(s, k2)), BaS.wtree(m, l, w, 0n, ab, k2, h, H), sv_wtree(m, l, w, s, ab, k2, h, H)) :
        {Ba.Add{_, Served.unshift(BaS.wtree(m, Nat.add(l, BaS.off(1n+m)), w, s, ab, k2, h, H), Nat.mul(s, k2))} ==
          Ba.Add{BaS.wtree(m, l, w, 0n, ab, k2, h, H), BaS.wtree(m, Nat.add(l, BaS.off(1n+m)), w, 0n, ab, k2, h, H)} : Ba.Ex}
      %Equal.sym(Ba.Ex, Served.unshift(BaS.wtree(m, Nat.add(l, BaS.off(1n+m)), w, s, ab, k2, h, H), Nat.mul(s, k2)),
          BaS.wtree(m, Nat.add(l, BaS.off(1n+m)), w, 0n, ab, k2, h, H), sv_wtree(m, Nat.add(l, BaS.off(1n+m)), w, s, ab, k2, h, H)) :
        {Ba.Add{BaS.wtree(m, l, w, 0n, ab, k2, h, H), _} ==
          Ba.Add{BaS.wtree(m, l, w, 0n, ab, k2, h, H), BaS.wtree(m, Nat.add(l, BaS.off(1n+m)), w, 0n, ab, k2, h, H)} : Ba.Ex}
      {==}

def sv_wfold(fuel: Nat, +w: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, +v: Ba.Ex)
  -> {Served.unshift(BaS.wfold(fuel, w, s, ab, k2, h, H, v), Nat.mul(s, k2)) == BaS.wfold(fuel, w, 0n, ab, k2, h, H, Served.unshift(v, Nat.mul(s, k2))) : Ba.Ex}:
  match fuel:
    case 0n:
      {==}
    case 1n+more:
      Equal.trans(Ba.Ex, Served.unshift(BaS.wfold(more, 1n+w, s, ab, k2, h, H, Ba.Add{v, BaS.wtree(5n, 0n, w, s, ab, k2, h, H)}), Nat.mul(s, k2)),
        BaS.wfold(more, 1n+w, 0n, ab, k2, h, H, Served.unshift(Ba.Add{v, BaS.wtree(5n, 0n, w, s, ab, k2, h, H)}, Nat.mul(s, k2))),
        BaS.wfold(more, 1n+w, 0n, ab, k2, h, H, Ba.Add{Served.unshift(v, Nat.mul(s, k2)), BaS.wtree(5n, 0n, w, 0n, ab, k2, h, H)}),
        sv_wfold(more, 1n+w, s, ab, k2, h, H, Ba.Add{v, BaS.wtree(5n, 0n, w, s, ab, k2, h, H)}),
        Equal.cong(Ba.Ex, Ba.Ex, y => BaS.wfold(more, 1n+w, 0n, ab, k2, h, H, Ba.Add{Served.unshift(v, Nat.mul(s, k2)), y}),
          Served.unshift(BaS.wtree(5n, 0n, w, s, ab, k2, h, H), Nat.mul(s, k2)), BaS.wtree(5n, 0n, w, 0n, ab, k2, h, H),
          sv_wtree(5n, 0n, w, s, ab, k2, h, H)))

def sv_bias(hb: Bool, +o: Nat, +v: Ba.Ex, +off: Nat)
  -> {Served.unshift(Ba.with_bias(hb, o, v), off) == Ba.with_bias(hb, o, Served.unshift(v, off)) : Ba.Ex}:
  match hb:
    case True{}:
      {==}
    case False{}:
      {==}

# The row-s b/a value, relabelled to operand row 0, is the row-0 value.
def sv_value(+s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, +hb: Bool)
  -> {Served.unshift(BaS.value(s, ab, k2, h, H, hb), Nat.mul(s, k2)) == BaS.value(0n, ab, k2, h, H, hb) : Ba.Ex}:
  Equal.trans(Ba.Ex, Served.unshift(BaS.value(s, ab, k2, h, H, hb), Nat.mul(s, k2)),
    Ba.with_bias(hb, BaS.wrow(ab, h, H), Served.unshift(BaS.wfold(16n, 0n, s, ab, k2, h, H, Ba.ZeroF{}), Nat.mul(s, k2))),
    BaS.value(0n, ab, k2, h, H, hb),
    sv_bias(hb, BaS.wrow(ab, h, H), BaS.wfold(16n, 0n, s, ab, k2, h, H, Ba.ZeroF{}), Nat.mul(s, k2)),
    Equal.cong(Ba.Ex, Ba.Ex, y => Ba.with_bias(hb, BaS.wrow(ab, h, H), y),
      Served.unshift(BaS.wfold(16n, 0n, s, ab, k2, h, H, Ba.ZeroF{}), Nat.mul(s, k2)), BaS.wfold(16n, 0n, 0n, ab, k2, h, H, Ba.ZeroF{}),
      sv_wfold(16n, 0n, s, ab, k2, h, H, Ba.ZeroF{})))

# One b/a task of row r in an m-row launch (r < m <= 8), relabelled, is row 0's in a 1-row launch.
def sv_task(+m: Nat, +r: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, +hb: Bool, +rm: {Nat.is_lt(r, m) == True{} : Bool},
    +r8: {Nat.is_lt(r, 8n) == True{} : Bool}, +a2: {Nat.is_lt(ab, 2n) == True{} : Bool})
  -> {Served.unshift(Ba.task(m, r, ab, k2, h, H, hb), Nat.mul(r, k2)) == Served.unshift(Ba.task(1n, 0n, ab, k2, h, H, hb), Nat.mul(0n, k2)) : Ba.Ex}:
  Equal.trans(Ba.Ex, Served.unshift(Ba.task(m, r, ab, k2, h, H, hb), Nat.mul(r, k2)), BaS.value(0n, ab, k2, h, H, hb),
    Served.unshift(Ba.task(1n, 0n, ab, k2, h, H, hb), Nat.mul(0n, k2)),
    Equal.trans(Ba.Ex, Served.unshift(Ba.task(m, r, ab, k2, h, H, hb), Nat.mul(r, k2)), Served.unshift(BaS.value(r, ab, k2, h, H, hb), Nat.mul(r, k2)),
      BaS.value(0n, ab, k2, h, H, hb),
      Equal.cong(Ba.Ex, Ba.Ex, y => Served.unshift(y, Nat.mul(r, k2)), Ba.task(m, r, ab, k2, h, H, hb), BaS.value(r, ab, k2, h, H, hb),
        BaL.task_value(m, r, ab, k2, h, H, hb, rm, r8, a2)),
      sv_value(r, ab, k2, h, H, hb)),
    Equal.sym(Ba.Ex, Served.unshift(Ba.task(1n, 0n, ab, k2, h, H, hb), Nat.mul(0n, k2)), BaS.value(0n, ab, k2, h, H, hb),
      Equal.trans(Ba.Ex, Served.unshift(Ba.task(1n, 0n, ab, k2, h, H, hb), Nat.mul(0n, k2)), Served.unshift(BaS.value(0n, ab, k2, h, H, hb), Nat.mul(0n, k2)),
        BaS.value(0n, ab, k2, h, H, hb),
        Equal.cong(Ba.Ex, Ba.Ex, y => Served.unshift(y, Nat.mul(0n, k2)), Ba.task(1n, 0n, ab, k2, h, H, hb), BaS.value(0n, ab, k2, h, H, hb),
          BaL.task_value(1n, 0n, ab, k2, h, H, hb, {==}, {==}, a2)),
        sv_value(0n, ab, k2, h, H, hb))))

def sv_ba_tab(k: Nat, +h: Nat, +m: Nat, +r: Nat, +k2: Nat, +H: Nat, +hb: Bool, +rm: {Nat.is_lt(r, m) == True{} : Bool},
    +r8: {Nat.is_lt(r, 8n) == True{} : Bool})
  -> {Served.ba_tab(k, h, m, r, k2, H, hb) == Served.ba_tab(k, h, 1n, 0n, k2, H, hb) : List<&2, Ba.Ex>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      LinkProof.ri_cong_cons(~Ba.Ex, Served.unshift(Ba.task(m, r, 0n, k2, h, H, hb), Nat.mul(r, k2)),
        Served.unshift(Ba.task(1n, 0n, 0n, k2, h, H, hb), Nat.mul(0n, k2)),
        Served.unshift(Ba.task(m, r, 1n, k2, h, H, hb), Nat.mul(r, k2)) <> Served.ba_tab(k1, 1n+h, m, r, k2, H, hb),
        Served.unshift(Ba.task(1n, 0n, 1n, k2, h, H, hb), Nat.mul(0n, k2)) <> Served.ba_tab(k1, 1n+h, 1n, 0n, k2, H, hb),
        sv_task(m, r, 0n, k2, h, H, hb, rm, r8, {==}),
        LinkProof.ri_cong_cons(~Ba.Ex, Served.unshift(Ba.task(m, r, 1n, k2, h, H, hb), Nat.mul(r, k2)),
          Served.unshift(Ba.task(1n, 0n, 1n, k2, h, H, hb), Nat.mul(0n, k2)),
          Served.ba_tab(k1, 1n+h, m, r, k2, H, hb), Served.ba_tab(k1, 1n+h, 1n, 0n, k2, H, hb),
          sv_task(m, r, 1n, k2, h, H, hb, rm, r8, {==}), sv_ba_tab(k1, 1n+h, m, r, k2, H, hb, rm, r8)))

# ---------------------------------------------------------------- 3006: the tile plan

def sv_tp(k: Nat, +p0: Nat, +x: Nat, +it: Nat, +d1: Nat, +q1: Nat, +j1: Nat, +d2: Nat, +q2: Nat, +j2: Nat, +S: Nat,
    +xb: {Nat.is_lt(x, S) == True{} : Bool}, +row1: {Nat.is_lt(j1, q1) == True{} : Bool}, +row2: {Nat.is_lt(j2, q2) == True{} : Bool},
    +same: {Nat.add(d1, j1) == Nat.add(d2, j2) : Nat})
  -> {Served.tiles_p(k, p0, x, it, Nat.add(d1, q1), S, q1, j1) == Served.tiles_p(k, p0, x, it, Nat.add(d2, q2), S, q2, j2) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +t1 = fst({Stride.tile_hits(x, it, p0, Nat.add(d1, q1), S, q1, j1) == Stride.tile_hits(x, it, p0, Nat.add(d2, q2), S, q2, j2) : Nat},
        {Stride.cta_hits(x, p0, Nat.add(d1, q1), S, q1, j1) == Stride.cta_hits(x, p0, Nat.add(d2, q2), S, q2, j2) : Nat} &
        {Stride.merged(Nat.add(d1, q1), S, q1, j1) == Stride.merged(Nat.add(d2, q2), S, q2, j2) : List<&2, Nat>},
        StrideLaws.row_invariant_rounds(d1, q1, j1, d2, q2, j2, S, x, it, p0, xb, row1, row2, same))
      LinkProof.ri_cong_cons(~Nat, Stride.tile_hits(x, it, p0, Nat.add(d1, q1), S, q1, j1), Stride.tile_hits(x, it, p0, Nat.add(d2, q2), S, q2, j2),
        Served.tiles_p(k1, 1n+p0, x, it, Nat.add(d1, q1), S, q1, j1), Served.tiles_p(k1, 1n+p0, x, it, Nat.add(d2, q2), S, q2, j2),
        t1, sv_tp(k1, 1n+p0, x, it, d1, q1, j1, d2, q2, j2, S, xb, row1, row2, same))

def sv_ti(k: Nat, +it0: Nat, +x: Nat, +d1: Nat, +q1: Nat, +j1: Nat, +d2: Nat, +q2: Nat, +j2: Nat, +S: Nat, +A1: Nat,
    +xb: {Nat.is_lt(x, S) == True{} : Bool}, +row1: {Nat.is_lt(j1, q1) == True{} : Bool}, +row2: {Nat.is_lt(j2, q2) == True{} : Bool},
    +same: {Nat.add(d1, j1) == Nat.add(d2, j2) : Nat})
  -> {Served.tiles_it(k, it0, x, Nat.add(d1, q1), S, q1, j1, A1) == Served.tiles_it(k, it0, x, Nat.add(d2, q2), S, q2, j2, A1) : List<&2, List<&2, Nat>>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      LinkProof.ri_cong_cons(~List<&2, Nat>, Served.tiles_p(A1, 0n, x, it0, Nat.add(d1, q1), S, q1, j1), Served.tiles_p(A1, 0n, x, it0, Nat.add(d2, q2), S, q2, j2),
        Served.tiles_it(k1, 1n+it0, x, Nat.add(d1, q1), S, q1, j1, A1), Served.tiles_it(k1, 1n+it0, x, Nat.add(d2, q2), S, q2, j2, A1),
        sv_tp(A1, 0n, x, it0, d1, q1, j1, d2, q2, j2, S, xb, row1, row2, same),
        sv_ti(k1, 1n+it0, x, d1, q1, j1, d2, q2, j2, S, A1, xb, row1, row2, same))

def sv_tx(k: Nat, +x0: Nat, +d1: Nat, +q1: Nat, +j1: Nat, +d2: Nat, +q2: Nat, +j2: Nat, +S: Nat, +A1: Nat,
    +hb: {Nat.is_le(Nat.add(x0, k), S) == True{} : Bool}, +row1: {Nat.is_lt(j1, q1) == True{} : Bool}, +row2: {Nat.is_lt(j2, q2) == True{} : Bool},
    +same: {Nat.add(d1, j1) == Nat.add(d2, j2) : Nat})
  -> {Served.tiles_x(k, x0, Nat.add(d1, q1), S, q1, j1, A1) == Served.tiles_x(k, x0, Nat.add(d2, q2), S, q2, j2, A1) : List<&2, List<&2, List<&2, Nat>>>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +xb = GP.ar_lt_le_trans(x0, Nat.add(x0, 1n+k1), S, LinkProof.ri_lt_add(x0, k1), hb)
      +hb2 = Equal.trans(Bool, Nat.is_le(Nat.add(1n+x0, k1), S), Nat.is_le(Nat.add(x0, 1n+k1), S), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, S), 1n+Nat.add(x0, k1), Nat.add(x0, 1n+k1), LinkProof.ri_sr(x0, k1)), hb)
      LinkProof.ri_cong_cons(~List<&2, List<&2, Nat>>, Served.tiles_it(A1, 0n, x0, Nat.add(d1, q1), S, q1, j1, A1),
        Served.tiles_it(A1, 0n, x0, Nat.add(d2, q2), S, q2, j2, A1),
        Served.tiles_x(k1, 1n+x0, Nat.add(d1, q1), S, q1, j1, A1), Served.tiles_x(k1, 1n+x0, Nat.add(d2, q2), S, q2, j2, A1),
        sv_ti(A1, 0n, x0, d1, q1, j1, d2, q2, j2, S, A1, xb, row1, row2, same),
        sv_tx(k1, 1n+x0, d1, q1, j1, d2, q2, j2, S, A1, hb2, row1, row2, same))

# ---------------------------------------------------------------- chain rounds: paths 0 .. r, gathers 0 .. r - 1

def sq_len(k: Nat, +s: Nat) -> {List.length(&2, Nat, Served.seqn(k, s)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, Nat, Served.seqn(k1, 1n+s)), k1, sq_len(k1, 1n+s))

def sq_snoc(k: Nat, +s: Nat) -> {Served.seqn(1n+k, s) == List.append(&2, Nat, Served.seqn(k, s), [Nat.add(s, k)]) : List<&2, Nat>}:
  match k:
    case 0n:
      %LinkProof.ri_zr(s) : {[s] == [_] : List<&2, Nat>}
      {==}
    case 1n+k1:
      +k1 = k1
      %LinkProof.ri_sr(s, k1) :
        {s <> Served.seqn(1n+k1, 1n+s) == s <> List.append(&2, Nat, Served.seqn(k1, 1n+s), [_]) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => s <> y, Served.seqn(1n+k1, 1n+s),
        List.append(&2, Nat, Served.seqn(k1, 1n+s), [Nat.add(1n+s, k1)]), sq_snoc(k1, 1n+s))

def sq_take(k: Nat, +s: Nat, +j: Nat, h: {Nat.is_le(j, k) == True{} : Bool})
  -> {List.take(&2, Nat, Served.seqn(k, s), j) == Served.seqn(j, s) : List<&2, Nat>}:
  match k:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+j1:
          Empty.absurd({List.take(&2, Nat, Nil{}, 1n+j1) == Served.seqn(1n+j1, s) : List<&2, Nat>}, GP.ar_false_true(h))
    case 1n+k1:
      match j:
        case 0n:
          {==}
        case 1n+j1:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, y => s <> y, List.take(&2, Nat, Served.seqn(k1, 1n+s), j1), Served.seqn(j1, 1n+s),
            sq_take(k1, 1n+s, j1, h))

def sq_nth(k: Nat, +s: Nat, +j: Nat, h: {Nat.is_lt(j, k) == True{} : Bool})
  -> {Link.nthn(Served.seqn(k, s), j) == Nat.add(s, j) : Nat}:
  match k:
    case 0n:
      Empty.absurd({Link.nthn(Nil{}, j) == Nat.add(s, j) : Nat}, LinkProof.ri_lt_zero(j, h))
    case 1n+k1:
      match j:
        case 0n:
          LinkProof.ri_zr(s)
        case 1n+j1:
          Equal.trans(Nat, Link.nthn(Served.seqn(k1, 1n+s), j1), Nat.add(1n+s, j1), Nat.add(s, 1n+j1), sq_nth(k1, 1n+s, j1, h),
            LinkProof.ri_sr(s, j1))

# dep(Chain, r) == r
def sq_dep(+r: Nat) -> {Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r) == r : Nat}:
  %Equal.sym(Nat, List.length(&2, Nat, Served.seqn(1n+r, 0n)), 1n+r, sq_len(1n+r, 0n)) : {Nat.sub(_, 1n) == r : Nat}
  GP.ar_sub_zero_r(r)

# ---------------------------------------------------------------- Bool algebra

def sd_or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sd_or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sd_and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sd_and_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(b, Bool.and(a, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Bool, Bool.and(b, False{}), False{}, sd_and_false(b))

def sd_and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sd_or_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, Bool.or(b, True{}), True{}, sd_or_true(b))
    case False{}:
      {==}

def sd_or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sd_not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, GP.ar_false_true(h))
    case False{}:
      {==}

# a < b  ->  b <= a is False
def sd_lt_nle(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  sd_not_true(Nat.is_le(b, a), Equal.trans(Bool, Bool.not(Nat.is_le(b, a)), Nat.is_lt(a, b), True{},
    Equal.sym(Bool, Nat.is_lt(a, b), Bool.not(Nat.is_le(b, a)), GP.ar_lt_not_le(a, b)), h))

# ---------------------------------------------------------------- the scheduler's arrival orders

def sd_ins_len(xs: List<&2, Nat>, +i: Nat, +x: Nat) -> {List.length(&2, Nat, Served.ins_at(xs, i, x)) == 1n+List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, Served.ins_at(rest, j, x)), 1n+List.length(&2, Nat, rest), sd_ins_len(rest, j, x))

def sd_ins_only(xs: List<&2, Nat>, +i: Nat, +x: Nat, +lo: Nat)
  -> {Served.arr_only(Served.ins_at(xs, i, x), lo) == Bool.and(Nat.is_le(lo, x), Served.arr_only(xs, lo)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Equal.trans(Bool, Bool.and(Nat.is_le(lo, y), Served.arr_only(Served.ins_at(rest, j, x), lo)),
            Bool.and(Nat.is_le(lo, y), Bool.and(Nat.is_le(lo, x), Served.arr_only(rest, lo))),
            Bool.and(Nat.is_le(lo, x), Bool.and(Nat.is_le(lo, y), Served.arr_only(rest, lo))),
            Equal.cong(Bool, Bool, z => Bool.and(Nat.is_le(lo, y), z), Served.arr_only(Served.ins_at(rest, j, x), lo),
              Bool.and(Nat.is_le(lo, x), Served.arr_only(rest, lo)), sd_ins_only(rest, j, x, lo)),
            sd_and_swap(Nat.is_le(lo, y), Nat.is_le(lo, x), Served.arr_only(rest, lo)))

def sd_ins_arr(xs: List<&2, Nat>, +i: Nat, +x: Nat, +y: Nat)
  -> {PSpec.arrived(Served.ins_at(xs, i, x), y) == Bool.or(Nat.is_eq(x, y), PSpec.arrived(xs, y)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          Equal.trans(Bool, Bool.or(Nat.is_eq(a, y), PSpec.arrived(Served.ins_at(rest, j, x), y)),
            Bool.or(Nat.is_eq(a, y), Bool.or(Nat.is_eq(x, y), PSpec.arrived(rest, y))),
            Bool.or(Nat.is_eq(x, y), Bool.or(Nat.is_eq(a, y), PSpec.arrived(rest, y))),
            Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(a, y), z), PSpec.arrived(Served.ins_at(rest, j, x), y),
              Bool.or(Nat.is_eq(x, y), PSpec.arrived(rest, y)), sd_ins_arr(rest, j, x, y)),
            sd_or_swap(Nat.is_eq(a, y), Nat.is_eq(x, y), PSpec.arrived(rest, y)))

def sd_perm_len(cs: List<&2, Nat>, +ix: List<&2, Nat>, +acc: List<&2, Nat>)
  -> {List.length(&2, Nat, Served.perm(cs, ix, acc)) == Nat.add(List.length(&2, Nat, cs), List.length(&2, Nat, acc)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      +acc2 = Served.ins_at(acc, Served.ix_hd(ix), c)
      Equal.trans(Nat, List.length(&2, Nat, Served.perm(rest, Served.ix_tl(ix), acc2)),
        Nat.add(List.length(&2, Nat, rest), List.length(&2, Nat, acc2)),
        1n+Nat.add(List.length(&2, Nat, rest), List.length(&2, Nat, acc)),
        sd_perm_len(rest, Served.ix_tl(ix), acc2),
        Equal.trans(Nat, Nat.add(List.length(&2, Nat, rest), List.length(&2, Nat, acc2)),
          Nat.add(List.length(&2, Nat, rest), 1n+List.length(&2, Nat, acc)),
          1n+Nat.add(List.length(&2, Nat, rest), List.length(&2, Nat, acc)),
          Equal.cong(Nat, Nat, z => Nat.add(List.length(&2, Nat, rest), z), List.length(&2, Nat, acc2), 1n+List.length(&2, Nat, acc),
            sd_ins_len(acc, Served.ix_hd(ix), c)),
          GP.ar_add_succ_r(List.length(&2, Nat, rest), List.length(&2, Nat, acc))))

def sd_perm_only(cs: List<&2, Nat>, +ix: List<&2, Nat>, +acc: List<&2, Nat>, +lo: Nat)
  -> {Served.arr_only(Served.perm(cs, ix, acc), lo) == Bool.and(Served.arr_only(cs, lo), Served.arr_only(acc, lo)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      +acc2 = Served.ins_at(acc, Served.ix_hd(ix), c)
      Equal.trans(Bool, Served.arr_only(Served.perm(rest, Served.ix_tl(ix), acc2), lo),
        Bool.and(Served.arr_only(rest, lo), Served.arr_only(acc2, lo)),
        Bool.and(Bool.and(Nat.is_le(lo, c), Served.arr_only(rest, lo)), Served.arr_only(acc, lo)),
        sd_perm_only(rest, Served.ix_tl(ix), acc2, lo),
        Equal.trans(Bool, Bool.and(Served.arr_only(rest, lo), Served.arr_only(acc2, lo)),
          Bool.and(Served.arr_only(rest, lo), Bool.and(Nat.is_le(lo, c), Served.arr_only(acc, lo))),
          Bool.and(Bool.and(Nat.is_le(lo, c), Served.arr_only(rest, lo)), Served.arr_only(acc, lo)),
          Equal.cong(Bool, Bool, z => Bool.and(Served.arr_only(rest, lo), z), Served.arr_only(acc2, lo),
            Bool.and(Nat.is_le(lo, c), Served.arr_only(acc, lo)), sd_ins_only(acc, Served.ix_hd(ix), c, lo)),
          Equal.trans(Bool, Bool.and(Served.arr_only(rest, lo), Bool.and(Nat.is_le(lo, c), Served.arr_only(acc, lo))),
            Bool.and(Nat.is_le(lo, c), Bool.and(Served.arr_only(rest, lo), Served.arr_only(acc, lo))),
            Bool.and(Bool.and(Nat.is_le(lo, c), Served.arr_only(rest, lo)), Served.arr_only(acc, lo)),
            sd_and_swap(Served.arr_only(rest, lo), Nat.is_le(lo, c), Served.arr_only(acc, lo)),
            Equal.sym(Bool, Bool.and(Bool.and(Nat.is_le(lo, c), Served.arr_only(rest, lo)), Served.arr_only(acc, lo)),
              Bool.and(Nat.is_le(lo, c), Bool.and(Served.arr_only(rest, lo), Served.arr_only(acc, lo))),
              sd_and_assoc(Nat.is_le(lo, c), Served.arr_only(rest, lo), Served.arr_only(acc, lo))))))

def sd_perm_arr(cs: List<&2, Nat>, +ix: List<&2, Nat>, +acc: List<&2, Nat>, +y: Nat)
  -> {PSpec.arrived(Served.perm(cs, ix, acc), y) == Bool.or(PSpec.arrived(cs, y), PSpec.arrived(acc, y)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      +acc2 = Served.ins_at(acc, Served.ix_hd(ix), c)
      Equal.trans(Bool, PSpec.arrived(Served.perm(rest, Served.ix_tl(ix), acc2), y),
        Bool.or(PSpec.arrived(rest, y), PSpec.arrived(acc2, y)),
        Bool.or(Bool.or(Nat.is_eq(c, y), PSpec.arrived(rest, y)), PSpec.arrived(acc, y)),
        sd_perm_arr(rest, Served.ix_tl(ix), acc2, y),
        Equal.trans(Bool, Bool.or(PSpec.arrived(rest, y), PSpec.arrived(acc2, y)),
          Bool.or(PSpec.arrived(rest, y), Bool.or(Nat.is_eq(c, y), PSpec.arrived(acc, y))),
          Bool.or(Bool.or(Nat.is_eq(c, y), PSpec.arrived(rest, y)), PSpec.arrived(acc, y)),
          Equal.cong(Bool, Bool, z => Bool.or(PSpec.arrived(rest, y), z), PSpec.arrived(acc2, y),
            Bool.or(Nat.is_eq(c, y), PSpec.arrived(acc, y)), sd_ins_arr(acc, Served.ix_hd(ix), c, y)),
          Equal.trans(Bool, Bool.or(PSpec.arrived(rest, y), Bool.or(Nat.is_eq(c, y), PSpec.arrived(acc, y))),
            Bool.or(Nat.is_eq(c, y), Bool.or(PSpec.arrived(rest, y), PSpec.arrived(acc, y))),
            Bool.or(Bool.or(Nat.is_eq(c, y), PSpec.arrived(rest, y)), PSpec.arrived(acc, y)),
            sd_or_swap(PSpec.arrived(rest, y), Nat.is_eq(c, y), PSpec.arrived(acc, y)),
            Equal.sym(Bool, Bool.or(Bool.or(Nat.is_eq(c, y), PSpec.arrived(rest, y)), PSpec.arrived(acc, y)),
              Bool.or(Nat.is_eq(c, y), Bool.or(PSpec.arrived(rest, y), PSpec.arrived(acc, y))),
              sd_or_assoc(Nat.is_eq(c, y), PSpec.arrived(rest, y), PSpec.arrived(acc, y))))))

def sd_all_perm(k: Nat, +b: Nat, +cs: List<&2, Nat>, +ix: List<&2, Nat>)
  -> {Served.arr_all(k, b, Served.perm(cs, ix, Nil{})) == Served.arr_all(k, b, cs) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +P = Served.perm(cs, ix, Nil{})
      +e1 = Equal.trans(Bool, PSpec.arrived(P, b), Bool.or(PSpec.arrived(cs, b), False{}), PSpec.arrived(cs, b),
        sd_perm_arr(cs, ix, Nil{}, b), sd_or_false(PSpec.arrived(cs, b)))
      %e1 : {Bool.and(PSpec.arrived(P, b), Served.arr_all(k1, 1n+b, P)) == Bool.and(_, Served.arr_all(k1, 1n+b, cs)) : Bool}
      %sd_all_perm(k1, 1n+b, cs, ix) : {Bool.and(PSpec.arrived(P, b), Served.arr_all(k1, 1n+b, P)) == Bool.and(PSpec.arrived(P, b), _) : Bool}
      {==}

def sd_all_cons(k: Nat, +b: Nat, +x: Nat, +xs: List<&2, Nat>, h: {Served.arr_all(k, b, xs) == True{} : Bool})
  -> {Served.arr_all(k, b, x <> xs) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +h2 = h
      +ha = GP.ar_and_l(PSpec.arrived(xs, b), Served.arr_all(k1, 1n+b, xs), h2)
      +hb = sd_all_cons(k1, 1n+b, x, xs, GP.ar_and_r(PSpec.arrived(xs, b), Served.arr_all(k1, 1n+b, xs), h2))
      %Equal.sym(Bool, PSpec.arrived(xs, b), True{}, ha) :
        {Bool.and(Bool.or(Nat.is_eq(x, b), _), Served.arr_all(k1, 1n+b, x <> xs)) == True{} : Bool}
      %Equal.sym(Bool, Bool.or(Nat.is_eq(x, b), True{}), True{}, sd_or_true(Nat.is_eq(x, b))) :
        {Bool.and(_, Served.arr_all(k1, 1n+b, x <> xs)) == True{} : Bool}
      hb

def sd_all_seqn(n: Nat, +s: Nat) -> {Served.arr_all(n, s, Served.seqn(n, s)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+n1:
      +n1 = n1
      %Equal.sym(Bool, Nat.is_eq(s, s), True{}, GP.ar_eq_refl(s)) :
        {Bool.and(Bool.or(_, PSpec.arrived(Served.seqn(n1, 1n+s), s)), Served.arr_all(n1, 1n+s, s <> Served.seqn(n1, 1n+s))) == True{} : Bool}
      sd_all_cons(n1, 1n+s, s, Served.seqn(n1, 1n+s), sd_all_seqn(n1, 1n+s))

def sd_only_seqn(n: Nat, +s: Nat, +lo: Nat, +h: {Nat.is_le(lo, s) == True{} : Bool}) -> {Served.arr_only(Served.seqn(n, s), lo) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+n1:
      +n1 = n1
      %Equal.sym(Bool, Nat.is_le(lo, s), True{}, h) : {Bool.and(_, Served.arr_only(Served.seqn(n1, 1n+s), lo)) == True{} : Bool}
      sd_only_seqn(n1, 1n+s, lo, GP.ar_le_trans(lo, s, 1n+s, h, GP.ar_h_le_succ(s)))

def sd_and_tt(-a: Bool, h: {a == True{} : Bool}) -> {Bool.and(a, True{}) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def Laws.arrivals_exact(ix, lo, nc):
  +ix = ix
  +lo = lo
  +nc = nc
  +S = Served.seqn(nc, lo)
  (Equal.trans(Bool, Served.arr_only(Served.perm(S, ix, Nil{}), lo), Bool.and(Served.arr_only(S, lo), True{}), True{},
      sd_perm_only(S, ix, Nil{}, lo), sd_and_tt(Served.arr_only(S, lo), sd_only_seqn(nc, lo, lo, GP.ar_le_refl(lo)))),
    Equal.trans(Bool, Served.arr_all(nc, lo, Served.perm(S, ix, Nil{})), Served.arr_all(nc, lo, S), True{},
      sd_all_perm(nc, lo, S, ix), sd_all_seqn(nc, lo)),
    Equal.trans(Nat, List.length(&2, Nat, Served.perm(S, ix, Nil{})), Nat.add(List.length(&2, Nat, S), 0n), nc,
      sd_perm_len(S, ix, Nil{}),
      Equal.trans(Nat, Nat.add(List.length(&2, Nat, S), 0n), List.length(&2, Nat, S), nc, GP.ar_add_zero_r(List.length(&2, Nat, S)), sq_len(nc, lo))))

# ---------------------------------------------------------------- every arrival order is reachable

def sd_pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def sd_succ_zero(-k: Nat, h: {1n+k == 0n : Nat}) -> Empty:
  GP.ar_false_true(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 1n+k, 0n, h))

# perm over cs ++ [c] with one more index i inserts c at i into perm over cs.
def sd_perm_snoc(cs: List<&2, Nat>, ix: List<&2, Nat>, +acc: List<&2, Nat>, +c: Nat, +i: Nat,
    h: {List.length(&2, Nat, ix) == List.length(&2, Nat, cs) : Nat})
  -> {Served.perm(List.append(&2, Nat, cs, [c]), List.append(&2, Nat, ix, [i]), acc) == Served.ins_at(Served.perm(cs, ix, acc), i, c) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      match ix:
        case Nil{}:
          {==}
        case +j <> +ixr:
          Empty.absurd({Served.perm([c], List.append(&2, Nat, j <> ixr, [i]), acc) == Served.ins_at(acc, i, c) : List<&2, Nat>},
            sd_succ_zero(List.length(&2, Nat, ixr), h))
    case +c0 <> +rest:
      match ix:
        case Nil{}:
          Empty.absurd({Served.perm(c0 <> List.append(&2, Nat, rest, [c]), [i], acc) == Served.ins_at(Served.perm(c0 <> rest, Nil{}, acc), i, c) : List<&2, Nat>},
            sd_succ_zero(List.length(&2, Nat, rest), Equal.sym(Nat, 0n, 1n+List.length(&2, Nat, rest), h)))
        case +j <> +ixr:
          sd_perm_snoc(rest, ixr, Served.ins_at(acc, j, c0), c, i,
            Equal.cong(Nat, Nat, z => sd_pred(z), 1n+List.length(&2, Nat, ixr), 1n+List.length(&2, Nat, rest), h))

# Inserting at |a| into a ++ b puts x between a and b.
def sd_ins_mid(a: List<&2, Nat>, b: List<&2, Nat>, +x: Nat)
  -> {Served.ins_at(List.append(&2, Nat, a, b), List.length(&2, Nat, a), x) == List.append(&2, Nat, a, x <> b) : List<&2, Nat>}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case +y <> +r:
          {==}
    case +y <> +a2:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => y <> z, Served.ins_at(List.append(&2, Nat, a2, b), List.length(&2, Nat, a2), x),
        List.append(&2, Nat, a2, x <> b), sd_ins_mid(a2, b, x))

def Laws.perm_reach_step(cs, ix, a, b, c, len, order):
  +cs = cs
  +ix = ix
  +a = a
  +b = b
  +c = c
  %Equal.sym(List<&2, Nat>, Served.perm(List.append(&2, Nat, cs, [c]), List.append(&2, Nat, ix, [List.length(&2, Nat, a)]), Nil{}),
      Served.ins_at(Served.perm(cs, ix, Nil{}), List.length(&2, Nat, a), c), sd_perm_snoc(cs, ix, Nil{}, c, List.length(&2, Nat, a), len)) :
    {_ == List.append(&2, Nat, a, c <> b) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.perm(cs, ix, Nil{}), List.append(&2, Nat, a, b), order) :
    {Served.ins_at(_, List.length(&2, Nat, a), c) == List.append(&2, Nat, a, c <> b) : List<&2, Nat>}
  sd_ins_mid(a, b, c)

# ---------------------------------------------------------------- the counter barrier

def sd_lt_add_zero(c: Nat) -> {Nat.is_lt(c, Nat.add(c, 0n)) == False{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+c1:
      sd_lt_add_zero(c1)

def sd_lt_add_pos(c: Nat, +k: Nat) -> {Nat.is_lt(c, Nat.add(c, 1n+k)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+c1:
      sd_lt_add_pos(c1, k)

def sd_seen_step(rest: List<&2, Nat>, +c8: Nat,
    ih: {Served.seen(rest, c8, Nat.add(c8, Nat.mul(List.length(&2, Nat, rest), 8n))) == rest : List<&2, Nat>})
  -> {Served.seen.cut(Nat.is_lt(c8, Nat.add(c8, Nat.mul(List.length(&2, Nat, rest), 8n))),
        Served.seen(rest, c8, Nat.add(c8, Nat.mul(List.length(&2, Nat, rest), 8n)))) == rest : List<&2, Nat>}:
  match rest:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_lt(c8, Nat.add(c8, 0n)), False{}, sd_lt_add_zero(c8)) :
        {Served.seen.cut(_, Served.seen(Nil{}, c8, Nat.add(c8, 0n))) == Nil{} : List<&2, Nat>}
      {==}
    case +b2 <> +r2:
      +X = Nat.add(7n, Nat.mul(List.length(&2, Nat, r2), 8n))
      %Equal.sym(Bool, Nat.is_lt(c8, Nat.add(c8, 1n+X)), True{}, sd_lt_add_pos(c8, X)) :
        {Served.seen.cut(_, Served.seen(b2 <> r2, c8, Nat.add(c8, 1n+X))) == b2 <> r2 : List<&2, Nat>}
      ih

def sd_seen(order: List<&2, Nat>, +cnt: Nat) -> {Served.seen(order, cnt, Nat.add(cnt, Nat.mul(List.length(&2, Nat, order), 8n))) == order : List<&2, Nat>}:
  match order:
    case Nil{}:
      {==}
    case +b <> +rest:
      +c8 = Nat.add(cnt, 8n)
      +M = Nat.mul(List.length(&2, Nat, rest), 8n)
      %GP.ar_add_assoc(cnt, 8n, M) :
        {b <> Served.seen.cut(Nat.is_lt(c8, _), Served.seen(rest, c8, _)) == b <> rest : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => b <> y, Served.seen.cut(Nat.is_lt(c8, Nat.add(c8, M)), Served.seen(rest, c8, Nat.add(c8, M))), rest,
        sd_seen_step(rest, c8, sd_seen(rest, c8)))

def Laws.barrier_sees_all(order, nc, len):
  +order = order
  %len : {Served.seen(order, 0n, Nat.mul(_, 8n)) == order : List<&2, Nat>}
  sd_seen(order, 0n)

def sd_fill_len(k: Nat, ws: List<&2, PSpec.Sum>) -> {List.length(&2, PSpec.Sum, Served.fill(k, ws)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match ws:
        case Nil{}:
          Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, PSpec.Sum, Served.fill(k1, Nil{})), k1, sd_fill_len(k1, Nil{}))
        case w <> rest:
          Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, PSpec.Sum, Served.fill(k1, rest)), k1, sd_fill_len(k1, rest))

# ---------------------------------------------------------------- the contributors of a group

def sd_and_ff(-a: Bool, -c: Bool, h: {a == False{} : Bool}) -> {Bool.and(a, c) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {Bool.and(_, c) == False{} : Bool}
  {==}

def sd_and_xf(a: Bool, -c: Bool, h: {c == False{} : Bool}) -> {Bool.and(a, c) == False{} : Bool}:
  %Equal.sym(Bool, c, False{}, h) : {Bool.and(a, _) == False{} : Bool}
  sd_and_false(a)

def sd_and_tt2(-a: Bool, -c: Bool, ha: {a == True{} : Bool}, hc: {c == True{} : Bool}) -> {Bool.and(a, c) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, c) == True{} : Bool}
  hc

def sd_keep_app(c: Bool, +b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>)
  -> {List.append(&2, Nat, Served.keep(c, b, xs), ys) == Served.keep(c, b, List.append(&2, Nat, xs, ys)) : List<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# is_le(b + (1 + k), x) as is_le(1 + (b + k), x)
def sd_le_sr(+b: Nat, +k: Nat, +x: Nat, h: {Nat.is_le(Nat.add(b, 1n+k), x) == True{} : Bool}) -> {Nat.is_le(1n+Nat.add(b, k), x) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(1n+Nat.add(b, k), x), Nat.is_le(Nat.add(b, 1n+k), x), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, x), 1n+Nat.add(b, k), Nat.add(b, 1n+k), LinkProof.ri_sr(b, k)), h)

# b < x from 1 + (b + k) <= x
def sd_lt_of(+b: Nat, +k: Nat, +x: Nat, +h: {Nat.is_le(1n+Nat.add(b, k), x) == True{} : Bool}) -> {Nat.is_lt(b, x) == True{} : Bool}:
  GP.ar_le_lt_trans(b, Nat.add(b, k), x, GP.ar_le_add_r(b, k),
    Equal.trans(Bool, Nat.is_lt(Nat.add(b, k), x), Nat.is_le(1n+Nat.add(b, k), x), True{}, GP.ar_lt_succ_le(Nat.add(b, k), x), h))

# Contributor lists split at any point.
def sd_capp(k1: Nat, +k2: Nat, +b: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat)
  -> {Served.contribs(Nat.add(k1, k2), b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == List.append(&2, Nat, Served.contribs(k1, b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(b, k1), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : List<&2, Nat>}:
  match k1:
    case 0n:
      Equal.cong(Nat, List<&2, Nat>, z => Served.contribs(k2, z, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Nat.add(b, 0n), LinkProof.ri_zr(b))
    case 1n+j:
      +j = j
      Equal.trans(List<&2, Nat>, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(Nat.add(j, k2), 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
        Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, List.append(&2, Nat, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))),
        List.append(&2, Nat, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.contribs(k2, Nat.add(b, 1n+j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, z), Served.contribs(Nat.add(j, k2), 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
          List.append(&2, Nat, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), sd_capp(j, k2, 1n+b, groups, KT, G, nsm, w0, w1, g)),
        Equal.trans(List<&2, Nat>, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, List.append(&2, Nat, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))),
          List.append(&2, Nat, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
          List.append(&2, Nat, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.contribs(k2, Nat.add(b, 1n+j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
          Equal.sym(List<&2, Nat>, List.append(&2, Nat, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
            Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, List.append(&2, Nat, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))),
            sd_keep_app(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(k2, Nat.add(1n+b, j), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))),
          Equal.cong(Nat, List<&2, Nat>, z => List.append(&2, Nat, Served.keep(WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, Served.contribs(j, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.contribs(k2, z, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
            1n+Nat.add(b, j), Nat.add(b, 1n+j), LinkProof.ri_sr(b, j))))

# Blocks below first_contrib(g) do not touch g.
def sd_cz(k: Nat, +b: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +hlG: {Nat.is_lt(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool}, hk: {Nat.is_le(Nat.add(b, k), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool})
  -> {Served.contribs(k, b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == Nil{} : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +hk1 = sd_le_sr(b, k1, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), hk)
      +hblo = sd_lt_of(b, k1, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), hk1)
      +ht = Equal.trans(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Bool.and(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))), False{}, WpL.contributors_contiguous(groups, KT, G, nsm, w0, w1, g, b, valid, tiles, group, GP.ar_lt_trans(b, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G, hblo, hlG)),
        sd_and_ff(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), sd_lt_nle(b, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), hblo)))
      %Equal.sym(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), False{}, ht) : {Served.keep(_, b, Served.contribs(k1, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Nil{} : List<&2, Nat>}
      sd_cz(k1, 1n+b, groups, KT, G, nsm, w0, w1, g, valid, tiles, group, hlG, hk1)

# Blocks first_contrib(g) .. last_contrib(g) all touch g.
def sd_cin(k: Nat, +b: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +hb: {Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b) == True{} : Bool}, +hhG: {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool},
    hk: {Nat.is_le(Nat.add(b, k), 1n+Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool})
  -> {Served.contribs(k, b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == Served.seqn(k, b) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +hk1 = sd_le_sr(b, k1, 1n+Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), hk)
      +hbhi = GP.ar_le_trans(b, Nat.add(b, k1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), GP.ar_le_add_r(b, k1), hk1)
      +ht = Equal.trans(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Bool.and(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))), True{}, WpL.contributors_contiguous(groups, KT, G, nsm, w0, w1, g, b, valid, tiles, group, GP.ar_le_lt_trans(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G, hbhi, hhG)),
        sd_and_tt2(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), hb, hbhi))
      %Equal.sym(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), True{}, ht) : {Served.keep(_, b, Served.contribs(k1, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Served.seqn(1n+k1, b) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => b <> z, Served.contribs(k1, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.seqn(k1, 1n+b),
        sd_cin(k1, 1n+b, groups, KT, G, nsm, w0, w1, g, valid, tiles, group, GP.ar_le_trans(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, 1n+b, hb, GP.ar_h_le_succ(b)), hhG, hk1))

# Blocks above last_contrib(g) do not touch g.
def sd_cout(k: Nat, +b: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +hb: {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b) == True{} : Bool}, hk: {Nat.is_le(Nat.add(b, k), G) == True{} : Bool})
  -> {Served.contribs(k, b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == Nil{} : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +hk1 = sd_le_sr(b, k1, G, hk)
      +ht = Equal.trans(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Bool.and(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))), False{}, WpL.contributors_contiguous(groups, KT, G, nsm, w0, w1, g, b, valid, tiles, group, sd_lt_of(b, k1, G, hk1)),
        sd_and_xf(Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b), Nat.is_le(b, Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), sd_lt_nle(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, hb)))
      %Equal.sym(Bool, WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), False{}, ht) : {Served.keep(_, b, Served.contribs(k1, 1n+b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Nil{} : List<&2, Nat>}
      sd_cout(k1, 1n+b, groups, KT, G, nsm, w0, w1, g, valid, tiles, group, GP.ar_lt_trans(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b, 1n+b, hb, LinkProof.ri_lt_s(b)), hk1)

# The host-guard facts of a group: lo <= hi, hi < G, nc <= max_contrib (gemm_m16_wpart_laws
# valid_domain + contrib_bounds).
def sd_bounds(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool},
    +group: {Nat.is_lt(g, groups) == True{} : Bool}) -> {Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool} & {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  WpL.contrib_bounds(groups, KT, G, nsm, w0, w1, g, fst({Nat.is_lt(0n, w0) == True{} : Bool}, {Nat.is_lt(0n, w1) == True{} : Bool} & {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, WpL.valid_domain(Nat.mul(groups, KT), G, nsm, w0, w1, valid)), fst({Nat.is_lt(0n, w1) == True{} : Bool}, {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, snd({Nat.is_lt(0n, w0) == True{} : Bool}, {Nat.is_lt(0n, w1) == True{} : Bool} & {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, WpL.valid_domain(Nat.mul(groups, KT), G, nsm, w0, w1, valid))), fst({Nat.is_lt(0n, G) == True{} : Bool}, {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, snd({Nat.is_lt(0n, w1) == True{} : Bool}, {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, snd({Nat.is_lt(0n, w0) == True{} : Bool}, {Nat.is_lt(0n, w1) == True{} : Bool} & {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, WpL.valid_domain(Nat.mul(groups, KT), G, nsm, w0, w1, valid)))), tiles, group)

def sd_lohi(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool}) -> {Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}:
  fst({Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}, {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool} & {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, sd_bounds(groups, KT, G, nsm, w0, w1, g, valid, tiles, group))

def sd_hiG(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool}) -> {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool}:
  fst({Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool}, {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, snd({Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}, {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool} & {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, sd_bounds(groups, KT, G, nsm, w0, w1, g, valid, tiles, group)))

def sd_room(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool}) -> {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  snd({Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}, {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, snd({Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool}, {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, snd({Nat.is_le(Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}, {Nat.is_lt(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool} & {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} & {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}, sd_bounds(groups, KT, G, nsm, w0, w1, g, valid, tiles, group))))

def Laws.contributors_seqn(groups_, KT_, G_, nsm_, w0_, w1_, g_, valid_, tiles_, group_):
  +groups = groups_
  +KT = KT_
  +G = G_
  +nsm = nsm_
  +w0 = w0_
  +w1 = w1_
  +g = g_
  +valid = valid_
  +tiles = tiles_
  +group = group_
  +hl = sd_lohi(groups, KT, G, nsm, w0, w1, g, valid, tiles, group)
  +hhG = sd_hiG(groups, KT, G, nsm, w0, w1, g, valid, tiles, group)
  +lo = Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +hi = Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +sb = Nat.sub(hi, lo)
  +nc = Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +R = Nat.sub(G, 1n+hi)
  # lo + nc == 1 + hi
  +E1 = Equal.trans(Nat, Nat.add(lo, Nat.add(sb, 1n)), Nat.add(lo, 1n+sb), 1n+hi,
    Equal.cong(Nat, Nat, z => Nat.add(lo, z), Nat.add(sb, 1n), 1n+sb, GP.ar_add_comm(sb, 1n)),
    Equal.trans(Nat, Nat.add(lo, 1n+sb), 1n+Nat.add(lo, sb), 1n+hi, GP.ar_add_succ_r(lo, sb),
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(lo, sb), hi, GP.ar_sub_add(hi, lo, hl))))
  # (1 + hi) + R == G
  +E2 = GP.ar_sub_add(G, 1n+hi, Equal.trans(Bool, Nat.is_le(1n+hi, G), Nat.is_lt(hi, G), True{}, Equal.sym(Bool, Nat.is_lt(hi, G), Nat.is_le(1n+hi, G), GP.ar_lt_succ_le(hi, G)), hhG))
  +E4 = Equal.trans(Nat, Nat.add(Nat.add(lo, nc), R), Nat.add(1n+hi, R), G, Equal.cong(Nat, Nat, z => Nat.add(z, R), Nat.add(lo, nc), 1n+hi, E1), E2)
  +E3 = Equal.trans(Nat, Nat.add(lo, Nat.add(nc, R)), Nat.add(Nat.add(lo, nc), R), G, Equal.sym(Nat, Nat.add(Nat.add(lo, nc), R), Nat.add(lo, Nat.add(nc, R)), GP.ar_add_assoc(lo, nc, R)), E4)
  +C1 = sd_capp(lo, Nat.add(nc, R), 0n, groups, KT, G, nsm, w0, w1, g)
  +C2 = sd_cz(lo, 0n, groups, KT, G, nsm, w0, w1, g, valid, tiles, group, GP.ar_le_lt_trans(lo, hi, G, hl, hhG), GP.ar_le_refl(lo))
  +C3 = sd_capp(nc, R, lo, groups, KT, G, nsm, w0, w1, g)
  +C4 = sd_cin(nc, lo, groups, KT, G, nsm, w0, w1, g, valid, tiles, group, GP.ar_le_refl(lo), hhG,
    Equal.trans(Bool, Nat.is_le(Nat.add(lo, nc), 1n+hi), Nat.is_le(1n+hi, 1n+hi), True{},
      Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+hi), Nat.add(lo, nc), 1n+hi, E1), GP.ar_le_refl(1n+hi)))
  +C5 = sd_cout(R, Nat.add(lo, nc), groups, KT, G, nsm, w0, w1, g, valid, tiles, group,
    Equal.trans(Bool, Nat.is_lt(hi, Nat.add(lo, nc)), Nat.is_lt(hi, 1n+hi), True{},
      Equal.cong(Nat, Bool, z => Nat.is_lt(hi, z), Nat.add(lo, nc), 1n+hi, E1), LinkProof.ri_lt_s(hi)),
    Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(lo, nc), R), G), Nat.is_le(G, G), True{},
      Equal.cong(Nat, Bool, z => Nat.is_le(z, G), Nat.add(Nat.add(lo, nc), R), G, E4), GP.ar_le_refl(G)))
  %E3 : {Served.contribs(_, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == Served.seqn(nc, lo) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.contribs(Nat.add(lo, Nat.add(nc, R)), 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), List.append(&2, Nat, Served.contribs(lo, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(Nat.add(nc, R), lo, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), C1) :
    {_ == Served.seqn(nc, lo) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.contribs(lo, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Nil{}, C2) : {List.append(&2, Nat, _, Served.contribs(Nat.add(nc, R), lo, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Served.seqn(nc, lo) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.contribs(Nat.add(nc, R), lo, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), List.append(&2, Nat, Served.contribs(nc, lo, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.contribs(R, Nat.add(lo, nc), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), C3) :
    {_ == Served.seqn(nc, lo) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.contribs(nc, lo, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Served.seqn(nc, lo), C4) : {List.append(&2, Nat, _, Served.contribs(R, Nat.add(lo, nc), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Served.seqn(nc, lo) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Served.contribs(R, Nat.add(lo, nc), g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Nil{}, C5) : {List.append(&2, Nat, Served.seqn(nc, lo), _) == Served.seqn(nc, lo) : List<&2, Nat>}
  LinkProof.ri_app_nil(~Nat, Served.seqn(nc, lo))

def sv_nc_pos(+x: Nat) -> {Nat.is_lt(0n, Nat.add(x, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+Nat.add(x, 0n), GP.ar_add_succ_r(x, 0n)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}


# ---------------------------------------------------------------- H_sched discharged: every group's finisher sum

# Under the host guard the finisher sum of group g < groups is the ascending fold, for every scheduler
# choice and stale workspace: the arrivals are a permutation of exactly the contributors
# (contributors_seqn, arrivals_exact), the barrier shows all of them (barrier_sees_all), the region has
# max_contrib >= nc slots (contrib_bounds), so splitk_finish_asc applies.
def sd_fin(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +m: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool})
  -> {Served.fin_g(~arr, ~wsi, m, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == Served.asc(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : PSpec.Sum}:
  +lo = Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +nc = Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +mc = Wp.max_contrib(groups, KT, G, nsm, w0, w1)
  +S = Served.seqn(nc, lo)
  +ix = arr(m, lo, nc)
  +P = Served.perm(S, ix, Nil{})
  +W = Served.fill(mc, wsi(m, mc))
  +only = fst({Served.arr_only(P, lo) == True{} : Bool}, {Served.arr_all(nc, lo, P) == True{} : Bool} & {List.length(&2, Nat, P) == nc : Nat}, Laws.arrivals_exact(ix, lo, nc))
  +all = fst({Served.arr_all(nc, lo, P) == True{} : Bool}, {List.length(&2, Nat, P) == nc : Nat}, snd({Served.arr_only(P, lo) == True{} : Bool}, {Served.arr_all(nc, lo, P) == True{} : Bool} & {List.length(&2, Nat, P) == nc : Nat}, Laws.arrivals_exact(ix, lo, nc)))
  +len = snd({Served.arr_all(nc, lo, P) == True{} : Bool}, {List.length(&2, Nat, P) == nc : Nat}, snd({Served.arr_only(P, lo) == True{} : Bool}, {Served.arr_all(nc, lo, P) == True{} : Bool} & {List.length(&2, Nat, P) == nc : Nat}, Laws.arrivals_exact(ix, lo, nc)))
  +room = Equal.trans(Bool, Nat.is_le(nc, List.length(&2, PSpec.Sum, W)), Nat.is_le(nc, mc), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(nc, z), List.length(&2, PSpec.Sum, W), mc, sd_fill_len(mc, wsi(m, mc))),
    sd_room(groups, KT, G, nsm, w0, w1, g, valid, tiles, group))
  +pos = sv_nc_pos(Nat.sub(Wp.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), lo))
  %Equal.sym(List<&2, Nat>, Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), S, Laws.contributors_seqn(groups, KT, G, nsm, w0, w1, g, valid, tiles, group)) :
    {Served.fin_g(~arr, ~wsi, m, lo, nc, mc, _) == Served.asc(nc, lo) : PSpec.Sum}
  %Equal.sym(List<&2, Nat>, Served.seen(P, 0n, Nat.mul(nc, 8n)), P, Laws.barrier_sees_all(P, nc, len)) :
    {Part.finish(Part.arrive(_, W, lo), nc) == Served.asc(nc, lo) : PSpec.Sum}
  Laws.splitk_finish_asc(P, W, lo, nc, only, all, room, pos)

def Laws.splitk_group(arr, wsi, m, groups_, KT_, G_, nsm_, w0_, w1_, g_, valid_, tiles_, group_):
  +groups = groups_
  +KT = KT_
  +G = G_
  +nsm = nsm_
  +w0 = w0_
  +w1 = w1_
  +g = g_
  +valid = valid_
  +tiles = tiles_
  +group = group_
  sd_fin(~arr, ~wsi, m, groups, KT, G, nsm, w0, w1, g, valid, tiles, group)

def sv_kg(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, k: Nat, +g: Nat, +KT: Nat, +G: Nat,
    +nsm: Nat, +w0: Nat, +w1: Nat, +groups: Nat, +m: Nat, +m2: Nat,
    +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}, +tiles: {Nat.is_lt(0n, KT) == True{} : Bool},
    hg: {Nat.is_le(Nat.add(g, k), groups) == True{} : Bool})
  -> {Served.kgroups(~arr, ~wsi, k, g, KT, G, nsm, w0, w1, groups, m) == Served.kgroups(~arr, ~wsi, k, g, KT, G, nsm, w0, w1, groups, m2) : List<&2, PSpec.Sum>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +hg1 = sd_le_sr(g, k1, groups, hg)
      +grp = sd_lt_of(g, k1, groups, hg1)
      LinkProof.ri_cong_cons(~PSpec.Sum, Served.fin_g(~arr, ~wsi, m, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.fin_g(~arr, ~wsi, m2, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
        Served.kgroups(~arr, ~wsi, k1, 1n+g, KT, G, nsm, w0, w1, groups, m), Served.kgroups(~arr, ~wsi, k1, 1n+g, KT, G, nsm, w0, w1, groups, m2),
        Equal.trans(PSpec.Sum, Served.fin_g(~arr, ~wsi, m, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.asc(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.fin_g(~arr, ~wsi, m2, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
          sd_fin(~arr, ~wsi, m, groups, KT, G, nsm, w0, w1, g, valid, tiles, grp),
          Equal.sym(PSpec.Sum, Served.fin_g(~arr, ~wsi, m2, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), Served.asc(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), sd_fin(~arr, ~wsi, m2, groups, KT, G, nsm, w0, w1, g, valid, tiles, grp))),
        sv_kg(~arr, ~wsi, k1, 1n+g, KT, G, nsm, w0, w1, groups, m, m2, valid, tiles, hg1))

def sv_ks(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, gs: List<&2, Served.GDesc>, +m: Nat, +m2: Nat,
    +hok: {Served.gdesc_ok(gs) == True{} : Bool})
  -> {Served.ksum(~arr, ~wsi, gs, m) == Served.ksum(~arr, ~wsi, gs, m2) : List<&2, PSpec.Sum>}:
  match gs:
    case Nil{}:
      {==}
    case Served.GDesc{+KT, +G, +nsm, +w0, +w1, +groups} <> +rest:
      +hd = GP.ar_and_l(Bool.and(Nat.is_lt(0n, KT), Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1)), Served.gdesc_ok(rest), hok)
      +tiles = GP.ar_and_l(Nat.is_lt(0n, KT), Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1), hd)
      +valid = GP.ar_and_r(Nat.is_lt(0n, KT), Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1), hd)
      +hr = GP.ar_and_r(Bool.and(Nat.is_lt(0n, KT), Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1)), Served.gdesc_ok(rest), hok)
      %Equal.sym(List<&2, PSpec.Sum>, Served.kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m),
          Served.kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m2),
          sv_kg(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m, m2, valid, tiles, GP.ar_le_refl(groups))) :
        {List.append(&2, PSpec.Sum, _, Served.ksum(~arr, ~wsi, rest, m)) ==
          List.append(&2, PSpec.Sum, Served.kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m2), Served.ksum(~arr, ~wsi, rest, m2)) : List<&2, PSpec.Sum>}
      %Equal.sym(List<&2, PSpec.Sum>, Served.ksum(~arr, ~wsi, rest, m), Served.ksum(~arr, ~wsi, rest, m2), sv_ks(~arr, ~wsi, rest, m, m2, hr)) :
        {List.append(&2, PSpec.Sum, Served.kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m2), _) ==
          List.append(&2, PSpec.Sum, Served.kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m2), Served.ksum(~arr, ~wsi, rest, m2)) : List<&2, PSpec.Sum>}
      {==}

# ---------------------------------------------------------------- H_grid discharged

def sd_max1_pos(x: Nat) -> {Nat.is_lt(0n, Nat.max(1n, x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+x1:
      {==}

def Laws.grid_pos(sms, kvh):
  sd_max1_pos(Nat.div(sms, kvh))

# ---------------------------------------------------------------- 8205 tail: the main loop of every block

def sv_tw(k: Nat, +b: Nat, +G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +m2: Nat, +a0: Nat, +b0: Nat, +a1: Nat,
    +b1: Nat, +a2: Nat, +b2: Nat)
  -> {Served.tail_works(k, b, G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2) == Served.tail_works(k, b, G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2)
      : List<&2, List<&2, PSpec.Ev>>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +TE1 = Ws.tevents(G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2, b)
      +TE2 = Ws.tevents(G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2, b)
      +c2 = fst({TSpec.works(TE1) == TSpec.works(TE2) : List<&2, PSpec.Ev>},
        {TSpec.syncs(TE1) == TSpec.syncs(TE2) : List<&2, MSpec.Ev>} &
        {TSpec.bars(TE1) == TSpec.bar_seq() : List<&2, Nat>} &
        {TSpec.works(TE1) == Part.mainloop(Ws.s0(G, nsm, A, H, a0, b0, b), Ws.e0(G, nsm, A, H, a0, b0, b), Tail.kt0(A)) : List<&2, PSpec.Ev>} &
        {TSpec.syncs(TE1) == Ws.events(G, nsm, H, I, a1, b1, a2, b2, b) : List<&2, MSpec.Ev>},
        snd({TSpec.bars(TE1) == TSpec.bars(TE2) : List<&2, Nat>},
          {TSpec.works(TE1) == TSpec.works(TE2) : List<&2, PSpec.Ev>} &
          {TSpec.syncs(TE1) == TSpec.syncs(TE2) : List<&2, MSpec.Ev>} &
          {TSpec.bars(TE1) == TSpec.bar_seq() : List<&2, Nat>} &
          {TSpec.works(TE1) == Part.mainloop(Ws.s0(G, nsm, A, H, a0, b0, b), Ws.e0(G, nsm, A, H, a0, b0, b), Tail.kt0(A)) : List<&2, PSpec.Ev>} &
          {TSpec.syncs(TE1) == Ws.events(G, nsm, H, I, a1, b1, a2, b2, b) : List<&2, MSpec.Ev>},
          WsTL.wtail_rows(G, nsm, A, H, I, m, m2, a0, b0, a1, b1, a2, b2, b)))
      LinkProof.ri_cong_cons(~List<&2, PSpec.Ev>, TSpec.works(Ws.tevents(G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2, b)),
        TSpec.works(Ws.tevents(G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2, b)),
        Served.tail_works(k1, 1n+b, G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2), Served.tail_works(k1, 1n+b, G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2),
        c2, sv_tw(k1, 1n+b, G, nsm, A, H, I, m, m2, a0, b0, a1, b1, a2, b2))

# ---------------------------------------------------------------- O_plan / O_head for the served plan

def sv_cong_plan(-a1: Nat, -b1: Nat, -a2: List<&2, Nat>, -b2: List<&2, Nat>, -a3: List<&2, List<&2, List<&2, Nat>>>,
    -b3: List<&2, List<&2, List<&2, Nat>>>, -a4: List<&2, PSpec.Sum>, -b4: List<&2, PSpec.Sum>, -a5: List<&2, List<&2, PSpec.Ev>>,
    -b5: List<&2, List<&2, PSpec.Ev>>, -a6: List<&2, Ba.Ex>, -b6: List<&2, Ba.Ex>, -a7: Lm.HeadPlan, -b7: Lm.HeadPlan, h1: {a1 == b1 : Nat},
    h2: {a2 == b2 : List<&2, Nat>}, h3: {a3 == b3 : List<&2, List<&2, List<&2, Nat>>>}, h4: {a4 == b4 : List<&2, PSpec.Sum>},
    h5: {a5 == b5 : List<&2, List<&2, PSpec.Ev>>}, h6: {a6 == b6 : List<&2, Ba.Ex>}, h7: {a7 == b7 : Lm.HeadPlan})
  -> {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{b1, b2, b3, b4, b5, b6, b7} : Served.Plan}:
  %h1 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{_, b2, b3, b4, b5, b6, b7} : Served.Plan}
  %h2 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, _, b3, b4, b5, b6, b7} : Served.Plan}
  %h3 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, a2, _, b4, b5, b6, b7} : Served.Plan}
  %h4 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, a2, a3, _, b5, b6, b7} : Served.Plan}
  %h5 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, a2, a3, a4, _, b6, b7} : Served.Plan}
  %h6 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, a2, a3, a4, a5, _, b7} : Served.Plan}
  %h7 : {Served.Plan{a1, a2, a3, a4, a5, a6, a7} == Served.Plan{a1, a2, a3, a4, a5, a6, _} : Served.Plan}
  {==}

def sv_plan_of(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, c: Served.Cfg, +base: Nat, +m: Nat, +r: Nat,
    +d: Nat, +hc: {Served.cfg_ok(c) == True{} : Bool}, +dr: {Nat.is_le(d, r) == True{} : Bool}, +rm: {Nat.is_lt(r, m) == True{} : Bool},
    +m8: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {Served.plan_of(~arr, ~wsi, c, base, m, r, d) == Served.plan_of(~arr, ~wsi, c, Nat.add(base, d), 1n, 0n, 0n) : Served.Plan}:
  match c:
    case Served.Cfg{+sms, +kvh, +tG, +tnsm, +tA, +tH, +tI, +a0, +b0, +a1, +b1, +a2, +b2, +bk2, +bH, +bhb, +hdim, +vsize, +gemms}:
      +S = Served.grid_S(sms, kvh)
      +hS = Laws.grid_pos(sms, kvh)
      +a = Nat.add(base, d)
      +dm = GP.ar_le_lt_trans(d, r, m, dr, rm)
      +r8 = GP.ar_lt_le_trans(r, m, 8n, rm, m8)
      +e1 = LinkProof.ri_zr(a)
      +t3 = snd({Stride.cta_hits(0n, 0n, Nat.add(base, m), S, m, d) == Stride.cta_hits(0n, 0n, Nat.add(a, 1n), S, 1n, 0n) : Nat},
        {Stride.merged(Nat.add(base, m), S, m, d) == Stride.merged(Nat.add(a, 1n), S, 1n, 0n) : List<&2, Nat>},
        snd({Stride.tile_hits(0n, 0n, 0n, Nat.add(base, m), S, m, d) == Stride.tile_hits(0n, 0n, 0n, Nat.add(a, 1n), S, 1n, 0n) : Nat},
          {Stride.cta_hits(0n, 0n, Nat.add(base, m), S, m, d) == Stride.cta_hits(0n, 0n, Nat.add(a, 1n), S, 1n, 0n) : Nat} &
          {Stride.merged(Nat.add(base, m), S, m, d) == Stride.merged(Nat.add(a, 1n), S, 1n, 0n) : List<&2, Nat>},
          StrideLaws.row_invariant_rounds(base, m, d, a, 1n, 0n, S, 0n, 0n, 0n, hS, dm, {==}, e1)))
      +e3 = Equal.trans(List<&2, List<&2, List<&2, Nat>>>, Served.tiles_x(S, 0n, Nat.add(base, m), S, m, d, 1n+a),
        Served.tiles_x(S, 0n, Nat.add(a, 1n), S, 1n, 0n, 1n+a), Served.tiles_x(S, 0n, Nat.add(a, 1n), S, 1n, 0n, 1n+Nat.add(a, 0n)),
        sv_tx(S, 0n, base, m, d, a, 1n, 0n, S, 1n+a, GP.ar_le_refl(S), dm, {==}, e1),
        Equal.cong(Nat, List<&2, List<&2, List<&2, Nat>>>, y => Served.tiles_x(S, 0n, Nat.add(a, 1n), S, 1n, 0n, 1n+y), a, Nat.add(a, 0n), e1))
      sv_cong_plan(a, Nat.add(a, 0n), Stride.merged(Nat.add(base, m), S, m, d), Stride.merged(Nat.add(a, 1n), S, 1n, 0n),
        Served.tiles_x(S, 0n, Nat.add(base, m), S, m, d, 1n+a), Served.tiles_x(S, 0n, Nat.add(a, 1n), S, 1n, 0n, 1n+Nat.add(a, 0n)),
        Served.ksum(~arr, ~wsi, gemms, m), Served.ksum(~arr, ~wsi, gemms, 1n),
        Served.tail_works(tG, 0n, tG, tnsm, tA, tH, tI, m, a0, b0, a1, b1, a2, b2), Served.tail_works(tG, 0n, tG, tnsm, tA, tH, tI, 1n, a0, b0, a1, b1, a2, b2),
        Served.ba_tab(bH, 0n, m, r, bk2, bH, bhb), Served.ba_tab(bH, 0n, 1n, 0n, bk2, bH, bhb),
        Lm.hp_head(Lm.served_tab(), 6n, hdim, vsize, base, m, r, d), Lm.hp_head(Lm.served_tab(), 6n, hdim, vsize, a, 1n, 0n, 0n),
        e1, t3, e3, sv_ks(~arr, ~wsi, gemms, m, 1n, hc),
        sv_tw(tG, 0n, tG, tnsm, tA, tH, tI, m, 1n, a0, b0, a1, b1, a2, b2), sv_ba_tab(bH, 0n, m, r, bk2, bH, bhb, rm, r8),
        LmL.o_head_served(hdim, vsize, base, m, r, d, dr, rm, m8))

def Laws.served_o_plan(cfg, arr, wsi, hcfg, l, base, m, r, d, dr, rm, m8):
  sv_plan_of(~arr, ~wsi, cfg, base, m, r, d, hcfg, dr, rm, m8)

def Laws.served_o_head(cfg, arr, wsi, hcfg, base, m, r, d, dr, rm, m8):
  sv_plan_of(~arr, ~wsi, cfg, base, m, r, d, hcfg, dr, rm, m8)

# ---------------------------------------------------------------- tree rounds: membership in the 5040 shapes

def all_f(~pred: List<&2, Nat> -> Bool, xs: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(pred(p), all_f(~pred, rest))

def mb_and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mb_all_app(~pred: List<&2, Nat> -> Bool, xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>)
  -> {all_f(~pred, List.append(&2, List<&2, Nat>, xs, ys)) == Bool.and(all_f(~pred, xs), all_f(~pred, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(Bool, all_f(~pred, List.append(&2, List<&2, Nat>, rest, ys)), Bool.and(all_f(~pred, rest), all_f(~pred, ys)), mb_all_app(~pred, rest, ys)) :
        {Bool.and(pred(p), _) == Bool.and(Bool.and(pred(p), all_f(~pred, rest)), all_f(~pred, ys)) : Bool}
      mb_and_assoc(pred(p), all_f(~pred, rest), all_f(~pred, ys))

def mb_ext_all_app(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +r: Nat)
  -> {GtS.ext_all(List.append(&2, List<&2, Nat>, xs, ys), r) == List.append(&2, List<&2, Nat>, GtS.ext_all(xs, r), GtS.ext_all(ys, r)) : List<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(List<&2, List<&2, Nat>>, GtS.ext_all(List.append(&2, List<&2, Nat>, rest, ys), r),
          List.append(&2, List<&2, Nat>, GtS.ext_all(rest, r), GtS.ext_all(ys, r)), mb_ext_all_app(rest, ys, r)) :
        {List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), _) ==
          List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), GtS.ext_all(rest, r)), GtS.ext_all(ys, r)) : List<&2, List<&2, Nat>>}
      Equal.sym(List<&2, List<&2, Nat>>,
        List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), GtS.ext_all(rest, r)), GtS.ext_all(ys, r)),
        List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), List.append(&2, List<&2, Nat>, GtS.ext_all(rest, r), GtS.ext_all(ys, r))),
        LinkProof.ri_app_assoc(~List<&2, Nat>, GtS.ext_one(r, p), GtS.ext_all(rest, r), GtS.ext_all(ys, r)))

def mb_levels_app(n: Nat, +r: Nat, +xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>)
  -> {GtS.levels(n, r, List.append(&2, List<&2, Nat>, xs, ys)) == List.append(&2, List<&2, Nat>, GtS.levels(n, r, xs), GtS.levels(n, r, ys)) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(List<&2, List<&2, Nat>>, GtS.ext_all(List.append(&2, List<&2, Nat>, xs, ys), r),
          List.append(&2, List<&2, Nat>, GtS.ext_all(xs, r), GtS.ext_all(ys, r)), mb_ext_all_app(xs, ys, r)) :
        {GtS.levels(k, 1n+r, _) == List.append(&2, List<&2, Nat>, GtS.levels(k, 1n+r, GtS.ext_all(xs, r)), GtS.levels(k, 1n+r, GtS.ext_all(ys, r))) : List<&2, List<&2, Nat>>}
      mb_levels_app(k, 1n+r, GtS.ext_all(xs, r), GtS.ext_all(ys, r))

def sv_lt_ne(+q: Nat, +j: Nat, hq: {Nat.is_lt(q, 1n+j) == True{} : Bool}, e: {Nat.is_eq(q, j) == False{} : Bool})
  -> {Nat.is_lt(q, j) == True{} : Bool}:
  match q j:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, GP.ar_true_false(e))
    case 0n 1n+j1:
      {==}
    case 1n+q1 0n:
      Empty.absurd({Nat.is_lt(1n+q1, 0n) == True{} : Bool}, LinkProof.ri_lt_zero(q1, hq))
    case 1n+q1 1n+j1:
      sv_lt_ne(q1, j1, hq, e)

# The shapes under ext_one(k, pre) at any later level include pre ++ [q] for q < k.
def mb_pick_case(~pred: List<&2, Nat> -> Bool, b: Bool, +j: Nat, +pre: List<&2, Nat>, +q: Nat, +n: Nat, +r: Nat,
    e: {Nat.is_eq(q, j) == b : Bool}, hq: {Nat.is_lt(q, 1n+j) == True{} : Bool},
    hr: {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [Nat.sub(1n+j, 1n)])])) == True{} : Bool},
    ih: {Nat.is_lt(q, j) == True{} : Bool} -> {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [q])])) == True{} : Bool})
  -> {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [q])])) == True{} : Bool}:
  match b:
    case True{}:
      +qj = GP.ar_eq_true(q, j, e)
      %Equal.sym(Nat, q, j, qj) : {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [_])])) == True{} : Bool}
      %GP.ar_sub_zero_r(j) : {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [_])])) == True{} : Bool}
      hr
    case False{}:
      ih(sv_lt_ne(q, j, hq, e))

def mb_pick(~pred: List<&2, Nat> -> Bool, k: Nat, +pre: List<&2, Nat>, +q: Nat, +n: Nat, +r: Nat, hq: {Nat.is_lt(q, k) == True{} : Bool},
    +h: {all_f(~pred, GtS.levels(n, r, GtS.ext_one(k, pre))) == True{} : Bool})
  -> {all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [q])])) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({all_f(~pred, GtS.levels(n, r, [GtS.cat(pre, [q])])) == True{} : Bool}, LinkProof.ri_lt_zero(q, hq))
    case 1n+j:
      +j = j
      +A = GtS.levels(n, r, GtS.ext_one(j, pre))
      +B = GtS.levels(n, r, [GtS.cat(pre, [Nat.sub(1n+j, 1n)])])
      +hab = Equal.trans(Bool, Bool.and(all_f(~pred, A), all_f(~pred, B)),
        all_f(~pred, List.append(&2, List<&2, Nat>, A, B)), True{},
        Equal.sym(Bool, all_f(~pred, List.append(&2, List<&2, Nat>, A, B)), Bool.and(all_f(~pred, A), all_f(~pred, B)), mb_all_app(~pred, A, B)),
        Equal.trans(Bool, all_f(~pred, List.append(&2, List<&2, Nat>, A, B)),
          all_f(~pred, GtS.levels(n, r, List.append(&2, List<&2, Nat>, GtS.ext_one(j, pre), [GtS.cat(pre, [Nat.sub(1n+j, 1n)])]))), True{},
          Equal.cong(List<&2, List<&2, Nat>>, Bool, y => all_f(~pred, y), List.append(&2, List<&2, Nat>, A, B),
            GtS.levels(n, r, List.append(&2, List<&2, Nat>, GtS.ext_one(j, pre), [GtS.cat(pre, [Nat.sub(1n+j, 1n)])])),
            Equal.sym(List<&2, List<&2, Nat>>, GtS.levels(n, r, List.append(&2, List<&2, Nat>, GtS.ext_one(j, pre), [GtS.cat(pre, [Nat.sub(1n+j, 1n)])])),
              List.append(&2, List<&2, Nat>, A, B), mb_levels_app(n, r, GtS.ext_one(j, pre), [GtS.cat(pre, [Nat.sub(1n+j, 1n)])]))),
          h))
      mb_pick_case(~pred, Nat.is_eq(q, j), j, pre, q, n, r, {==}, hq, GP.ar_and_r(all_f(~pred, A), all_f(~pred, B), hab),
        lt => mb_pick(~pred, j, pre, q, n, r, lt, GP.ar_and_l(all_f(~pred, A), all_f(~pred, B), hab)))

def mb_step(~pred: List<&2, Nat> -> Bool, +n: Nat, +r: Nat, +p: List<&2, Nat>, +q: Nat, hq: {Nat.is_lt(q, r) == True{} : Bool},
    h: {all_f(~pred, GtS.levels(1n+n, r, [p])) == True{} : Bool})
  -> {all_f(~pred, GtS.levels(n, 1n+r, [GtS.cat(p, [q])])) == True{} : Bool}:
  mb_pick(~pred, r, p, q, n, 1n+r, hq,
    Equal.trans(Bool, all_f(~pred, GtS.levels(n, 1n+r, GtS.ext_one(r, p))),
      all_f(~pred, GtS.levels(n, 1n+r, List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), Nil{}))), True{},
      Equal.cong(List<&2, List<&2, Nat>>, Bool, y => all_f(~pred, GtS.levels(n, 1n+r, y)), GtS.ext_one(r, p),
        List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), Nil{}),
        Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, GtS.ext_one(r, p), Nil{}), GtS.ext_one(r, p),
          LinkProof.ri_app_nil(~List<&2, Nat>, GtS.ext_one(r, p)))),
      h))

# The path built by mb_member's steps is the literal parent array (mb_member's instances at concrete
# predicates then never evaluate a predicate on two different spellings of the shape).
def mb_cat7(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat)
  -> {[0n, q1, q2, q3, q4, q5, q6, q7] ==
      GtS.cat(GtS.cat(GtS.cat(GtS.cat(GtS.cat(GtS.cat(GtS.cat([0n], [q1]), [q2]), [q3]), [q4]), [q5]), [q6]), [q7]) : List<&2, Nat>}:
  {==}

# GtS.shapes() as the first step of the level recursion (stated once, so that mb_member's steps are
# syntactic and the BendTT kernel never compares the 5040-shape lists inside a predicate).
def mb_shapes_eq() -> {GtS.shapes() == GtS.levels(1n+6n, 1n, [[0n]]) : List<&2, List<&2, Nat>>}:
  {==}

def mb_h0(~pred: List<&2, Nat> -> Bool, h: {all_f(~pred, GtS.shapes()) == True{} : Bool})
  -> {all_f(~pred, GtS.levels(1n+6n, 1n, [[0n]])) == True{} : Bool}:
  %mb_shapes_eq() : {all_f(~pred, _) == True{} : Bool}
  h

# A legal shape [0, q1, .., q7] satisfies every predicate true on all of GtS.shapes().
def mb_member(~pred: List<&2, Nat> -> Bool, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, h: {all_f(~pred, GtS.shapes()) == True{} : Bool})
  -> {pred([0n, q1, q2, q3, q4, q5, q6, q7]) == True{} : Bool}:
  +l1 = GP.ar_and_l(Nat.is_lt(q1, 1n), Bool.and(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)))))), legal)
  +r1 = GP.ar_and_r(Nat.is_lt(q1, 1n), Bool.and(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)))))), legal)
  +l2 = GP.ar_and_l(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n))))), r1)
  +r2 = GP.ar_and_r(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n))))), r1)
  +l3 = GP.ar_and_l(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)))), r2)
  +r3 = GP.ar_and_r(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)))), r2)
  +l4 = GP.ar_and_l(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n))), r3)
  +r4 = GP.ar_and_r(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n))), r3)
  +l5 = GP.ar_and_l(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)), r4)
  +r5 = GP.ar_and_r(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)), r4)
  +l6 = GP.ar_and_l(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n), r5)
  +l7 = GP.ar_and_r(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n), r5)
  +h0 = mb_h0(~pred, h)
  +p1 = GtS.cat([0n], [q1])
  +p2 = GtS.cat(p1, [q2])
  +p3 = GtS.cat(p2, [q3])
  +p4 = GtS.cat(p3, [q4])
  +p5 = GtS.cat(p4, [q5])
  +p6 = GtS.cat(p5, [q6])
  +p7 = GtS.cat(p6, [q7])
  +h1 = mb_step(~pred, 6n, 1n, [0n], q1, l1, h0)
  +h2 = mb_step(~pred, 5n, 2n, p1, q2, l2, h1)
  +h3 = mb_step(~pred, 4n, 3n, p2, q3, l3, h2)
  +h4 = mb_step(~pred, 3n, 4n, p3, q4, l4, h3)
  +h5 = mb_step(~pred, 2n, 5n, p4, q5, l5, h4)
  +h6 = mb_step(~pred, 1n, 6n, p5, q6, l6, h5)
  +h7 = mb_step(~pred, 0n, 7n, p6, q7, l7, h6)
  %Equal.sym(List<&2, Nat>, [0n, q1, q2, q3, q4, q5, q6, q7], p7, mb_cat7(q1, q2, q3, q4, q5, q6, q7)) : {pred(_) == True{} : Bool}
  GP.ar_and_l(pred(p7), True{}, h7)

# ---------------------------------------------------------------- tree rounds: the per-shape decision procedure

# The reference ancestors of row r at depths j .. j + k - 1 (attn_tree_spec).
def atab(k: Nat, +j: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      AtS.anc(ps, r, j) <> atab(k1, 1n+j, ps, r)

# Ancestors j .. j + k - 1 of the path pi: each one's path is pi's prefix (W_pre), a row < 8 (W_rng).
def pre_ok(k: Nat, +j: Nat, +par: List<&2, Nat>, +pi: List<&2, Nat>) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+k1:
      Bool.and(Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, j)), List.take(&2, Nat, pi, 1n+j)), Nat.is_lt(Link.nthn(pi, j), 8n)),
        pre_ok(k1, 1n+j, par, pi))

# Row r of the shape par = [0, q1, .., q7]: W_last, W_pre / W_rng, W_dep, and the attention
# reference (attn_tree_spec depth and ancestors) agrees with the path.
def trow_ok(+par: List<&2, Nat>, +r: Nat) -> Bool:
  +pi = GtS.path(par, r)
  +d = Nat.sub(List.length(&2, Nat, pi), 1n)
  +ps = List.tail(&2, Nat, par)
  Bool.and(GtS.nat_eq_list(List.append(&2, Nat, List.take(&2, Nat, pi, d), [r]), pi),
    Bool.and(pre_ok(d, 0n, par, pi),
      Bool.and(Nat.is_le(d, r),
        Bool.and(Nat.is_eq(AtS.depth(ps, r), d), GtS.nat_eq_list(atab(d, 0n, ps, r), List.take(&2, Nat, pi, d))))))

def trows_ok(k: Nat, +r: Nat, +par: List<&2, Nat>) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+k1:
      Bool.and(trow_ok(par, r), trows_ok(k1, 1n+r, par))

def link_ok(par: List<&2, Nat>) -> Bool:
  trows_ok(8n, 0n, par)

# The one computed fact: the checker evaluates link_ok on all 5040 shapes, split by the first three
# parents (the 6 prefixes [0, 0, q2, q3] of GtS.shapes() at level 4, 840 shapes each) so that each
# evaluation fits the BendTT kernel's per-definition fuel.
def ta_split(+a: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, ha: {all_f(~link_ok, GtS.levels(4n, 4n, [a])) == True{} : Bool},
    hr: {all_f(~link_ok, GtS.levels(4n, 4n, rest)) == True{} : Bool})
  -> {all_f(~link_ok, GtS.levels(4n, 4n, a <> rest)) == True{} : Bool}:
  Equal.trans(Bool, all_f(~link_ok, GtS.levels(4n, 4n, a <> rest)),
    all_f(~link_ok, List.append(&2, List<&2, Nat>, GtS.levels(4n, 4n, [a]), GtS.levels(4n, 4n, rest))), True{},
    Equal.cong(List<&2, List<&2, Nat>>, Bool, y => all_f(~link_ok, y), GtS.levels(4n, 4n, a <> rest),
      List.append(&2, List<&2, Nat>, GtS.levels(4n, 4n, [a]), GtS.levels(4n, 4n, rest)), mb_levels_app(4n, 4n, [a], rest)),
    Equal.trans(Bool, all_f(~link_ok, List.append(&2, List<&2, Nat>, GtS.levels(4n, 4n, [a]), GtS.levels(4n, 4n, rest))),
      Bool.and(all_f(~link_ok, GtS.levels(4n, 4n, [a])), all_f(~link_ok, GtS.levels(4n, 4n, rest))), True{},
      mb_all_app(~link_ok, GtS.levels(4n, 4n, [a]), GtS.levels(4n, 4n, rest)),
      sd_and_tt2(all_f(~link_ok, GtS.levels(4n, 4n, [a])), all_f(~link_ok, GtS.levels(4n, 4n, rest)), ha, hr)))

def ta_0() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 0n, 0n]])) == True{} : Bool}:
  {==}

def ta_1() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 0n, 1n]])) == True{} : Bool}:
  {==}

def ta_2() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 0n, 2n]])) == True{} : Bool}:
  {==}

def ta_3() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 1n, 0n]])) == True{} : Bool}:
  {==}

def ta_4() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 1n, 1n]])) == True{} : Bool}:
  {==}

def ta_5() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 1n, 2n]])) == True{} : Bool}:
  {==}

def ta_all() -> {all_f(~link_ok, GtS.levels(4n, 4n, [[0n, 0n, 0n, 0n], [0n, 0n, 0n, 1n], [0n, 0n, 0n, 2n], [0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]])) == True{} : Bool}:
  ta_split([0n, 0n, 0n, 0n], [[0n, 0n, 0n, 1n], [0n, 0n, 0n, 2n], [0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]], ta_0(),
    ta_split([0n, 0n, 0n, 1n], [[0n, 0n, 0n, 2n], [0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]], ta_1(),
      ta_split([0n, 0n, 0n, 2n], [[0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]], ta_2(),
        ta_split([0n, 0n, 1n, 0n], [[0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]], ta_3(),
          ta_split([0n, 0n, 1n, 1n], [[0n, 0n, 1n, 2n]], ta_4(),
            ta_split([0n, 0n, 1n, 2n], Nil{}, ta_5(), {==}))))))

# GtS.shapes() is that level-4 split (the checker builds both lists; no predicate is evaluated).
def ta_shapes() -> {GtS.shapes() == GtS.levels(4n, 4n, [[0n, 0n, 0n, 0n], [0n, 0n, 0n, 1n], [0n, 0n, 0n, 2n], [0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]]) : List<&2, List<&2, Nat>>}:
  {==}

def tree_all() -> {all_f(~link_ok, GtS.shapes()) == True{} : Bool}:
  %Equal.sym(List<&2, List<&2, Nat>>, GtS.shapes(), GtS.levels(4n, 4n, [[0n, 0n, 0n, 0n], [0n, 0n, 0n, 1n], [0n, 0n, 0n, 2n], [0n, 0n, 1n, 0n], [0n, 0n, 1n, 1n], [0n, 0n, 1n, 2n]]), ta_shapes()) : {all_f(~link_ok, _) == True{} : Bool}
  ta_all()

# ---------------------------------------------------------------- elimination

def nel(xs: List<&2, Nat>, ys: List<&2, Nat>, h: {GtS.nat_eq_list(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> b:
          Empty.absurd({Nil{} == y <> b : List<&2, Nat>}, GP.ar_false_true(h))
    case +x <> +a:
      match ys:
        case Nil{}:
          Empty.absurd({x <> a == Nil{} : List<&2, Nat>}, GP.ar_false_true(h))
        case +y <> +b:
          +hh = h
          +exy = GP.ar_eq_true(x, y, GP.ar_and_l(Nat.is_eq(x, y), GtS.nat_eq_list(a, b), hh))
          +eab = nel(a, b, GP.ar_and_r(Nat.is_eq(x, y), GtS.nat_eq_list(a, b), hh))
          LinkProof.ri_cong_cons(~Nat, x, y, a, b, exy, eab)

def trows_el(+k: Nat, +r0: Nat, +par: List<&2, Nat>, +t: Nat, ht: {Nat.is_lt(t, k) == True{} : Bool},
    +h: {trows_ok(k, r0, par) == True{} : Bool}) -> {trow_ok(par, Nat.add(r0, t)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({trow_ok(par, Nat.add(r0, t)) == True{} : Bool}, LinkProof.ri_lt_zero(t, ht))
    case 1n+k1:
      match t:
        case 0n:
          %LinkProof.ri_zr(r0) : {trow_ok(par, _) == True{} : Bool}
          GP.ar_and_l(trow_ok(par, r0), trows_ok(k1, 1n+r0, par), h)
        case 1n+t1:
          %LinkProof.ri_sr(r0, t1) : {trow_ok(par, _) == True{} : Bool}
          trows_el(k1, 1n+r0, par, t1, ht, GP.ar_and_r(trow_ok(par, r0), trows_ok(k1, 1n+r0, par), h))

def pre_el(+k: Nat, +j0: Nat, +par: List<&2, Nat>, +pi: List<&2, Nat>, +t: Nat, ht: {Nat.is_lt(t, k) == True{} : Bool},
    +h: {pre_ok(k, j0, par, pi) == True{} : Bool})
  -> {Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, Nat.add(j0, t))), List.take(&2, Nat, pi, 1n+Nat.add(j0, t))),
        Nat.is_lt(Link.nthn(pi, Nat.add(j0, t)), 8n)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, Nat.add(j0, t))), List.take(&2, Nat, pi, 1n+Nat.add(j0, t))),
        Nat.is_lt(Link.nthn(pi, Nat.add(j0, t)), 8n)) == True{} : Bool}, LinkProof.ri_lt_zero(t, ht))
    case 1n+k1:
      match t:
        case 0n:
          %LinkProof.ri_zr(j0) : {Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, _)), List.take(&2, Nat, pi, 1n+_)),
            Nat.is_lt(Link.nthn(pi, _), 8n)) == True{} : Bool}
          GP.ar_and_l(Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, j0)), List.take(&2, Nat, pi, 1n+j0)), Nat.is_lt(Link.nthn(pi, j0), 8n)),
            pre_ok(k1, 1n+j0, par, pi), h)
        case 1n+t1:
          %LinkProof.ri_sr(j0, t1) : {Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, _)), List.take(&2, Nat, pi, 1n+_)),
            Nat.is_lt(Link.nthn(pi, _), 8n)) == True{} : Bool}
          pre_el(k1, 1n+j0, par, pi, t1, ht,
            GP.ar_and_r(Bool.and(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, j0)), List.take(&2, Nat, pi, 1n+j0)), Nat.is_lt(Link.nthn(pi, j0), 8n)),
              pre_ok(k1, 1n+j0, par, pi), h))

# ---------------------------------------------------------------- tree rounds: the 5109 law, per shape

def gt_ok(par: List<&2, Nat>) -> Bool:
  GtL.shape_ok(par)

def gt_all(xs: List<&2, List<&2, Nat>>) -> {GtL.all_ok(xs) == all_f(~gt_ok, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +p <> rest:
      Equal.cong(Bool, Bool, y => Bool.and(GtL.shape_ok(p), y), GtL.all_ok(rest), all_f(~gt_ok, rest), gt_all(rest))

def gt_rows(+par: List<&2, Nat>, w: GtI.W, h: {GtL.shape_w(par, w) == True{} : Bool})
  -> {GtL.rows_ok.go(8n, 0n, par, Served.outs_of(w)) == True{} : Bool}:
  match w:
    case GtI.W{a, b, +outs, +bufs}:
      GP.ar_and_l(GtL.rows_ok.go(8n, 0n, par, outs), GtL.commit_rows.go(8n, 0n, par),
        GP.ar_and_r(Bool.and(GtL.prog_ok(par), GtL.alternates(bufs)), Bool.and(GtL.rows_ok.go(8n, 0n, par, outs), GtL.commit_rows.go(8n, 0n, par)), h))

def gt_rows_el(+k: Nat, +r0: Nat, +par: List<&2, Nat>, +outs: List<&2, GtI.Out>, +t: Nat, ht: {Nat.is_lt(t, k) == True{} : Bool},
    +h: {GtL.rows_ok.go(k, r0, par, outs) == True{} : Bool}) -> {GtL.row_ok(Nat.add(r0, t), par, outs) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({GtL.row_ok(Nat.add(r0, t), par, outs) == True{} : Bool}, LinkProof.ri_lt_zero(t, ht))
    case 1n+k1:
      match t:
        case 0n:
          %LinkProof.ri_zr(r0) : {GtL.row_ok(_, par, outs) == True{} : Bool}
          GP.ar_and_l(GtL.row_ok(r0, par, outs), GtL.rows_ok.go(k1, 1n+r0, par, outs), h)
        case 1n+t1:
          %LinkProof.ri_sr(r0, t1) : {GtL.row_ok(_, par, outs) == True{} : Bool}
          gt_rows_el(k1, 1n+r0, par, outs, t1, ht, GP.ar_and_r(GtL.row_ok(r0, par, outs), GtL.rows_ok.go(k1, 1n+r0, par, outs), h))

def sv_hist(+r: Nat, outs: List<&2, GtI.Out>) -> {Served.hist(r, outs) == GtL.hist_of(r, outs) : List<&2, Nat>}:
  match outs:
    case Nil{}:
      {==}
    case GtI.Out{+x, +h} <> rest:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => GtS.sel_l(Nat.is_eq(x, r), h, y), Served.hist(r, rest), GtL.hist_of(r, rest), sv_hist(r, rest))

# 5109 row r of a legal shape: the program's row_ok conjuncts (gdn_tree_laws.tree_all_shapes).
def gt_row(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool})
  -> {GtL.row_ok(r, [0n, q1, q2, q3, q4, q5, q6, q7], Served.outs_of(GtI.run([0n, q1, q2, q3, q4, q5, q6, q7]))) == True{} : Bool}:
  +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
  +all = Equal.trans(Bool, all_f(~gt_ok, GtS.shapes()), GtL.all_ok(GtS.shapes()), True{},
    Equal.sym(Bool, GtL.all_ok(GtS.shapes()), all_f(~gt_ok, GtS.shapes()), gt_all(GtS.shapes())),
    snd({Nat.is_eq(List.length(&2, List<&2, Nat>, GtS.shapes()), 5040n) == True{} : Bool}, {GtL.all_ok(GtS.shapes()) == True{} : Bool},
      GtL.tree_all_shapes()))
  +hs = mb_member(~gt_ok, q1, q2, q3, q4, q5, q6, q7, legal, all)
  gt_rows_el(8n, 0n, par, Served.outs_of(GtI.run(par)), r, hr, gt_rows(par, GtI.run(par), hs))

# The state history row r is emitted from is its path.
def gt_hist(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool})
  -> {Served.hist(r, Served.outs_of(GtI.run([0n, q1, q2, q3, q4, q5, q6, q7]))) == GtS.path([0n, q1, q2, q3, q4, q5, q6, q7], r) : List<&2, Nat>}:
  +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
  +outs = Served.outs_of(GtI.run(par))
  +P = GtS.path(par, r)
  +hrow = gt_row(q1, q2, q3, q4, q5, q6, q7, legal, r, hr)
  +emit = GP.ar_and_l(Bool.and(Nat.is_eq(GtL.count_row(r, outs), 1n), GtS.nat_eq_list(GtL.hist_of(r, outs), P)),
    Bool.and(Bool.and(GtS.nat_eq_list(GtI.window(par, r), GtS.verify_window(par, r)), Nat.is_le(GtL.maxl(GtI.window(par, r)), Nat.add(4n, r))),
      GtS.nat_eq_list(GtI.replay_rows(GtI.row_map(P, GtS.len(P)), GtS.len(P)), GtL.hist_of(r, outs))), hrow)
  Equal.trans(List<&2, Nat>, Served.hist(r, outs), GtL.hist_of(r, outs), P, sv_hist(r, outs),
    nel(GtL.hist_of(r, outs), P, GP.ar_and_r(Nat.is_eq(GtL.count_row(r, outs), 1n), GtS.nat_eq_list(GtL.hist_of(r, outs), P), emit)))

def Laws.gdn_tree_conv_window(q1, q2, q3, q4, q5, q6, q7, legal, r, hr):
  +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
  +outs = Served.outs_of(GtI.run(par))
  +P = GtS.path(par, r)
  +hrow = gt_row(q1, q2, q3, q4, q5, q6, q7, legal, r, hr)
  +rest = GP.ar_and_r(Bool.and(Nat.is_eq(GtL.count_row(r, outs), 1n), GtS.nat_eq_list(GtL.hist_of(r, outs), P)),
    Bool.and(Bool.and(GtS.nat_eq_list(GtI.window(par, r), GtS.verify_window(par, r)), Nat.is_le(GtL.maxl(GtI.window(par, r)), Nat.add(4n, r))),
      GtS.nat_eq_list(GtI.replay_rows(GtI.row_map(P, GtS.len(P)), GtS.len(P)), GtL.hist_of(r, outs))), hrow)
  +win = GP.ar_and_l(Bool.and(GtS.nat_eq_list(GtI.window(par, r), GtS.verify_window(par, r)), Nat.is_le(GtL.maxl(GtI.window(par, r)), Nat.add(4n, r))),
    GtS.nat_eq_list(GtI.replay_rows(GtI.row_map(P, GtS.len(P)), GtS.len(P)), GtL.hist_of(r, outs)), rest)
  nel(GtI.window(par, r), GtS.verify_window(par, r),
    GP.ar_and_l(GtS.nat_eq_list(GtI.window(par, r), GtS.verify_window(par, r)), Nat.is_le(GtL.maxl(GtI.window(par, r)), Nat.add(4n, r)), win))

# ---------------------------------------------------------------- tree rounds: 3012 gathers

# The admitting pass's stash rows at in-round columns j0 .. j0 + k - 1 are r's reference ancestors
# (attn_tree_laws.path_prefix, for columns <= depth[r]).
def ag_eq(+k: Nat, +j0: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool},
    +hk: {Nat.is_le(Nat.add(j0, k), AtS.depth([q1, q2, q3, q4, q5, q6, q7], r)) == True{} : Bool})
  -> {Served.agather(k, j0, AtS.desc([q1, q2, q3, q4, q5, q6, q7]), r) == atab(k, j0, [q1, q2, q3, q4, q5, q6, q7], r) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +ps = {[q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +d = AtS.desc(ps)
      +hj = GP.ar_lt_le(j0, AtS.depth(ps, r), GP.ar_lt_le_trans(j0, Nat.add(j0, 1n+k1), AtS.depth(ps, r), LinkProof.ri_lt_add(j0, k1), hk))
      +hd = snd({Nat.is_le(AtS.depth(ps, r), AtI.depth(d, AtI.leaf_of(d, r))) == True{} : Bool},
        {AtI.path(d, AtI.leaf_of(d, r), j0) == AtS.anc(ps, r, j0) : Nat},
        AtL.path_prefix(q1, q2, q3, q4, q5, q6, q7, legal, r, j0, hr, hj))
      +hk2 = Equal.trans(Bool, Nat.is_le(Nat.add(1n+j0, k1), AtS.depth(ps, r)), Nat.is_le(Nat.add(j0, 1n+k1), AtS.depth(ps, r)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, AtS.depth(ps, r)), 1n+Nat.add(j0, k1), Nat.add(j0, 1n+k1), LinkProof.ri_sr(j0, k1)), hk)
      LinkProof.ri_cong_cons(~Nat, AtI.path(d, AtI.leaf_of(d, r), j0), AtS.anc(ps, r, j0),
        Served.agather(k1, 1n+j0, d, r), atab(k1, 1n+j0, ps, r), hd,
        ag_eq(k1, 1n+j0, q1, q2, q3, q4, q5, q6, q7, legal, r, hr, hk2))

# ---------------------------------------------------------------- the served path / gather obligations

# Row r of a legal tree: the decided conjuncts (tree_all + membership).
def tf_row(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool})
  -> {trow_ok([0n, q1, q2, q3, q4, q5, q6, q7], r) == True{} : Bool}:
  trows_el(8n, 0n, [0n, q1, q2, q3, q4, q5, q6, q7], r, hr, mb_member(~link_ok, q1, q2, q3, q4, q5, q6, q7, legal, tree_all()))

# The conjuncts, by name.
def TA(+par: List<&2, Nat>, +r: Nat) -> Bool:
  GtS.nat_eq_list(List.append(&2, Nat, List.take(&2, Nat, GtS.path(par, r), Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n)), [r]), GtS.path(par, r))

def TB(+par: List<&2, Nat>, +r: Nat) -> Bool:
  pre_ok(Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n), 0n, par, GtS.path(par, r))

def TC(+par: List<&2, Nat>, +r: Nat) -> Bool:
  Nat.is_le(Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n), r)

def TD(+par: List<&2, Nat>, +r: Nat) -> Bool:
  Nat.is_eq(AtS.depth(List.tail(&2, Nat, par), r), Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n))

def TE(+par: List<&2, Nat>, +r: Nat) -> Bool:
  GtS.nat_eq_list(atab(Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n), 0n, List.tail(&2, Nat, par), r),
    List.take(&2, Nat, GtS.path(par, r), Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n)))

def tf_a(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool}) -> {TA(par, r) == True{} : Bool}:
  GP.ar_and_l(TA(par, r), Bool.and(TB(par, r), Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r)))), h)

def tf_rest1(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool})
  -> {Bool.and(TB(par, r), Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r)))) == True{} : Bool}:
  GP.ar_and_r(TA(par, r), Bool.and(TB(par, r), Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r)))), h)

def tf_b(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool}) -> {TB(par, r) == True{} : Bool}:
  GP.ar_and_l(TB(par, r), Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r))), tf_rest1(par, r, h))

def tf_rest2(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool})
  -> {Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r))) == True{} : Bool}:
  GP.ar_and_r(TB(par, r), Bool.and(TC(par, r), Bool.and(TD(par, r), TE(par, r))), tf_rest1(par, r, h))

def tf_c(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool}) -> {TC(par, r) == True{} : Bool}:
  GP.ar_and_l(TC(par, r), Bool.and(TD(par, r), TE(par, r)), tf_rest2(par, r, h))

def tf_d(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool}) -> {TD(par, r) == True{} : Bool}:
  GP.ar_and_l(TD(par, r), TE(par, r), GP.ar_and_r(TC(par, r), Bool.and(TD(par, r), TE(par, r)), tf_rest2(par, r, h)))

def tf_e(+par: List<&2, Nat>, +r: Nat, +h: {trow_ok(par, r) == True{} : Bool}) -> {TE(par, r) == True{} : Bool}:
  GP.ar_and_r(TD(par, r), TE(par, r), GP.ar_and_r(TC(par, r), Bool.and(TD(par, r), TE(par, r)), tf_rest2(par, r, h)))

# ok(Tree, m): the shape is legal and m == 8
def ok_legal(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +m: Nat,
    +h: {Served.ok(Served.Tree{q1, q2, q3, q4, q5, q6, q7}, m) == True{} : Bool}) -> {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}:
  GP.ar_and_l(AtS.legal(q1, q2, q3, q4, q5, q6, q7), Nat.is_eq(m, 8n), h)

def ok_m8(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +m: Nat,
    +h: {Served.ok(Served.Tree{q1, q2, q3, q4, q5, q6, q7}, m) == True{} : Bool}) -> {m == 8n : Nat}:
  GP.ar_eq_true(m, 8n, GP.ar_and_r(AtS.legal(q1, q2, q3, q4, q5, q6, q7), Nat.is_eq(m, 8n), h))

def ok_r8(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +m: Nat, +r: Nat,
    +h: {Served.ok(Served.Tree{q1, q2, q3, q4, q5, q6, q7}, m) == True{} : Bool}, +rm: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Nat.is_lt(r, 8n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(r, 8n), Nat.is_lt(r, m), True{},
    Equal.cong(Nat, Bool, y => Nat.is_lt(r, y), 8n, m, Equal.sym(Nat, m, 8n, ok_m8(q1, q2, q3, q4, q5, q6, q7, m, h))), rm)

def sv_w_last(sh: Served.Shape, +m: Nat, +r: Nat, ok_: {Served.ok(sh, m) == True{} : Bool}, rm_: {Nat.is_lt(r, m) == True{} : Bool})
  -> {List.append(&2, Nat, List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)), [r]) == Served.pth(sh, r) : List<&2, Nat>}:
  match sh:
    case Served.Chain{}:
      +ok = ok_
      +rm = rm_
      %Equal.sym(Nat, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r), r, sq_dep(r)) :
        {List.append(&2, Nat, List.take(&2, Nat, Served.seqn(1n+r, 0n), _), [r]) == Served.seqn(1n+r, 0n) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.take(&2, Nat, Served.seqn(1n+r, 0n), r), Served.seqn(r, 0n), sq_take(1n+r, 0n, r, GP.ar_h_le_succ(r))) :
        {List.append(&2, Nat, _, [r]) == Served.seqn(1n+r, 0n) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, Served.seqn(1n+r, 0n), List.append(&2, Nat, Served.seqn(r, 0n), [r]), sq_snoc(r, 0n))
    case Served.Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +ok = ok_
      +rm = rm_
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +h = tf_row(q1, q2, q3, q4, q5, q6, q7, ok_legal(q1, q2, q3, q4, q5, q6, q7, m, ok), r, ok_r8(q1, q2, q3, q4, q5, q6, q7, m, r, ok, rm))
      nel(List.append(&2, Nat, List.take(&2, Nat, GtS.path(par, r), Nat.sub(List.length(&2, Nat, GtS.path(par, r)), 1n)), [r]), GtS.path(par, r),
        tf_a(par, r, h))

def sv_w_dep(sh: Served.Shape, +m: Nat, +r: Nat, ok_: {Served.ok(sh, m) == True{} : Bool}, rm_: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Nat.is_le(Link.dep(~Served.Shape, ~Served.pth, sh, r), r) == True{} : Bool}:
  match sh:
    case Served.Chain{}:
      +ok = ok_
      +rm = rm_
      %Equal.sym(Nat, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r), r, sq_dep(r)) : {Nat.is_le(_, r) == True{} : Bool}
      GP.ar_le_refl(r)
    case Served.Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +ok = ok_
      +rm = rm_
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      tf_c(par, r, tf_row(q1, q2, q3, q4, q5, q6, q7, ok_legal(q1, q2, q3, q4, q5, q6, q7, m, ok), r, ok_r8(q1, q2, q3, q4, q5, q6, q7, m, r, ok, rm)))

def Laws.served_w_pre(sh, m, r, j, ok_, rm_, jd_):
  match sh:
    case Served.Chain{}:
      +ok = ok_
      +rm = rm_
      +jd = jd_
      +jr = Equal.trans(Bool, Nat.is_lt(j, r), Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(j, y), r, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r),
          Equal.sym(Nat, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r), r, sq_dep(r))), jd)
      +jr1 = GP.ar_lt_trans(j, r, 1n+r, jr, LinkProof.ri_lt_s(r))
      %Equal.sym(Nat, Link.nthn(Served.seqn(1n+r, 0n), j), j, sq_nth(1n+r, 0n, j, jr1)) :
        {Served.seqn(1n+_, 0n) == List.take(&2, Nat, Served.seqn(1n+r, 0n), 1n+j) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.take(&2, Nat, Served.seqn(1n+r, 0n), 1n+j), Served.seqn(1n+j, 0n),
        sq_take(1n+r, 0n, 1n+j, GP.ar_lt_le(j, r, jr)))
    case Served.Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +ok = ok_
      +rm = rm_
      +jd = jd_
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +pi = GtS.path(par, r)
      +d = Nat.sub(List.length(&2, Nat, pi), 1n)
      +h = tf_row(q1, q2, q3, q4, q5, q6, q7, ok_legal(q1, q2, q3, q4, q5, q6, q7, m, ok), r, ok_r8(q1, q2, q3, q4, q5, q6, q7, m, r, ok, rm))
      nel(GtS.path(par, Link.nthn(pi, j)), List.take(&2, Nat, pi, 1n+j),
        GP.ar_and_l(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, j)), List.take(&2, Nat, pi, 1n+j)), Nat.is_lt(Link.nthn(pi, j), 8n),
          pre_el(d, 0n, par, pi, j, jd, tf_b(par, r, h))))

def sv_w_rng(sh: Served.Shape, +m: Nat, +r: Nat, +j: Nat, ok_: {Served.ok(sh, m) == True{} : Bool}, rm_: {Nat.is_lt(r, m) == True{} : Bool},
    jd_: {Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, sh, r)) == True{} : Bool})
  -> {Nat.is_lt(Link.nthn(Served.pth(sh, r), j), m) == True{} : Bool}:
  match sh:
    case Served.Chain{}:
      +ok = ok_
      +rm = rm_
      +jd = jd_
      +jr = Equal.trans(Bool, Nat.is_lt(j, r), Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(j, y), r, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r),
          Equal.sym(Nat, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r), r, sq_dep(r))), jd)
      %Equal.sym(Nat, Link.nthn(Served.seqn(1n+r, 0n), j), j, sq_nth(1n+r, 0n, j, GP.ar_lt_trans(j, r, 1n+r, jr, LinkProof.ri_lt_s(r)))) :
        {Nat.is_lt(_, m) == True{} : Bool}
      GP.ar_lt_trans(j, r, m, jr, rm)
    case Served.Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +ok = ok_
      +rm = rm_
      +jd = jd_
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +pi = GtS.path(par, r)
      +d = Nat.sub(List.length(&2, Nat, pi), 1n)
      +h = tf_row(q1, q2, q3, q4, q5, q6, q7, ok_legal(q1, q2, q3, q4, q5, q6, q7, m, ok), r, ok_r8(q1, q2, q3, q4, q5, q6, q7, m, r, ok, rm))
      %Equal.sym(Nat, m, 8n, ok_m8(q1, q2, q3, q4, q5, q6, q7, m, ok)) : {Nat.is_lt(Link.nthn(pi, j), _) == True{} : Bool}
      GP.ar_and_r(GtS.nat_eq_list(GtS.path(par, Link.nthn(pi, j)), List.take(&2, Nat, pi, 1n+j)), Nat.is_lt(Link.nthn(pi, j), 8n),
        pre_el(d, 0n, par, pi, j, jd, tf_b(par, r, h)))

# Tree gathers, by layer kind.
def og_tree(b: Bool, +l: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat,
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool},
    e: {Served.is_attn(l) == b : Bool})
  -> {Served.gat(l, Served.Tree{q1, q2, q3, q4, q5, q6, q7}, r) ==
      List.take(&2, Nat, GtS.path([0n, q1, q2, q3, q4, q5, q6, q7], r), Nat.sub(List.length(&2, Nat, GtS.path([0n, q1, q2, q3, q4, q5, q6, q7], r)), 1n)) : List<&2, Nat>}:
  match b:
    case True{}:
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +ps = {[q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +pi = GtS.path(par, r)
      +d = Nat.sub(List.length(&2, Nat, pi), 1n)
      %Equal.sym(Bool, Served.is_attn(l), True{}, e) : {Served.pick_l(_, Served.attn_gather(ps, r), Served.gdn_gather(par, r)) == List.take(&2, Nat, pi, d) : List<&2, Nat>}
      +h = tf_row(q1, q2, q3, q4, q5, q6, q7, legal, r, hr)
      +dd = GP.ar_eq_true(AtS.depth(ps, r), d, tf_d(par, r, h))
      +e1 = Equal.cong(Nat, List<&2, Nat>, y => Served.agather(y, 0n, AtS.desc(ps), r), AtI.depth(AtS.desc(ps), r), d,
        Equal.trans(Nat, AtI.depth(AtS.desc(ps), r), AtS.depth(ps, r), d, AtP.br_depth(ps, r, hr), dd))
      +e2 = ag_eq(d, 0n, q1, q2, q3, q4, q5, q6, q7, legal, r, hr,
        Equal.trans(Bool, Nat.is_le(d, AtS.depth(ps, r)), Nat.is_le(d, d), True{},
          Equal.cong(Nat, Bool, y => Nat.is_le(d, y), AtS.depth(ps, r), d, dd), GP.ar_le_refl(d)))
      +e3 = nel(atab(d, 0n, ps, r), List.take(&2, Nat, pi, d), tf_e(par, r, h))
      Equal.trans(List<&2, Nat>, Served.agather(AtI.depth(AtS.desc(ps), r), 0n, AtS.desc(ps), r), Served.agather(d, 0n, AtS.desc(ps), r),
        List.take(&2, Nat, pi, d), e1,
        Equal.trans(List<&2, Nat>, Served.agather(d, 0n, AtS.desc(ps), r), atab(d, 0n, ps, r), List.take(&2, Nat, pi, d), e2, e3))
    case False{}:
      +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +ps = {[q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
      +pi = GtS.path(par, r)
      %Equal.sym(Bool, Served.is_attn(l), False{}, e) : {Served.pick_l(_, Served.attn_gather(ps, r), Served.gdn_gather(par, r)) ==
        List.take(&2, Nat, pi, Nat.sub(List.length(&2, Nat, pi), 1n)) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, y => Served.init(y), Served.hist(r, Served.outs_of(GtI.run(par))), pi,
        gt_hist(q1, q2, q3, q4, q5, q6, q7, legal, r, hr))

def Laws.served_o_gat(l, sh, m, r, ok_, rm_):
  match sh:
    case Served.Chain{}:
      +ok = ok_
      +rm = rm_
      %Equal.sym(Nat, Link.dep(~Served.Shape, ~Served.pth, Served.Chain{}, r), r, sq_dep(r)) :
        {Served.seqn(r, 0n) == List.take(&2, Nat, Served.seqn(1n+r, 0n), _) : List<&2, Nat>}
      Equal.sym(List<&2, Nat>, List.take(&2, Nat, Served.seqn(1n+r, 0n), r), Served.seqn(r, 0n), sq_take(1n+r, 0n, r, GP.ar_h_le_succ(r)))
    case Served.Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +ok = ok_
      +rm = rm_
      og_tree(Served.is_attn(l), l, q1, q2, q3, q4, q5, q6, q7, ok_legal(q1, q2, q3, q4, q5, q6, q7, m, ok), r,
        ok_r8(q1, q2, q3, q4, q5, q6, q7, m, r, ok, rm), {==})

# ---------------------------------------------------------------- the guarded path obligations

# "o implies b" in the guarded form of rowinv_link_laws.compose.
def sd_guard(o: Bool, -b: Bool, h: {o == True{} : Bool} -> {b == True{} : Bool}) -> {Bool.and(o, b) == o : Bool}:
  match o:
    case True{}:
      h({==})
    case False{}:
      {==}

# Reflexivity of the row-list equality check.
def sd_nle_refl(xs: List<&2, Nat>) -> {Link.nat_list_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, GP.ar_eq_refl(x)) : {Bool.and(_, Link.nat_list_eq(xr, xr)) == True{} : Bool}
      sd_nle_refl(xr)

def sd_nle_of_eq(xs: List<&2, Nat>, -ys: List<&2, Nat>, h: {xs == ys : List<&2, Nat>}) -> {Link.nat_list_eq(xs, ys) == True{} : Bool}:
  %h : {Link.nat_list_eq(xs, _) == True{} : Bool}
  sd_nle_refl(xs)

def Laws.served_w_last(sh, m, r, rm_):
  +sh = sh
  +m = m
  +r = r
  +rm = rm_
  sd_guard(Served.ok(sh, m),
    Link.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)), [r]), Served.pth(sh, r)),
    hok => sd_nle_of_eq(List.append(&2, Nat, List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)), [r]), Served.pth(sh, r),
      sv_w_last(sh, m, r, hok, rm)))

def Laws.served_w_rng(sh, m, r, j, rm_, jd_):
  +sh = sh
  +m = m
  +r = r
  +j = j
  +rm = rm_
  +jd = jd_
  sd_guard(Served.ok(sh, m), Nat.is_lt(Link.nthn(Served.pth(sh, r), j), m), hok => sv_w_rng(sh, m, r, j, hok, rm, jd))

def Laws.served_w_dep(sh, m, r, rm_):
  +sh = sh
  +m = m
  +r = r
  +rm = rm_
  sd_guard(Served.ok(sh, m), Nat.is_le(Link.dep(~Served.Shape, ~Served.pth, sh, r), r), hok => sv_w_dep(sh, m, r, hok, rm))

# ---------------------------------------------------------------- the served compose / commit

def i_o_plan(~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    l: Nat, base: Nat, m: Nat, r: Nat, d: Nat, h1: {Nat.is_le(d, r) == True{} : Bool}, h2: {Nat.is_lt(r, m) == True{} : Bool},
    h3: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {Served.plan(~cfg, ~arr, ~wsi, l, base, m, r, d) == Served.plan(~cfg, ~arr, ~wsi, l, Nat.add(base, d), 1n, 0n, 0n) : Served.Plan}:
  Laws.served_o_plan(~cfg, ~arr, ~wsi, ~hcfg, l, base, m, r, d, h1, h2, h3)

def i_o_head(~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    base: Nat, m: Nat, r: Nat, d: Nat, h1: {Nat.is_le(d, r) == True{} : Bool}, h2: {Nat.is_lt(r, m) == True{} : Bool},
    h3: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {Served.hplan(~cfg, ~arr, ~wsi, base, m, r, d) == Served.hplan(~cfg, ~arr, ~wsi, Nat.add(base, d), 1n, 0n, 0n) : Served.Plan}:
  Laws.served_o_head(~cfg, ~arr, ~wsi, ~hcfg, base, m, r, d, h1, h2, h3)

def i_o_gat(l: Nat, sh: Served.Shape, m: Nat, r: Nat, h1: {Served.ok(sh, m) == True{} : Bool}, h2: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Served.gat(l, sh, r) == List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)) : List<&2, Nat>}:
  Laws.served_o_gat(l, sh, m, r, h1, h2)

def i_w_last(sh: Served.Shape, m: Nat, r: Nat, h2: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Bool.and(Served.ok(sh, m), Link.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)), [r]),
      Served.pth(sh, r))) == Served.ok(sh, m) : Bool}:
  Laws.served_w_last(sh, m, r, h2)

def i_w_pre(sh: Served.Shape, m: Nat, r: Nat, j: Nat, h1: {Served.ok(sh, m) == True{} : Bool}, h2: {Nat.is_lt(r, m) == True{} : Bool},
    h3: {Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, sh, r)) == True{} : Bool})
  -> {Served.pth(sh, Link.nthn(Served.pth(sh, r), j)) == List.take(&2, Nat, Served.pth(sh, r), 1n+j) : List<&2, Nat>}:
  Laws.served_w_pre(sh, m, r, j, h1, h2, h3)

def i_w_rng(sh: Served.Shape, m: Nat, r: Nat, j: Nat, h2: {Nat.is_lt(r, m) == True{} : Bool},
    h3: {Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, sh, r)) == True{} : Bool})
  -> {Bool.and(Served.ok(sh, m), Nat.is_lt(Link.nthn(Served.pth(sh, r), j), m)) == Served.ok(sh, m) : Bool}:
  Laws.served_w_rng(sh, m, r, j, h2, h3)

def i_w_dep(sh: Served.Shape, m: Nat, r: Nat, h2: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Bool.and(Served.ok(sh, m), Nat.is_le(Link.dep(~Served.Shape, ~Served.pth, sh, r), r)) == Served.ok(sh, m) : Bool}:
  Laws.served_w_dep(sh, m, r, h2)

def Laws.served_compose(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pcs, n0, u, cs, toks, sh, r, commit, shape, rows8, row):
  LinkLaws.compose(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
    ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, ~Served.ok, ~i_o_plan(~cfg, ~arr, ~wsi, ~hcfg), ~i_o_head(~cfg, ~arr, ~wsi, ~hcfg),
    ~i_o_gat, ~i_w_last, ~i_w_pre, ~i_w_rng, ~i_w_dep, pcs, n0, u, cs, toks, sh, r, commit, shape, rows8, row)

def Laws.served_commit(V, E, C, z, emb, F, ent, adv, cfg, arr, wsi, hcfg, pcs, n0, u, cs, toks, sh, r, commit, shape, rows8, row):
  LinkLaws.commit_path(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth,
    ~Served.gat, ~Served.ok, ~i_o_plan(~cfg, ~arr, ~wsi, ~hcfg), ~i_o_gat, ~i_w_last, ~i_w_pre, ~i_w_rng, ~i_w_dep,
    pcs, n0, u, cs, toks, sh, r, commit, shape, rows8, row)

# ---------------------------------------------------------------- the spec_inv_tree adapter

def ri_take_pre(~A: Data, xs: List<&2, A>, +ys: List<&2, A>) -> {List.take(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      LinkProof.ri_take_nil(~A, ys)
    case +h <> t:
      Equal.cong(List<&2, A>, List<&2, A>, y => h <> y, List.take(&2, A, List.append(&2, A, t, ys), List.length(&2, A, t)), t, ri_take_pre(~A, t, ys))

def ri_drop_pre(~A: Data, xs: List<&2, A>, +ys: List<&2, A>) -> {List.drop(&2, A, List.append(&2, A, xs, ys), List.length(&2, A, xs)) == ys : List<&2, A>}:
  match xs:
    case Nil{}:
      LinkProof.ri_drop_zero(~A, ys)
    case h <> t:
      ri_drop_pre(~A, t, ys)

# parent / token of row 1 + q of the Draft's node list are the served shape's parent and token
def pa_eq(+q: Nat, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32,
    +x5: U32, +x6: U32, +x7: U32)
  -> {GtS.nth([0n, q1, q2, q3, q4, q5, q6, q7], 1n+q) ==
      TAS.parent_at([TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}], 1n, 1n+q) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+f:
                          match f:
                            case 0n:
                              {==}
                            case 1n+g:
                              {==}

def tk_eq(+q: Nat, +anchor: U32, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32,
    +x5: U32, +x6: U32, +x7: U32)
  -> {Link.at(~U32, ~0, [anchor, x1, x2, x3, x4, x5, x6, x7], 1n+q) ==
      TAS.token_at([TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}], 1n, 1n+q) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+f:
                          match f:
                            case 0n:
                              {==}
                            case 1n+g:
                              {==}

# The tokens along the served path of row r are the anchor, then spec_inv_tree's tokens of r's
# ancestors below the root and r (Impl.toks), for every fuel.
def st_path(+f: Nat, +r: Nat, +anchor: U32, +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32,
    +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32)
  -> {Link.stream([anchor, x1, x2, x3, x4, x5, x6, x7], GtS.path.go(f, [0n, q1, q2, q3, q4, q5, q6, q7], r)) ==
      anchor <> SIT.toks(f, [TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}], r)
      : List<&2, U32>}:
  match f:
    case 0n:
      {==}
    case 1n+f1:
      match r:
        case 0n:
          {==}
        case 1n+q:
          +tl = {[anchor, x1, x2, x3, x4, x5, x6, x7] : List<&2, U32>}
          +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
          +ns = {[TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}] : List<&2, TAS.Node>}
          +pq = GtS.nth(par, 1n+q)
          +e1 = LinkProof.ri_stream_app(tl, GtS.path.go(f1, par, pq), [1n+q])
          +e2 = Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, y, [Link.at(~U32, ~0, tl, 1n+q)]),
            Link.stream(tl, GtS.path.go(f1, par, pq)), anchor <> SIT.toks(f1, ns, pq),
            st_path(f1, pq, anchor, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7))
          %pa_eq(q, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) :
            {Link.stream(tl, GtS.cat(GtS.path.go(f1, par, pq), [1n+q])) == anchor <> List.append(&2, U32, SIT.toks(f1, ns, _), [TAS.token_at(ns, 1n, 1n+q)]) : List<&2, U32>}
          %tk_eq(q, anchor, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7) :
            {Link.stream(tl, GtS.cat(GtS.path.go(f1, par, pq), [1n+q])) == anchor <> List.append(&2, U32, SIT.toks(f1, ns, pq), [_]) : List<&2, U32>}
          Equal.trans(List<&2, U32>, Link.stream(tl, List.append(&2, Nat, GtS.path.go(f1, par, pq), [1n+q])),
            List.append(&2, U32, Link.stream(tl, GtS.path.go(f1, par, pq)), [Link.at(~U32, ~0, tl, 1n+q)]),
            anchor <> List.append(&2, U32, SIT.toks(f1, ns, pq), [Link.at(~U32, ~0, tl, 1n+q)]), e1, e2)

def and_true(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# spec_inv_tree's legality (exl3_tree_accept_spec.legal over rows 1..7) is attn_tree_spec's.
def leg_conv(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat)
  -> {TAS.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == AtS.legal(q1, q2, q3, q4, q5, q6, q7) : Bool}:
  %Equal.sym(Bool, Bool.and(Nat.is_lt(q7, 7n), True{}), Nat.is_lt(q7, 7n), and_true(Nat.is_lt(q7, 7n))) :
    {Bool.and(Nat.is_lt(q1, 1n), Bool.and(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n), Bool.and(Nat.is_lt(q4, 4n),
      Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), _)))))) == AtS.legal(q1, q2, q3, q4, q5, q6, q7) : Bool}
  {==}

def rinv_inst(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, ~row: List<&2, U32> -> Nat -> U32,
    ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32},
    p: List<&2, U32>, r: Nat) -> {row(p, r) == row(p, 0n) : U32}:
  +p = p
  Equal.trans(U32, row(p, r), LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p),
    row(p, 0n), isref(p, r),
    Equal.sym(U32, row(p, 0n), LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p),
      isref(p, 0n)))

def Laws.served_rinv(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, row, isref, p, r):
  rinv_inst(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, ~row, ~isref, p, r)

def gA(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run) -> Type:
  {SIS.greedy(~row, budget, stops, prompt) ==
    List.append(&2, U32, SIC.out(J), SIS.after(~row, SIC.stopped(J), SIC.budget(J), stops, List.append(&2, U32, prompt, SIC.out(J)))) : List<&2, U32>}

def gB(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J: SIC.Run) -> Type:
  {List.take(&2, U32, SIS.greedy(~row, budget, stops, prompt), List.length(&2, U32, SIC.out(J))) == SIC.out(J) : List<&2, U32>}

def gC(+J: SIC.Run) -> Type:
  {Bool.or(SIC.stopped(J), Nat.is_lt(0n, SIC.budget(J))) == True{} : Bool}

def Laws.served_tree_greedy(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, row, isref,
    prompt, stops, base, interval, trees, position, budget, anchor, checkpoint, positive, legal):
  +J = SIT.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)
  fst(gB(~row, prompt, stops, budget, J), gC(J), snd(gA(~row, prompt, stops, budget, J), gB(~row, prompt, stops, budget, J) & gC(J),
    SITL.tree_prefix_of_greedy(~row, ~rinv_inst(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, ~row, ~isref),
      prompt, stops, base, interval, trees, position, budget, anchor, checkpoint, positive, legal)))

# One row of a tree round: spec_inv_tree's row(prefix(seq, nodes, r), r) is the served verify id of row r.
def tr_row(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, ~row: List<&2, U32> -> Nat -> U32,
    ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32},
    +pre: List<&2, U32>, +u: List<&2, U32>, +anchor: U32, +cs: List<&2, C>,
    +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +x1: U32, +x2: U32, +x3: U32, +x4: U32, +x5: U32, +x6: U32, +x7: U32,
    +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}, +r: Nat, +hr: {Nat.is_lt(r, 8n) == True{} : Bool})
  -> {row(SIT.prefix(List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])),
        [TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}], r), r) ==
      Link.at(~U32, ~0, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
        ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), [anchor, x1, x2, x3, x4, x5, x6, x7], Served.Tree{q1, q2, q3, q4, q5, q6, q7}), r)
      : U32}:
  +ns = {[TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}] : List<&2, TAS.Node>}
  +tl = {[anchor, x1, x2, x3, x4, x5, x6, x7] : List<&2, U32>}
  +par = {[0n, q1, q2, q3, q4, q5, q6, q7] : List<&2, Nat>}
  +W = List.append(&2, U32, u, [anchor])
  +T = SIT.toks(8n, ns, r)
  +P = List.append(&2, U32, List.append(&2, U32, pre, W), T)
  # P == pre ++ (W ++ T)
  +ea = LinkProof.ri_app_assoc(~U32, pre, W, T)
  # take P n0 == pre, drop P n0 == W ++ T
  +etake = Equal.trans(List<&2, U32>, List.take(&2, U32, P, n0), List.take(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), n0), pre,
    Equal.cong(List<&2, U32>, List<&2, U32>, y => List.take(&2, U32, y, n0), P, List.append(&2, U32, pre, List.append(&2, U32, W, T)), ea),
    Equal.trans(List<&2, U32>, List.take(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), n0),
      List.take(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), List.length(&2, U32, pre)), pre,
      Equal.cong(Nat, List<&2, U32>, y => List.take(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), y), n0, List.length(&2, U32, pre),
        Equal.sym(Nat, List.length(&2, U32, pre), n0, hpre)),
      ri_take_pre(~U32, pre, List.append(&2, U32, W, T))))
  +edrop = Equal.trans(List<&2, U32>, List.drop(&2, U32, P, n0), List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), n0),
    List.append(&2, U32, W, T),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => List.drop(&2, U32, y, n0), P, List.append(&2, U32, pre, List.append(&2, U32, W, T)), ea),
    Equal.trans(List<&2, U32>, List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), n0),
      List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), List.length(&2, U32, pre)), List.append(&2, U32, W, T),
      Equal.cong(Nat, List<&2, U32>, y => List.drop(&2, U32, List.append(&2, U32, pre, List.append(&2, U32, W, T)), y), n0, List.length(&2, U32, pre),
        Equal.sym(Nat, List.length(&2, U32, pre), n0, hpre)),
      ri_drop_pre(~U32, pre, List.append(&2, U32, W, T))))
  # W ++ T == u ++ stream(tl, path(par, r))
  +ew = Equal.trans(List<&2, U32>, List.append(&2, U32, W, T), List.append(&2, U32, u, anchor <> T),
    List.append(&2, U32, u, Link.stream(tl, GtS.path(par, r))),
    LinkProof.ri_app_assoc(~U32, u, [anchor], T),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, u, y), anchor <> T, Link.stream(tl, GtS.path(par, r)),
      Equal.sym(List<&2, U32>, Link.stream(tl, GtS.path(par, r)), anchor <> T,
        st_path(8n, r, anchor, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7))))
  +REF = LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0,
    List.append(&2, U32, u, Link.stream(tl, GtS.path(par, r))))
  +eref = Equal.trans(U32,
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, P, n0)), n0, List.drop(&2, U32, P, n0)),
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.drop(&2, U32, P, n0)),
    REF,
    Equal.cong(List<&2, U32>, U32, y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(y), n0,
      List.drop(&2, U32, P, n0)), List.take(&2, U32, P, n0), pre, etake),
    Equal.cong(List<&2, U32>, U32, y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, y),
      List.drop(&2, U32, P, n0), List.append(&2, U32, u, Link.stream(tl, GtS.path(par, r))),
      Equal.trans(List<&2, U32>, List.drop(&2, U32, P, n0), List.append(&2, U32, W, T), List.append(&2, U32, u, Link.stream(tl, GtS.path(par, r))), edrop, ew)))
  +shape = Equal.trans(Bool, Served.ok(Served.Tree{q1, q2, q3, q4, q5, q6, q7}, 8n), AtS.legal(q1, q2, q3, q4, q5, q6, q7), True{},
    and_true(AtS.legal(q1, q2, q3, q4, q5, q6, q7)), legal)
  +comp = Laws.served_compose(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg,
    pf(pre), n0, u, cs, tl, Served.Tree{q1, q2, q3, q4, q5, q6, q7}, r, commit, shape, {==}, hr)
  Equal.trans(U32, row(P, r), REF,
    Link.at(~U32, ~0, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
      ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), tl, Served.Tree{q1, q2, q3, q4, q5, q6, q7}), r),
    Equal.trans(U32, row(P, r),
      LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, P, n0)), n0, List.drop(&2, U32, P, n0)),
      REF, isref(P, r), eref),
    Equal.sym(U32, Link.at(~U32, ~0, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
      ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), tl, Served.Tree{q1, q2, q3, q4, q5, q6, q7}), r), REF, comp))

def heads_len(~V: Data, ~P: Data, ~T: Data, ~z: V, ~head: P -> V -> U32, ~hp: Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>)
  -> {List.length(&2, U32, Link.heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k, r, sh, base, m, vals)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, U32, Link.heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k1, 1n+r, sh, base, m, vals)), k1,
        heads_len(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k1, 1n+r, sh, base, m, vals))

# The reference of a prefix (pre ++ W) ++ X whose first n0 = |pre| tokens were prefilled.
def ref_split(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +pre: List<&2, U32>, +Y: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat})
  -> {LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, List.append(&2, U32, pre, Y)) ==
      LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, Y) : U32}:
  +P = List.append(&2, U32, pre, Y)
  +etake = Equal.trans(List<&2, U32>, List.take(&2, U32, P, n0), List.take(&2, U32, P, List.length(&2, U32, pre)), pre,
    Equal.cong(Nat, List<&2, U32>, y => List.take(&2, U32, P, y), n0, List.length(&2, U32, pre), Equal.sym(Nat, List.length(&2, U32, pre), n0, hpre)),
    ri_take_pre(~U32, pre, Y))
  +edrop = Equal.trans(List<&2, U32>, List.drop(&2, U32, P, n0), List.drop(&2, U32, P, List.length(&2, U32, pre)), Y,
    Equal.cong(Nat, List<&2, U32>, y => List.drop(&2, U32, P, y), n0, List.length(&2, U32, pre), Equal.sym(Nat, List.length(&2, U32, pre), n0, hpre)),
    ri_drop_pre(~U32, pre, Y))
  Equal.trans(U32,
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, P, n0)), n0, List.drop(&2, U32, P, n0)),
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.drop(&2, U32, P, n0)),
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, Y),
    Equal.cong(List<&2, U32>, U32, y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(y), n0,
      List.drop(&2, U32, P, n0)), List.take(&2, U32, P, n0), pre, etake),
    Equal.cong(List<&2, U32>, U32, y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, y),
      List.drop(&2, U32, P, n0), Y, edrop))

# ---------------------------------------------------------------- the spec_inv (chain) adapter

# The tokens along the chain path 0 .. k - 1 from s are the first k tokens from s.
def ch_stream(k: Nat, +s: Nat, +tl: List<&2, U32>, +h: {Nat.is_le(Nat.add(s, k), List.length(&2, U32, tl)) == True{} : Bool})
  -> {Link.stream(tl, Served.seqn(k, s)) == List.take(&2, U32, List.drop(&2, U32, tl, s), k) : List<&2, U32>}:
  match k:
    case 0n:
      Equal.sym(List<&2, U32>, List.take(&2, U32, List.drop(&2, U32, tl, s), 0n), Nil{}, LinkProof.ri_take_nil(~U32, List.drop(&2, U32, tl, s)))
    case 1n+k1:
      +k1 = k1
      +hs = GP.ar_lt_le_trans(s, Nat.add(s, 1n+k1), List.length(&2, U32, tl), LinkProof.ri_lt_add(s, k1), h)
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.add(1n+s, k1), List.length(&2, U32, tl)), Nat.is_le(Nat.add(s, 1n+k1), List.length(&2, U32, tl)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, List.length(&2, U32, tl)), 1n+Nat.add(s, k1), Nat.add(s, 1n+k1), LinkProof.ri_sr(s, k1)), h)
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, tl, s), Link.at(~U32, ~0, tl, s) <> List.drop(&2, U32, tl, 1n+s), LinkProof.ri_drop_at(~U32, ~0, tl, s, hs)) :
        {Link.at(~U32, ~0, tl, s) <> Link.stream(tl, Served.seqn(k1, 1n+s)) == List.take(&2, U32, _, 1n+k1) : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Link.at(~U32, ~0, tl, s) <> y, Link.stream(tl, Served.seqn(k1, 1n+s)),
        List.take(&2, U32, List.drop(&2, U32, tl, 1n+s), k1), ch_stream(k1, 1n+s, tl, h2))

# Element j of spec_inv's rows after the first: row seq ++ first 1 + j drafts, as row 1 + r0 + j.
def ch_after(~row: List<&2, U32> -> Nat -> U32, ds: List<&2, U32>, +seq: List<&2, U32>, +r0: Nat, +j: Nat,
    h: {Nat.is_lt(j, List.length(&2, U32, ds)) == True{} : Bool})
  -> {Link.at(~U32, ~0, SIC.rows_after(~row, ds, seq, r0), j) ==
      row(List.append(&2, U32, seq, List.take(&2, U32, ds, 1n+j)), 1n+Nat.add(r0, j)) : U32}:
  match ds:
    case Nil{}:
      Empty.absurd({Link.at(~U32, ~0, SIC.rows_after(~row, Nil{}, seq, r0), j) ==
        row(List.append(&2, U32, seq, List.take(&2, U32, Nil{}, 1n+j)), 1n+Nat.add(r0, j)) : U32}, LinkProof.ri_lt_zero(j, h))
    case +d <> +rest:
      match j:
        case 0n:
          %Equal.sym(List<&2, U32>, List.take(&2, U32, rest, 0n), Nil{}, LinkProof.ri_take_nil(~U32, rest)) :
            {row(List.append(&2, U32, seq, [d]), 1n+r0) == row(List.append(&2, U32, seq, d <> _), 1n+Nat.add(r0, 0n)) : U32}
          %LinkProof.ri_zr(r0) : {row(List.append(&2, U32, seq, [d]), 1n+r0) == row(List.append(&2, U32, seq, [d]), 1n+_) : U32}
          {==}
        case 1n+j1:
          %LinkProof.ri_app_assoc(~U32, seq, [d], List.take(&2, U32, rest, 1n+j1)) :
            {Link.at(~U32, ~0, SIC.rows_after(~row, rest, List.append(&2, U32, seq, [d]), 1n+r0), j1) == row(_, 1n+Nat.add(r0, 1n+j1)) : U32}
          %LinkProof.ri_sr(r0, j1) : {Link.at(~U32, ~0, SIC.rows_after(~row, rest, List.append(&2, U32, seq, [d]), 1n+r0), j1) ==
            row(List.append(&2, U32, List.append(&2, U32, seq, [d]), List.take(&2, U32, rest, 1n+j1)), 1n+_) : U32}
          ch_after(~row, rest, List.append(&2, U32, seq, [d]), 1n+r0, j1, h)

# spec_inv's verify id of row r is the reference of u ++ (first 1 + r tokens of anchor <> ds).
def ch_spec(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, ~row: List<&2, U32> -> Nat -> U32,
    ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32},
    r: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +anchor: U32, +ds: List<&2, U32>, +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +hr: {Nat.is_lt(r, 1n+List.length(&2, U32, ds)) == True{} : Bool})
  -> {Link.at(~U32, ~0, SIC.targets(~row, ds, List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])), 0n), r) ==
      LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0,
        List.append(&2, U32, u, List.take(&2, U32, anchor <> ds, 1n+r))) : U32}:
  match r:
    case 0n:
      +W = List.append(&2, U32, u, [anchor])
      %Equal.sym(List<&2, U32>, List.take(&2, U32, ds, 0n), Nil{}, LinkProof.ri_take_nil(~U32, ds)) :
        {row(List.append(&2, U32, pre, W), 0n) ==
          LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0,
            List.append(&2, U32, u, anchor <> _)) : U32}
      Equal.trans(U32, row(List.append(&2, U32, pre, W), 0n),
        LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, List.append(&2, U32, pre, W)),
        LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, W),
        isref(List.append(&2, U32, pre, W), 0n),
        ref_split(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, pre, W, hpre))
    case 1n+j:
      +j = j
      +W = List.append(&2, U32, u, [anchor])
      +X = List.take(&2, U32, ds, 1n+j)
      +e1 = ch_after(~row, ds, List.append(&2, U32, pre, W), 0n, j, hr)
      +e2 = isref(List.append(&2, U32, List.append(&2, U32, pre, W), X), 1n+j)
      +e3 = Equal.cong(List<&2, U32>, U32,
        y => LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, y),
        List.append(&2, U32, List.append(&2, U32, pre, W), X), List.append(&2, U32, pre, List.append(&2, U32, W, X)),
        LinkProof.ri_app_assoc(~U32, pre, W, X))
      +e4 = ref_split(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, pre, List.append(&2, U32, W, X), hpre)
      +e5 = Equal.cong(List<&2, U32>, U32,
        y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, y),
        List.append(&2, U32, W, X), List.append(&2, U32, u, anchor <> X), LinkProof.ri_app_assoc(~U32, u, [anchor], X))
      Equal.trans(U32, Link.at(~U32, ~0, SIC.rows_after(~row, ds, List.append(&2, U32, pre, W), 0n), j),
        row(List.append(&2, U32, List.append(&2, U32, pre, W), X), 1n+j),
        LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, anchor <> X)),
        e1,
        Equal.trans(U32, row(List.append(&2, U32, List.append(&2, U32, pre, W), X), 1n+j),
          LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0,
            List.append(&2, U32, List.append(&2, U32, pre, W), X)),
          LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, anchor <> X)),
          e2,
          Equal.trans(U32,
            LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0,
              List.append(&2, U32, List.append(&2, U32, pre, W), X)),
            LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0,
              List.append(&2, U32, pre, List.append(&2, U32, W, X))),
            LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, anchor <> X)),
            e3,
            Equal.trans(U32,
              LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0,
                List.append(&2, U32, pre, List.append(&2, U32, W, X))),
              LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, W, X)),
              LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0, List.append(&2, U32, u, anchor <> X)),
              e4, e5))))

# Row r of a chain round: spec_inv's verify id = the served one; both are the reference of
# u ++ (first 1 + r tokens of anchor <> ds).
def ch_pt(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, ~row: List<&2, U32> -> Nat -> U32,
    ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32},
    +r: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +anchor: U32, +ds: List<&2, U32>, +cs: List<&2, C>,
    +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool}, +hr: {Nat.is_lt(r, 1n+List.length(&2, U32, ds)) == True{} : Bool})
  -> {Link.at(~U32, ~0, SIC.targets(~row, ds, List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])), 0n), r) ==
      Link.at(~U32, ~0, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
        ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{}), r) : U32}:
  +W = List.append(&2, U32, u, [anchor])
  +tl = {anchor <> ds : List<&2, U32>}
  +REF = LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0,
    List.append(&2, U32, u, List.take(&2, U32, tl, 1n+r)))
  +TOKS = Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
    ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), tl, Served.Chain{})
  # served side
  +hle = Equal.trans(Bool, Nat.is_le(Nat.add(0n, 1n+r), List.length(&2, U32, tl)), Nat.is_lt(r, 1n+List.length(&2, U32, ds)), True{},
    Equal.sym(Bool, Nat.is_lt(r, 1n+List.length(&2, U32, ds)), Nat.is_le(1n+r, 1n+List.length(&2, U32, ds)), GP.ar_lt_succ_le(r, 1n+List.length(&2, U32, ds))), hr)
  +est = Equal.trans(List<&2, U32>, Link.stream(tl, Served.seqn(1n+r, 0n)), List.take(&2, U32, List.drop(&2, U32, tl, 0n), 1n+r), List.take(&2, U32, tl, 1n+r),
    ch_stream(1n+r, 0n, tl, hle),
    Equal.cong(List<&2, U32>, List<&2, U32>, y => List.take(&2, U32, y, 1n+r), List.drop(&2, U32, tl, 0n), tl, LinkProof.ri_drop_zero(~U32, tl)))
  +small8 = Equal.trans(Bool, Nat.is_le(1n+List.length(&2, U32, ds), 8n), Nat.is_le(List.length(&2, U32, ds), 7n), True{},
    GP.ar_le_add_cancel(1n, List.length(&2, U32, ds), 7n), small)
  +comp = Laws.served_compose(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg,
    pf(pre), n0, u, cs, tl, Served.Chain{}, r, commit, {==}, small8, hr)
  +eserv = Equal.trans(U32, Link.at(~U32, ~0, TOKS, r),
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pf(pre), n0,
      List.append(&2, U32, u, Link.stream(tl, Served.seqn(1n+r, 0n)))), REF, comp,
    Equal.cong(List<&2, U32>, U32, y => LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
      pf(pre), n0, List.append(&2, U32, u, y)), Link.stream(tl, Served.seqn(1n+r, 0n)), List.take(&2, U32, tl, 1n+r), est))
  Equal.trans(U32, Link.at(~U32, ~0, SIC.targets(~row, ds, List.append(&2, U32, pre, W), 0n), r), REF, Link.at(~U32, ~0, TOKS, r),
    ch_spec(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, ~row, ~isref, r, pre, u, anchor, ds, hpre, hr),
    Equal.sym(U32, Link.at(~U32, ~0, TOKS, r), REF, eserv))

def ch_drop(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32,
    ~cfg: Served.Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool},
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, ~row: List<&2, U32> -> Nat -> U32,
    ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) ==
      LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32},
    +k: Nat, +r0: Nat, +pre: List<&2, U32>, +u: List<&2, U32>, +anchor: U32, +ds: List<&2, U32>, +cs: List<&2, C>,
    +hpre: {List.length(&2, U32, pre) == n0 : Nat},
    +commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>},
    +small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool}, +hk: {Nat.add(r0, k) == 1n+List.length(&2, U32, ds) : Nat})
  -> {List.drop(&2, U32, SIC.targets(~row, ds, List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])), 0n), r0) ==
      List.drop(&2, U32, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
        ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{}), r0) : List<&2, U32>}:
  match k:
    case 0n:
      +seq = List.append(&2, U32, pre, List.append(&2, U32, u, [anchor]))
      +TG = SIC.targets(~row, ds, seq, 0n)
      +TOKS = Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
        ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{})
      +FW = Link.fwd(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, 0n,
        Served.Chain{}, Nat.add(n0, List.length(&2, U32, u)), 1n+List.length(&2, U32, ds), Link.embs(~V, ~emb, anchor <> ds))
      +lenTG = SIP.si_shaped(~row, ds, seq, 0n)
      +lenTO = heads_len(~V, ~Served.Plan, ~Served.Shape, ~z, ~head, ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, 1n+List.length(&2, U32, ds), 0n, Served.Chain{},
        Nat.add(n0, List.length(&2, U32, u)), 1n+List.length(&2, U32, ds), FW)
      +e = Equal.trans(Nat, r0, Nat.add(r0, 0n), 1n+List.length(&2, U32, ds), LinkProof.ri_zr(r0), hk)
      Equal.trans(List<&2, U32>, List.drop(&2, U32, TG, r0), Nil{}, List.drop(&2, U32, TOKS, r0),
        Equal.trans(List<&2, U32>, List.drop(&2, U32, TG, r0), List.drop(&2, U32, TG, List.length(&2, U32, TG)), Nil{},
          Equal.cong(Nat, List<&2, U32>, y => List.drop(&2, U32, TG, y), r0, List.length(&2, U32, TG),
            Equal.trans(Nat, r0, 1n+List.length(&2, U32, ds), List.length(&2, U32, TG), e, Equal.sym(Nat, List.length(&2, U32, TG), 1n+List.length(&2, U32, ds), lenTG))),
          LinkProof.ri_drop_len(~U32, TG)),
        Equal.sym(List<&2, U32>, List.drop(&2, U32, TOKS, r0), Nil{},
          Equal.trans(List<&2, U32>, List.drop(&2, U32, TOKS, r0), List.drop(&2, U32, TOKS, List.length(&2, U32, TOKS)), Nil{},
            Equal.cong(Nat, List<&2, U32>, y => List.drop(&2, U32, TOKS, y), r0, List.length(&2, U32, TOKS),
              Equal.trans(Nat, r0, 1n+List.length(&2, U32, ds), List.length(&2, U32, TOKS), e, Equal.sym(Nat, List.length(&2, U32, TOKS), 1n+List.length(&2, U32, ds), lenTO))),
            LinkProof.ri_drop_len(~U32, TOKS))))
    case 1n+k1:
      +k1 = k1
      +seq = List.append(&2, U32, pre, List.append(&2, U32, u, [anchor]))
      +TG = SIC.targets(~row, ds, seq, 0n)
      +TOKS = Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
        ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{})
      +FW = Link.fwd(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, 0n,
        Served.Chain{}, Nat.add(n0, List.length(&2, U32, u)), 1n+List.length(&2, U32, ds), Link.embs(~V, ~emb, anchor <> ds))
      +lenTG = SIP.si_shaped(~row, ds, seq, 0n)
      +lenTO = heads_len(~V, ~Served.Plan, ~Served.Shape, ~z, ~head, ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, 1n+List.length(&2, U32, ds), 0n, Served.Chain{},
        Nat.add(n0, List.length(&2, U32, u)), 1n+List.length(&2, U32, ds), FW)
      +hr = Equal.trans(Bool, Nat.is_lt(r0, 1n+List.length(&2, U32, ds)), Nat.is_lt(r0, Nat.add(r0, 1n+k1)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(r0, y), 1n+List.length(&2, U32, ds), Nat.add(r0, 1n+k1), Equal.sym(Nat, Nat.add(r0, 1n+k1), 1n+List.length(&2, U32, ds), hk)),
        LinkProof.ri_lt_add(r0, k1))
      +hTG = Equal.trans(Bool, Nat.is_lt(r0, List.length(&2, U32, TG)), Nat.is_lt(r0, 1n+List.length(&2, U32, ds)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(r0, y), List.length(&2, U32, TG), 1n+List.length(&2, U32, ds), lenTG), hr)
      +hTO = Equal.trans(Bool, Nat.is_lt(r0, List.length(&2, U32, TOKS)), Nat.is_lt(r0, 1n+List.length(&2, U32, ds)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(r0, y), List.length(&2, U32, TOKS), 1n+List.length(&2, U32, ds), lenTO), hr)
      +hk2 = Equal.trans(Nat, Nat.add(1n+r0, k1), Nat.add(r0, 1n+k1), 1n+List.length(&2, U32, ds), LinkProof.ri_sr(r0, k1), hk)
      +pt = ch_pt(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref,
        r0, pre, u, anchor, ds, cs, hpre, commit, small, hr)
      +ih = ch_drop(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref,
        k1, 1n+r0, pre, u, anchor, ds, cs, hpre, commit, small, hk2)
      Equal.trans(List<&2, U32>, List.drop(&2, U32, TG, r0), Link.at(~U32, ~0, TG, r0) <> List.drop(&2, U32, TG, 1n+r0), List.drop(&2, U32, TOKS, r0),
        LinkProof.ri_drop_at(~U32, ~0, TG, r0, hTG),
        Equal.trans(List<&2, U32>, Link.at(~U32, ~0, TG, r0) <> List.drop(&2, U32, TG, 1n+r0),
          Link.at(~U32, ~0, TOKS, r0) <> List.drop(&2, U32, TOKS, 1n+r0), List.drop(&2, U32, TOKS, r0),
          LinkProof.ri_cong_cons(~U32, Link.at(~U32, ~0, TG, r0), Link.at(~U32, ~0, TOKS, r0), List.drop(&2, U32, TG, 1n+r0), List.drop(&2, U32, TOKS, 1n+r0), pt, ih),
          Equal.sym(List<&2, U32>, List.drop(&2, U32, TOKS, r0), Link.at(~U32, ~0, TOKS, r0) <> List.drop(&2, U32, TOKS, 1n+r0),
            LinkProof.ri_drop_at(~U32, ~0, TOKS, r0, hTO))))

def Laws.served_chain_round(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, row, isref,
    pre, u, anchor, ds, cs, hpre, commit, small):
  +seq = List.append(&2, U32, pre, List.append(&2, U32, u, [anchor]))
  +TG = SIC.targets(~row, ds, seq, 0n)
  +TOKS = Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi),
    ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{})
  Equal.trans(List<&2, U32>, TG, List.drop(&2, U32, TG, 0n), TOKS,
    Equal.sym(List<&2, U32>, List.drop(&2, U32, TG, 0n), TG, LinkProof.ri_drop_zero(~U32, TG)),
    Equal.trans(List<&2, U32>, List.drop(&2, U32, TG, 0n), List.drop(&2, U32, TOKS, 0n), TOKS,
      ch_drop(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref,
        1n+List.length(&2, U32, ds), 0n, pre, u, anchor, ds, cs, hpre, commit, small, {==}),
      LinkProof.ri_drop_zero(~U32, TOKS)))

def cA(+J1: SIC.Run) -> Type:
  {SIC.stopped(J1) == True{} : Bool}

def cG(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat, +J1: SIC.Run) -> Type:
  {SIC.out(J1) == SIS.greedy(~row, budget, stops, prompt) : List<&2, U32>}

def cE(+J1: SIC.Run, +J2: SIC.Run) -> Type:
  {SIC.out(J1) == SIC.out(J2) : List<&2, U32>}

def Laws.served_chain_invariance(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, row, isref,
    prompt, stops, base, interval, drafts1, drafts2, position, budget, anchor, checkpoint, positive, enough1, enough2):
  +J1 = SIC.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)
  +J2 = SIC.job(~row, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint)
  snd(cG(~row, prompt, stops, budget, J1), cE(J1, J2), snd(cA(J2), cG(~row, prompt, stops, budget, J1) & cE(J1, J2),
    snd(cA(J1), cA(J2) & cG(~row, prompt, stops, budget, J1) & cE(J1, J2),
    SIL.speculation_invariance(~row, ~rinv_inst(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0, ~row, ~isref),
      prompt, stops, base, interval, drafts1, drafts2, position, budget, anchor, checkpoint, positive, enough1, enough2))))


def Laws.served_tree_round(V, E, C, z, emb, F, ent, adv, head, cfg, arr, wsi, hcfg, pf, n0, row, isref,
    pre, u, anchor, t, cs, hpre_, commit_, legal):
  match t:
    case SIT.Draft{+q1, +q2, +q3, +q4, +q5, +q6, +q7, +x1, +x2, +x3, +x4, +x5, +x6, +x7}:
      +hpre = hpre_
      +commit = commit_
      +seq = List.append(&2, U32, pre, List.append(&2, U32, u, [anchor]))
      +ns = {[TAS.Node{q1, x1}, TAS.Node{q2, x2}, TAS.Node{q3, x3}, TAS.Node{q4, x4}, TAS.Node{q5, x5}, TAS.Node{q6, x6}, TAS.Node{q7, x7}] : List<&2, TAS.Node>}
      +tl = {[anchor, x1, x2, x3, x4, x5, x6, x7] : List<&2, U32>}
      +TOK = Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, Nat.add(n0, List.length(&2, U32, u)), tl, Served.Tree{q1, q2, q3, q4, q5, q6, q7})
      +legA = Equal.trans(Bool, AtS.legal(q1, q2, q3, q4, q5, q6, q7), TAS.legal([q1, q2, q3, q4, q5, q6, q7], 1n), True{},
        Equal.sym(Bool, TAS.legal([q1, q2, q3, q4, q5, q6, q7], 1n), AtS.legal(q1, q2, q3, q4, q5, q6, q7), leg_conv(q1, q2, q3, q4, q5, q6, q7)), legal)
      LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 0n), 0n), Link.at(~U32, ~0, TOK, 0n), [row(SIT.prefix(seq, ns, 1n), 1n), row(SIT.prefix(seq, ns, 2n), 2n), row(SIT.prefix(seq, ns, 3n), 3n), row(SIT.prefix(seq, ns, 4n), 4n), row(SIT.prefix(seq, ns, 5n), 5n), row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 1n), Link.at(~U32, ~0, TOK, 2n), Link.at(~U32, ~0, TOK, 3n), Link.at(~U32, ~0, TOK, 4n), Link.at(~U32, ~0, TOK, 5n), Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 0n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 1n), 1n), Link.at(~U32, ~0, TOK, 1n), [row(SIT.prefix(seq, ns, 2n), 2n), row(SIT.prefix(seq, ns, 3n), 3n), row(SIT.prefix(seq, ns, 4n), 4n), row(SIT.prefix(seq, ns, 5n), 5n), row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 2n), Link.at(~U32, ~0, TOK, 3n), Link.at(~U32, ~0, TOK, 4n), Link.at(~U32, ~0, TOK, 5n), Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 1n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 2n), 2n), Link.at(~U32, ~0, TOK, 2n), [row(SIT.prefix(seq, ns, 3n), 3n), row(SIT.prefix(seq, ns, 4n), 4n), row(SIT.prefix(seq, ns, 5n), 5n), row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 3n), Link.at(~U32, ~0, TOK, 4n), Link.at(~U32, ~0, TOK, 5n), Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 2n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 3n), 3n), Link.at(~U32, ~0, TOK, 3n), [row(SIT.prefix(seq, ns, 4n), 4n), row(SIT.prefix(seq, ns, 5n), 5n), row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 4n), Link.at(~U32, ~0, TOK, 5n), Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 3n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 4n), 4n), Link.at(~U32, ~0, TOK, 4n), [row(SIT.prefix(seq, ns, 5n), 5n), row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 5n), Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 4n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 5n), 5n), Link.at(~U32, ~0, TOK, 5n), [row(SIT.prefix(seq, ns, 6n), 6n), row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 6n), Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 5n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 6n), 6n), Link.at(~U32, ~0, TOK, 6n), [row(SIT.prefix(seq, ns, 7n), 7n)], [Link.at(~U32, ~0, TOK, 7n)],
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 6n, {==}),
        LinkProof.ri_cong_cons(~U32, row(SIT.prefix(seq, ns, 7n), 7n), Link.at(~U32, ~0, TOK, 7n), Nil{}, Nil{},
        tr_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~hcfg, ~pf, ~n0, ~row, ~isref, pre, u, anchor, cs, q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7, hpre, commit, legA, 7n, {==}),
        {==}))))))))
