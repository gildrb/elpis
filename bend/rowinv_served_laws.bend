# The ~rinv link for the served configuration (model rowinv_served.bend over the generic
# rowinv_link.bend, reference rowinv_link_spec.bend): every per-layer and head obligation of
# rowinv_link_laws.compose / commit_path is discharged from the existing per-kernel laws and the
# discharge laws below, and what remains is a short list of named physical / conformance facts.
# Domain: every configuration Cfg the host admits (Served.cfg_ok: every split-K descriptor passes the
# host guard), every scheduler choice of split-K arrival order (arr) and every stale workspace content
# (wsi), every round shape the engine runs (chain rounds of 1..8 rows, the 5040 legal 8-row trees),
# every row.
#
# Discharged (formerly hypotheses):
#   H_lmhead (o_head) the head plan is Served.hplan, whose head field is lmhead.hp_head over the
#             persisted autotune records: served_o_head, from lmhead_laws.o_head_served.
#   H_grid    (h_S) the 3006 split grid is grid_S(sms, kvh) = max(1, sms // kvh) (3006 bc_attn.py,
#             source link rinv_grid_diff.py), positive for every input: grid_pos.
#   H_sched   (h_only, h_all, h_room) the contributors of a group are exactly blocks lo .. lo + nc - 1
#             (contributors_seqn, from gemm_m16_wpart_laws.contributors_contiguous / contrib_bounds
#             under the host guard); every scheduler order of them (and every order is one:
#             perm_reach_step) is only and all of them (arrivals_exact); the counter barrier shows the
#             finisher all of them (barrier_sees_all); the region has max_contrib >= nc slots
#             (contrib_bounds): splitk_group.
#
# Remaining named hypotheses (none is a Bend hypothesis of the laws below; each is the reading of the
# opaque functions F / ent / adv / head / emb and of the plan):
#   H_lmhead_hw (bend/lmhead.bend header; LmHead LAWS-proposal "Remaining hypothesis"):
#     H_mma     mma.m16n8k16 (fp16 accumulate) computes D[r][j] from A[r][:], B[:][j], C[r][j] only, in
#               an internal order independent of r and of the other rows' contents (including stale /
#               NaN rows >= size_m left by the predicated A load, GI:134). Hardware, undocumented.
#     H_slots   the input / output Hadamard warps (GK:16-30, 55-75) and the four accumulator slots of
#               an element (GI:808-811, 359, 389) run identical code per 128-chunk / slot, so a row's
#               arithmetic does not depend on which warp or slot holds it. Source-read.
#     H_deploy  (H_conform) the persisted autotune records lmhead.served_tab are present and loaded
#               (HOME / XDG_CACHE_HOME set, file readable, CA:75-119; the served container's
#               coop_autotune_v1.bin byte-identical to the decoded copy) and the environment is default
#               (EXL3_INT8_GEMV_MAX_K unset, force_shape_idx / force_num_sms 0). Deployment facts.
#     H_rowloc  the final norm and the fused argmax are row-local: one block per row reading only its
#               row (norm_fuse spec mem(buf, row, c); SF:667-670 row = blockIdx.y), argmax = the lowest
#               index of the row maximum over the first vsize logits (SF:59-69, 707-709, 737-766),
#               independent of the block split. Source-read; argmax split-invariance not in Bend.
#   H_mem     (GPU memory model, split-K barrier) a contributor warp's slot stores (__stcg, 8201
#             patch:738) made before its __threadfence + __syncwarp + counter atomicAdd (patch:743-745)
#             or before grid.sync() (2102 patch:771, 2105 patch:353) are visible to the finisher
#             block's slot loads issued after its poller observed the counter at the target with an
#             acquire load (exl3_mlp_wait, patch:460-468: ld_acquire loop, __threadfence; then
#             __syncthreads, patch:846-852) / after grid.sync; counters are 0 at every launch start
#             (self-reset by the last waiter, patch:382-384, exl3_mlp_pass patch:473-478; launches
#             stream-ordered); the target the schedule table supplies (pr[0], patch:848) is 8 * nc
#             (H_conform, mlp_m16_sched tables). So the finisher reads exactly the slots written by
#             Served.seen's arrivals.
#   H_det / H_conform / H_fp: the GPU computes a kernel's result as a function of its plan and
#             operands (same instruction sequence and operands, same bits, whichever block / warp /
#             MMA row slot runs it); every shipped kernel and host path conforms to its Bend model
#             (transcriptions, *_diff.py source links, including that the host launches a split-K
#             descriptor only when it passes the guard Served.gdesc_ok); the plan captures every m-
#             or row-dependent choice, in particular masked tiles / non-admitting passes are exact
#             no-ops (alpha = 1, p = 0, mma(c, 0 * finite) == c) and PEEK / ADV / REPLAY share one
#             arithmetic body.
#   commit    (premise of served_compose, not a hypothesis of the engine) the committed state at a
#             round start is what 1-row rounds over the committed decode stream leave from the prefill
#             state; served_commit is the induction step that re-establishes it.
import Base
import ./rowinv_link.bend as Link
import ./rowinv_link_spec.bend as LSpec
import ./rowinv_served.bend as Served
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./attn_tree_spec.bend as AtS
import ./gdn_tree.bend as GtI
import ./gdn_tree_spec.bend as GtS
import ./spec_inv_tree.bend as SIT
import ./spec_inv_spec.bend as SIS
import ./spec_inv.bend as SIC

# (NEW, split-K finisher) For any arrival order of a group's contributors lo .. lo + nc - 1 (only
# blocks >= lo, all of them, repeats allowed) into a workspace with >= nc slots, the finisher's
# slot-order sum (gemm_m16_partition.bend finish: slot 0, then slots 1 .. nc - 1) is the ascending
# fold of the contributors' partials. It depends on (lo, nc) only: not on the arrival order, the
# workspace contents, the token-row count m or which warp finishes. Generalizes
# gemm_m16_partition_laws.reduction_order (v2 contributor ranges) to any contributor range, hence
# to the slot-weighted m16g (2105) / 8201 / 8205 tail partitions of gemm_m16_wpart.bend.
law splitk_finish_asc:
  for +order: List<&2, Nat>
  for +ws: List<&2, PSpec.Sum>
  for +lo: Nat
  for +nc: Nat
  for only: {Served.arr_only(order, lo) == True{} : Bool}
  for all: {Served.arr_all(nc, lo, order) == True{} : Bool}
  for room: {Nat.is_le(nc, List.length(&2, PSpec.Sum, ws)) == True{} : Bool}
  for pos: {Nat.is_lt(0n, nc) == True{} : Bool}
  {Part.finish(Part.arrive(order, ws, lo), nc) == Served.asc(nc, lo) : PSpec.Sum}

# H_grid: the 3006 split grid the host computes is at least 1 for every SM count and kv-head count.
law grid_pos:
  for +sms: Nat
  for +kvh: Nat
  {Nat.is_lt(0n, Served.grid_S(sms, kvh)) == True{} : Bool}

# H_sched (who arrives): under the host guard, the blocks b < G that touch group g < groups, in
# ascending order, are exactly first_contrib(g), .., first_contrib(g) + nc(g) - 1.
law contributors_seqn:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  {Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) ==
    Served.seqn(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : List<&2, Nat>}

# H_sched (in which order): every order the scheduler's insertion indices produce from the
# contributors lo .. lo + nc - 1 holds only contributors, all of them, and nc arrivals.
law arrivals_exact:
  for +ix: List<&2, Nat>
  for +lo: Nat
  for +nc: Nat
  {Served.arr_only(Served.perm(Served.seqn(nc, lo), ix, Nil{}), lo) == True{} : Bool} &
  {Served.arr_all(nc, lo, Served.perm(Served.seqn(nc, lo), ix, Nil{})) == True{} : Bool} &
  {List.length(&2, Nat, Served.perm(Served.seqn(nc, lo), ix, Nil{})) == nc : Nat}

# The scheduler model is not a restriction: if the indices ix of the first contributors cs give the
# order a ++ b, the index |a| for one more contributor c places it between a and b. With
# perm([], [], []) == [], induction on the number of contributors gives every order of them as
# perm(cs, ix, []) for some ix.
law perm_reach_step:
  for +cs: List<&2, Nat>
  for +ix: List<&2, Nat>
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: Nat
  for len: {List.length(&2, Nat, ix) == List.length(&2, Nat, cs) : Nat}
  for order: {Served.perm(cs, ix, Nil{}) == List.append(&2, Nat, a, b) : List<&2, Nat>}
  {Served.perm(List.append(&2, Nat, cs, [c]), List.append(&2, Nat, ix, [List.length(&2, Nat, a)]), Nil{}) ==
    List.append(&2, Nat, a, c <> b) : List<&2, Nat>}

# H_sched (what the finisher sees): with nc arrivals each adding 8 to the counter, the finisher that
# waits for 8 * nc observes all of them.
law barrier_sees_all:
  for +order: List<&2, Nat>
  for +nc: Nat
  for len: {List.length(&2, Nat, order) == nc : Nat}
  {Served.seen(order, 0n, Nat.mul(nc, 8n)) == order : List<&2, Nat>}

# H_sched discharged: under the host guard, for every scheduler choice and every stale workspace, the
# finisher sum of group g < groups is the ascending fold of its contributors' partials.
law splitk_group:
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for +m: Nat
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  {Served.fin_g(~arr, ~wsi, m, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
      Wp.max_contrib(groups, KT, G, nsm, w0, w1), Served.contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) ==
    Served.asc(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : PSpec.Sum}

# O_plan for the served plan: the plan of row r (depth d <= r) of an m-row launch (m <= 8) at row-0
# position base is the plan of row 0 of a 1-row launch at base + d, in every layer. Fieldwise:
# position (arithmetic); 3006 combine order and tile plan (attn_stride_laws.row_invariant_rounds over
# grid_S, grid_pos); split-K finisher sums (splitk_group: m-free); 8205 tail main loop per block
# (m16_wsched_tables_laws.wtail_rows); 5106 b/a GEMV value per head relabelled to the row's own
# operands (gdn_ba_ksplit_laws.task_value); head plan (lmhead_laws.o_head_served).
law served_o_plan:
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for +l: Nat
  for +base: Nat
  for +m: Nat
  for +r: Nat
  for +d: Nat
  for dr: {Nat.is_le(d, r) == True{} : Bool}
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  for m8: {Nat.is_le(m, 8n) == True{} : Bool}
  {Served.plan(~cfg, ~arr, ~wsi, l, base, m, r, d) == Served.plan(~cfg, ~arr, ~wsi, l, Nat.add(base, d), 1n, 0n, 0n) : Served.Plan}

# O_head (H_lmhead discharged): the head plan of row r of an m-row round is that of row 0 of a 1-row
# round at base + d.
law served_o_head:
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for +base: Nat
  for +m: Nat
  for +r: Nat
  for +d: Nat
  for dr: {Nat.is_le(d, r) == True{} : Bool}
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  for m8: {Nat.is_le(m, 8n) == True{} : Bool}
  {Served.hplan(~cfg, ~arr, ~wsi, base, m, r, d) == Served.hplan(~cfg, ~arr, ~wsi, Nat.add(base, d), 1n, 0n, 0n) : Served.Plan}

# O_gat for the served shapes: every layer's gather is the row's proper ancestors, root first.
# Chain rounds: rows 0 .. r - 1 (the 3006 causal bound / the GDN verify scan; for GDN
# gdn_chain_rows below ties it to gdn_rounds_laws.verify_split_point). Tree rounds, attention
# layers: attn_tree_laws.path_prefix (the admitting pass's stash rows are r's ancestors) with the
# reference ancestors decided equal to the path for all 5040 shapes; GDN layers:
# gdn_tree_laws.tree_all_shapes (row r is emitted from state history path[r]).
law served_o_gat:
  for +l: Nat
  for +sh: Served.Shape
  for +m: Nat
  for +r: Nat
  for ok: {Served.ok(sh, m) == True{} : Bool}
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  {Served.gat(l, sh, r) == List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)) : List<&2, Nat>}

# W_last / W_pre / W_rng / W_dep for the served shapes (chain: generically; tree: the 5040 shapes).
# W_last / W_rng / W_dep in rowinv_link_laws.compose's guarded form {Bool.and(ok, check) == ok}
# ("ok(sh, m) implies check").
law served_w_last:
  for +sh: Served.Shape
  for +m: Nat
  for +r: Nat
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  {Bool.and(Served.ok(sh, m), Link.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, Served.pth(sh, r), Link.dep(~Served.Shape, ~Served.pth, sh, r)), [r]),
    Served.pth(sh, r))) == Served.ok(sh, m) : Bool}

law served_w_pre:
  for +sh: Served.Shape
  for +m: Nat
  for +r: Nat
  for +j: Nat
  for ok: {Served.ok(sh, m) == True{} : Bool}
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  for jd: {Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, sh, r)) == True{} : Bool}
  {Served.pth(sh, Link.nthn(Served.pth(sh, r), j)) == List.take(&2, Nat, Served.pth(sh, r), 1n+j) : List<&2, Nat>}

law served_w_rng:
  for +sh: Served.Shape
  for +m: Nat
  for +r: Nat
  for +j: Nat
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  for jd: {Nat.is_lt(j, Link.dep(~Served.Shape, ~Served.pth, sh, r)) == True{} : Bool}
  {Bool.and(Served.ok(sh, m), Nat.is_lt(Link.nthn(Served.pth(sh, r), j), m)) == Served.ok(sh, m) : Bool}

law served_w_dep:
  for +sh: Served.Shape
  for +m: Nat
  for +r: Nat
  for rm: {Nat.is_lt(r, m) == True{} : Bool}
  {Bool.and(Served.ok(sh, m), Nat.is_le(Link.dep(~Served.Shape, ~Served.pth, sh, r), r)) == Served.ok(sh, m) : Bool}

# 5109 conv window along the tree (the other read of the GDN tree kernel): for every legal shape and
# row, the kernel's conv window indices are the last K of the committed window followed by the row's
# path inputs (gdn_tree_laws.tree_all_shapes, per shape); the served context folds exactly those
# rows (served_o_gat), so the conv input window is the one the row's absolute prefix determines.
law gdn_tree_conv_window:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {AtS.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +r: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  {GtI.window([0n, q1, q2, q3, q4, q5, q6, q7], r) == GtS.verify_window([0n, q1, q2, q3, q4, q5, q6, q7], r) : List<&2, Nat>}

# ---------------------------------------------------------------- the served ~rinv

# C1 for the served configuration (headline): with every per-layer and head obligation discharged
# above, for every admitted configuration (hcfg), scheduler choice and stale workspace, and every
# opaque arithmetic (emb / F / ent / adv / head: H_det), given commit, the verify id of every row r of
# every admitted round (chain of 1..8 rows or legal 8-row tree) is the token of its absolute prefix
# computed as row 0 of a 1-row round.
law served_compose:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for +pcs: List<&2, C>
  for +n0: Nat
  for +u: List<&2, U32>
  for +cs: List<&2, C>
  for +toks: List<&2, U32>
  for +sh: Served.Shape
  for +r: Nat
  for commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pcs, n0, u) : List<&2, C>}
  for shape: {Served.ok(sh, List.length(&2, U32, toks)) == True{} : Bool}
  for rows8: {Nat.is_le(List.length(&2, U32, toks), 8n) == True{} : Bool}
  for row: {Nat.is_lt(r, List.length(&2, U32, toks)) == True{} : Bool}
  {Link.at(~U32, ~0, Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, Nat.add(n0, List.length(&2, U32, u)), toks, sh), r) ==
    LSpec.ref(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), pcs, n0,
      List.append(&2, U32, u, Link.stream(toks, Served.pth(sh, r)))) : U32}

# C2 for the served configuration (the induction step of commit): the engine's commit of the rows on
# row r's path leaves exactly the committed state 1-row rounds leave over u ++ the path's tokens.
law served_commit:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for +pcs: List<&2, C>
  for +n0: Nat
  for +u: List<&2, U32>
  for +cs: List<&2, C>
  for +toks: List<&2, U32>
  for +sh: Served.Shape
  for +r: Nat
  for commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pcs, n0, u) : List<&2, C>}
  for shape: {Served.ok(sh, List.length(&2, U32, toks)) == True{} : Bool}
  for rows8: {Nat.is_le(List.length(&2, U32, toks), 8n) == True{} : Bool}
  for row: {Nat.is_lt(r, List.length(&2, U32, toks)) == True{} : Bool}
  {Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, 0n, Served.pth(sh, r), sh, Nat.add(n0, List.length(&2, U32, u)), List.length(&2, U32, toks), Link.embs(~V, ~emb, toks)) ==
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pcs, n0,
      List.append(&2, U32, u, Link.stream(toks, Served.pth(sh, r)))) : List<&2, C>}

# Adapter to spec_inv_tree (T0/T1's round): for any row function that is the served reference on
# every whole token prefix (prefill of the first n0 tokens by pf, then 1-row rounds), one tree round
# of spec_inv_tree (Impl.verify: row r's prefix is seq ++ tokens of path[r] below the root) gives
# exactly the served forward's verify ids for that round, the committed sequence being pre (n0
# prefilled tokens) ++ u (committed decode tokens) ++ [anchor].
law served_tree_round:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}
  for +pre: List<&2, U32>
  for +u: List<&2, U32>
  for +anchor: U32
  for +t: SIT.Draft
  for +cs: List<&2, C>
  for hpre: {List.length(&2, U32, pre) == n0 : Nat}
  for commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>}
  for legal: {SIT.legal(t) == True{} : Bool}
  {SIT.verify(~row, List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])), SIT.nodes(t)) ==
    Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, Nat.add(n0, List.length(&2, U32, u)), Served.tree_toks(anchor, t), Served.tree_shape(t)) : List<&2, U32>}

# ~rinv, with the exact type of spec_inv_laws / spec_inv_tree_laws, holds for that row function ...
law served_rinv:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}
  for +p: List<&2, U32>
  for +r: Nat
  {row(p, r) == row(p, 0n) : U32}

# ... so spec_inv_tree_laws.tree_prefix_of_greedy applies to it verbatim (the hypothesis ~rinv is
# discharged, not assumed): after any legal tree rounds the emitted tokens followed by what greedy
# decoding still emits are the greedy output, and are a prefix of it.
law served_tree_greedy:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +trees: List<&2, SIT.Draft>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for legal: {SIT.all_legal(trees) == True{} : Bool}
  {List.take(&2, U32, SIS.greedy(~row, budget, stops, prompt),
      List.length(&2, U32, SIC.out(SIT.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)))) ==
    SIC.out(SIT.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)) : List<&2, U32>}

# Adapter to spec_inv (D0 / D1's round): for the same row function, one chain round of spec_inv
# (Impl.targets: row j's prefix is seq ++ d_1 .. d_j) with k <= 7 drafts gives exactly the served
# forward's verify ids of the chain round (anchor, d_1 .. d_k).
law served_chain_round:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}
  for +pre: List<&2, U32>
  for +u: List<&2, U32>
  for +anchor: U32
  for +ds: List<&2, U32>
  for +cs: List<&2, C>
  for hpre: {List.length(&2, U32, pre) == n0 : Nat}
  for commit: {cs == LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(pre), n0, u) : List<&2, C>}
  for small: {Nat.is_le(List.length(&2, U32, ds), 7n) == True{} : Bool}
  {SIC.targets(~row, ds, List.append(&2, U32, pre, List.append(&2, U32, u, [anchor])), 0n) ==
    Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat,
      cs, Nat.add(n0, List.length(&2, U32, u)), anchor <> ds, Served.Chain{}) : List<&2, U32>}

# ... and spec_inv_laws.speculation_invariance applies to it verbatim (~rinv discharged): any two
# drafters emit the same tokens, the greedy output.
law served_chain_invariance:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p) : U32}
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +drafts1: List<&2, List<&2, U32>>
  for +drafts2: List<&2, List<&2, U32>>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for enough1: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts1)) == True{} : Bool}
  for enough2: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts2)) == True{} : Bool}
  {SIC.out(SIC.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)) ==
    SIC.out(SIC.job(~row, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint)) : List<&2, U32>}
