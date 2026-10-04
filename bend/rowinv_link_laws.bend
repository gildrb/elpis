# The ~rinv link: per-layer kernel obligations compose into "a verify row's token depends only on
# its absolute prefix" (the hypothesis ~rinv of spec_inv_laws.bend / spec_inv_tree_laws.bend), over
# the served-forward model rowinv_link.bend against the 1-row-round reference
# rowinv_link_spec.bend.
#
# Domain: every hidden / entry / state / plan / shape type, every embedding, layer, entry, state
# update and head function (opaque: the model's only floating-point assumption is that each is a
# function, i.e. H_det below), every plan function, every shape family, every prefill state and
# prefill length, every committed decode stream, every round of m <= 8 rows (any tokens), every row.
#
# Obligations (template hypotheses, each a property of one kernel family; rowinv_served_laws.bend
# discharges them for the served configuration from the existing per-kernel laws):
#   O_plan  plan(l, base, m, r, d) == plan(l, base + d, 1, 0, 0) for d <= r < m <= 8: a kernel's
#           arithmetic sequence for a row depends on the row's absolute position base + d only,
#           not on m, on the row index r, or on the other rows of the launch;
#   O_head  the same for the head (final norm, lm_head, argmax);
#   O_gat   every layer's gather is the row's proper ancestors, root first:
#           gat(l, sh, r) == take(pth(sh, r), dep(sh, r));
#   W_last / W_pre / W_rng / W_dep  the shape's paths form a tree over the round's rows: a path
#           ends with its row, the path of the j-th ancestor is the first j + 1 entries, ancestors
#           are rows of the round, and a row's depth is at most its index. W_last / W_rng / W_dep
#           are stated as guarded Bool checks {Bool.and(ok(sh, m), check) == ok(sh, m)}, i.e.
#           "ok(sh, m) implies check" (the same content; the form lets the BendTT kernel build a
#           model of the template hypothesis, see rowinv_link_proof.bend);
#   commit  the engine's committed state of every layer is the one 1-row rounds over the
#           committed decode stream u leave (rowinv_link_spec.committed), which the prefill
#           starts (u = []: the prefill state itself, law committed_prefill). This is a premise
#           of compose; law commit_path shows that the engine's commit of a round (Impl.commit
#           over an accepted path) re-establishes it, so it holds at every round start by
#           induction (rinv_laws.bend).
# Witnesses (plan_leak_differs, gather_drop_differs) show O_plan and O_gat are needed: a plan that
# leaks the round size, or a gather that drops an ancestor, changes a row token of a concrete round.
# H_det (not a Bend hypothesis, the model's reading): each kernel's result is a function of its
# plan and operands, so equal plans and equal operands give equal bits.
import Base
import ./rowinv_link.bend as Impl
import ./rowinv_link_spec.bend as Spec

# C1 (composition, headline): under the obligations, the verify id of every row r of a round
# (committed state cs, row 0 = the anchor at absolute position n0 + |u|, row tokens toks, shape
# sh) is the token of its absolute prefix computed as row 0 of a 1-row round: prefill state pcs,
# decode stream u followed by the tokens along r's path.
law compose:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~P: Data
  for ~T: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> P -> C -> V -> V
  for ~ent: Nat -> P -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: P -> V -> U32
  for ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P
  for ~hp: Nat -> Nat -> Nat -> Nat -> P
  for ~pth: T -> Nat -> List<&2, Nat>
  for ~gat: Nat -> T -> Nat -> List<&2, Nat>
  for ~ok: T -> Nat -> Bool
  for ~o_plan: @l:Nat -> @base:Nat -> @m:Nat -> @r:Nat -> @d:Nat -> {Nat.is_le(d, r) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} -> {Nat.is_le(m, 8n) == True{} : Bool} ->
    {plan(l, base, m, r, d) == plan(l, Nat.add(base, d), 1n, 0n, 0n) : P}
  for ~o_head: @base:Nat -> @m:Nat -> @r:Nat -> @d:Nat -> {Nat.is_le(d, r) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} -> {Nat.is_le(m, 8n) == True{} : Bool} ->
    {hp(base, m, r, d) == hp(Nat.add(base, d), 1n, 0n, 0n) : P}
  for ~o_gat: @l:Nat -> @sh:T -> @m:Nat -> @r:Nat -> {ok(sh, m) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} ->
    {gat(l, sh, r) == List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)) : List<&2, Nat>}
  for ~w_last: @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Impl.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]), pth(sh, r))) == ok(sh, m) : Bool}
  for ~w_pre: @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {ok(sh, m) == True{} : Bool} -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {pth(sh, Impl.nthn(pth(sh, r), j)) == List.take(&2, Nat, pth(sh, r), 1n+j) : List<&2, Nat>}
  for ~w_rng: @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_lt(Impl.nthn(pth(sh, r), j), m)) == ok(sh, m) : Bool}
  for ~w_dep: @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_le(Impl.dep(~T, ~pth, sh, r), r)) == ok(sh, m) : Bool}
  for +pcs: List<&2, C>
  for +n0: Nat
  for +u: List<&2, U32>
  for +cs: List<&2, C>
  for +toks: List<&2, U32>
  for +sh: T
  for +r: Nat
  for commit: {cs == Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u) : List<&2, C>}
  for shape: {ok(sh, List.length(&2, U32, toks)) == True{} : Bool}
  for rows8: {Nat.is_le(List.length(&2, U32, toks), 8n) == True{} : Bool}
  for row: {Nat.is_lt(r, List.length(&2, U32, toks)) == True{} : Bool}
  {Impl.at(~U32, ~0, Impl.tokens(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, ~pth, ~gat,
      cs, Nat.add(n0, List.length(&2, U32, u)), toks, sh), r) ==
    Spec.ref(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, pcs, n0,
      List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))) : U32}

# C2 (commit, the induction step of the hypothesis `commit`): under the same obligations, the
# engine's commit of the rows on row r's path (root first: the accepted path ending at r) leaves
# exactly the committed state 1-row rounds leave over the decode stream u followed by the tokens
# along r's path. So if the round started from the 1-row-rounds state of u, the next round starts
# from the 1-row-rounds state of u ++ stream(toks, pth(sh, r)).
law commit_path:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~P: Data
  for ~T: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> P -> C -> V -> V
  for ~ent: Nat -> P -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P
  for ~pth: T -> Nat -> List<&2, Nat>
  for ~gat: Nat -> T -> Nat -> List<&2, Nat>
  for ~ok: T -> Nat -> Bool
  for ~o_plan: @l:Nat -> @base:Nat -> @m:Nat -> @r:Nat -> @d:Nat -> {Nat.is_le(d, r) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} -> {Nat.is_le(m, 8n) == True{} : Bool} ->
    {plan(l, base, m, r, d) == plan(l, Nat.add(base, d), 1n, 0n, 0n) : P}
  for ~o_gat: @l:Nat -> @sh:T -> @m:Nat -> @r:Nat -> {ok(sh, m) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} ->
    {gat(l, sh, r) == List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)) : List<&2, Nat>}
  for ~w_last: @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Impl.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]), pth(sh, r))) == ok(sh, m) : Bool}
  for ~w_pre: @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {ok(sh, m) == True{} : Bool} -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {pth(sh, Impl.nthn(pth(sh, r), j)) == List.take(&2, Nat, pth(sh, r), 1n+j) : List<&2, Nat>}
  for ~w_rng: @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_lt(Impl.nthn(pth(sh, r), j), m)) == ok(sh, m) : Bool}
  for ~w_dep: @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_le(Impl.dep(~T, ~pth, sh, r), r)) == ok(sh, m) : Bool}
  for +pcs: List<&2, C>
  for +n0: Nat
  for +u: List<&2, U32>
  for +cs: List<&2, C>
  for +toks: List<&2, U32>
  for +sh: T
  for +r: Nat
  for commit: {cs == Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u) : List<&2, C>}
  for shape: {ok(sh, List.length(&2, U32, toks)) == True{} : Bool}
  for rows8: {Nat.is_le(List.length(&2, U32, toks), 8n) == True{} : Bool}
  for row: {Nat.is_lt(r, List.length(&2, U32, toks)) == True{} : Bool}
  {Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, cs, 0n, pth(sh, r), sh,
      Nat.add(n0, List.length(&2, U32, u)), List.length(&2, U32, toks), Impl.embs(~V, ~emb, toks)) ==
    Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0,
      List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))) : List<&2, C>}

# D (mutation witnesses): each obligation is needed. One layer, committed context 0, a 2-row chain
# round with tokens [5, 6] from position 0 (no prefill); the reference token of row 1's prefix is 1.
# (a) With plans independent of m and the ancestor gather, row 1's served token is 1 (= reference).
# (b) A plan that leaks the round size m (O_plan fails): row 1's served token is 0.
# (c) A gather that drops row 1's ancestor (O_gat fails): row 1's served token is 0.
law plan_leak_differs:
  {Spec.ref(~Nat, ~Nat, ~Nat, ~Nat, ~0n, ~Impl.w_emb, ~Impl.w_F, ~Impl.w_ent, ~Impl.w_adv, ~Impl.w_head, ~Impl.w_plan, ~Impl.w_hp,
    [0n], 0n, [5, 6]) == 1 : U32} &
  {Impl.at(~U32, ~0, Impl.tokens(~Nat, ~Nat, ~Nat, ~Nat, ~Nat, ~0n, ~Impl.w_emb, ~Impl.w_F, ~Impl.w_ent, ~Impl.w_adv, ~Impl.w_head,
    ~Impl.w_plan, ~Impl.w_hp, ~Impl.w_pth, ~Impl.w_gat, [0n], 0n, [5, 6], 0n), 1n) == 1 : U32} &
  {Impl.at(~U32, ~0, Impl.tokens(~Nat, ~Nat, ~Nat, ~Nat, ~Nat, ~0n, ~Impl.w_emb, ~Impl.w_F, ~Impl.w_ent, ~Impl.w_adv, ~Impl.w_head,
    ~Impl.w_plan_m, ~Impl.w_hp, ~Impl.w_pth, ~Impl.w_gat, [0n], 0n, [5, 6], 0n), 1n) == 0 : U32} &
  {Spec.ref(~Nat, ~Nat, ~Nat, ~Nat, ~0n, ~Impl.w_emb, ~Impl.w_F, ~Impl.w_ent, ~Impl.w_adv, ~Impl.w_head, ~Impl.w_plan_m, ~Impl.w_hp,
    [0n], 0n, [5, 6]) == 1 : U32}

law gather_drop_differs:
  {Impl.at(~U32, ~0, Impl.tokens(~Nat, ~Nat, ~Nat, ~Nat, ~Nat, ~0n, ~Impl.w_emb, ~Impl.w_F, ~Impl.w_ent, ~Impl.w_adv, ~Impl.w_head,
    ~Impl.w_plan, ~Impl.w_hp, ~Impl.w_pth, ~Impl.w_gat_drop, [0n], 0n, [5, 6], 0n), 1n) == 0 : U32}

# ~rinv in its exact spec_inv type follows for any row function that is the reference on every
# whole prefix (the prefill of the first n0 tokens by pf, then 1-row rounds).
law ref_rinv:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~P: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> P -> C -> V -> V
  for ~ent: Nat -> P -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: P -> V -> U32
  for ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P
  for ~hp: Nat -> Nat -> Nat -> Nat -> P
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for ~row: List<&2, U32> -> Nat -> U32
  for ~isref: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == Spec.ref_prefix(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, ~pf, ~n0, p) : U32}
  for +p: List<&2, U32>
  for +r: Nat
  {row(p, r) == row(p, 0n) : U32}

# Starting state: before any decode token is committed the committed state is the prefill state.
law committed_prefill:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~P: Data
  for ~emb: U32 -> V
  for ~F: Nat -> P -> C -> V -> V
  for ~ent: Nat -> P -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P
  for +pcs: List<&2, C>
  for +n0: Nat
  {Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, Nil{}) == pcs : List<&2, C>}
