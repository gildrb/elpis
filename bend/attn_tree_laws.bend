# Obligations for the TREE verify split kernel of ext patch 3012 (attn_tree.bend) against the tree
# reference (attn_tree_spec.bend). Domain: every legal 8-row shape (parents q_r < r, the 5040 parent
# arrays of DESIGN.md 2.1) with the TreeDesc the host validates for it (Spec.desc: the DESIGN.md 2.2
# fields), every row r < 8, in-round column j < 8, pass p < n_leaf, round start base and tile.
# Everything else a row's result depends on (its tile list, slot, combine order, the non-tail
# tiles) is the 3006 kernel, shared by both instantiations (attn_stride_laws.bend). Floating point
# is outside this model: that a pass not admitting a row (an all-masked tile) leaves its (m, l, acc)
# bit-identical is the same CUDA arithmetic fact 3006 relies on, checked by the GPU differential.
import Base
import ./attn_tree.bend as Impl
import ./attn_tree_spec.bend as Spec
import ./attn_stride.bend as Stride

# 1. Tail tiles: every in-round column base + j (j < 8) lies in T0 = base / 64 or T1 = (base + 7) / 64;
# T1 is the last live tile of the round (live tiles = T1 + 1, L = base + 8) and T0 is T1 or the one
# before; every tile below T0 holds committed positions only (below base, visible to every row as in
# the chain), so the tail tiles are the only tiles whose contents or visibility the tree changes.
law tail_cover:
  for +base: Nat
  for +j: Nat
  for hj: {Nat.is_lt(j, 8n) == True{} : Bool}
  {Bool.or(Nat.is_eq(Nat.div(Nat.add(base, j), 64n), Impl.tail_lo(base)),
    Nat.is_eq(Nat.div(Nat.add(base, j), 64n), Impl.tail_hi(base))) == True{} : Bool}

law tail_last:
  for +base: Nat
  {1n+Impl.tail_hi(base) == Stride.live_tiles(Nat.add(base, 8n)) : Nat} &
  {Nat.is_le(Impl.tail_hi(base), 1n+Impl.tail_lo(base)) == True{} : Bool} &
  {Nat.is_le(Impl.tail_lo(base), Impl.tail_hi(base)) == True{} : Bool}

law context_tiles:
  for +base: Nat
  for +tile: Nat
  for below: {Nat.is_lt(tile, Impl.tail_lo(base)) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.mul(tile, 64n), 64n), base) == True{} : Bool}

# 2. No trap: for every legal shape the host-validated TreeDesc passes the kernel's entry checks
# for every row (q_len 8) and the leaf / stash-row checks of every pass and in-round column.
law entry_ok:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +r: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  {Impl.entry_ok(8n, Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r) == True{} : Bool}

law pass_ok:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +p: Nat
  for +j: Nat
  for hp: {Nat.is_lt(p, Impl.n_leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)))) == True{} : Bool}
  for hj: {Nat.is_lt(j, 8n) == True{} : Bool}
  {Impl.pass_ok(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), p, j) == True{} : Bool}

# 3. Single pass per row: every row is admitted by exactly one of the n_leaf passes of a tail tile.
law pass_once:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +r: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  {Impl.pass_count(Impl.n_leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7))),
    Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r) == 1n : Nat}

# 4. Path prefix: the pass serving row r (leaf_of[r]) is at least as deep as r and its path starts
# with r's root-to-r path: path[leaf_of[r]][j] is r's depth-j ancestor for every j <= depth[r].
law path_prefix:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +r: Nat
  for +j: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  for hj: {Nat.is_le(j, Spec.depth(Spec.shape(q1, q2, q3, q4, q5, q6, q7), r)) == True{} : Bool}
  {Nat.is_le(Spec.depth(Spec.shape(q1, q2, q3, q4, q5, q6, q7), r),
    Impl.depth(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)),
      Impl.leaf_of(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r))) == True{} : Bool} &
  {Impl.path(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)),
    Impl.leaf_of(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r), j) ==
    Spec.anc(Spec.shape(q1, q2, q3, q4, q5, q6, q7), r, j) : Nat}

# 5. Row r sees its path (headline). Over the pass loop of a tail tile, in-round column base + j
# enters row r (q_abs = base + depth[r]) exactly once when j <= depth[r] and never otherwise, as in
# the chain row at base + depth[r]; and a pass that lets it in holds there stash row (slot base + ..)
# r's depth-j ancestor: the chain holding r's path at base .. base + depth[r].
law sees_once:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +base: Nat
  for +r: Nat
  for +j: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  for hj: {Nat.is_lt(j, 8n) == True{} : Bool}
  {Impl.pass_hits(Impl.n_leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7))),
    Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r, Nat.add(base, j),
    Impl.q_abs(base, Impl.depth(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r))) ==
    Spec.once(Spec.chain_sees(j, Spec.depth(Spec.shape(q1, q2, q3, q4, q5, q6, q7), r))) : Nat}

law sees_path:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +base: Nat
  for +r: Nat
  for +p: Nat
  for +j: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  for hp: {Nat.is_lt(p, Impl.n_leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)))) == True{} : Bool}
  for hj: {Nat.is_lt(j, 8n) == True{} : Bool}
  for admitted: {Impl.sees(True{}, Impl.leaf_of(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r),
    Impl.leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), p), Nat.add(base, j),
    Impl.q_abs(base, Impl.depth(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r))) == True{} : Bool}
  {Impl.slot(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), p, j) ==
    Spec.anc(Spec.shape(q1, q2, q3, q4, q5, q6, q7), r, j) : Nat}

# 6. Committed columns of a tail tile (tok <= base) enter every row exactly once over the pass loop,
# as in the chain's single pass.
law context_once:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal(q1, q2, q3, q4, q5, q6, q7) == True{} : Bool}
  for +base: Nat
  for +tok: Nat
  for +r: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  for ctx: {Nat.is_le(tok, base) == True{} : Bool}
  {Impl.pass_hits(Impl.n_leaf(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7))),
    Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r, tok,
    Impl.q_abs(base, Impl.depth(Spec.desc(Spec.shape(q1, q2, q3, q4, q5, q6, q7)), r))) == 1n : Nat}

# 7. CHAIN is the 3006 kernel: one pass admitting every row, the identity stash copy, and row r at
# 3006's causal bound L - q_len + r (L = base + 8, q_len 8).
law chain:
  for +base: Nat
  for +r: Nat
  for +j: Nat
  for hr: {Nat.is_lt(r, 8n) == True{} : Bool}
  for hj: {Nat.is_lt(j, 8n) == True{} : Bool}
  {Impl.n_leaf(Spec.desc(Spec.chain())) == 1n : Nat} &
  {Impl.in_pass(True{}, Impl.leaf_of(Spec.desc(Spec.chain()), r), Impl.leaf(Spec.desc(Spec.chain()), 0n)) == True{} : Bool} &
  {Impl.slot(Spec.desc(Spec.chain()), 0n, j) == j : Nat} &
  {Impl.q_abs(base, Impl.depth(Spec.desc(Spec.chain()), r)) == Stride.q_abs(Nat.add(base, 8n), 8n, r) : Nat}
