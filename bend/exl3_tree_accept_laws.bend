# Obligations for the ExLlamaV3 8-row tree acceptance leaves executed by the
# patched generator (via the unchanged emitted C of bend/EXL3_TREE_ACCEPT.bend)
# and for their independent list reference (DESIGN.md §3(d) laws L1-L5).
import Base
import ./exl3_tree_accept.bend as Impl
import ./exl3_tree_accept_spec.bend as Spec
import ./exl3_accept.bend as Chain
import ./exl3_accept_spec.bend as ChainSpec

# L1 tree_refinement (accept): the executed scalar leaf equals the list
# reference for every register value: verify ids, tokens, parents (any, the
# legal-domain check is the glue's), stop count and slots, budget, checkpoint.
law tree_refinement:
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  {Impl.accept_tree(budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4, t5, t6, t7, x1, x2, x3, x4, x5, x6, x7, q1, q2, q3, q4, q5, q6, q7) ==
    Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint) : Spec.TreeVerdict}

# L2 chain_reduction: on the chain shape (parent[r] = r - 1) the tree leaf is
# the chain leaf with k = 7 on the whole window, last = count - 1, and derive
# gives the CHAIN descriptor of DESIGN.md §2.2 byte for byte.
law chain_reduction:
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  {Impl.accept_tree(budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4, t5, t6, t7, x1, x2, x3, x4, x5, x6, x7, 0n, 1n, 2n, 3n, 4n, 5n, 6n) ==
    Spec.from_chain(Chain.accept(7n, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4, t5, t6, t7, x1, x2, x3, x4, x5, x6, x7)) : Spec.TreeVerdict}

law chain_desc:
  {Impl.bytes(Impl.derive(0n, 1n, 2n, 3n, 4n, 5n, 6n)) == [84n, 1n, 8n, 1n, 8n, 0n, 0n, 0n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 1n, 3n, 7n, 15n, 31n, 63n, 127n, 255n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n] : List<&2, Nat>} &
  {Spec.derive([0n, 1n, 2n, 3n, 4n, 5n, 6n]) == [84n, 1n, 8n, 1n, 8n, 0n, 0n, 0n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 1n, 3n, 7n, 15n, 31n, 63n, 127n, 255n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n] : List<&2, Nat>}

# L1 tree_refinement (derive): on every legal parent array the executed
# derive leaf gives the reference's 128 TreeDesc bytes.
law derive_refinement:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {Impl.bytes(Impl.derive(q1, q2, q3, q4, q5, q6, q7)) == Spec.derive([q1, q2, q3, q4, q5, q6, q7]) : List<&2, Nat>}

# L5 derive_sound: on every legal parent array the reference descriptor has
# the §2.2 fields in place (header, n_leaf, kind); every row's parent, depth
# and path follow the parent recurrence (path[r] = path[parent[r]] + [r]:
# r's ancestors by depth, 0xFF after), anc_mask is the path's bit set,
# leaf_of[r] is a leaf whose path extends path[r] and is reached through the
# lowest child, leaves are the childless rows ascending, and the program
# (n_prog <= 16, valid ops, 0xFF padding) outputs every row exactly once
# with the state history path[r] (Spec.sound).
law derive_sound:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {Spec.sound([q1, q2, q3, q4, q5, q6, q7], Spec.derive([q1, q2, q3, q4, q5, q6, q7])) == True{} : Bool}

# The soundness check is not vacuous: it rejects the CHAIN descriptor with
# leaf_of[3] = 6, with ADV 2 / ADV 3 swapped, and with path[5][2] = 3.
law sound_rejects:
  {Spec.sound([0n, 1n, 2n, 3n, 4n, 5n, 6n], [84n, 1n, 8n, 1n, 8n, 0n, 0n, 0n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 1n, 3n, 7n, 15n, 31n, 63n, 127n, 255n, 7n, 7n, 7n, 6n, 7n, 7n, 7n, 7n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n]) == False{} : Bool} &
  {Spec.sound([0n, 1n, 2n, 3n, 4n, 5n, 6n], [84n, 1n, 8n, 1n, 8n, 0n, 0n, 0n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 1n, 3n, 7n, 15n, 31n, 63n, 127n, 255n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 3n, 2n, 4n, 5n, 6n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n]) == False{} : Bool} &
  {Spec.sound([0n, 1n, 2n, 3n, 4n, 5n, 6n], [84n, 1n, 8n, 1n, 8n, 0n, 0n, 0n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 1n, 3n, 7n, 15n, 31n, 63n, 127n, 255n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 255n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 255n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 255n, 255n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 255n, 255n, 255n, 0n, 1n, 3n, 3n, 4n, 5n, 255n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 255n, 0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n]) == False{} : Bool}

# L3 linearization (Spec.accept_tree is by definition the chain reference on
# the linearized path P = Spec.path): P starts at the root, every row of P
# after the root extends the previous one (its parent is that row and its
# token is that row's verify id: every committed row after the root carries
# token == verify[parent]), and on the legal domain no row extends the last
# row of P (P is maximal: the walk's fuel never cuts it short).
law path_matches:
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {Spec.row_at(Spec.path([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7]), 0n) == 0n : Nat} &
  {Spec.pext(List.tail(&2, Nat, Spec.path([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7])), [Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], 0n) == True{} : Bool}

# L3 committed rows: 1 <= count <= |P|, and last = P[count - 1], so the
# committed rows are P[0..count) (for every input, legal or not).
law committed_rows:
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  {Nat.is_lt(0n, Spec.count(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint))) == True{} : Bool} &
  {Nat.is_le(Spec.count(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)), List.length(&2, Nat, Spec.path([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7]))) == True{} : Bool} &
  {Spec.last(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)) == Spec.row_at(Spec.path([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7]), Nat.sub(Spec.count(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)), 1n)) : Nat}

# L4 maximal: a round ends before the end of P only with eos (stop token or
# exhausted budget) or at the checkpoint boundary; since P is maximal, no
# longer matching path is ever left uncommitted otherwise.
law maximal:
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +x1: U32
  for +x2: U32
  for +x3: U32
  for +x4: U32
  for +x5: U32
  for +x6: U32
  for +x7: U32
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Spec.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {Bool.or(Spec.eos(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)), Bool.or(Nat.is_eq(Spec.count(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)), checkpoint),
    Nat.is_eq(Spec.count(Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7], List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)), List.length(&2, Nat, Spec.path([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7]))))) == True{} : Bool}
