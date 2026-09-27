# Tree speculation invariance (DESIGN.md §3(d) L6, §4.1) over the model
# bend/spec_inv_tree.bend (tree acceptance reference + exl3_round advance kernel)
# against plain greedy decoding bend/spec_inv_spec.bend.
#
# Hypothesis ~rinv as in spec_inv_laws.bend: a verify row's token depends only on
# its absolute prefix. For a tree row the prefix is the committed sequence
# followed by the tokens of its ancestors below the root and its own
# (seq ++ tokens[path[r][1..]]); DESIGN.md §4.1 argues the engine side (tree
# attention passes, GDN program) in those terms. Domain: every legal tree
# (q_r < r) with any tokens in every round, any prompt, stop list, budget,
# checkpoint base and interval, any initial running device state.
import Base
import ./spec_inv_tree.bend as Impl
import ./spec_inv_spec.bend as Spec
import ./spec_inv.bend as Chain
import ./exl3_tree_accept_spec.bend as Tree

# T0: one tree round from any prefix with remaining budget 1 + bp commits exactly
# the greedy continuation (its committed verify ids followed by what greedy
# decoding still emits after them are the greedy output), and a round that does
# not end the job leaves budget.
law tree_round_commits_greedy:
  for ~row: List<&2, U32> -> Nat -> U32
  for ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32}
  for +seq: List<&2, U32>
  for +t: Impl.Draft
  for +stops: List<&2, U32>
  for +bp: Nat
  for +checkpoint: Nat
  for legal: {Impl.legal(t) == True{} : Bool}
  {Spec.greedy(~row, 1n+bp, stops, seq) ==
    List.append(&2, U32,
      List.take(&2, U32, Impl.path_ids(Impl.verify(~row, seq, Impl.nodes(t)), Impl.nodes(t)),
        Tree.count(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint))),
      Spec.after(~row, Tree.eos(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint)),
        Nat.sub(1n+bp, Tree.count(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint))),
        stops,
        List.append(&2, U32, seq,
          List.take(&2, U32, Impl.path_ids(Impl.verify(~row, seq, Impl.nodes(t)), Impl.nodes(t)),
            Tree.count(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint)))))) : List<&2, U32>} &
  {Bool.or(Tree.eos(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint)),
    Nat.is_lt(Tree.count(Tree.accept_tree(Impl.nodes(t), Impl.verify(~row, seq, Impl.nodes(t)), stops, 1n+bp, checkpoint)), 1n+bp)) == True{} : Bool}

# T1: after any tree rounds (any legal trees, any tokens), the emitted tokens
# followed by what greedy decoding still emits from them (nothing once stopped)
# are the greedy output of the prompt; so the emitted tokens are a prefix of it;
# a running job keeps a positive budget.
law tree_prefix_of_greedy:
  for ~row: List<&2, U32> -> Nat -> U32
  for ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32}
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +trees: List<&2, Impl.Draft>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for legal: {Impl.all_legal(trees) == True{} : Bool}
  {Spec.greedy(~row, budget, stops, prompt) ==
    List.append(&2, U32,
      Chain.out(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)),
      Spec.after(~row,
        Chain.stopped(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)),
        Chain.budget(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)),
        stops,
        List.append(&2, U32, prompt,
          Chain.out(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint))))) : List<&2, U32>} &
  {List.take(&2, U32, Spec.greedy(~row, budget, stops, prompt),
      List.length(&2, U32, Chain.out(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)))) ==
    Chain.out(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)) : List<&2, U32>} &
  {Bool.or(Chain.stopped(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)),
    Nat.is_lt(0n, Chain.budget(Impl.job(~row, prompt, stops, base, interval, trees, position, budget, anchor, checkpoint)))) == True{} : Bool}

# T2 (mutation witness): a row output that leaks its row index (Chain.leak: row 0
# answers 0, later rows 1; it violates ~rinv) breaks tree invariance: prompt [5],
# no stops, budget 2; one legal chain-shaped tree round drafting [0, 1, ...]
# emits [0, 1], while greedy decoding emits [0, 0].
law tree_row_index_leak_differs:
  {U32.is_eq(Chain.leak([5, 0], 1n), Chain.leak([5, 0], 0n)) == False{} : Bool} &
  {Impl.legal(Impl.Draft{0n, 1n, 2n, 3n, 4n, 5n, 6n, 0, 1, 1, 1, 1, 1, 1}) == True{} : Bool} &
  {Chain.out(Impl.job(~Chain.leak, [5], Nil{}, 0n, 0n, [Impl.Draft{0n, 1n, 2n, 3n, 4n, 5n, 6n, 0, 1, 1, 1, 1, 1, 1}], 0n, 2n, 0n, 0n)) == [0, 1] : List<&2, U32>} &
  {Spec.greedy(~Chain.leak, 2n, Nil{}, [5]) == [0, 0] : List<&2, U32>}
