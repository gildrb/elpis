# Proofs of the ext 5109 laws (gdn_tree_laws.bend): finite facts over all 5040 shapes, decided by the checker's
# evaluation. No unsafe definitions, axioms or holes.
import Base
import ./gdn_tree.bend as Impl
import ./gdn_tree_spec.bend as Spec
import ./gdn_tree_laws.bend as Laws

def Laws.tree_all_shapes():
  ({==}, {==})

def Laws.tree_chain():
  ({==}, {==}, {==})
