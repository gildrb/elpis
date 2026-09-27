# Agreement of the two TreeDesc references (DESIGN.md §2.2): the host derive
# reference (bend/exl3_tree_accept_spec.bend, which the shipped derive leaf equals
# on every legal parent array) and the tree-attention reference
# (bend/attn_tree_spec.bend, which the TREE split kernel's laws read) give the same
# magic, version, n_rows, n_leaf, depth, leaf_of, leaves and path bytes on every
# legal parent array, so the attention laws hold for the descriptor the host
# derives and uploads.
import Base
import ./exl3_tree_accept_spec.bend as Derive
import ./attn_tree.bend as AttnTree
import ./attn_tree_spec.bend as AttnSpec
import ./gdn_tree_spec.bend as GdnSpec

def attn_bytes(d: AttnTree.TreeDesc) -> List<&2, Nat>:
  match d:
    case AttnTree.TreeDesc{magic, version, n_rows, n_leaf, depth, leaf_of, leaves, path}:
      List.concat(&2, Nat, [[magic, version, n_rows, n_leaf], depth, leaf_of, leaves,
        List.concat(&2, Nat, path)])

def derive_bytes(+d: List<&2, Nat>) -> List<&2, Nat>:
  List.concat(&2, Nat, [Derive.field(d, 0n, 4n), Derive.field(d, 16n, 8n),
    Derive.field(d, 32n, 16n), Derive.field(d, 64n, 64n)])

# The GDN reference's program (bend/gdn_tree_spec.bend, parents with an unused
# row-0 entry) in the TreeDesc byte encoding op << 4 | row, 0xFF-padded to 16.
def enc(ops: List<&2, GdnSpec.Op>) -> List<&2, Nat>:
  match ops:
    case Nil{}:
      Nil{}
    case GdnSpec.Op{op, row} <> rest:
      Nat.add(Nat.mul(op, 16n), row) <> enc(rest)

def gdn_prog(+ps: List<&2, Nat>) -> List<&2, Nat>:
  +ops = GdnSpec.prog(0n <> ps)
  List.length(&2, GdnSpec.Op, ops) <> Derive.pad(enc(ops), 16n, 255n)

def derive_prog(+d: List<&2, Nat>) -> List<&2, Nat>:
  Derive.row_at(d, 4n) <> Derive.field(d, 48n, 16n)

law tree_desc_agree:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Derive.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {derive_bytes(Derive.derive([q1, q2, q3, q4, q5, q6, q7])) == attn_bytes(AttnSpec.desc([q1, q2, q3, q4, q5, q6, q7])) : List<&2, Nat>}

# ... and with the GDN reference on the program: n_prog and the 16 prog bytes.
law tree_prog_agree:
  for +q1: Nat
  for +q2: Nat
  for +q3: Nat
  for +q4: Nat
  for +q5: Nat
  for +q6: Nat
  for +q7: Nat
  for legal: {Derive.legal([q1, q2, q3, q4, q5, q6, q7], 1n) == True{} : Bool}
  {derive_prog(Derive.derive([q1, q2, q3, q4, q5, q6, q7])) == gdn_prog([q1, q2, q3, q4, q5, q6, q7]) : List<&2, Nat>}
