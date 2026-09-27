# Reference program: renders the tree acceptance table (exl3_tree_table.bend)
# through the list reference exl3_tree_accept_spec.bend. The build pins its
# output and requires EXL3_TREE_ACCEPT.bend to print the same bytes.
import Base
import ./exl3_tree_accept_spec.bend as Spec
import ./exl3_tree_table.bend as Table

def acc(q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat, budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32, s3: U32, t0: U32, t1: U32, t2: U32, t3: U32, t4: U32, t5: U32, t6: U32, t7: U32, x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32) -> Spec.TreeVerdict:
  Spec.accept_tree([Spec.Node{q1, x1}, Spec.Node{q2, x2}, Spec.Node{q3, x3}, Spec.Node{q4, x4}, Spec.Node{q5, x5}, Spec.Node{q6, x6}, Spec.Node{q7, x7}], [t0, t1, t2, t3, t4, t5, t6, t7],
    List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)

def der(q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat) -> List<&2, Nat>:
  Spec.derive([q1, q2, q3, q4, q5, q6, q7])

def main() -> IO(Unit):
  Table.table(~acc, ~der)
