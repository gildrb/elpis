# Production program: its unchanged emitted C is compiled into the serving
# shared library, whose glue calls only the scalar leaves Impl.accept_tree and
# Impl.derive. main renders the tree acceptance table (exl3_tree_table.bend)
# through those leaves; it must be byte-identical to EXL3_TREE_ACCEPT_SPEC.bend's.
import Base
import ./exl3_tree_accept.bend as Impl
import ./exl3_tree_accept_spec.bend as Spec
import ./exl3_tree_table.bend as Table

def acc(q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat, budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32, s3: U32, t0: U32, t1: U32, t2: U32, t3: U32, t4: U32, t5: U32, t6: U32, t7: U32, x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32) -> Spec.TreeVerdict:
  Impl.accept_tree(budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4, t5, t6, t7, x1, x2, x3, x4, x5, x6, x7, q1, q2, q3, q4, q5, q6, q7)

def der(q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat) -> List<&2, Nat>:
  Impl.bytes(Impl.derive(q1, q2, q3, q4, q5, q6, q7))

def main() -> IO(Unit):
  Table.table(~acc, ~der)
