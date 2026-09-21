# Startup CPU table wire, not per-step subprocess execution. Original Bend
# IO.print supplies the sole final newline after END_QWEN_RUNTIME_CONTROL.
import Base
import ./transaction.bend as Transaction

def rows(values: List<&2, Nat>) -> String:
  match values:
    case Nil{}:
      ""
    case value <> rest:
      Nat.show(value) ++ "\n" ++ rows(rest)

def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V1\nFREE_MIRROR\n8\n" ++
    rows(Transaction.free_table(3n, False{}, False{}, False{})) ++
    "STATUS\n8\n" ++
    rows(Transaction.status_table(3n, False{}, False{}, False{})) ++
    "END_QWEN_RUNTIME_CONTROL"

def main() -> IO(Unit):
  IO.print(protocol())
