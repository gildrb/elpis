# Qualification/startup CPU executable. IO.print adds the sole final newline;
# enumeration reaches the same scalar decide7 leaf called by the GPU wrapper.
import Base
import ./speculation.bend as Speculation
import ./speculation_spec.bend as Spec

def row(value: Spec.Decision) -> String:
  match value:
    case Spec.Decision{accepted, committed, bonus, advance}:
      Nat.show(accepted) ++ "\n" ++ Nat.show(committed) ++ "\n" ++
        Nat.show(bonus) ++ "\n" ++ Nat.show(advance) ++ "\n"

def rows(values: List<&2, Spec.Decision>) -> String:
  match values:
    case Nil{}:
      ""
    case value <> rest:
      row(value) ++ rows(rest)

def protocol() -> String:
  "QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n" ++ rows(Speculation.decisions()) ++
    "END_QWEN_DFLASH_GREEDY"

def main() -> IO(Unit):
  IO.print(protocol())
