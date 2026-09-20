# Startup/qualification CPU entry point, never a per-token subprocess.
# IO.print contributes exactly one newline after the protocol's final marker.
import Base
import ./acceptance.bend as Acceptance

def rows(values: List<&2, Nat>) -> String:
  match values:
    case Nil{}:
      ""
    case value <> rest:
      Nat.show(value) ++ "\n" ++ rows(rest)

def protocol() -> String:
  "QWEN_DFLASH_ACCEPT_V1\n7\n128\n" ++ rows(Acceptance.values()) ++
    "END_QWEN_DFLASH_ACCEPT"

def main() -> IO(Unit):
  IO.print(protocol())
