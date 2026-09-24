# Finite differential table of the verify-attention partition model (bend/attn_split.bend),
# compared byte for byte by bend/attn_split_diff.py against the index expressions of
# exllamav3_ext/attn_verify.cuh + attn_verify.cu (ext patch 3003) compiled for the CPU.
# Per (L, S): split_len and live, then per launched split i < S: n_start, n_end, runs.
import Base
import ./attn_split.bend as Impl

def bool_text(b: Bool) -> String:
  match b:
    case False{}:
      "0"
    case True{}:
      "1"

def splits(k: Nat, +i: Nat, +L: Nat, +S: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(Impl.n_start(i, L, S)) ++ ":" ++ Nat.show(Impl.n_end(i, L, S)) ++ ":" ++
        bool_text(Impl.runs(i, L, S)) ++ splits(m, 1n+i, L, S)

def line(+L: Nat, +S: Nat) -> String:
  "L=" ++ Nat.show(L) ++ " S=" ++ Nat.show(S) ++ " sl=" ++ Nat.show(Impl.split_len(L, S)) ++
    " live=" ++ Nat.show(Impl.live(L, S)) ++ splits(S, 0n, L, S)

def per_s(ss: List<&2, Nat>, +L: Nat) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case s <> rest:
      do IO<Unit>:
        IO.print(line(L, s))
        per_s(rest, L)

def per_l(ls: List<&2, Nat>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        per_s([1n, 2n, 3n, 7n, 20n, 40n, 82n], l)
        per_l(rest)

# L = depth + 8: depths 0 .. 32728 incl. page/tile boundaries and the traced depths
def main() -> IO(Unit):
  per_l([1n, 8n, 63n, 64n, 65n, 115n, 127n, 128n, 129n, 256n, 257n, 1000n, 1288n, 2056n, 4104n,
    8198n, 12808n, 18608n, 32736n])
