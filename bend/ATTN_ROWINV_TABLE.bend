# Finite differential table of the row-invariant verify-attention partition model
# (bend/attn_rowinv.bend, ext patch 3005), compared byte for byte by bend/attn_rowinv_diff.py
# against the index expressions of modules/attention_fn/triton_paged.py evaluated in Python.
# Served geometry SPLITS 39, BLOCK_N 32, MIN_SPLIT 128, q_len 8; every round start c in 0 .. 8192
# and every row r < 8. Per (c, r): sA, sB, in_pass_b, runs_pass_b, the row's split length, then
# every split k < SPLITS whose chunk [lo, hi) is non-empty, as k=lo:hi. Impl definitions only.
import Base
import ./attn_rowinv.bend as Impl

def bool_text(b: Bool) -> String:
  match b:
    case False{}:
      "0"
    case True{}:
      "1"

def chunk_text(b: Bool, +k: Nat, +lo: Nat, +hi: Nat) -> String:
  match b:
    case False{}:
      ""
    case True{}:
      " " ++ Nat.show(k) ++ "=" ++ Nat.show(lo) ++ ":" ++ Nat.show(hi)

def chunks(left: Nat, +k: Nat, +c: Nat, +r: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+m:
      +lo = Impl.chunk_lo(c, 8n, r, k, 39n, 32n, 128n)
      +hi = Impl.chunk_hi(c, 8n, r, k, 39n, 32n, 128n)
      chunk_text(Nat.is_lt(lo, hi), k, lo, hi) ++ chunks(m, 1n+k, c, r)

def line(+c: Nat, +r: Nat) -> String:
  "c=" ++ Nat.show(c) ++ " r=" ++ Nat.show(r) ++
    " sA=" ++ Nat.show(Impl.pass_a_len(c, 39n, 32n, 128n)) ++
    " sB=" ++ Nat.show(Impl.pass_b_len(c, 8n, 39n, 32n, 128n)) ++
    " b=" ++ bool_text(Impl.in_pass_b(c, r, 39n, 32n, 128n)) ++
    " run=" ++ bool_text(Impl.runs_pass_b(c, 8n, 39n, 32n, 128n)) ++
    " s=" ++ Nat.show(Impl.kernel_row_split_len(c, 8n, r, 39n, 32n, 128n)) ++
    chunks(39n, 0n, c, r)

def per_r(left: Nat, +c: Nat, +r: Nat) -> IO(Unit):
  match left:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(line(c, r))
        per_r(m, c, 1n+r)

def per_c(left: Nat, +c: Nat) -> IO(Unit):
  match left:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        per_r(8n, c, 0n)
        per_c(m, 1n+c)

# c = 0 .. 8192 (8193 round starts), 8 rows each
def main() -> IO(Unit):
  per_c(8193n, 0n)
