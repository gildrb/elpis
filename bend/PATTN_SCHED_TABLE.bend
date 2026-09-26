# Finite differential table of the ext 3010 prefill attention schedule model (bend/pattn_sched.bend),
# compared byte for byte by bend/pattn_sched_diff.py against the index expressions quoted from
# exllamav3_ext/pattn_kernel.cuh (compiled for the CPU).
# V L q qb r: for keys p = 0 .. L + 1, how many tile iterations put p into thread row r of query block qb.
# P it: page offset of tile it. G kvh w: q head of warp w. S d: span of dim / key d.
import Base
import ./pattn_sched.bend as P

def bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def hits(k: Nat, +it: Nat, +L: Nat, +q: Nat, +qb: Nat, +r: Nat, +p: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+m:
      Nat.add(bit(P.visits(L, q, qb, r, it, p)), hits(m, 1n+it, L, q, qb, r, p))

def counts(k: Nat, +p: Nat, +L: Nat, +q: Nat, +qb: Nat, +r: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      Nat.show(hits(Nat.add(P.ntiles(L, q, qb), 2n), 0n, L, q, qb, r, p)) ++ counts(m, 1n+p, L, q, qb, r)

def row_line(ok: Bool, +r: Nat, +L: Nat, +q: Nat, +qb: Nat) -> IO(Unit):
  match ok:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      IO.print("V " ++ Nat.show(L) ++ " " ++ Nat.show(q) ++ " " ++ Nat.show(qb) ++ " " ++ Nat.show(r) ++ " " ++
        counts(Nat.add(L, 2n), 0n, L, q, qb, r))

def rows(k: Nat, +r: Nat, +L: Nat, +q: Nat, +qb: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        row_line(Nat.is_lt(P.q_pos(qb, r), q), r, L, q, qb)
        rows(m, 1n+r, L, q, qb)

def blocks(k: Nat, +qb: Nat, +L: Nat, +q: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        rows(16n, 0n, L, q, qb)
        blocks(m, 1n+qb, L, q)

def chunk(+L: Nat, +q: Nat) -> IO(Unit):
  blocks(Nat.div(Nat.add(q, 15n), 16n), 0n, L, q)

def pages(k: Nat, +it: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print("P " ++ Nat.show(it) ++ " " ++ Nat.show(P.page_off(it)))
        pages(m, 1n+it)

def heads(k: Nat, +h: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print("G " ++ Nat.show(Nat.div(h, 6n)) ++ " " ++ Nat.show(Nat.mod(h, 6n)) ++ " " ++ Nat.show(P.q_head(Nat.div(h, 6n), Nat.mod(h, 6n))))
        heads(m, 1n+h)

def spans(k: Nat, +d: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print("S " ++ Nat.show(d) ++ " " ++ Nat.show(P.span(d)))
        spans(m, Nat.add(d, 7n))

# Must match CASES of pattn_sched_diff.py
def main() -> IO(Unit):
  do IO<Unit>:
    chunk(1n, 1n)
    chunk(17n, 5n)
    chunk(31n, 16n)
    chunk(32n, 17n)
    chunk(33n, 33n)
    chunk(47n, 20n)
    chunk(64n, 64n)
    chunk(65n, 16n)
    chunk(100n, 37n)
    chunk(130n, 3n)
    chunk(62n, 32n)
    chunk(81n, 19n)
    pages(20n, 0n)
    heads(24n, 0n)
    spans(40n, 0n)
