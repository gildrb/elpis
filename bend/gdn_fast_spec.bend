# Independent reference for the 5101 fused GDN verify kernel mapping (gdn_fast.bend).
import Base
import ./gemm_m16_partition_spec.bend as MS

# ---- (1) ownership: the (k slice k, v column v) state chain of a head belongs to one thread.
# Fused verify block (512 threads): thread v / 32 * 128 + k * 32 + v % 32.
def verify_thread(+k: Nat, +v: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.div(v, 32n), 128n), Nat.mul(k, 32n)), Nat.mod(v, 32n))

# Replay: block v / 32 of the head, thread k * 32 + v % 32 of that 128-thread block.
def replay_block(+v: Nat) -> Nat:
  Nat.div(v, 32n)

def replay_thread(+k: Nat, +v: Nat) -> Nat:
  Nat.add(Nat.mul(k, 32n), Nat.mod(v, 32n))

# ---- shared recurrence: the state after tokens is the left fold of step.
def fold(~S: Data, ~X: Data, ~step: S -> X -> S, xs: List<&2, X>, s: S) -> S:
  match xs:
    case Nil{}:
      s
    case x <> rest:
      fold(~S, ~X, ~step, rest, step(s, x))

# Per-token outputs: token i emits out(state after tokens 0..i, token i).
def outputs(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    xs: List<&2, X>, s: S) -> List<&2, O>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      +n = step(s, x)
      out(n, x) <> outputs(~S, ~X, ~O, ~step, ~out, rest, n)

# ---- (2)-(4) exactly-once coverage: an index x of [0, n) is produced once, others never.
def covered(+x: Nat, +n: Nat) -> Nat:
  MS.bit(Nat.is_lt(x, n))

# Row-major flat index of (row r, column c) with `width` columns.
def flat(+r: Nat, +c: Nat, +width: Nat) -> Nat:
  Nat.add(Nat.mul(r, width), c)

# ---- (5) conv channels. Layout of the qkv / conv rows: q heads [0, Nk), k heads [Nk, 2 Nk),
# v heads [2 Nk, 2 Nk + H), 128 channels each; F = (2 Nk + H) * 128.
def F(+Nk: Nat, +H: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.add(Nk, Nk), H), 128n)

# The v heads of k head k0 are the contiguous range [k0 * group, k0 * group + group).
def consumes(+g: Nat, +k0: Nat, +h: Nat) -> Bool:
  Bool.and(Nat.is_le(Nat.mul(k0, g), h), Nat.is_lt(h, Nat.add(Nat.mul(k0, g), g)))

# Its maximum.
def last(+g: Nat, +k0: Nat) -> Nat:
  Nat.add(Nat.mul(k0, g), Nat.sub(g, 1n))

def store_block.row(+Nk: Nat, +g: Nat, +j: Nat, isq: Bool, isk: Bool) -> Nat:
  match isq:
    case True{}:
      last(g, j)
    case False{}:
      match isk:
        case True{}:
          last(g, Nat.sub(j, Nk))
        case False{}:
          Nat.sub(j, Nat.add(Nk, Nk))

# Block (v head) that must store channel c: v head j - 2 Nk of a v row, the last v head
# (k0 + 1) * group - 1 of the k head k0 of a q/k row (the q/k rows are shared by that k head's
# group of v heads).
def store_block(+Nk: Nat, +g: Nat, +c: Nat) -> Nat:
  store_block.row(Nk, g, Nat.div(c, 128n), Nat.is_lt(Nat.div(c, 128n), Nk),
    Nat.is_lt(Nat.div(c, 128n), Nat.add(Nk, Nk)))

def store_thread.base(isq: Bool, isk: Bool) -> Nat:
  match isq:
    case True{}:
      0n
    case False{}:
      match isk:
        case True{}:
          128n
        case False{}:
          256n

# Thread of that block that holds c: offset 0 / 128 / 256 by row kind, plus c % 128.
def store_thread(+Nk: Nat, +c: Nat) -> Nat:
  Nat.add(store_thread.base(Nat.is_lt(Nat.div(c, 128n), Nk),
    Nat.is_lt(Nat.div(c, 128n), Nat.add(Nk, Nk))), Nat.mod(c, 128n))
