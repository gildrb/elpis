# Independent reference for the row-invariant verify-attention partition (ext 3005): the key range
# 0 .. p of the query at absolute position p is cut into chunks of one length that depends on p
# alone: the per-split share of the p + 1 keys over SPLITS splits, rounded up to a whole BLOCK_N
# tile, and at least MIN_SPLIT. The row's attention is the fixed left-to-right merge of the
# partials of its own chunks. Nothing here mentions rounds, passes or the launched grid.
import Base

def ceil_div(a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

def row_len(+n: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.max(min_split, Nat.mul(block_n, ceil_div(ceil_div(n, splits), block_n)))

# Chunk k of position p: [k * len, min((k + 1) * len, p + 1)).
def chunk_lo(+p: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.mul(k, row_len(1n+p, splits, block_n, min_split))

def chunk_hi(+p: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.min(Nat.add(chunk_lo(p, k, splits, block_n, min_split), row_len(1n+p, splits, block_n, min_split)), 1n+p)

# Number of chunks of position p.
def chunks(+p: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  ceil_div(1n+p, row_len(1n+p, splits, block_n, min_split))

def fold.go(~A: Data, ~merge: A -> A -> A, ~P: Nat -> Nat -> A, left: Nat, +k: Nat, +p: Nat,
    +splits: Nat, +block_n: Nat, +min_split: Nat, acc: A) -> A:
  match left:
    case 0n:
      acc
    case 1n+more:
      fold.go(~A, ~merge, ~P, more, 1n+k, p, splits, block_n, min_split,
        merge(acc, P(chunk_lo(p, k, splits, block_n, min_split), chunk_hi(p, k, splits, block_n, min_split))))

# The row's attention result: e merged with its chunks' partials 0 .. chunks - 1, in order.
def row_result(~A: Data, ~merge: A -> A -> A, ~P: Nat -> Nat -> A, ~e: A, +p: Nat, +splits: Nat,
    +block_n: Nat, +min_split: Nat) -> A:
  fold.go(~A, ~merge, ~P, chunks(p, splits, block_n, min_split), 0n, p, splits, block_n, min_split, e)
