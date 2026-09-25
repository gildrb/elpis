# Per-row split partition of the dense verify-attention GQA split kernel under ext patch
# 3005-attn-row-invariant-split (modules/attention_fn/triton_paged.py), and, for comparison, the
# round-relative partition of ext 3002 it replaces (triton_paged.py:1212-1220), over Nat. A round
# starts at cache length c and verifies q_len rows; row r is the query at absolute position
# p = c + r (causal: keys 0 .. p, i.e. n = p + 1 keys). Triton integer arithmetic on the
# non-negative values used here is Nat arithmetic. The floating-point combine is modeled by an
# abstract merge and partial (template parameters). Independent reference: attn_rowinv_spec.bend;
# laws: attn_rowinv_laws.bend. Extends attn_split.bend (same ceil division).
import Base
import ./attn_split.bend as Split

# 3005: s(n) = max(MIN_SPLIT, BLOCK_N * cdiv(n, SPLITS * BLOCK_N)) for a row with n keys.
def row_split_len(+n: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.max(min_split, Nat.mul(block_n, Split.cdiv(n, Nat.mul(splits, block_n))))

# Pass A split length sA = s(c + 1) (first row of the round).
def pass_a_len(+c: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  row_split_len(1n+c, splits, block_n, min_split)

# Pass B split length sB = s(c + q_len) (last row of the round).
def pass_b_len(+c: Nat, +q_len: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  row_split_len(Nat.add(c, q_len), splits, block_n, min_split)

# Row r belongs to pass B iff s(p + 1) != sA.
def in_pass_b(+c: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Bool:
  Bool.not(Nat.is_eq(row_split_len(1n+Nat.add(c, r), splits, block_n, min_split),
    pass_a_len(c, splits, block_n, min_split)))

# Pass B is launched only if sB != sA.
def runs_pass_b(+c: Nat, +q_len: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Bool:
  Bool.not(Nat.is_eq(pass_b_len(c, q_len, splits, block_n, min_split),
    pass_a_len(c, splits, block_n, min_split)))

def pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# The split length of the pass that computes row r's partials (the other pass masks the row).
def kernel_row_split_len(+c: Nat, +q_len: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  pick(in_pass_b(c, r, splits, block_n, min_split), pass_b_len(c, q_len, splits, block_n, min_split),
    pass_a_len(c, splits, block_n, min_split))

# Split k of row r's pass: n_start = k * s, n_end = min(n_start + s, total), total = c + q_len;
# the causal mask keeps keys <= p, so the row's chunk is [n_start, min(n_end, p + 1)).
def chunk_lo(+c: Nat, +q_len: Nat, +r: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.mul(k, kernel_row_split_len(c, q_len, r, splits, block_n, min_split))

def chunk_hi(+c: Nat, +q_len: Nat, +r: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  Nat.min(Nat.min(Nat.add(chunk_lo(c, q_len, r, k, splits, block_n, min_split),
    kernel_row_split_len(c, q_len, r, splits, block_n, min_split)), Nat.add(c, q_len)), 1n+Nat.add(c, r))

# The row's stored partial for one split: the partial of its chunk when the chunk is non-empty,
# the identity partial e (m = -inf, l = 0, acc = 0) when it is empty.
def partial(~A: Data, ~P: Nat -> Nat -> A, ~e: A, has: Bool, +lo: Nat, +hi: Nat) -> A:
  match has:
    case True{}:
      P(lo, hi)
    case False{}:
      e

# Combine: `for s in range(SPLITS)` merges split s's partial into the running result, in this
# fixed increasing order, starting from the identity.
def combine.go(~A: Data, ~merge: A -> A -> A, ~P: Nat -> Nat -> A, ~e: A, left: Nat, +k: Nat,
    +c: Nat, +q_len: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat, acc: A) -> A:
  match left:
    case 0n:
      acc
    case 1n+more:
      +lo = chunk_lo(c, q_len, r, k, splits, block_n, min_split)
      +hi = chunk_hi(c, q_len, r, k, splits, block_n, min_split)
      combine.go(~A, ~merge, ~P, ~e, more, 1n+k, c, q_len, r, splits, block_n, min_split,
        merge(acc, partial(~A, ~P, ~e, Nat.is_lt(lo, hi), lo, hi)))

def combine(~A: Data, ~merge: A -> A -> A, ~P: Nat -> Nat -> A, ~e: A, +c: Nat, +q_len: Nat,
    +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> A:
  combine.go(~A, ~merge, ~P, ~e, splits, 0n, c, q_len, r, splits, block_n, min_split, e)

# Key j in split k of row r's pass (triton_paged.py, causal full-context launch): lo = 0 (1170),
# n_start = lo + split * s_len (1190) and n_end = min(n_start + s_len, total_k_len) (1191) with
# s_len the row's pass length and total_k_len = c + q_len; the tile loop
# `for n0 in range(n_start, n_end, BLOCK_N)` with offs_n = n0 + arange(BLOCK_N) masked by
# offs_n < n_end (1210-1214, _gqa_step 1120) visits exactly n_start <= j < n_end, and the causal
# mask offs_n <= q_abs (1122) with q_abs = total_k_len - q_len + row_q = c + r (1107) keeps j <= c + r.
def key_valid(+c: Nat, +q_len: Nat, +r: Nat, +k: Nat, +j: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Bool:
  +s = kernel_row_split_len(c, q_len, r, splits, block_n, min_split)
  +n_start = Nat.mul(k, s)
  +n_end = Nat.min(Nat.add(n_start, s), Nat.add(c, q_len))
  Bool.and(Nat.is_le(n_start, j), Bool.and(Nat.is_lt(j, n_end), Nat.is_le(j, Nat.add(c, r))))

# Number of splits k < `left` from k whose chunk for row r is non-empty (lo < hi).
def chunk_count.go(left: Nat, +k: Nat, +c: Nat, +q_len: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  match left:
    case 0n:
      0n
    case 1n+more:
      Nat.add(Split.bit(Nat.is_lt(chunk_lo(c, q_len, r, k, splits, block_n, min_split),
          chunk_hi(c, q_len, r, k, splits, block_n, min_split))),
        chunk_count.go(more, 1n+k, c, q_len, r, splits, block_n, min_split))

# Number of the SPLITS launched splits that hold a non-empty chunk of row r.
def chunk_count(+c: Nat, +q_len: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  chunk_count.go(splits, 0n, c, q_len, r, splits, block_n, min_split)

# store_acc = lo + split * s_a < total_k_len (1351): pass A's split k has key work, so the
# accumulator rows of block k are written (by pass A and, for its rows, pass B).
def store_acc(+c: Nat, +q_len: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Bool:
  Nat.is_lt(Nat.mul(k, pass_a_len(c, splits, block_n, min_split)), Nat.add(c, q_len))

# Ext 3002 (replaced): total = c + q_len (the round's end), lo = 0,
# live = max(1, min(SPLITS, cdiv(total, MIN_SPLIT))), s_len = cdiv(cdiv(total, live), BLOCK_N) * BLOCK_N,
# the same for every row of the round.
def old_split_len(+total: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  +live = Nat.max(1n, Nat.min(splits, Split.cdiv(total, min_split)))
  Nat.mul(Split.cdiv(Split.cdiv(total, live), block_n), block_n)

def old_row_split_len(+c: Nat, +q_len: Nat, +r: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  old_split_len(Nat.add(c, q_len), splits, block_n, min_split)

def old_chunk_hi(+c: Nat, +q_len: Nat, +r: Nat, +k: Nat, +splits: Nat, +block_n: Nat, +min_split: Nat) -> Nat:
  +s = old_row_split_len(c, q_len, r, splits, block_n, min_split)
  Nat.min(Nat.min(Nat.add(Nat.mul(k, s), s), Nat.add(c, q_len)), 1n+Nat.add(c, r))
