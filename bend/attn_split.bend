# Split/combine partition of the target verify-attention kernels (ext patch 3003,
# exllamav3_ext/attn_verify.cuh + attn_verify.cu: attn_verify_split_k3v3 / _k4v4 and
# attn_verify_combine), transcribed from the CUDA integer expressions over Nat. H = attn_verify.cuh,
# C = attn_verify.cu. C `int` arithmetic on the non-negative values used here is Nat arithmetic
# while nothing overflows (L <= 2^18 + 8, S <= 82, AV_T = 64). The independent reference is
# attn_split_spec.bend; the laws are attn_split_laws.bend.
import Base

# H: ceil division (a + b - 1) / b as written in av_split_len / av_live_splits
def cdiv(a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

# H av_split_len: per = (L + S - 1) / S; ((per + AV_T - 1) / AV_T) * AV_T, AV_T = 64
def split_len(+L: Nat, +S: Nat) -> Nat:
  Nat.mul(cdiv(cdiv(L, S), 64n), 64n)

# C split_body: n_start = split * s_len
def n_start(i: Nat, +L: Nat, +S: Nat) -> Nat:
  Nat.mul(i, split_len(L, S))

# C split_body: n_end = min(n_start + s_len, L)
def n_end(+i: Nat, +L: Nat, +S: Nat) -> Nat:
  Nat.min(Nat.add(n_start(i, L, S), split_len(L, S)), L)

# C split_body: `if (n_start >= L) return;` -- the CTA of split i runs (and writes its partial
# row block) iff n_start < L
def runs(+i: Nat, +L: Nat, +S: Nat) -> Bool:
  Bool.not(Nat.is_le(L, n_start(i, L, S)))

# C split_body, for the CTA of split i and a thread row with q_pos = gid < q_len: token `tok`
# of a staged tile enters the softmax iff `tok < n_end && tok <= q_abs`, q_abs = L - q_len + gid
# (the tiles n0 = n_start + it * AV_T, it < ntiles, start at n_start; row validity is separate).
# `p` is the absolute kv position; tokens below n_start belong to no tile of this CTA.
def visits(+i: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Bool:
  Bool.and(Nat.is_le(n_start(i, L, S), p),
    Bool.and(Nat.is_lt(p, n_end(i, L, S)),
      Nat.is_le(p, Nat.add(Nat.sub(L, q_len), qpos))))

def bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# Number of CTAs among splits 0 .. k - 1 (grid x = S) that let position p into row qpos's softmax.
def hits(+k: Nat, +p: Nat, +L: Nat, +S: Nat, +q_len: Nat, +qpos: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+j:
      Nat.add(hits(j, p, L, S, q_len, qpos), bit(visits(j, p, L, S, q_len, qpos)))

# H av_live_splits: ceil(L / split_len); C attn_verify_combine loops s = 0 .. live - 1
def live(+L: Nat, +S: Nat) -> Nat:
  cdiv(L, split_len(L, S))

# C attn_verify_combine: `for (int s = 0; s < live; ++s)`, twice (max, then weighted sum), in
# this fixed increasing order; `left` = live - s.
def combine.go(left: Nat, +s: Nat) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+r:
      s <> combine.go(r, 1n+s)

def combine_order(+L: Nat, +S: Nat) -> List<&2, Nat>:
  combine.go(live(L, S), 0n)
