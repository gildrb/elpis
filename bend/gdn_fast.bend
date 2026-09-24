# Thread/block mapping of the fused GDN conv + gated delta rule + gated RMS norm verify kernel
# (ext patch 5101 v2, exllamav3_ext/gdn.cu, gdn_conv_rule_norm_kernel) and of the shared per-thread
# token routine gdn_rule_tokens<MODE, GROUPS> that the fused verify kernels (RULE_VERIFY, GROUPS = 4,
# 512 threads, one block per (h, b), thread map gdn_rule_thread(0)) and the commit replay
# batched_state_replay_kernel (RULE_COMMIT, GROUPS = 1, 128 threads, block = v chunk of 32 columns,
# gdn_rule_thread(blockIdx.x * 32)) both call. Transcribed from the CUDA integer expressions over
# Nat. C `int` arithmetic on the non-negative values used here is Nat arithmetic while nothing
# overflows (t < 512, S <= 16, H, Nk <= 2^10, F < 2^20); `x >> 1` and `x & 1` of a non-negative int
# are x / 2 and x % 2. Strided `for (x = start; x < n; x += step)` loops are the m16 finisher loop
# model M16.jobloop.go (fuel n + 1, never short for step >= 1).
# Reference: gdn_fast_spec.bend; laws: gdn_fast_laws.bend. Proof model only (not shipped).
import Base
import ./gemm_m16_partition.bend as M16
import ./gemm_m16_partition_spec.bend as MS

# C ternary `c ? x : y`
def pick(c: Bool, +x: Nat, +y: Nat) -> Nat:
  match c:
    case True{}:
      x
    case False{}:
      y

# ==== (1) recurrence ownership: gdn_rule_thread(v_start) ====
# chunk = threadIdx.x / 128; kslice = (threadIdx.x - chunk * 128) / 32
def kslice(+t: Nat) -> Nat:
  Nat.div(Nat.sub(t, Nat.mul(Nat.div(t, 128n), 128n)), 32n)

# vcol = v_start + chunk * 32 + threadIdx.x % 32
def vcol(+vstart: Nat, +t: Nat) -> Nat:
  Nat.add(Nat.add(vstart, Nat.mul(Nat.div(t, 128n), 32n)), Nat.mod(t, 32n))

# The shared per-(k slice, v column) token routine. `step` is the per-token state update of the
# thread's 32 state values (dot1 over the k slice, SUBK-ordered sum, state/v_out chains) and `out`
# its per-token partial; both are uninterpreted: every law holds for every choice. The routine runs
# `steps` tokens of `xs` in order from state `s` and records (state after the token, output).
type Tok<-S: Data, -O: Data> is Data:
  Tok{state: S, out: O}

def run(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O, steps: Nat,
    xs: List<&2, X>, s: S) -> List<&2, Tok<S, O>>:
  match steps:
    case 0n:
      Nil{}
    case 1n+more:
      match xs:
        case Nil{}:
          Nil{}
        case +x <> rest:
          +n = step(s, x)
          Tok{n, out(n, x)} <> run(~S, ~X, ~O, ~step, ~out, more, rest, n)

# State after a token trace from s0: the last recorded state, s0 when no token ran.
def final(~S: Data, ~O: Data, ts: List<&2, Tok<S, O>>, s0: S) -> S:
  match ts:
    case Nil{}:
      s0
    case Tok{st, o} <> rest:
      final(~S, ~O, rest, st)

def outs(~S: Data, ~O: Data, ts: List<&2, Tok<S, O>>) -> List<&2, O>:
  match ts:
    case Nil{}:
      Nil{}
    case Tok{st, o} <> rest:
      o <> outs(~S, ~O, rest)

# Fused verify (RULE_VERIFY, GROUPS = 4): one run over all S = len(xs) tokens of the round.
def verify_trace(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    +xs: List<&2, X>, s0: S) -> List<&2, Tok<S, O>>:
  run(~S, ~X, ~O, ~step, ~out, List.length(&2, X, xs), xs, s0)

def verify_outputs(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    +xs: List<&2, X>, s0: S) -> List<&2, O>:
  outs(~S, ~O, verify_trace(~S, ~X, ~O, ~step, ~out, xs, s0))

# The verify kernel's internal state after its first r tokens (a prefix of the one verify run).
def verify_state(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O, +r: Nat,
    +xs: List<&2, X>, +s0: S) -> S:
  final(~S, ~O, List.take(&2, Tok<S, O>, verify_trace(~S, ~X, ~O, ~step, ~out, xs, s0), r), s0)

# Commit replay (RULE_COMMIT, GROUPS = 1): the same routine with steps = c accepted tokens.
def commit(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O, +c: Nat,
    +xs: List<&2, X>, +s0: S) -> S:
  final(~S, ~O, run(~S, ~X, ~O, ~step, ~out, c, xs, s0), s0)

# ==== (2) output reduction (gdn_rule_tokens<RULE_VERIFY, 4>, THREADS = 512):
# for (e = threadIdx.x; e < S * 128; e += THREADS) { s = e / 128; c = e - s * 128 } ====
def strided(+t: Nat, +step: Nat, +J: Nat) -> List<&2, Nat>:
  M16.jobloop.go(1n+J, Nat.is_lt(t, J), t, step, J)

# Number of threads t < n whose strided loop visits x.
def stride_hits(+n: Nat, +x: Nat, +step: Nat, +J: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+t:
      Nat.add(stride_hits(t, x, step, J), MS.bit(MS.member(strided(t, step, J), x)))

def red_hits(+x: Nat, +S: Nat) -> Nat:
  stride_hits(512n, x, 512n, Nat.mul(S, 128n))

def red_s(+e: Nat) -> Nat:
  Nat.div(e, 128n)

def red_c(+e: Nat) -> Nat:
  Nat.sub(e, Nat.mul(red_s(e), 128n))

# ==== (3) gated RMS norm: `if (warp_id < S)`, warp w normalizes token w (row_off uses warp_id) ====
def norm_hits(+n: Nat, +s: Nat, +S: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+w:
      Nat.add(norm_hits(w, s, S), MS.bit(Bool.and(Nat.is_lt(w, S), Nat.is_eq(w, s))))

# ==== (4) b/a GEMV (conv kernel) and q/k l2 norms (gdn_rule_tokens): for (task = warp; task < 2 * S;
# task += THREADS / 32), THREADS = 512, with ab = task & 1, s = task >> 1 ====
def task_hits(+x: Nat, +S: Nat) -> Nat:
  stride_hits(16n, x, 16n, Nat.mul(2n, S))

def task_s(+task: Nat) -> Nat:
  Nat.div(task, 2n)

def task_ab(+task: Nat) -> Nat:
  Nat.mod(task, 2n)

# ==== (5) conv channel ownership ====
# group = H / Nk; kh = h / group; owner = h % group == group - 1
def kh(+g: Nat, +h: Nat) -> Nat:
  Nat.div(h, g)

def owner(+g: Nat, +h: Nat) -> Bool:
  Nat.is_eq(Nat.mod(h, g), Nat.sub(g, 1n))

# c = t < HD ? kh * HD + t : (t < 2 * HD ? (Nk + kh) * HD + t - HD : 2 * Nk * HD + h * HD + t - 2 * HD)
def chan(+Nk: Nat, +g: Nat, +h: Nat, +t: Nat) -> Nat:
  pick(Nat.is_lt(t, 128n), Nat.add(Nat.mul(kh(g, h), 128n), t),
    pick(Nat.is_lt(t, 256n), Nat.sub(Nat.add(Nat.mul(Nat.add(Nk, kh(g, h)), 128n), t), 128n),
      Nat.sub(Nat.add(Nat.add(Nat.mul(Nat.mul(2n, Nk), 128n), Nat.mul(h, 128n)), t), 256n)))

# store = owner || t >= 2 * HD  (conv_out store; the conv_state write-back stores the same set:
# v windows by every block, q/k windows only `if (owner)`)
def store(+g: Nat, +h: Nat, +t: Nat) -> Bool:
  Bool.or(owner(g, h), Nat.is_le(256n, t))

# conv_sync[b * Nk + kh]: every non-owner block of k head k0 adds 1 once (`if (!owner && t == 0)
# atomicAdd`). Total adds over blocks h < n.
def ctr_adds(+n: Nat, +g: Nat, +k0: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+h:
      Nat.add(ctr_adds(h, g, k0), MS.bit(Bool.and(Bool.not(owner(g, h)), Nat.is_eq(kh(g, h), k0))))

# Owner blocks of k head k0 among blocks h < n.
def owners(+n: Nat, +g: Nat, +k0: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+h:
      Nat.add(owners(h, g, k0), MS.bit(Bool.and(owner(g, h), Nat.is_eq(kh(g, h), k0))))

# The owner (group > 1) spins `while (*ctr < group - 1)`, then `*ctr = 0`: with `adds` adds in
# total the wait can exit (wait_exits) and the counter ends at adds - (group - 1) after the reset
# (adds made after the reset survive it).
def wait_exits(+g: Nat, +adds: Nat) -> Bool:
  Bool.not(Nat.is_lt(adds, Nat.sub(g, 1n)))

def ctr_end(+g: Nat, +adds: Nat) -> Nat:
  Nat.sub(adds, Nat.sub(g, 1n))
