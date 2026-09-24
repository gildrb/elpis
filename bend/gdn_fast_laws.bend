# Obligations for the thread/block mapping of the 5101 fused GDN verify kernel
# (gdn_conv_rule_norm_kernel) and of the per-thread token routine it shares with the commit replay
# kernel, over the Nat model gdn_fast.bend against gdn_fast_spec.bend. Domains: every S (token
# count; the kernel launches 1 <= S <= 16), every head count Nk >= 0 and group >= 1 (H = Nk * group
# v heads; served shape Nk = 16, group = 3), every step/out function and state/token type of the
# routine. Nat model of the C int expressions: overflow, fp32 values, memory ordering of the
# conv_sync atomics (__threadfence / volatile spin) and the GPU scheduler are outside this contract.
import Base
import ./gdn_fast.bend as Impl
import ./gdn_fast_spec.bend as Spec
import ./gdn_replay.bend as GR

# (1) Fused verify block (gdn_rule_thread(0), 512 threads): thread t owns the (k slice, v column) chain
# (kslice, vcol) in [0, 4) x [0, 128) and is the reference owner of it ...
law own_verify_into:
  for +t: Nat
  for tr: {Nat.is_lt(t, 512n) == True{} : Bool}
  {Bool.and(Nat.is_lt(Impl.kslice(t), 4n), Bool.and(Nat.is_lt(Impl.vcol(0n, t), 128n),
    Nat.is_eq(Spec.verify_thread(Impl.kslice(t), Impl.vcol(0n, t)), t))) == True{} : Bool}

# ... and every chain (k, v) of the head is owned by that thread: t -> (kslice, vcol) is a bijection
# [0, 512) -> [0, 4) x [0, 128), so every (head, v column, token) partial is computed exactly once.
law own_verify_onto:
  for +k: Nat
  for +v: Nat
  for kr: {Nat.is_lt(k, 4n) == True{} : Bool}
  for vr: {Nat.is_lt(v, 128n) == True{} : Bool}
  {Bool.and(Nat.is_lt(Spec.verify_thread(k, v), 512n),
    Bool.and(Nat.is_eq(Impl.kslice(Spec.verify_thread(k, v)), k),
      Nat.is_eq(Impl.vcol(0n, Spec.verify_thread(k, v)), v))) == True{} : Bool}

# (1') Commit replay (gdn_rule_thread(blockIdx.x * 32), 128 threads, block b < 4): thread t of block b owns
# (kslice, vcol) with vcol in [32 b, 32 b + 32) (vcol / 32 == b) ...
law own_replay_into:
  for +b: Nat
  for +t: Nat
  for br: {Nat.is_lt(b, 4n) == True{} : Bool}
  for tr: {Nat.is_lt(t, 128n) == True{} : Bool}
  {Bool.and(Nat.is_lt(Impl.kslice(t), 4n), Bool.and(Nat.is_lt(Impl.vcol(Nat.mul(b, 32n), t), 128n),
    Bool.and(Nat.is_eq(Spec.replay_block(Impl.vcol(Nat.mul(b, 32n), t)), b),
      Nat.is_eq(Spec.replay_thread(Impl.kslice(t), Impl.vcol(Nat.mul(b, 32n), t)), t)))) == True{} : Bool}

# ... and every chain (k, v) of [0, 4) x [0, 128) is owned by thread replay_thread(k, v) of block
# v / 32: per block a bijection onto [0, 4) x [32 b, 32 b + 32), over the 4 blocks exactly once.
law own_replay_onto:
  for +k: Nat
  for +v: Nat
  for kr: {Nat.is_lt(k, 4n) == True{} : Bool}
  for vr: {Nat.is_lt(v, 128n) == True{} : Bool}
  {Bool.and(Nat.is_lt(Spec.replay_block(v), 4n), Bool.and(Nat.is_lt(Spec.replay_thread(k, v), 128n),
    Bool.and(Nat.is_eq(Impl.kslice(Spec.replay_thread(k, v)), k),
      Nat.is_eq(Impl.vcol(Nat.mul(Spec.replay_block(v), 32n), Spec.replay_thread(k, v)), v)))) == True{} : Bool}

# (R) The shared token routine: the fused verify's per-token outputs are the reference outputs ...
law routine_verify_outputs:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +xs: List<&2, X>
  for +s0: S
  {Impl.verify_outputs(~S, ~X, ~O, ~step, ~out, xs, s0) == Spec.outputs(~S, ~X, ~O, ~step, ~out, xs, s0) : List<&2, O>}

# ... the commit replay of c tokens is the fold of the first c tokens ...
law routine_commit_fold:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +c: Nat
  for +xs: List<&2, X>
  for +s0: S
  {Impl.commit(~S, ~X, ~O, ~step, ~out, c, xs, s0) == Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, c), s0) : S}

# ... and equals the verify kernel's internal state after its first c tokens, for every c (in
# particular every accepted count c in 1..S) ...
law commit_is_verify_prefix:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +c: Nat
  for +xs: List<&2, X>
  for +s0: S
  {Impl.commit(~S, ~X, ~O, ~step, ~out, c, xs, s0) == Impl.verify_state(~S, ~X, ~O, ~step, ~out, c, xs, s0) : S}

# ... so verifying tokens c.. from the commit(c) state yields rows c.. of the one-round verify.
law resume_outputs:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +c: Nat
  for +xs: List<&2, X>
  for +s0: S
  {Impl.verify_outputs(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), Impl.commit(~S, ~X, ~O, ~step, ~out, c, xs, s0)) ==
    List.drop(&2, O, Impl.verify_outputs(~S, ~X, ~O, ~step, ~out, xs, s0), c) : List<&2, O>}

# The shared routine is the recurrence of the engine model bend/gdn_replay.bend (RULE_VERIFY
# verify, RULE_COMMIT replay), so gdn_replay's proven round laws (commit_prefix, compose, ...) hold
# for the 5101 kernels.
law routine_is_gdn_replay:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +c: Nat
  for +xs: List<&2, X>
  for +s0: S
  {GR.replay(~S, ~X, ~step, c, xs, s0) == Impl.commit(~S, ~X, ~O, ~step, ~out, c, xs, s0) : S} &
  {GR.verify(~S, ~X, ~O, ~step, ~out, xs, s0) == Impl.verify_outputs(~S, ~X, ~O, ~step, ~out, xs, s0) : List<&2, O>}

# (2) Output reduction: every flat index e < S * 128 is reduced by exactly one (thread, iteration),
# no index past the end by any, for every S ...
law red_exactly_once:
  for +x: Nat
  for +S: Nat
  {Impl.red_hits(x, S) == Spec.covered(x, Nat.mul(S, 128n)) : Nat}

# ... and e <-> (s, c) = (e / 128, e - s * 128) is a bijection [0, S * 128) -> [0, S) x [0, 128).
law red_decode:
  for +s: Nat
  for +c: Nat
  for cr: {Nat.is_lt(c, 128n) == True{} : Bool}
  {Impl.red_s(Spec.flat(s, c, 128n)) == s : Nat} & {Impl.red_c(Spec.flat(s, c, 128n)) == c : Nat}

law red_decode_range:
  for +e: Nat
  for +S: Nat
  for er: {Nat.is_lt(e, Nat.mul(S, 128n)) == True{} : Bool}
  {Nat.is_lt(Impl.red_s(e), S) == True{} : Bool} & {Nat.is_lt(Impl.red_c(e), 128n) == True{} : Bool} &
  {Spec.flat(Impl.red_s(e), Impl.red_c(e), 128n) == e : Nat}

# (3) Gated RMS norm: with S <= 16 every token row s < S is normalized by exactly one of the 16
# warps, no other row by any.
law norm_exactly_once:
  for +s: Nat
  for +S: Nat
  for sr: {Nat.is_le(S, 16n) == True{} : Bool}
  {Impl.norm_hits(16n, s, S) == Spec.covered(s, S) : Nat}

# (4) b/a GEMV and q/k l2-norm tasks: every task < 2 S is run by exactly one (warp, iteration) ...
law task_exactly_once:
  for +x: Nat
  for +S: Nat
  {Impl.task_hits(x, S) == Spec.covered(x, Nat.mul(2n, S)) : Nat}

# ... and task <-> (s, ab) = (task >> 1, task & 1) is a bijection [0, 2 S) -> [0, S) x {0, 1}.
law task_decode:
  for +s: Nat
  for +ab: Nat
  for abr: {Nat.is_lt(ab, 2n) == True{} : Bool}
  {Impl.task_s(Spec.flat(s, ab, 2n)) == s : Nat} & {Impl.task_ab(Spec.flat(s, ab, 2n)) == ab : Nat}

law task_decode_range:
  for +x: Nat
  for +S: Nat
  for xr: {Nat.is_lt(x, Nat.mul(2n, S)) == True{} : Bool}
  {Nat.is_lt(Impl.task_s(x), S) == True{} : Bool} & {Nat.is_lt(Impl.task_ab(x), 2n) == True{} : Bool} &
  {Spec.flat(Impl.task_s(x), Impl.task_ab(x), 2n) == x : Nat}

# (5a) A (block h, thread t < 384) that stores (conv_out and conv_state window) reads and stores
# channel chan(h, t) < F, and is the reference storer of that channel (injective) ...
law conv_store_into:
  for +Nk: Nat
  for +g: Nat
  for +h: Nat
  for +t: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  for hr: {Nat.is_lt(h, Nat.mul(Nk, g)) == True{} : Bool}
  for tr: {Nat.is_lt(t, 384n) == True{} : Bool}
  for st: {Impl.store(g, h, t) == True{} : Bool}
  {Spec.store_block(Nk, g, Impl.chan(Nk, g, h, t)) == h : Nat} &
  {Spec.store_thread(Nk, Impl.chan(Nk, g, h, t)) == t : Nat} &
  {Nat.is_lt(Impl.chan(Nk, g, h, t), Spec.F(Nk, Nat.mul(Nk, g))) == True{} : Bool}

# (5a, 5b) ... and every channel c < F is read and stored by its reference storer: exactly one block
# per batch row stores each channel, and the storing block consumes it.
law conv_store_onto:
  for +Nk: Nat
  for +g: Nat
  for +c: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  for cr: {Nat.is_lt(c, Spec.F(Nk, Nat.mul(Nk, g))) == True{} : Bool}
  {Nat.is_lt(Spec.store_block(Nk, g, c), Nat.mul(Nk, g)) == True{} : Bool} &
  {Nat.is_lt(Spec.store_thread(Nk, c), 384n) == True{} : Bool} &
  {Impl.store(g, Spec.store_block(Nk, g, c), Spec.store_thread(Nk, c)) == True{} : Bool} &
  {Impl.chan(Nk, g, Spec.store_block(Nk, g, c), Spec.store_thread(Nk, c)) == c : Nat}

# (5d) A v channel (c >= 2 Nk * 128) is read only by the block that stores it (its own v head):
# no cross-block read-after-write hazard on v windows.
law conv_v_private:
  for +Nk: Nat
  for +g: Nat
  for +h: Nat
  for +t: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  for hr: {Nat.is_lt(h, Nat.mul(Nk, g)) == True{} : Bool}
  for tr: {Nat.is_lt(t, 384n) == True{} : Bool}
  for isv: {Nat.is_le(Nat.mul(Nat.add(Nk, Nk), 128n), Impl.chan(Nk, g, h, t)) == True{} : Bool}
  {Spec.store_block(Nk, g, Impl.chan(Nk, g, h, t)) == h : Nat}

# (5c) The blocks reading the q/k channels of k head k0 (kh == k0) are exactly the v heads
# [k0 * group, k0 * group + group) ...
law conv_qk_consumers:
  for +g: Nat
  for +h: Nat
  for +k0: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  {Nat.is_eq(Impl.kh(g, h), k0) == Spec.consumes(g, k0, h) : Bool}

# ... the owner of k0 is exactly the maximum of that range (so it waits only on lower blocks) ...
law conv_owner_last:
  for +g: Nat
  for +h: Nat
  for +k0: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  {Bool.and(Impl.owner(g, h), Nat.is_eq(Impl.kh(g, h), k0)) == Nat.is_eq(h, Spec.last(g, k0)) : Bool}

law conv_last_max:
  for +g: Nat
  for +h: Nat
  for +k0: Nat
  for gpos: {Nat.is_lt(0n, g) == True{} : Bool}
  for hc: {Spec.consumes(g, k0, h) == True{} : Bool}
  {Nat.is_le(h, Spec.last(g, k0)) == True{} : Bool} & {Spec.consumes(g, k0, Spec.last(g, k0)) == True{} : Bool}

# ... every k head has exactly one owner, and conv_sync[b][k0] receives exactly group - 1 adds (one
# per non-owner consumer). SCOPE: proven for the served shape only (Nk = 16 k heads, group = 3,
# H = 48 v heads), by evaluating all 16 k heads; the laws above hold for every Nk and group.
law conv_ctr_adds:
  for +k0: Nat
  for kr: {Nat.is_lt(k0, 16n) == True{} : Bool}
  {Impl.ctr_adds(Nat.mul(16n, 3n), 3n, k0) == Nat.sub(3n, 1n) : Nat} &
  {Impl.owners(Nat.mul(16n, 3n), 3n, k0) == 1n : Nat}

# ... so the owner's spin `while (*ctr < group - 1)` exits exactly when all adds have arrived (a is
# the number of adds seen so far), and the reset leaves the counter at 0 for the next launch.
# SCOPE: served shape (Nk = 16, group = 3).
law conv_ctr_wait:
  for +k0: Nat
  for +a: Nat
  for kr: {Nat.is_lt(k0, 16n) == True{} : Bool}
  for ar: {Nat.is_le(a, Impl.ctr_adds(Nat.mul(16n, 3n), 3n, k0)) == True{} : Bool}
  {Impl.wait_exits(3n, a) == Nat.is_eq(a, Impl.ctr_adds(Nat.mul(16n, 3n), 3n, k0)) : Bool} &
  {Impl.ctr_end(3n, Impl.ctr_adds(Nat.mul(16n, 3n), 3n, k0)) == 0n : Nat}
