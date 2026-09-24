# Laws of the GDN history-free verify + commit-time replay model
# (bend/gdn_replay.bend) against the independent reference
# (bend/gdn_replay_spec.bend). `step` and `out` are template parameters: the
# checker treats them as opaque functions, so every law holds for every
# per-token update and readout, and for every state / input / output type.
# A round's decision is the greedy acceptance verdict (count, eos) of
# bend/exl3_accept_spec.bend; its count is >= 1 on every well-shaped round
# (Exl3AcceptLaws.accept_progress), EOS and an exhausted budget report eos,
# a checkpoint boundary, a mismatch and the bonus position do not.
# Domains: all window (k), all count c, all K (conv_kernel_size) and H
# (max_history); the conv laws need 1 <= k <= H (the engine drafts k >= 1:
# dflash returns no draft for window 0, and seqlen <= max_history + 1 is
# checked by cuda_recurrent_gated_delta_rule); k <= 7 is a special case.
import Base
import ./gdn_replay.bend as Impl
import ./gdn_replay_spec.bend as Spec
import ./exl3_accept_spec.bend as Accept

# Verify (RULE_VERIFY): row i's output is the readout of the state after the
# first i + 1 verified tokens, starting from row 0; no state row is written
# (the model's verify returns outputs only; round passes row 0 on untouched).
law verify_outputs:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +xs: List<&2, X>
  for +s0: S
  {Impl.verify(~S, ~X, ~O, ~step, ~out, xs, s0) ==
    Spec.outputs(~S, ~X, ~O, ~step, ~out, xs, s0, Nil{}) : List<&2, O>}

# (a) A round that does not end the job (checkpoint boundary, mismatch or the
# bonus position: eos = False) leaves row 0 equal to the fold of exactly its
# first c verified tokens, for every c <= k + 1 (c = 0 included: refused, (b)).
law commit_prefix:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for bounded: {Nat.is_le(count, 1n+window) == True{} : Bool}
  {Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) ==
    Spec.fold(~S, ~X, ~step, List.take(&2, X, xs, count), s0) : S}

# (a, eos) A round that ends the job (EOS or exhausted budget) commits ALL
# k + 1 verified tokens, whatever its count (generator.py:1295 rejects none).
# Sound only if a completed job's recurrent/conv state and post-stop KV pages
# are never reused (else the engine must replay only c). Audited for this
# deployment: a finished job's pages are freed without a stash
# (generator.py:1335-1343), the recurrent checkpoint stash is keyed by the
# committed kv_position (job.py:1600-1620), and a reused slot is cleared on
# get_new_state (cache.py:324-335).
law commit_eos:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  {Impl.row0_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) ==
    Spec.fold(~S, ~X, ~step, xs, s0) : S}

# (b) c = 0 without eos is refused before any launch: row 0 is unchanged.
law commit_empty:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  {Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{0n, False{}}) == Impl.Refused{s0} : Impl.Outcome<S, Y>}

# Every count the acceptance leaf can return (1..k+1), and every eos round,
# commits: the host checks never refuse them.
law commit_happens:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for progress: {Nat.is_le(1n, count) == True{} : Bool}
  for bounded: {Nat.is_le(count, 1n+window) == True{} : Bool}
  {Impl.committed(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) == True{} : Bool}

law commit_happens_eos:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  {Impl.committed(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) == True{} : Bool}

# (c) The conv window (columns [0, K)) after a non-eos commit is the last K
# conv inputs of the pre-round window followed by the first c tokens; the
# buffer keeps its K + H columns.
law conv_window:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for shaped_ys: {List.length(&2, Y, ys) == 1n+window : Nat}
  for shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat}
  for drafted: {Nat.is_le(1n, window) == True{} : Bool}
  for fits: {Nat.is_le(window, H) == True{} : Bool}
  for progress: {Nat.is_le(1n, count) == True{} : Bool}
  for bounded: {Nat.is_le(count, 1n+window) == True{} : Bool}
  {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})), K) ==
    Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K),
      List.take(&2, Y, ys, count))) : List<&2, Y>} &
  {List.length(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}}))) ==
    Nat.add(K, H) : Nat}

# (c, eos) Same dependency as commit_eos: all k + 1 conv inputs are kept.
law conv_window_eos:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for shaped_ys: {List.length(&2, Y, ys) == 1n+window : Nat}
  for shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat}
  for drafted: {Nat.is_le(1n, window) == True{} : Bool}
  for fits: {Nat.is_le(window, H) == True{} : Bool}
  {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})), K) ==
    Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), ys))
    : List<&2, Y>}

# (d) The position advances by exactly c (eos: by k + 1) and last_history is
# cleared.
law position_advance:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for progress: {Nat.is_le(1n, count) == True{} : Bool}
  for bounded: {Nat.is_le(count, 1n+window) == True{} : Bool}
  {Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) == Nat.add(position, count)
    : Nat} &
  {Impl.last_history_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, False{}})) == 0n : Nat}

law position_advance_eos:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  {Impl.position_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) ==
    Nat.add(position, 1n+window) : Nat} &
  {Impl.last_history_of(~S, ~Y, Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh}, window, xs, ys, Accept.Verdict{count, True{}})) == 0n : Nat}

# (e) Compositionality: two non-eos rounds equal one fold over the
# concatenation of their committed prefixes, for row 0, the conv window and
# the position.
law compose:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +w1: Nat
  for +xs1: List<&2, X>
  for +ys1: List<&2, Y>
  for +c1: Nat
  for +w2: Nat
  for +xs2: List<&2, X>
  for +ys2: List<&2, Y>
  for +c2: Nat
  for shaped_xs1: {List.length(&2, X, xs1) == 1n+w1 : Nat}
  for shaped_xs2: {List.length(&2, X, xs2) == 1n+w2 : Nat}
  for progress1: {Nat.is_le(1n, c1) == True{} : Bool}
  for bounded1: {Nat.is_le(c1, 1n+w1) == True{} : Bool}
  for progress2: {Nat.is_le(1n, c2) == True{} : Bool}
  for bounded2: {Nat.is_le(c2, 1n+w2) == True{} : Bool}
  for shaped_ys1: {List.length(&2, Y, ys1) == 1n+w1 : Nat}
  for shaped_ys2: {List.length(&2, Y, ys2) == 1n+w2 : Nat}
  for shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat}
  for drafted1: {Nat.is_le(1n, w1) == True{} : Bool}
  for fits1: {Nat.is_le(w1, H) == True{} : Bool}
  for drafted2: {Nat.is_le(1n, w2) == True{} : Bool}
  for fits2: {Nat.is_le(w2, H) == True{} : Bool}
  {Impl.row0_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H,
      Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh},
        w1, xs1, ys1, Accept.Verdict{c1, False{}}),
      w2, xs2, ys2, Accept.Verdict{c2, False{}})) ==
    Spec.fold(~S, ~X, ~step, List.append(&2, X, List.take(&2, X, xs1, c1),
      List.take(&2, X, xs2, c2)), s0) : S} &
  {List.take(&2, Y, Impl.conv_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H,
      Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh},
        w1, xs1, ys1, Accept.Verdict{c1, False{}}),
      w2, xs2, ys2, Accept.Verdict{c2, False{}})), K) ==
    Spec.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K),
      List.append(&2, Y, List.take(&2, Y, ys1, c1), List.take(&2, Y, ys2, c2))))
    : List<&2, Y>} &
  {Impl.position_of(~S, ~Y, Impl.round_after(~S, ~X, ~Y, ~step, K, H,
      Impl.round(~S, ~X, ~Y, ~step, K, H, Impl.Engine{s0, buf, position, lh},
        w1, xs1, ys1, Accept.Verdict{c1, False{}}),
      w2, xs2, ys2, Accept.Verdict{c2, False{}})) == Nat.add(position, Nat.add(c1, c2))
    : Nat}
