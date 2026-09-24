# Model of the GDN recurrent-state bookkeeping of one greedy speculative verify
# round in the patched ExLlamaV3 engine: a history-free verify (RULE_VERIFY) of
# window + 1 tokens, then the commit-time replay of the round's decision
# (RULE_COMMIT through batched_state_replay), the conv-window tail write and
# rewind, and the position / last_history bookkeeping. The per-token recurrent
# update is the template `step` (any function), its readout `out`, and the
# state, rule-input, conv-input and output types are opaque: every law about
# this model holds for every choice of them. Pinned sources (post-images of
# patches/exl3 + patches/exl3-ext, SHA-256 in exl3-patches.json /
# exl3-ext.json): generator/generator.py, generator/gdn_rewind.py,
# modules/gated_delta_net.py, cache/recurrent_util.py, exllamav3_ext/gdn.cu.
# This is a proof model (lists), not a shipped artifact; the finite link to the
# sources is bend/gdn_replay_diff.py against GDN_REPLAY_TABLE.bend.
import Base
import ./exl3_accept_spec.bend as Accept

# One slot of one GDN layer between rounds: recurrent_state[slot, 0] (row0),
# conv_state[slot, d, :] for one channel d (conv_kernel_size + max_history
# columns, gated_delta_net.py:190), GDNState.position and last_history.
type Engine<-S: Data, -Y: Data> is Data:
  Engine{row0: S, conv: List<&2, Y>, position: Nat, last_history: Nat}

# Committed: the rewind launched and returned. Refused: the host raised before
# any replay was launched (gdn_rewind.py:103-105 IndexError, replay_job's
# assert, batched_state_replay's TORCH_CHECK), so row 0 still holds the
# pre-verify state (a RULE_VERIFY launch writes no state row).
type Outcome<-S: Data, -Y: Data> is Data:
  Committed{engine: Engine<S, Y>}
  Refused{row0: S}

# gated_delta_rule_128_reg<RULE_VERIFY> (gdn.cu, patch 0003): the state is
# loaded from row 0, every one of the seqlen tokens updates it and emits its
# attention output from the updated state; no state row is written.
def verify(~S: Data, ~X: Data, ~O: Data, ~step: S -> X -> S,
    ~out: S -> X -> O, xs: List<&2, X>, s: S) -> List<&2, O>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      +t = step(s, x)
      out(t, x) <> verify(~S, ~X, ~O, ~step, ~out, rest, t)

# gated_delta_rule_128_reg<RULE_COMMIT> via batched_state_replay_kernel
# (gdn.cu:2923-2948): `for (s = 0; s < steps; ++s)` over token s of the job's
# batch row (base row * seqlen, one token per iteration), from row 0, final
# state back into row 0. steps <= seqlen is checked on the host first.
def replay(~S: Data, ~X: Data, ~step: S -> X -> S, steps: Nat,
    xs: List<&2, X>, s: S) -> S:
  match steps:
    case 0n:
      s
    case 1n+more:
      match xs:
        case Nil{}:
          s
        case x <> rest:
          replay(~S, ~X, ~step, more, rest, step(s, x))

# History-mode conv window write-back (gdn.cu:1912-1924, fused copy
# gdn.cu:2465-2475): the input sequence is conv_state[0:K] ++ x (seqlen
# inputs); its last write_size = min(state_size, K + seqlen) entries go to the
# tail of the state_size-column buffer, the other columns keep their contents.
def conv_write(~Y: Data, +K: Nat, +W: Nat, +buf: List<&2, Y>,
    +ys: List<&2, Y>) -> List<&2, Y>:
  +seq = List.append(&2, Y, List.take(&2, Y, buf, K), ys)
  +total = Nat.add(K, List.length(&2, Y, ys))
  +write = Nat.min(W, total)
  +dst = Nat.sub(W, write)
  +src = Nat.sub(total, write)
  List.append(&2, Y, List.take(&2, Y, buf, dst),
    List.append(&2, Y, List.take(&2, Y, List.drop(&2, Y, seq, src), write),
      List.drop(&2, Y, buf, Nat.add(dst, write))))

# GDNLayerState.rewind_conv_job (gated_delta_net.py:327-340) executed by
# batched_conv_rewind_kernel (gdn.cu:2836-2845): p = state_size - num_tokens,
# columns [p - cdim, p) are read into registers, then written to [0, cdim).
def conv_rewind(~Y: Data, +K: Nat, +W: Nat, n: Nat, +buf: List<&2, Y>)
  -> List<&2, Y>:
  List.append(&2, Y,
    List.take(&2, Y, List.drop(&2, Y, buf, Nat.sub(Nat.sub(W, n), K)), K),
    List.drop(&2, Y, buf, K))

# rewind_conv_job returns None when last_history == 0 (gated_delta_net.py:327).
def conv_job(~Y: Data, idle: Bool, +K: Nat, +W: Nat, n: Nat,
    +buf: List<&2, Y>) -> List<&2, Y>:
  match idle:
    case True{}:
      buf
    case False{}:
      conv_rewind(~Y, K, W, n, buf)

# generator.py:1295:
#   num_rejected = window + 1 - count if not eos and count <= window else 0
def rejected_if(le: Bool, +window: Nat, +count: Nat) -> Nat:
  match le:
    case True{}:
      Nat.sub(1n+window, count)
    case False{}:
      0n

def num_rejected(+window: Nat, +count: Nat, eos: Bool) -> Nat:
  match eos:
    case True{}:
      0n
    case False{}:
      rejected_if(Nat.is_le(count, window), window, count)

# The replay job's host checks: 1 <= steps <= seqlen (gated_delta_net.py
# replay_job assert, gdn.cu:2967 TORCH_CHECK).
def replay_checked(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S,
    ok: Bool, +steps: Nat, xs: List<&2, X>, +row0: S, conv: List<&2, Y>,
    position: Nat) -> Outcome<S, Y>:
  match ok:
    case True{}:
      Committed{Engine{replay(~S, ~X, ~step, steps, xs, row0), conv, position,
        0n}}
    case False{}:
      Refused{row0}

# RewindPlans.rewind (gdn_rewind.py:95-112): launches has window + 1 entries
# (num_tokens in range(window + 1), gdn_rewind.py:80); entry num_tokens holds
# the conv job and the replay job of steps = window + 1 - num_tokens
# (gdn_rewind.py:80-90); then position -= num_tokens, last_history = 0
# (gdn_rewind.py:110-111).
def launch(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, in_range: Bool,
    +K: Nat, +W: Nat, +window: Nat, +num: Nat, +xs: List<&2, X>, +row0: S,
    +buf: List<&2, Y>, +position: Nat) -> Outcome<S, Y>:
  match in_range:
    case True{}:
      +steps = Nat.sub(1n+window, num)
      replay_checked(~S, ~X, ~Y, ~step,
        Bool.and(Nat.is_le(1n, steps),
          Nat.is_le(steps, List.length(&2, X, xs))),
        steps, xs, row0,
        conv_job(~Y, Nat.is_eq(window, 0n), K, W, num, buf),
        Nat.sub(position, num))
    case False{}:
      Refused{row0}

# One round on one slot and layer: the verify forward of window + 1 tokens
# (rule inputs xs, conv inputs ys) with history, which advances position by
# seqlen and sets last_history = seqlen - 1 = window (recurrent_util.py:73-74),
# writes the conv tail and leaves row 0 untouched; then the decision
# (count, eos) of the greedy acceptance leaf selects the rewind. K is
# conv_kernel_size, H is max_history (state_size = K + H).
def round(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    e: Engine<S, Y>, +window: Nat, +xs: List<&2, X>, +ys: List<&2, Y>,
    v: Accept.Verdict) -> Outcome<S, Y>:
  match e:
    case Engine{row0, conv, position, last_history}:
      match v:
        case Accept.Verdict{+count, eos}:
          +W = Nat.add(K, H)
          +num = num_rejected(window, count, eos)
          launch(~S, ~X, ~Y, ~step, Nat.is_le(num, window), K, W, window, num,
            xs, row0, conv_write(~Y, K, W, conv, ys),
            Nat.add(position, 1n+window))

# A second round runs on the engine the first one committed.
def round_after(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat,
    +H: Nat, o: Outcome<S, Y>, +window: Nat, +xs: List<&2, X>,
    +ys: List<&2, Y>, v: Accept.Verdict) -> Outcome<S, Y>:
  match o:
    case Committed{e}:
      round(~S, ~X, ~Y, ~step, K, H, e, window, xs, ys, v)
    case Refused{r}:
      Refused{r}

def row0_of(~S: Data, ~Y: Data, o: Outcome<S, Y>) -> S:
  match o:
    case Committed{Engine{r, c, p, l}}:
      r
    case Refused{r}:
      r

def conv_of(~S: Data, ~Y: Data, o: Outcome<S, Y>) -> List<&2, Y>:
  match o:
    case Committed{Engine{r, c, p, l}}:
      c
    case Refused{r}:
      Nil{}

def position_of(~S: Data, ~Y: Data, o: Outcome<S, Y>) -> Nat:
  match o:
    case Committed{Engine{r, c, p, l}}:
      p
    case Refused{r}:
      0n

def last_history_of(~S: Data, ~Y: Data, o: Outcome<S, Y>) -> Nat:
  match o:
    case Committed{Engine{r, c, p, l}}:
      l
    case Refused{r}:
      0n

def committed(~S: Data, ~Y: Data, o: Outcome<S, Y>) -> Bool:
  match o:
    case Committed{e}:
      True{}
    case Refused{r}:
      False{}
