# Model of the device-resident round advance for the EXL3 + DFlash2 greedy
# speculative loop (DevicePipe's advance kernel plus the count-reading
# consumers; DESIGN.md sections 3 and 4). One sequence, one verify round:
# the accept leaf (exl3_accept.bend) writes the decision (count, eos) and
# this module is what the device does with it. Nat arithmetic models the
# kernel's int64 expressions; the int64 correspondence is checked by the
# finite differential, not proven. Independent reference:
# exl3_round_spec.bend.
import Base
import ./exl3_accept_spec.bend as Accept

# Per-job device state S. anchor is the index of the anchor token in the
# round's verify ids; checkpoint is the next round's accept input (0 = no
# boundary within the window); stopped freezes S after eos or an error.
type State is Data:
  State{position: Nat, budget: Nat, anchor: Nat, checkpoint: Nat,
    stopped: Bool}

def position(st: State) -> Nat:
  match st:
    case State{position, budget, anchor, checkpoint, stopped}:
      position

def budget(st: State) -> Nat:
  match st:
    case State{position, budget, anchor, checkpoint, stopped}:
      budget

def anchor(st: State) -> Nat:
  match st:
    case State{position, budget, anchor, checkpoint, stopped}:
      anchor

def checkpoint_of(st: State) -> Nat:
  match st:
    case State{position, budget, anchor, checkpoint, stopped}:
      checkpoint

def stopped(st: State) -> Bool:
  match st:
    case State{position, budget, anchor, checkpoint, stopped}:
      stopped

def fit(fits: Bool, c: Nat) -> Nat:
  match fits:
    case True{}:
      c
    case False{}:
      0n

# Advance kernel lines 122-123 (decode-branch _greedy_checkpoint,
# generator.py:1003-1004): c = interval - (kv - base) % interval (0 when
# interval = 0: Nat.sub saturates), checkpoint = (0 < c && c <= window) ? c : 0.
def checkpoint(+position: Nat, +base: Nat, +interval: Nat, +window: Nat)
  -> Nat:
  +c = Nat.sub(interval, Nat.mod(Nat.sub(position, base), interval))
  fit(Bool.and(Nat.is_lt(0n, c), Nat.is_le(c, window)), c)

# device_commit_steps (gdn.cu:2824-2832) and the advance kernel's guard
# (device_round.cu:110): a decision is usable iff r >= 2 and
# 1 <= count <= window + 1 (r = 2 * count + eos, so r >= 2 iff count >= 1).
def writes(+count: Nat, +window: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, count), Nat.is_le(count, 1n+window))

def commit(ok: Bool, +count: Nat, eos: Bool, +window: Nat, +base: Nat,
    +interval: Nat, position: Nat, budget: Nat, anchor: Nat, ckpt: Nat)
  -> State:
  match ok:
    case False{}:
      State{position, budget, anchor, ckpt, True{}}
    case True{}:
      +kv = Nat.add(position, count)
      State{kv, Nat.sub(budget, count), Nat.sub(count, 1n),
        checkpoint(kv, base, interval, window), eos}

# Advance kernel (device_round.cu:96-125): a stopped state is left as is; an
# unusable decision freezes S and sets stopped; otherwise kv += n,
# budget -= n, anchor = verify_ids[n - 1] (here its index), stopped = eos,
# and the next checkpoint is taken at the new kv (seqlens = kv).
def advance(+count: Nat, eos: Bool, +window: Nat, +base: Nat, +interval: Nat,
    st: State) -> State:
  match st:
    case State{position, budget, anchor, ckpt, stopped}:
      match stopped:
        case True{}:
          State{position, budget, anchor, ckpt, True{}}
        case False{}:
          commit(writes(count, window), count, eos, window, base, interval,
            position, budget, anchor, ckpt)

def full(cut: Bool, +count: Nat, +window: Nat) -> Nat:
  match cut:
    case True{}:
      1n+window
    case False{}:
      count

# GDN state replay (gdn.cu:2830): steps = (!eos && count <= window) ? count :
# window + 1, used only when writes holds.
def steps(+count: Nat, eos: Bool, +window: Nat) -> Nat:
  full(Bool.or(eos, Nat.is_gt(count, window)), count, window)

# GDN conv rewind src offset (gdn.cu:2852): num_tokens = window + 1 - steps,
# used only when writes holds.
def offset(+count: Nat, eos: Bool, +window: Nat) -> Nat:
  Nat.sub(1n+window, steps(count, eos, window))

# Draft KV refresh: window + 1 static rows written at the pre-round kv; the
# draft cache's committed length afterwards is kv + count.
def refresh_rows(window: Nat) -> Nat:
  1n+window

def refresh(position: Nat, count: Nat) -> Nat:
  Nat.add(position, count)

# The pipeline's round loop over decisions, in commit order.
def rounds(verdicts: List<&2, Accept.Verdict>, +window: Nat, +base: Nat,
    +interval: Nat, st: State) -> State:
  match verdicts:
    case Nil{}:
      st
    case Accept.Verdict{count, eos} <> rest:
      rounds(rest, window, base, interval,
        advance(count, eos, window, base, interval, st))
