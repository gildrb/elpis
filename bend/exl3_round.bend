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

# Decode-branch _greedy_checkpoint (generator.py:1003-1004): off = (kv -
# base) % interval, c = interval - off, checkpoint = c <= window ? c : 0.
def checkpoint(+position: Nat, +base: Nat, +interval: Nat, +window: Nat)
  -> Nat:
  +c = Nat.sub(interval, Nat.mod(Nat.sub(position, base), interval))
  fit(Nat.is_le(c, window), c)

def commit(+count: Nat, eos: Bool, +window: Nat, +base: Nat, +interval: Nat,
    position: Nat, budget: Nat, anchor: Nat, ckpt: Nat) -> State:
  match count:
    case 0n:
      State{position, budget, anchor, ckpt, True{}}
    case 1n+index:
      +kv = Nat.add(position, 1n+index)
      State{kv, Nat.sub(budget, 1n+index), index,
        checkpoint(kv, base, interval, window), eos}

# Advance kernel: ok = count >= 1 (decision r >= 2). A stopped state or an
# error freezes S and sets stopped; otherwise kv += n, budget -= n,
# anchor = n - 1, stopped = eos and the next checkpoint is taken at kv.
def advance(+count: Nat, eos: Bool, +window: Nat, +base: Nat, +interval: Nat,
    st: State) -> State:
  match st:
    case State{position, budget, anchor, ckpt, stopped}:
      match stopped:
        case True{}:
          State{position, budget, anchor, ckpt, True{}}
        case False{}:
          commit(count, eos, window, base, interval, position, budget, anchor,
            ckpt)

# Consumers of a decision; each writes only when count >= 1.
def writes(count: Nat) -> Bool:
  Nat.is_lt(0n, count)

def full(cut: Bool, +count: Nat, +window: Nat) -> Nat:
  match cut:
    case True{}:
      1n+window
    case False{}:
      count

# GDN state replay: steps = (!eos && count <= window) ? count : window + 1.
def steps(+count: Nat, eos: Bool, +window: Nat) -> Nat:
  full(Bool.or(eos, Nat.is_gt(count, window)), count, window)

def keep(cut: Bool, +count: Nat, +window: Nat) -> Nat:
  match cut:
    case True{}:
      0n
    case False{}:
      Nat.sub(1n+window, count)

# GDN conv rewind src offset: num_tokens = (eos || count > window) ? 0 :
# window + 1 - count.
def offset(+count: Nat, eos: Bool, +window: Nat) -> Nat:
  keep(Bool.or(eos, Nat.is_gt(count, window)), count, window)

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
