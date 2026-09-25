# Independent reference vocabulary for ext 8204's deferred phase-1 publish (bend/mlp_m16_defer.bend):
# the program-order events of one 8201 block's phase 1 and beyond (main-loop tiles and flushes, and
# ext 8201's counter signals / waits), and scans over those lists. The scans do not use the table
# formulas that the laws compare them with.
import Base
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched_spec.bend as MSpec

# One event of a block, in program order: Work{ev} is a phase-1 main-loop event (Tile / Flush of the
# gate+up split-K loop); Sync{ev} is one of ext 8201's counter signals / waits.
type Ev is Data:
  Work{ev: PSpec.Ev}
  Sync{ev: MSpec.Ev}

# The phase-1 main-loop events of an event list, in order.
def works(evs: List<&2, Ev>) -> List<&2, PSpec.Ev>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Work{e}:
          e <> works(rest)
        case Sync{e}:
          works(rest)

# The counter events of an event list, in order.
def syncs(evs: List<&2, Ev>) -> List<&2, MSpec.Ev>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Work{e}:
          syncs(rest)
        case Sync{e}:
          e <> syncs(rest)

# `seen` extended by the group of a main-loop event if it is a flush.
def note(ev: PSpec.Ev, +seen: List<&2, Nat>) -> List<&2, Nat>:
  match ev:
    case PSpec.Tile{g, it}:
      seen
    case PSpec.Flush{g}:
      g <> seen

# A counter event is allowed after the flushed groups `seen`: a signal on a phase-1 counter C1{g}
# needs group g flushed before it (its slot data written before the release); every other signal
# and every wait is unconstrained here.
def sync_ok(ev: MSpec.Ev, +seen: List<&2, Nat>) -> Bool:
  match ev:
    case MSpec.Sig{c, a, l}:
      match c:
        case MSpec.C1{g}:
          MSpec.member(seen, g)
        case MSpec.C2{p}:
          True{}
    case MSpec.Wait{c, m, l}:
      True{}

# Every phase-1 counter signal of the list comes after the flush of its group (the groups flushed
# before the list starts are `seen`).
def pub_after_flush(evs: List<&2, Ev>, +seen: List<&2, Nat>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case Work{e}:
          pub_after_flush(rest, note(e, seen))
        case Sync{e}:
          Bool.and(sync_ok(e, seen), pub_after_flush(rest, seen))
