# Independent reference vocabulary for the ext 8202 layer-tail schedule (bend/tail_m16_sched.bend):
# the program-order events of one block (grid barriers, phase-0 main-loop tiles and flushes, F0 and
# N jobs, ext 8201's counter events) and projections / counts that scan those event lists. The
# projections do not use the table formulas (start, owner, x mod G, ...) that the laws compare them
# with.
import Base
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched_spec.bend as MSpec

# The grid barriers in kernel order: 0 = S (after the prologue and the o-input Hadamard), 1 = A
# (after phase 0), 2 = B (after the F0 jobs), 3 = C (after the N jobs; replaces 8201's start
# barrier), 4 = D (8201's barrier before the down finish).
def bar_seq() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n]

# One event of a block, in program order: Bar{id} is grid barrier id; Work{ev} is a phase-0 main-loop
# event (Tile / Flush of the o_proj split-K loop); Fin{x} runs F0 job x; Norm{x} runs norm job x;
# Sync{ev} is one of ext 8201's counter signals / waits.
type Ev is Data:
  Bar{id: Nat}
  Work{ev: PSpec.Ev}
  Fin{x: Nat}
  Norm{x: Nat}
  Sync{ev: MSpec.Ev}

# The barrier ids of an event list, in order.
def bars(evs: List<&2, Ev>) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Bar{id}:
          id <> bars(rest)
        case Work{e}:
          bars(rest)
        case Fin{x}:
          bars(rest)
        case Norm{x}:
          bars(rest)
        case Sync{e}:
          bars(rest)

# The phase-0 main-loop events of an event list, in order.
def works(evs: List<&2, Ev>) -> List<&2, PSpec.Ev>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Bar{id}:
          works(rest)
        case Work{e}:
          e <> works(rest)
        case Fin{x}:
          works(rest)
        case Norm{x}:
          works(rest)
        case Sync{e}:
          works(rest)

# The counter events of an event list, in order.
def syncs(evs: List<&2, Ev>) -> List<&2, MSpec.Ev>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Bar{id}:
          syncs(rest)
        case Work{e}:
          syncs(rest)
        case Fin{x}:
          syncs(rest)
        case Norm{x}:
          syncs(rest)
        case Sync{e}:
          e <> syncs(rest)

# Number of runs of F0 job x in an event list.
def fin_hits(evs: List<&2, Ev>, +x: Nat) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case Bar{id}:
          fin_hits(rest, x)
        case Work{e}:
          fin_hits(rest, x)
        case Fin{y}:
          Nat.add(PSpec.bit(Nat.is_eq(y, x)), fin_hits(rest, x))
        case Norm{y}:
          fin_hits(rest, x)
        case Sync{e}:
          fin_hits(rest, x)

# Number of runs of norm job x in an event list.
def norm_hits(evs: List<&2, Ev>, +x: Nat) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case Bar{id}:
          norm_hits(rest, x)
        case Work{e}:
          norm_hits(rest, x)
        case Fin{y}:
          norm_hits(rest, x)
        case Norm{y}:
          Nat.add(PSpec.bit(Nat.is_eq(y, x)), norm_hits(rest, x))
        case Sync{e}:
          norm_hits(rest, x)

# Every non-barrier event sits in its region, k being the number of barriers passed so far:
# phase-0 work after 1 barrier (between S and A), F0 jobs after 2 (between A and B), N jobs after 3
# (between B and C), counter events after 4 (between C and D).
def staged(evs: List<&2, Ev>, +k: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case Bar{id}:
          staged(rest, 1n+k)
        case Work{e}:
          Bool.and(Nat.is_eq(k, 1n), staged(rest, k))
        case Fin{x}:
          Bool.and(Nat.is_eq(k, 2n), staged(rest, k))
        case Norm{x}:
          Bool.and(Nat.is_eq(k, 3n), staged(rest, k))
        case Sync{e}:
          Bool.and(Nat.is_eq(k, 4n), staged(rest, k))

# Token row of an F0 job (group, row, chunk).
def job_row(j: PSpec.Job) -> Nat:
  match j:
    case PSpec.Job{g, r, ch}:
      r
