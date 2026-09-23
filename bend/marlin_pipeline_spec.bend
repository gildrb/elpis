# Independent policy and proof-only mathematical copy-ring/unroll model.
# Never import this module from marlin_pipeline.bend or the RUNTIME graph.
import Base
import ./spec.bend as Sequence

# Declarative accepted combination, independent of the nested production guards.
def policy(eligible: Bool, safe: Bool, deterministic: Bool) -> Nat:
  match eligible safe deterministic:
    case True{} True{} True{}:
      1n
    case _ _ _:
      0n

def bit(index: Nat) -> Bool:
  Nat.is_ne(Nat.mod(index, 2n), 0n)

def row(+index: Nat) -> Nat:
  policy(bit(index), bit(Nat.div(index, 2n)), bit(Nat.div(index, 4n)))

def Action(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Unit
        case 1n+q:
          Empty

# A mathematical physical slot and its grouped-scale phase. Period two is
# group_blocks/thread_k_blocks = 8/4, not the number of reduction CTAs.
def slot(tile: Nat, stages: Nat) -> Nat:
  Nat.mod(tile, stages)

def phase(tile: Nat) -> Nat:
  Nat.mod(tile, 2n)

# Separate unrolled schedules, including every partial final iteration. They
# model only logical tile visitation, not copies, waits, pointers or barriers.
# A chunk starts at the current logical tile; no padding tile executes an MMA.
# This is an actual eight-tile unroll with seven distinct nonempty short tails.
def tiles8(count: Nat, +start: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      match p:
        case 0n:
          [start]
        case 1n+q:
          match q:
            case 0n:
              Sequence.seq(2n, start)
            case 1n+r:
              match r:
                case 0n:
                  Sequence.seq(3n, start)
                case 1n+s:
                  match s:
                    case 0n:
                      Sequence.seq(4n, start)
                    case 1n+t:
                      match t:
                        case 0n:
                          Sequence.seq(5n, start)
                        case 1n+u:
                          match u:
                            case 0n:
                              Sequence.seq(6n, start)
                            case 1n+v:
                              match v:
                                case 0n:
                                  Sequence.seq(7n, start)
                                case 1n+rest:
                                  List.append(&2, Nat, Sequence.seq(8n, start), tiles8(rest, 8n+start))

def tiles4(count: Nat, +start: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      match p:
        case 0n:
          [start]
        case 1n+q:
          match q:
            case 0n:
              Sequence.seq(2n, start)
            case 1n+r:
              match r:
                case 0n:
                  Sequence.seq(3n, start)
                case 1n+rest:
                  List.append(&2, Nat, Sequence.seq(4n, start), tiles4(rest, 4n+start))

# Each selected K64 tile has b_sh_wr_iters=2. The ordered identifiers below
# mean the matmul(0), matmul(1) call sites at tile t, flattened as 2*t+j.
# They are NOT scalar products to sum or a license to reassociate F32.
def mma_terms(tiles: List<&2, Nat>) -> List<&2, Nat>:
  match tiles:
    case Nil{}:
      Nil{}
    case +tile <> rest:
      +base = Nat.add(tile, tile)
      base <> (1n+base) <> mma_terms(rest)

# Syntactic recurrence retains the previous accumulator as an operand of EACH
# ordered MMA. It assumes no algebraic properties and performs no arithmetic.
type Accumulator is Data:
  Initial{identity: Nat}
  MMA{previous: Accumulator, term: Nat}

def recurrence(terms: List<&2, Nat>, accumulator: Accumulator) -> Accumulator:
  match terms:
    case Nil{}:
      accumulator
    case term <> rest:
      recurrence(rest, MMA{accumulator, term})

# Source-layout arithmetic, not a memory-safety or launch-reservation theorem.
# Exact selected marlin_template.h:343,459-497,638-649 uses int4 units:
# B=(64*128)/32=256; scales=128/8=16; A=(rows*64)/8; reduction=(2*8+1)*16=272.
# B and reduction alias, hence max rather than addition. No g_idx or ZP region.
# rows=8 is the selected M8 kernel; rows=16 conservatively pads the A region.
# At stages=8 these are 43008 and 51200 bytes respectively. The padded bound
# exceeds the actual bound by 8192 bytes; it does NOT lower the native reserve.
def shared_bytes(+stages: Nat, rows: Nat) -> Nat:
  b_stage = Nat.div(Nat.mul(64n, 128n), 32n)
  reduction = Nat.mul(1n+Nat.mul(2n, 8n), 16n)
  s_stage = Nat.div(128n, 8n)
  a_stage = Nat.div(Nat.mul(rows, 64n), 8n)
  Nat.mul(16n, Nat.add(Nat.max(reduction, Nat.mul(stages, b_stage)),
    Nat.mul(stages, Nat.add(s_stage, a_stage))))

# Arithmetic parameters from start_pipes and wait_for_stage, not an operational
# CUDA model. Each fetch_to_shared commits once even with pred=False. Under the
# native per-thread wait semantics, priming S-1 groups and thereafter committing
# once after each wait(S-2) bounds pending committed groups by S-1 (7 at S=8),
# below the eight-group hardware limit. Hardware semantics, instruction lowering,
# barriers and memory/reuse ordering remain external correspondence obligations.
def prime_groups(stages: Nat) -> Nat:
  Nat.sub(stages, 1n)

def wait_groups(stages: Nat) -> Nat:
  Nat.sub(stages, 2n)

# Independent full wire literal: existing controls, new section, row order and
# no trailing newline (IO.print supplies it). No production serializer is used.
def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V2\nFREE_MIRROR\n8\n0\n0\n0\n0\n1\n0\n1\n1\nSTATUS\n8\n0\n2\n0\n1\n0\n2\n0\n1\nMARLIN_EIGHT_STAGE\n8\n0\n0\n0\n0\n0\n0\n0\n1\nEND_QWEN_RUNTIME_CONTROL"
