# The split-K slot discard of ext 2113 (exllamav3_ext/quant/exl3_gemm_m16_kernel.cuh exl3_m16_discard_slots, called by
# the finishes of exl3_gemm_m16g_kernel, exl3_mlp_m16_kernel and exl3_tail_m16_kernel; the EXL3_SPLITK_DISCARD switch
# in exl3_gemm_m16.cu), transcribed from the kernel's integer expressions over Nat. Offsets count floats from the
# 128-byte-aligned workspace base (cudaMalloc, at least 256-byte aligned: the host TORCH_CHECKs 128). C int / size_t
# arithmetic on the non-negative values here is Nat arithmetic (every offset is below the 32 MB workspace); `i >> 2` is
# `i / 4` and `i & 3` is `i % 4` on non-negative ints.
#   - finish job (group g, row r, 128-column chunk ch), all six finishes:
#     s0 = ws + g * mc * EXL3_M16_SLOT_FLOATS + r * GW + ch * 128 (mc = max_contrib / mc0 / mc1 / mc2)
#   - its loads: float4 lane of s0 + c * EXL3_M16_SLOT_FLOATS for c < nc (slot 0 as s0 itself), then the output
#     Hadamard's float4 lane of s0 (had_ff_r_128_inner / had_fh_r_128_inner: ((float4*) input_ptr)[t])
#   - exl3_m16_discard_slots(s0, nc, lane): __syncwarp(); for (int i = lane; i < 4 * nc; i += 32)
#     discard.global.L2 [s0 + (i >> 2) * EXL3_M16_SLOT_FLOATS + (i & 3) * 32], 128
#   - contributor store: slot = ws + (g * mc + cidx) * SLOT + warp * 64 + (lane >> 2) (m16g; the MLP / tail form
#     ws + g * mc * SLOT + cidx * SLOT is slot_base_mlp), then slot + row * GW + t * 16 + (c >> 1) * 8 with
#     row = mt * 8 + 2 * (lane & 3) + (c & 1): the column terms warp * 64 + t * 16 + (c >> 1) * 8 + (lane >> 2) are
#     gemm_m16_partition.bend's col(w, t, h, q) and the row its row(mt, a, c1) (same K:259 / K:267-268 lines)
# Reference: m16_discard_spec.bend; laws: m16_discard_laws.bend. Proof model only (not shipped).
import Base
import ./gemm_m16_partition.bend as Part

# EXL3_M16_GW = EXL3_M16_WARPS * EXL3_M16_TILES_W * 16 = 8 * 4 * 16
def gw() -> Nat:
  Nat.mul(Nat.mul(8n, 4n), 16n)

# EXL3_M16_SLOT_FLOATS = 16 * EXL3_M16_GW
def slot() -> Nat:
  Nat.mul(16n, gw())

# s0 - ws: g * mc * SLOT + r * GW + ch * 128
def chunk(+g: Nat, +mc: Nat, +r: Nat, +ch: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.mul(g, mc), slot()), Nat.mul(r, gw())), Nat.mul(ch, 128n))

# the i of lane `lane` in iteration k of `for (int i = lane; i < 4 * nc; i += 32)`
def disc_i(+lane: Nat, +k: Nat) -> Nat:
  Nat.add(lane, Nat.mul(32n, k))

# the loop condition i < 4 * nc
def disc_active(+nc: Nat, +i: Nat) -> Bool:
  Nat.is_lt(i, Nat.mul(4n, nc))

# the discarded address - s0: (i >> 2) * SLOT + (i & 3) * 32
def disc_off(+i: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(i, 4n), slot()), Nat.mul(Nat.mod(i, 4n), 32n))

# element e < 4 of lane `lane`'s float4 load of slot c: (s0 + c * SLOT) + 4 lane + e (slot 0: the sum loop's first
# load and the output Hadamard's re-read of s0 are both read_off(0, lane, e))
def read_off(+c: Nat, +lane: Nat, +e: Nat) -> Nat:
  Nat.add(Nat.mul(c, slot()), Nat.add(Nat.mul(lane, 4n), e))

# contributor slot base, m16g form: (g * mc + cidx) * SLOT
def slot_base(+g: Nat, +mc: Nat, +cidx: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(g, mc), cidx), slot())

# contributor slot base, MLP / tail form: ws = p.ws + g * mc * SLOT; slot = ws + cidx * SLOT
def slot_base_mlp(+g: Nat, +mc: Nat, +cidx: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mul(g, mc), slot()), Nat.mul(cidx, slot()))

# the cell contributor cidx of group g stores from warp w, n-tile t, c >> 1 = h, lane >> 2 = q, token tile mt,
# lane & 3 = a, c & 1 = c1: slot base + row * GW + column
def write_addr(+g: Nat, +mc: Nat, +cidx: Nat, +w: Nat, +t: Nat, +h: Nat, +q: Nat, +mt: Nat, +a: Nat, +c1: Nat) -> Nat:
  Nat.add(Nat.add(slot_base(g, mc, cidx), Nat.mul(Part.row(mt, a, c1), gw())), Part.col(w, t, h, q))

# ---- one line's events over time. Time t = launch * 8 + step; the steps of one launch, in the order the kernels
# (and the stream) run them:
#   0 the contributors' __stcg slot stores (every cell of the line: laws cells_written / line_cells)
#   1 grid.sync (m16g, down finishes) or the cnt1 counter wait (pair finishes); F0 after exl3_mlp_grid_sync
#   2 the finish's slot loads
#   3 the finish's store of the sum to slot 0 (lines of slot 0 only)
#   4 __syncwarp
#   5 the output Hadamard's re-read of slot 0
#   6 exl3_m16_discard_slots' __syncwarp
#   7 discard.global.L2 (when the switch is on)
# The next launch on the stream starts after step 7 of this one.
def st_load() -> Nat:
  2n

def st_reload() -> Nat:
  5n

def st_bar() -> Nat:
  6n

def st_disc() -> Nat:
  7n

type Ev is Data:
  NoEv{}
  Wr{launch: Nat}
  Sum0{launch: Nat}
  Disc{launch: Nat}

def sum0_if(zero: Bool, +n: Nat) -> Ev:
  match zero:
    case True{}:
      Sum0{n}
    case False{}:
      NoEv{}

def disc_if(on: Bool, +n: Nat) -> Ev:
  match on:
    case True{}:
      Disc{n}
    case False{}:
      NoEv{}

def ev_step(+on: Bool, +zero: Bool, +n: Nat, st: Nat) -> Ev:
  match st:
    case 0n:
      Wr{n}
    case 1n+a:
      match a:
        case 0n:
          NoEv{}
        case 1n+b:
          match b:
            case 0n:
              NoEv{}
            case 1n+c:
              match c:
                case 0n:
                  sum0_if(zero, n)
                case 1n+d:
                  match d:
                    case 0n:
                      NoEv{}
                    case 1n+e:
                      match e:
                        case 0n:
                          NoEv{}
                        case 1n+f:
                          match f:
                            case 0n:
                              NoEv{}
                            case 1n+x:
                              disc_if(on, n)

# the event at time t
def ev_at(on: Bool, zero: Bool, +t: Nat) -> Ev:
  ev_step(on, zero, Nat.div(t, 8n), Nat.mod(t, 8n))

def keep(e: Ev, prev: Ev) -> Ev:
  match e:
    case NoEv{}:
      prev
    case Wr{n}:
      Wr{n}
    case Sum0{n}:
      Sum0{n}
    case Disc{n}:
      Disc{n}

# the last event strictly before time t (NoEv: the line's content before the first launch); what a load at time t
# observes: a Wr / Sum0 is a defined value, a Disc an undefined one
def last(+on: Bool, +zero: Bool, +t: Nat) -> Ev:
  match t:
    case 0n:
      NoEv{}
    case 1n+p:
      keep(ev_at(on, zero, p), last(on, zero, p))

# ---- EXL3_SPLITK_DISCARD. The host reads env[0] and env[1] of the C string (env[1] is the terminator of a
# one-character value): `if (!env || !env[0]) return 1;` then
# TORCH_CHECK((env[0] == '0' || env[0] == '1') && !env[1], ...) and `return env[0] - '0';`
type Env is Data:
  Unset{}
  Str{c0: Nat, c1: Nat}

type Knob is Data:
  Ok{v: Nat}
  Refused{}

def pick_knob(b: Bool, +v: Nat) -> Knob:
  match b:
    case True{}:
      Ok{v}
    case False{}:
      Refused{}

def knob_str(+c0: Nat, +c1: Nat) -> Knob:
  match c0:
    case 0n:
      Ok{1n}
    case 1n+p:
      pick_knob(Bool.and(Bool.or(Nat.is_eq(1n+p, 48n), Nat.is_eq(1n+p, 49n)), Nat.is_eq(c1, 0n)), Nat.sub(1n+p, 48n))

def knob(env: Env) -> Knob:
  match env:
    case Unset{}:
      Ok{1n}
    case Str{c0, c1}:
      knob_str(c0, c1)

# torch.ops.exl3_m16.discard(set): `if (set >= 0) mode = set > 0 ? 1 : 0; return mode;` (a query passes -1)
type SetArg is Data:
  Query{}
  Set{v: Nat}

def set_mode(+m: Nat, s: SetArg) -> Nat:
  match s:
    case Query{}:
      m
    case Set{v}:
      match v:
        case 0n:
          0n
        case 1n+p:
          1n

# the launchers pass args.discard = exl3_m16_discard(); the finishes discard `if (p.discard)`
def issues(+mode: Nat) -> Bool:
  Bool.not(Nat.is_eq(mode, 0n))
