# The input loader of ext 5108 (exllamav3_ext/gdn.cu, batched_state_replay_kernel<GATHER = true>), transcribed
# from the kernel's index expressions over Nat, next to the pre-5108 loader it replaces (gdn_rule_load_inputs<128>,
# still the GATHER = false instance). C int arithmetic on the non-negative values here is Nat arithmetic (t < 128,
# i < REPLAY_GI = 3, S <= GR_MAX_S = 16, e < 384, channels < F <= 2^20: no overflow).
#   - thread t, slot i: `e = threadIdx.x + i * 128`, active `if (e < S * REPLAY_PARTS)`, REPLAY_PARTS = 20,
#     REPLAY_GI = (GR_MAX_S * REPLAY_PARTS + 127) / 128
#   - `s = e / REPLAY_PARTS; p = e - s * REPLAY_PARTS`
#   - load: `ch = p < 16 ? k_ch + p * 8 : v_ch + (p - 16) * 8`, `r[i] = *(const uint4*) (src + s * F + ch)`,
#     k_ch = (Nk + kh) * HD, v_ch = 2 * Nk * HD + h * HD + blockIdx.x * 32 (src = conv_out row base)
#   - store: `dst = p < 16 ? m.k + s * HD + p * 8 : m.v + s * HD + blockIdx.x * 32 + (p - 16) * 8`, then
#     dst[0..7] = the 8 bf16 of r[i] widened: element 2m = `w[m] << 16`, element 2m + 1 = `w[m] & 0xffff0000u`
#   - old loader (gdn_rule_load_inputs): smem cell (part, s, c) of array q / k / v (part 0 / 1 / 2) holds
#     __bfloat162float(conv_out[s * F + ch]), ch = kh * HD + c / (Nk + kh) * HD + c / 2 * Nk * HD + h * HD + c
# A shared-memory cell is Loc{part, s, col} (array part, token s, column col of 128); a 16-byte chunk is named by
# the Loc of its first element. The bf16 widening is modelled on 32-bit words as their two 16-bit halves (lo = the
# lower address, little-endian), which is exact for `<< 16`, `& 0xffff0000u` and __uint_as_float.
# Reference: gdn_replay_gather_spec.bend; laws: gdn_replay_gather_laws.bend. Proof model only (not shipped).
import Base

type Loc is Data:
  Loc{part: Nat, s: Nat, col: Nat}

# A 32-bit word as its 16-bit halves (lo at the lower address).
type W is Data:
  W{lo: Nat, hi: Nat}

def parts() -> Nat:
  20n

def gr_max_s() -> Nat:
  16n

# REPLAY_GI
def gi() -> Nat:
  Nat.div(Nat.add(Nat.mul(gr_max_s(), parts()), 127n), 128n)

def elem(+t: Nat, +i: Nat) -> Nat:
  Nat.add(t, Nat.mul(i, 128n))

def active(+S: Nat, +e: Nat) -> Bool:
  Nat.is_lt(e, Nat.mul(S, parts()))

def e_s(+e: Nat) -> Nat:
  Nat.div(e, parts())

def e_p(+e: Nat) -> Nat:
  Nat.sub(e, Nat.mul(e_s(e), parts()))

def is_k(+e: Nat) -> Bool:
  Nat.is_lt(e_p(e), 16n)

# the chunk element e stores to (block v chunk c = blockIdx.x): first cell of the 8
def dst_by(k: Bool, +c: Nat, +s: Nat, +p: Nat) -> Loc:
  match k:
    case True{}:
      Loc{1n, s, Nat.mul(p, 8n)}
    case False{}:
      Loc{2n, s, Nat.add(Nat.mul(c, 32n), Nat.mul(Nat.sub(p, 16n), 8n))}

def dst(+c: Nat, +e: Nat) -> Loc:
  dst_by(is_k(e), c, e_s(e), e_p(e))

# element offset (bf16 units from the row base) of element q of the chunk the kernel loads
def src_by(k: Bool, +F: Nat, +Nk: Nat, +kh: Nat, +h: Nat, +c: Nat, +s: Nat, +p: Nat, +q: Nat) -> Nat:
  match k:
    case True{}:
      Nat.add(Nat.add(Nat.mul(s, F), Nat.add(Nat.mul(Nat.add(Nk, kh), 128n), Nat.mul(p, 8n))), q)
    case False{}:
      Nat.add(Nat.add(Nat.mul(s, F),
        Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(2n, Nk), 128n), Nat.mul(h, 128n)), Nat.mul(c, 32n)),
          Nat.mul(Nat.sub(p, 16n), 8n))), q)

def src(+F: Nat, +Nk: Nat, +kh: Nat, +h: Nat, +c: Nat, +e: Nat, +q: Nat) -> Nat:
  src_by(is_k(e), F, Nk, kh, h, c, e_s(e), e_p(e), q)

# column of element q of a chunk
def at(l: Loc, +q: Nat) -> Loc:
  match l:
    case Loc{+part, +s, +col}:
      Loc{part, s, Nat.add(col, q)}

# the old loader's source offset for smem cell l (gdn_rule_load_inputs)
def old_src(+F: Nat, +Nk: Nat, +kh: Nat, +h: Nat, l: Loc) -> Nat:
  match l:
    case Loc{+part, +s, +col}:
      match part:
        case 0n:
          Nat.add(Nat.mul(s, F), Nat.add(Nat.mul(kh, 128n), col))
        case 1n+z:
          match z:
            case 0n:
              Nat.add(Nat.mul(s, F), Nat.add(Nat.mul(Nat.add(Nk, kh), 128n), col))
            case 1n+w:
              Nat.add(Nat.mul(s, F), Nat.add(Nat.add(Nat.mul(Nat.mul(2n, Nk), 128n), Nat.mul(h, 128n)), col))

# ---- widening. The uint4's word m holds elements 2m (lo) and 2m + 1 (hi).
def shl16(w: W) -> W:
  match w:
    case W{+lo, +hi}:
      W{0n, lo}

def and_hi(w: W) -> W:
  match w:
    case W{+lo, +hi}:
      W{0n, hi}

# new element 2m + j of word w (j = 0: `w << 16`, j = 1: `w & 0xffff0000u`), as the fp32 bit pattern
def widen_new(w: W, +j: Nat) -> W:
  match j:
    case 0n:
      shl16(w)
    case 1n+z:
      and_hi(w)

# ---- EXL3_GDN_REPLAY_GATHER: Unset or Str(chars). Ok = the value used, Refused = the TORCH_CHECK fails
type Env is Data:
  Unset{}
  Str{cs: List<&2, Nat>}

type Knob is Data:
  Ok{v: Nat}
  Refused{}

def pick_knob(b: Bool, +v: Nat) -> Knob:
  match b:
    case True{}:
      Ok{v}
    case False{}:
      Refused{}

def knob_char(+c: Nat, rest: List<&2, Nat>) -> Knob:
  match rest:
    case Nil{}:
      pick_knob(Bool.or(Nat.is_eq(c, 48n), Nat.is_eq(c, 49n)), Nat.sub(c, 48n))
    case x <> more:
      Refused{}

def knob(env: Env) -> Knob:
  match env:
    case Unset{}:
      Ok{1n}
    case Str{xs}:
      match xs:
        case Nil{}:
          Refused{}
        case c <> rest:
          knob_char(c, rest)
