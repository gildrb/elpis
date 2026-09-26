# Ext 2107 (patch 2107-m16-decode-diet-on2106.patch, sha256 0584196d...): EXL3_M16_DIET mode 2 of the
# three decode m16 kernels (layer tail, 8201 MLP, m16g), transcribed over the nibble words and shared
# addresses of m16_diet2_spec.bend:
# - dq8_m16_regs (exl3_m16_decode.cuh): three funnel shifts u = {a:b} >> 4, s = >> 20, t = >> 24, seven
#   byte permutes with zero fill (__byte_perm(x, 0, 0x4410 / 0x4421 / 0x4432)) and one mask t & 0xffff;
# - the hoisted per-lane word addresses dw0 = rs + ((lane + 31) & 31) * 4, dw1 = rs + lane * 4 (once per
#   kernel), read per iteration at dw + cur_off with the tile immediate t * 128 (m16_lds<t * 128>), all 8
#   words read before the decodes (pure shared reads between the loop's __syncwarp()s);
# - the pinned activation base dxs = xbuf_sa (an empty asm "+r" pin: same value);
# - the mode switch EXL3_M16_DIET = 0 / 1 / 2 (exl3_gemm_m16.cu exl3_m16_diet) and the launchers'
#   instance selection (exl3_gemm_m16g.cu, exl3_mlp_m16.cu, exl3_tail_m16.cu get_launch).
# prmt selectors are given as their four selector nibbles, least significant first (0x4421 = 1, 2, 4, 4);
# every selector used is < 8, so prmt's sign-replicate mode never applies (bend/m16_diet2_diff.py checks).
import Base
import ./m16_diet2_spec.bend as Spec

# ---- extraction ----

# prmt.b32 byte k of {y:x} (x = bytes 0-3, y = bytes 4-7), k < 8.
def pbyte(+x: List<&2, Nat>, +y: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  Spec.ntake(2n, Spec.ndrop(Nat.mul(2n, k), Spec.cat(x, y)))

# __byte_perm(x, y, s3 s2 s1 s0): result byte i = byte s_i of {y:x}.
def prmt(+x: List<&2, Nat>, +y: List<&2, Nat>, +s0: Nat, +s1: Nat, +s2: Nat, +s3: Nat) -> List<&2, Nat>:
  Spec.cat(pbyte(x, y, s0), Spec.cat(pbyte(x, y, s1), Spec.cat(pbyte(x, y, s2), pbyte(x, y, s3))))

# dq8_m16_regs(a, b): u = __funnelshift_r(b, a, 4); s = (.., 20); t = (.., 24); w7 = __byte_perm(b, 0,
# 0x4410); w5 = (b, 0x4421); w3 = (b, 0x4432); w6 = (u, 0x4410); w4 = (u, 0x4421); w2 = (u, 0x4432);
# w1 = t & 0xffff; w0 = __byte_perm(s, 0, 0x4421)
def diet_windows(+a: List<&2, Nat>, +b: List<&2, Nat>) -> Spec.Win8:
  +u = Spec.shf(b, a, 1n)
  +s = Spec.shf(b, a, 5n)
  +t = Spec.shf(b, a, 6n)
  +z = Spec.zw()
  Spec.Win8{prmt(s, z, 1n, 2n, 4n, 4n), Spec.lo16(t), prmt(u, z, 2n, 3n, 4n, 4n), prmt(b, z, 2n, 3n, 4n, 4n),
    prmt(u, z, 1n, 2n, 4n, 4n), prmt(b, z, 1n, 2n, 4n, 4n), prmt(u, z, 0n, 1n, 4n, 4n), prmt(b, z, 0n, 1n, 4n, 4n)}

# ---- hoisted addresses ----

# dw0 = rs + ((lane + 31) & 31) * 4; dw1 = rs + lane * 4
def dw0(+rs: Nat, +lane: Nat) -> Nat:
  Nat.add(rs, Nat.mul(Nat.mod(Nat.add(lane, 31n), 32n), 4n))

def dw1(+rs: Nat, +lane: Nat) -> Nat:
  Nat.add(rs, Nat.mul(lane, 4n))

# m16_lds<OFF>(addr): ld.shared.u32 [addr + OFF], OFF = t * 128
def lds_addr(+addr: Nat, +t: Nat) -> Nat:
  Nat.add(addr, Nat.mul(t, 128n))

# The pinned activation base: asm volatile ("" : "+r"(dxs)) leaves the value unchanged.
def pin(+x: Nat) -> Nat:
  x

# Words wa[t], wb[t] for tiles t = tl .. 3, read up front.
type WP is Data:
  WP{wa: List<&2, Nat>, wb: List<&2, Nat>}

def loads(n: Nat, +t: Nat, +mem: List<&2, Spec.Cell>, +w0: Nat, +w1: Nat) -> List<&2, WP>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      WP{Spec.rd(mem, lds_addr(w0, t)), Spec.rd(mem, lds_addr(w1, t))} <> loads(m, 1n+t, mem, w0, w1)

def dtiles(ws: List<&2, WP>, +t: Nat, +MT: Nat) -> List<&2, Spec.TE>:
  match ws:
    case Nil{}:
      Nil{}
    case p <> rest:
      match p:
        case WP{a, b}:
          Spec.mmas(MT, 0n, t, diet_windows(a, b), dtiles(rest, 1n+t, MT))

# m16_tile_diet<MT, cb>(sa, w0, w1, hacc)
def tile_diet(+mem: List<&2, Spec.Cell>, +sa: Nat, +w0: Nat, +w1: Nat, +MT: Nat) -> List<&2, Spec.TE>:
  Spec.Ldsm{sa} <> dtiles(loads(4n, 0n, mem, w0, w1), 0n, MT)

# The mode-2 tile step of one loop iteration: m16_tile_diet(dxs + x_off, dw0 + cur_off, dw1 + cur_off).
def diet_iter(+mem: List<&2, Spec.Cell>, +rs: Nat, +lane: Nat, +xsa: Nat, +co: Nat, +xo: Nat, +MT: Nat) -> List<&2, Spec.TE>:
  tile_diet(mem, Nat.add(pin(xsa), xo), Nat.add(dw0(rs, lane), co), Nat.add(dw1(rs, lane), co), MT)

# ---- the mode switch ----

# EXL3_M16_DIET as the process sees it: unset, or a string of character codes.
type Env is Data:
  Unset{}
  Str{cs: List<&2, Nat>}

type Mode is Data:
  Ok{m: Nat}
  Bad{}

def digit_ok(ok: Bool, +c: Nat) -> Mode:
  match ok:
    case True{}:
      Ok{Nat.sub(c, 48n)}
    case False{}:
      Bad{}

# A one-character value c: '0', '1', '2' (codes 48, 49, 50) give c - '0'; anything else fails the
# TORCH_CHECK.
def digit(+c: Nat) -> Mode:
  digit_ok(Bool.and(Nat.is_le(48n, c), Nat.is_le(c, 50n)), c)

def parse_str(cs: List<&2, Nat>) -> Mode:
  match cs:
    case Nil{}:
      Ok{2n}
    case c <> rest:
      match rest:
        case Nil{}:
          digit(c)
        case d <> more:
          Bad{}

# exl3_m16_diet's initial mode: if (!env || !env[0]) return 2; TORCH_CHECK((env[0] == '0' || env[0] ==
# '1' || env[0] == '2') && !env[1], ...); return env[0] - '0';
def parse(env: Env) -> Mode:
  match env:
    case Unset{}:
      Ok{2n}
    case Str{cs}:
      parse_str(cs)

# torch.ops.exl3_m16.diet(set): set < 0 queries; else mode = set > 2 ? 2 : set.
type SetArg is Data:
  Query{}
  Put{x: Nat}

def set_mode(+m: Nat, s: SetArg) -> Nat:
  match s:
    case Query{}:
      m
    case Put{x}:
      Nat.min(x, 2n)

def sel(c: Bool, +t: Nat, +f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

# get_launch: k = diet == 2 ? X<.., 2> : diet == 1 ? X<.., 1> : X<.., 0>; the instance's DIET template value
# (the same selector in all three launchers; the cache is indexed [diet] with 3 entries).
def inst(+d: Nat) -> Nat:
  sel(Nat.is_eq(d, 2n), 2n, sel(Nat.is_eq(d, 1n), 1n, 0n))
