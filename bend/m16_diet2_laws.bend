# Semantic obligations for ext 2107 (EXL3_M16_DIET mode 2 of the decode m16 kernels: layer tail, 8201 MLP,
# m16g), bend/m16_diet2.bend, against the reference tile step and switch of bend/m16_diet2_spec.bend.
# Mode 2 runs 2106's loop bookkeeping (bend/m16_diet_laws.bend: same trace as DIET = 0) with a different
# tile step, so these laws, together with 2106's, cover the mode-2 loops:
# Must happen:
# - the byte-permute extraction yields, for every word pair {a:b} (all 8 + 8 nibbles symbolic), exactly
#   the windows at bit offsets 0, 4, ..., 28, as does the funnel-shift / bfe reference (diet2_extract);
# - the hoisted per-lane addresses plus the ring offset and the t * 128 immediate are the per-iteration
#   addresses of words i0 and i1 of every tile t, for every lane, ring offset and ring base (diet2_lds_addr);
# - the mode-2 tile step (ldmatrix address, the 8 words read, windows, decode arguments, fragment order,
#   MMA order over t and mt) equals mma_tile for every shared-memory content (diet2_tile), and so for every
#   iteration of every loop trace (diet2_trace);
# - EXL3_M16_DIET parses to 0 / 1 / 2 (default 2, anything else refused), torch.ops.exl3_m16.diet keeps the
#   mode in 0..2, every launcher runs the instance DIET = mode (cache index in range) and an instance runs
#   2106's bookkeeping iff DIET >= 1 and 2107's tile step iff DIET = 2 (diet2_mode, diet2_dispatch).
# Must never: a weight-word read outside its ring slot (diet2_lds_in_slot: for every lane < 32, tile t < 4
# and ring slot c < PF, words i0, i1 < 32 and c * W_STAGE <= address - ring < (c + 1) * W_STAGE with the
# served W_STAGE = 4 * 128) or outside the ring in any iteration of the mode-2 kernels (diet2_mlp_lds,
# diet2_tail_lds, diet2_m16g_lds); an out-of-range mode or cache index (diet2_mode, diet2_dispatch).
# Nibble words are exact for these operations (every shift / extract / byte offset is a multiple of 4
# bits, see the spec). About the Bend model; the CUDA code's conformance to it (bend/m16_diet2_diff.py
# checks the transcribed expressions and constants), the codebook, fp values and the memory model
# (ordering of the 8 reads between the loop's __syncwarp()s) are outside.
import Base
import ./m16_diet_spec.bend as DSpec
import ./m16_diet.bend as DImpl
import ./m16_diet2_spec.bend as Spec
import ./m16_diet2.bend as Impl

# ---- (1) extraction ----

law diet2_extract:
  for +a0: Nat
  for +a1: Nat
  for +a2: Nat
  for +a3: Nat
  for +a4: Nat
  for +a5: Nat
  for +a6: Nat
  for +a7: Nat
  for +b0: Nat
  for +b1: Nat
  for +b2: Nat
  for +b3: Nat
  for +b4: Nat
  for +b5: Nat
  for +b6: Nat
  for +b7: Nat
  {Spec.ref_windows([a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]) ==
    Spec.windows([a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]) : Spec.Win8} &
  {Impl.diet_windows([a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]) ==
    Spec.windows([a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7]) : Spec.Win8}

# ---- (2) addresses ----

law diet2_lds_addr:
  for +rs: Nat
  for +co: Nat
  for +lane: Nat
  for +t: Nat
  {Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), co), t) == Spec.ref_addr(rs, co, t, Spec.ref_i0(lane)) : Nat} &
  {Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t) == Spec.ref_addr(rs, co, t, Spec.ref_i1(lane)) : Nat}

law diet2_lds_in_slot:
  for +rs: Nat
  for +c: Nat
  for +pf: Nat
  for +lane: Nat
  for +t: Nat
  for lanes: {Nat.is_lt(lane, 32n) == True{} : Bool}
  for tiles: {Nat.is_lt(t, 4n) == True{} : Bool}
  for slot: {Nat.is_lt(c, pf) == True{} : Bool}
  {Nat.is_lt(Spec.ref_i0(lane), 32n) == True{} : Bool} & {Nat.is_lt(Spec.ref_i1(lane), 32n) == True{} : Bool} &
  {Nat.is_le(Nat.add(rs, Nat.mul(c, DImpl.cfg_ws())), Spec.ref_addr(rs, Nat.mul(c, DImpl.cfg_ws()), t, Spec.ref_i0(lane))) == True{} : Bool} &
  {Nat.is_lt(Spec.ref_addr(rs, Nat.mul(c, DImpl.cfg_ws()), t, Spec.ref_i0(lane)), Nat.add(rs, Nat.mul(1n+c, DImpl.cfg_ws()))) == True{} : Bool} &
  {Nat.is_le(Nat.add(rs, Nat.mul(c, DImpl.cfg_ws())), Spec.ref_addr(rs, Nat.mul(c, DImpl.cfg_ws()), t, Spec.ref_i1(lane))) == True{} : Bool} &
  {Nat.is_lt(Spec.ref_addr(rs, Nat.mul(c, DImpl.cfg_ws()), t, Spec.ref_i1(lane)), Nat.add(rs, Nat.mul(1n+c, DImpl.cfg_ws()))) == True{} : Bool} &
  {Nat.is_le(Nat.mul(1n+c, DImpl.cfg_ws()), Nat.mul(pf, DImpl.cfg_ws())) == True{} : Bool}

# ---- (3) the tile step, per iteration and over a loop trace ----

law diet2_tile:
  for +mem: List<&2, Spec.Cell>
  for +rs: Nat
  for +lane: Nat
  for +xsa: Nat
  for +co: Nat
  for +xo: Nat
  for +MT: Nat
  {Impl.diet_iter(mem, rs, lane, xsa, co, xo, MT) == Spec.ref_iter(mem, rs, lane, xsa, co, xo, MT) : List<&2, Spec.TE>}

# The tile steps of a loop trace (2106's event vocabulary): one per iteration, at its MMA ring offset and
# ldmatrix offset.
def iters_ref(evs: List<&2, DSpec.Ev>, +mem: List<&2, Spec.Cell>, +rs: Nat, +lane: Nat, +xsa: Nat, +MT: Nat)
    -> List<&2, Spec.TE>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, ring, xoff, fold}:
          List.append(&2, Spec.TE, Spec.ref_iter(mem, rs, lane, xsa, ring, xoff, MT), iters_ref(rest, mem, rs, lane, xsa, MT))
        case DSpec.Seg{g}:
          iters_ref(rest, mem, rs, lane, xsa, MT)
        case DSpec.Pro{w}:
          iters_ref(rest, mem, rs, lane, xsa, MT)
        case DSpec.Exit{st}:
          iters_ref(rest, mem, rs, lane, xsa, MT)

def iters_diet(evs: List<&2, DSpec.Ev>, +mem: List<&2, Spec.Cell>, +rs: Nat, +lane: Nat, +xsa: Nat, +MT: Nat)
    -> List<&2, Spec.TE>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, ring, xoff, fold}:
          List.append(&2, Spec.TE, Impl.diet_iter(mem, rs, lane, xsa, ring, xoff, MT), iters_diet(rest, mem, rs, lane, xsa, MT))
        case DSpec.Seg{g}:
          iters_diet(rest, mem, rs, lane, xsa, MT)
        case DSpec.Pro{w}:
          iters_diet(rest, mem, rs, lane, xsa, MT)
        case DSpec.Exit{st}:
          iters_diet(rest, mem, rs, lane, xsa, MT)

# For every event list (so for the traces of diet_mlp / diet_tail / diet_m16g, which 2106's laws equate
# with DIET = 0's), mode 2's tile steps are mma_tile's, iteration by iteration.
law diet2_trace:
  for +evs: List<&2, DSpec.Ev>
  for +mem: List<&2, Spec.Cell>
  for +rs: Nat
  for +lane: Nat
  for +xsa: Nat
  for +MT: Nat
  {iters_diet(evs, mem, rs, lane, xsa, MT) == iters_ref(evs, mem, rs, lane, xsa, MT) : List<&2, Spec.TE>}

# ---- (3b) must never: every weight-word read of every iteration inside the ring ----

# The 8 shared addresses mode 2 reads in an iteration at ring offset `ring` (tiles t = tl .. 3, words
# dw0 and dw1) are all below lim.
def lds_t(n: Nat, +t: Nat, +rs: Nat, +lane: Nat, +ring: Nat, +lim: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), ring), t), lim),
        Bool.and(Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), ring), t), lim), lds_t(m, 1n+t, rs, lane, ring, lim)))

def lds_ok(evs: List<&2, DSpec.Ev>, +rs: Nat, +lane: Nat, +lim: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, ring, xoff, fold}:
          Bool.and(lds_t(4n, 0n, rs, lane, ring, lim), lds_ok(rest, rs, lane, lim))
        case DSpec.Seg{g}:
          lds_ok(rest, rs, lane, lim)
        case DSpec.Pro{w}:
          lds_ok(rest, rs, lane, lim)
        case DSpec.Exit{st}:
          lds_ok(rest, rs, lane, lim)

# For every lane < 32 and every iteration of the mode-2 8201 / tail / m16g loops (2106's kernel traces at
# the served W_STAGE, any other parameters as in 2106's laws), every word read lies below ring + PF * W_STAGE
# (and at or above the ring base: every address is rs + a sum).
law diet2_mlp_lds:
  for +s1: Nat
  for +n1: Nat
  for +k1: Nat
  for +s2: Nat
  for +n2: Nat
  for +k2: Nat
  for +r2: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +xi: Nat
  for +rs: Nat
  for +lane: Nat
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  for lanes: {Nat.is_lt(lane, 32n) == True{} : Bool}
  {lds_ok(DImpl.diet_mlp(DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r2, pf, xr, fo, DImpl.cfg_ws(), xi), rs, lane,
    Nat.add(rs, Nat.mul(pf, DImpl.cfg_ws()))) == True{} : Bool}

law diet2_tail_lds:
  for +s0: Nat
  for +n0: Nat
  for +k0: Nat
  for +s1: Nat
  for +n1: Nat
  for +k1: Nat
  for +s2: Nat
  for +n2: Nat
  for +k2: Nat
  for +r1: Nat
  for +r2: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +xi: Nat
  for +rs: Nat
  for +lane: Nat
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  for lanes: {Nat.is_lt(lane, 32n) == True{} : Bool}
  for ring1: {Nat.is_lt(r1, pf) == True{} : Bool}
  {lds_ok(DImpl.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, pf, xr, fo, DImpl.cfg_ws(), xi),
    rs, lane, Nat.add(rs, Nat.mul(pf, DImpl.cfg_ws()))) == True{} : Bool}

law diet2_m16g_lds:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +xi: Nat
  for +rs: Nat
  for +lane: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for lanes: {Nat.is_lt(lane, 32n) == True{} : Bool}
  {lds_ok(DImpl.diet_m16g(s, n, KT, pf, xr, fo, DImpl.cfg_ws(), xi), rs, lane, Nat.add(rs, Nat.mul(pf, DImpl.cfg_ws()))) == True{} : Bool}

# ---- (4) the switch ----

def mode_ok(m: Impl.Mode) -> Bool:
  match m:
    case Impl.Ok{x}:
      Nat.is_lt(x, 3n)
    case Impl.Bad{}:
      True{}

law diet2_mode:
  for +env: Impl.Env
  for +m: Nat
  for +s: Impl.SetArg
  for range: {Nat.is_lt(m, 3n) == True{} : Bool}
  {Impl.parse(Impl.Unset{}) == Impl.Ok{2n} : Impl.Mode} & {Impl.parse(Impl.Str{Nil{}}) == Impl.Ok{2n} : Impl.Mode} &
  {Impl.parse(Impl.Str{[48n]}) == Impl.Ok{0n} : Impl.Mode} & {Impl.parse(Impl.Str{[49n]}) == Impl.Ok{1n} : Impl.Mode} &
  {Impl.parse(Impl.Str{[50n]}) == Impl.Ok{2n} : Impl.Mode} & {mode_ok(Impl.parse(env)) == True{} : Bool} &
  {Nat.is_lt(Impl.set_mode(m, s), 3n) == True{} : Bool}

law diet2_dispatch:
  for +m: Nat
  for range: {Nat.is_lt(m, 3n) == True{} : Bool}
  {Impl.inst(m) == m : Nat} & {Nat.is_lt(Impl.inst(m), 3n) == True{} : Bool} &
  {Spec.feat(Impl.inst(m)) == Spec.Feat{Nat.is_lt(0n, m), Nat.is_eq(m, 2n)} : Spec.Feat}
