# Semantic obligations for ext 2106 (the DIET = true instruction diet of the decode m16 main loops of
# the 8202 tail, the 8201 MLP and the 2102/2105 m16g kernels), bend/m16_diet.bend, against their
# DIET = false loops, bend/m16_diet_spec.bend. Every law is generic: any segment bounds s, n (so every
# slice of the 8205b weighted partition and of 2105's), any KT >= 1 per phase, any ring override below
# PF, and every configuration PF, XR, FOLD, W_STAGE, X_ITER >= 1 with FOLD | 2 XR (the kernels'
# static_assert); the served Exl3M16Cfg<MT> values (PF 8, XR 16, FOLD 4, W_STAGE 512, X_ITER 256 MT)
# are one instance (diet_served_cfg). Masks `x & (P - 1)` are `x mod P` (P a power of two,
# static_asserted; bend/m16_diet_diff.py checks the asserts and the instantiated constants).
# Must happen: the DIET = true loop produces the DIET = false event trace (x-chunk issue and barrier,
# weight-issue decision, ring offset and source, MMA ring offset, ldmatrix offset, fold, segment
# flushes, phase-exit cursor and slots) per iteration, per phase and per kernel.
# Must never: an extra or missing iteration (diet_skeleton), a ring / activation offset outside its
# buffer (diet_*_in_ring), a skipped or duplicated weight issue (diet_*_issues).
# About the Bend model; the CUDA code's conformance to it, fp values and the memory model are outside.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./m16_diet_spec.bend as Spec
import ./m16_diet.bend as Impl

# ---- must-never predicates over an event list ----

# Every ring byte offset (MMA and weight copy) is below PF * W_STAGE and every ldmatrix offset below
# 2 * XR * X_ITER.
def we_in(w: Spec.WE, +lim: Nat) -> Bool:
  match w:
    case Spec.NoW{}:
      True{}
    case Spec.Iss{off, run, k}:
      Nat.is_lt(off, lim)

def in_ring(evs: List<&2, Spec.Ev>, +rl: Nat, +xl: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          Bool.and(we_in(w, rl), Bool.and(Nat.is_lt(ring, rl), Bool.and(Nat.is_lt(xoff, xl), in_ring(rest, rl, xl))))
        case Spec.Seg{g}:
          in_ring(rest, rl, xl)
        case Spec.Pro{w}:
          Bool.and(we_in(w, rl), in_ring(rest, rl, xl))
        case Spec.Exit{st}:
          in_ring(rest, rl, xl)

# ---- (1) loop control: the countdown loop is v2's loop ----

# For every range [s, e) and KT >= 1 the `left` countdown with j = seg_end afterwards and the rebuilt
# index jc = seg_end - left runs exactly v2's iterations, in order, with the same segment flushes
# (with gemm_m16_partition's mainloop_trace: s .. e - 1 once each; no extra, no missing iteration,
# every do-while entered with left >= 1).
law diet_skeleton:
  for +s: Nat
  for +e: Nat
  for +KT: Nat
  for ordered: {Nat.is_le(s, e) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {Impl.dmainloop(s, e, KT) == Part.mainloop(s, e, KT) : List<&2, PSpec.Ev>}

# ---- (2) per-iteration bookkeeping ----

# Ring slot offsets: from slot c < PF, (c W + W) & (PF W - 1) is DIET = false's next slot times W, and
# that slot is again below PF.
law diet_ring_step:
  for +c: Nat
  for +pf: Nat
  for +ws: Nat
  for slot: {Nat.is_lt(c, pf) == True{} : Bool}
  for wpos: {Nat.is_lt(0n, ws) == True{} : Bool}
  {Impl.dring(Nat.mul(c, ws), pf, ws) == Nat.mul(Spec.nxt(c, pf), ws) : Nat} &
  {Nat.is_lt(Spec.nxt(c, pf), pf) == True{} : Bool}

# Activation piece: DIET = false's ((j / XR) & 1) XR + (j & (XR - 1)) is j mod 2 XR, and x_off =
# (j mod 2 XR) X_ITER steps to ((j + 1) mod 2 XR) X_ITER.
law diet_xoff:
  for +j: Nat
  for +xr: Nat
  for +xi: Nat
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  {Spec.rpiece(j, xr) == Nat.mod(j, Nat.mul(2n, xr)) : Nat} &
  {Impl.dxnext(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), xr, xi) == Nat.mul(Nat.mod(1n+j, Nat.mul(2n, xr)), xi) : Nat}

# The x-chunk test on x_off, with jc = j, is DIET = false's (j & (XR - 1)) == 0 test and chunk.
law diet_chunk:
  for +j: Nat
  for +xr: Nat
  for +xi: Nat
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  {Impl.dchunk(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), j, xr, xi) == Spec.rchunk(j, xr) : Spec.XE}

# The fold test on the incremented x_off is (j & (FOLD - 1)) == FOLD - 1 when FOLD divides 2 XR.
law diet_fold:
  for +j: Nat
  for +xr: Nat
  for +fo: Nat
  for +xi: Nat
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  {Impl.dfold(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), xr, fo, xi) == Spec.rfold(j, fo) : Bool}

# Tail / 8201 weight issue: with iss_j holding the run end (iss_j + iss_rem), the guard iss_rem > 0
# issues exactly when DIET = false's iss_j < n_tot does, the same copy (ring offset, source), and
# the cursor after the step is again DIET = false's in run-end form.
def phases_ok(phs: List<&2, Spec.Ph>) -> Bool:
  match phs:
    case Nil{}:
      True{}
    case p <> rest:
      match p:
        case Spec.Ph{s, n, kt}:
          Bool.and(Nat.is_lt(0n, kt), phases_ok(rest))

def dt_of(r: Spec.RIM) -> Impl.DIM:
  match r:
    case Spec.RT{+ij, +rem, run, k}:
      Impl.DT{Nat.add(ij, rem), rem, run, k}
    case Spec.RG{ij, kt, g, run, k}:
      Impl.DT{0n, 0n, 0n, 0n}

law diet_tail_issue:
  for +phs: List<&2, Spec.Ph>
  for +ij: Nat
  for +rem: Nat
  for +run: Nat
  for +k: Nat
  for +q: Nat
  for +ws: Nat
  for fits: {Nat.is_le(Nat.add(ij, rem), Spec.total(phs)) == True{} : Bool}
  for live: {Bool.or(Nat.is_le(Spec.total(phs), ij), Nat.is_lt(0n, rem)) == True{} : Bool}
  {Impl.d_we(Nat.mul(q, ws), Spec.t_ctx(phs), Impl.DT{Nat.add(ij, rem), rem, run, k}) ==
    Spec.r_we(q, ws, Spec.t_ctx(phs), Spec.RT{ij, rem, run, k}) : Spec.WE} &
  {Impl.d_next(Spec.t_ctx(phs), Impl.DT{Nat.add(ij, rem), rem, run, k}) ==
    dt_of(Spec.r_next(Spec.t_ctx(phs), Spec.RT{ij, rem, run, k})) : Impl.DIM}

# ---- (3) a whole phase (tail / 8201 run_phase) ----

# From any entry state the ref invariants allow (slots below PF, iss_j + iss_rem <= n_tot, a live
# cursor has iss_rem > 0), DIET = true's run_phase emits DIET = false's events and leaves the same
# cursor and slots.
law diet_phase:
  for +s: Nat
  for +n: Nat
  for +kt: Nat
  for +phs: List<&2, Spec.Ph>
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +ws: Nat
  for +xi: Nat
  for +cs: Nat
  for +qs: Nat
  for +ij: Nat
  for +rem: Nat
  for +run: Nat
  for +k: Nat
  for tiles: {Nat.is_lt(0n, kt) == True{} : Bool}
  for kts: {phases_ok(phs) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for cur: {Nat.is_lt(cs, pf) == True{} : Bool}
  for iss: {Nat.is_lt(qs, pf) == True{} : Bool}
  for fits: {Nat.is_le(Nat.add(ij, rem), Spec.total(phs)) == True{} : Bool}
  for live: {Bool.or(Nat.is_le(Spec.total(phs), ij), Nat.is_lt(0n, rem)) == True{} : Bool}
  {Impl.diet_phase(Spec.Ph{s, n, kt}, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.St{cs, qs, ij, rem, run, k}) ==
    Spec.ref_phase(Spec.Ph{s, n, kt}, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.St{cs, qs, ij, rem, run, k})
    : Spec.Res}

# ---- (4) whole kernels ----

# 8201: prologue, phase 1 (gate + up), phase 2 (down) after cur_slot = ring2.
law diet_mlp:
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
  for +ws: Nat
  for +xi: Nat
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {Impl.diet_mlp(Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r2, pf, xr, fo, ws, xi) ==
    Spec.ref_mlp(Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r2, pf, xr, fo, ws, xi) : List<&2, Spec.Ev>}

# 8202 tail: prologue, phase 0 (o_proj), phase 1 after cur_slot = ring1, phase 2 after cur_slot = ring2.
law diet_tail:
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
  for +ws: Nat
  for +xi: Nat
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring1: {Nat.is_lt(r1, pf) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {Impl.diet_tail(Spec.Ph{s0, n0, k0}, Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r1, r2, pf, xr, fo, ws, xi) ==
    Spec.ref_tail(Spec.Ph{s0, n0, k0}, Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r1, r2, pf, xr, fo, ws, xi)
    : List<&2, Spec.Ev>}

# m16g (2102 / 2105): prologue and the loop over the block slice [s, s + n).
law diet_m16g:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +ws: Nat
  for +xi: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  {Impl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi) == Spec.ref_m16g(s, n, KT, pf, xr, fo, ws, xi)
    : List<&2, Spec.Ev>}

# ---- (5) must never: out-of-ring offsets, skipped or duplicated weight copies ----

# Every MMA ring offset, weight-copy ring offset (prologue and loop) and ldmatrix offset of the DIET =
# true kernels lies inside its buffer: ring < PF * W_STAGE, activation < 2 * XR * X_ITER.
law diet_mlp_in_ring:
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
  for +ws: Nat
  for +xi: Nat
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {in_ring(Impl.diet_mlp(Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r2, pf, xr, fo, ws, xi), Nat.mul(pf, ws),
    Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}

law diet_tail_in_ring:
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
  for +ws: Nat
  for +xi: Nat
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring1: {Nat.is_lt(r1, pf) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {in_ring(Impl.diet_tail(Spec.Ph{s0, n0, k0}, Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r1, r2, pf, xr, fo, ws, xi),
    Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}

law diet_m16g_in_ring:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +ws: Nat
  for +xi: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  {in_ring(Impl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi), Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}

# The weight copies of a trace in order: stream tile run + k (tail / 8201: the pointer is (seek cursor, row
# steps)), or k-tile iteration run * KT + k (m16g: the pointer is (group, k-tile)).
def iss_t(w: Spec.WE, rest: List<&2, Nat>) -> List<&2, Nat>:
  match w:
    case Spec.NoW{}:
      rest
    case Spec.Iss{off, run, k}:
      Nat.add(run, k) <> rest

def issued(evs: List<&2, Spec.Ev>) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          iss_t(w, issued(rest))
        case Spec.Seg{g}:
          issued(rest)
        case Spec.Pro{w}:
          iss_t(w, issued(rest))
        case Spec.Exit{st}:
          issued(rest)

def iss_g(w: Spec.WE, +KT: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match w:
    case Spec.NoW{}:
      rest
    case Spec.Iss{off, run, k}:
      Nat.add(Nat.mul(run, KT), k) <> rest

def issued_g(evs: List<&2, Spec.Ev>, +KT: Nat) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          iss_g(w, KT, issued_g(rest, KT))
        case Spec.Seg{g}:
          issued_g(rest, KT)
        case Spec.Pro{w}:
          iss_g(w, KT, issued_g(rest, KT))
        case Spec.Exit{st}:
          issued_g(rest, KT)

# rng(n, a) = a, a + 1, ..., a + n - 1
def rng(n: Nat, +a: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      a <> rng(m, 1n+a)

# Every weight tile of the stream is copied exactly once, in stream order (no skipped, no duplicated
# copy): tail / 8201 stream tiles 0 .. n_tot - 1, m16g k-tile iterations s .. s + n - 1.
law diet_mlp_issues:
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
  for +ws: Nat
  for +xi: Nat
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {issued(Impl.diet_mlp(Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r2, pf, xr, fo, ws, xi)) == rng(Nat.add(n1, n2), 0n)
    : List<&2, Nat>}

law diet_tail_issues:
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
  for +ws: Nat
  for +xi: Nat
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  for ring1: {Nat.is_lt(r1, pf) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, pf) == True{} : Bool}
  {issued(Impl.diet_tail(Spec.Ph{s0, n0, k0}, Spec.Ph{s1, n1, k1}, Spec.Ph{s2, n2, k2}, r1, r2, pf, xr, fo, ws, xi)) ==
    rng(Nat.add(n0, Nat.add(n1, n2)), 0n) : List<&2, Nat>}

law diet_m16g_issues:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +pf: Nat
  for +xr: Nat
  for +fo: Nat
  for +ws: Nat
  for +xi: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for pfpos: {Nat.is_lt(0n, pf) == True{} : Bool}
  for xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}
  for fopos: {Nat.is_lt(0n, fo) == True{} : Bool}
  for wspos: {Nat.is_lt(0n, ws) == True{} : Bool}
  for xipos: {Nat.is_lt(0n, xi) == True{} : Bool}
  for cadence: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}
  {issued_g(Impl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi), KT) == rng(n, s) : List<&2, Nat>}

# ---- (6) the served configuration satisfies every hypothesis ----

# Exl3M16Cfg<MT> as modelled (Impl.cfg_*: PF 8, XR 16, FOLD 4, W_STAGE = 4 * 128, X_ITER = MT * 256;
# bend/M16_DIET_TABLE.bend prints them and bend/m16_diet_diff.py matches them against the patched
# sources): every parameter is positive and FOLD divides 2 XR, for every MT >= 1.
law diet_served_cfg:
  for +mt: Nat
  for mtpos: {Nat.is_lt(0n, mt) == True{} : Bool}
  {Nat.is_lt(0n, Impl.cfg_pf()) == True{} : Bool} & {Nat.is_lt(0n, Impl.cfg_xr()) == True{} : Bool} &
  {Nat.is_lt(0n, Impl.cfg_fold()) == True{} : Bool} & {Nat.is_lt(0n, Impl.cfg_ws()) == True{} : Bool} &
  {Nat.is_lt(0n, Impl.cfg_xi(mt)) == True{} : Bool} & {Nat.mod(Nat.mul(2n, Impl.cfg_xr()), Impl.cfg_fold()) == 0n : Nat}
