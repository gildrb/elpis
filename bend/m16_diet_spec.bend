# Reference (DIET = false) bookkeeping of ext 2106's three decode m16 main loops, and the shared event
# vocabulary. Transcribed from the DIET = false paths of the patched kernels (patch
# 2106-m16-diet-on8205b.patch, sha256 39da72c8...; T: = exl3_tail_m16_kernel.cuh, M: =
# exl3_mlp_m16_kernel.cuh, G: = exl3_gemm_m16g_kernel.cuh, all under exllamav3_ext/quant/):
# - the loop skeleton `for (g_cur = s / KT; j < n; ++g_cur) { seg_end = ...; for (; j < seg_end; ++j)
#   body; fold(); flush(g_cur); }` is 2001's v2 loop, already modelled as gemm_m16_partition's
#   mainloop (Tile{g, s + j} per iteration, Flush{g} per segment);
# - the per-iteration bookkeeping (activation chunk issue, weight issue guard and cursor, ring slots,
#   ldmatrix piece, fold test) is `rwalk` below, driven by that skeleton's events;
# - 8201 (2 phases) and the tail (3 phases) share one weight-issue cursor over the phase stream
#   (iss_seek / issue_w, M:297-331, T:163-206); m16g has its own (G:154-172).
# Every offset is the byte offset the kernel adds to its ring / activation base address. The C masks
# `x & (P - 1)` of the DIET = true path are modelled as `x mod P`; the kernels static_assert that
# every such P is a power of two (bend/m16_diet_diff.py checks the asserts and the constants).
# Config: pf = PF, xr = XR, fo = FOLD, ws = W_STAGE, xi = X_ITER (Exl3M16Cfg<MT>).
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec

# ---- vocabulary ----

# One phase of the weight stream: slice [s, s + n) of iterations, KT = kt k-tiles per group.
type Ph is Data:
  Ph{s: Nat, n: Nat, kt: Nat}

# Activation chunk issue at the top of an iteration: chunk c, preceded by __syncthreads iff bar.
type XE is Data:
  NoX{}
  Chunk{c: Nat, bar: Bool}

# Weight cp.async of an iteration: ring byte offset `off`, source pointer (run, k) = the pointer set
# by the last seek / wrap (`run`) advanced by k row steps.
type WE is Data:
  NoW{}
  Iss{off: Nat, run: Nat, k: Nat}

# Slots and issue cursor between phases (tail / 8201): cur_slot, iss_slot, iss_j, iss_rem, pointer.
type St is Data:
  St{cs: Nat, qs: Nat, ij: Nat, rem: Nat, run: Nat, k: Nat}

# What flows out of a main loop: the state the next phase starts from (tail / 8201), or nothing
# (m16g: only cp_async_wait<0> follows, G:297).
type Out is Data:
  Cont{st: St}
  End{}

# Observable events: It = one main-loop iteration (chunk issue, weight issue, MMA ring offset and
# ldmatrix offset, fold); Seg = fold() + flush(g) at a segment end; Pro = a prologue issue; Exit = the
# issue cursor and slots after a phase (read by the L2 prefetch and the next phase).
type Ev is Data:
  It{x: XE, w: WE, ring: Nat, xoff: Nat, fold: Bool}
  Seg{g: Nat}
  Pro{w: WE}
  Exit{st: St}

type Res is Data:
  Res{evs: List<&2, Ev>, out: Out}

# Issue-cursor context: the phase list and stream length n_tot (tail / 8201), or KT and n_iter (m16g).
type Ctx is Data:
  TCtx{phs: List<&2, Ph>, N: Nat}
  GCtx{KT: Nat, N: Nat}

# DIET = false issue cursor: RT = tail / 8201 (iss_j, iss_rem, pointer); RG = m16g (iss_j, iss_kt,
# iss_g, pointer).
type RIM is Data:
  RT{ij: Nat, rem: Nat, run: Nat, k: Nat}
  RG{ij: Nat, kt: Nat, g: Nat, run: Nat, k: Nat}

# ---- small helpers (a match needs a parameter scrutinee) ----

def sel(c: Bool, t: Nat, f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

def xsel(c: Bool, t: XE) -> XE:
  match c:
    case True{}:
      t
    case False{}:
      NoX{}

def wsel(c: Bool, t: WE) -> WE:
  match c:
    case True{}:
      t
    case False{}:
      NoW{}

def cons(ev: Ev, r: Res) -> Res:
  match r:
    case Res{e, o}:
      Res{ev <> e, o}

def res_evs(r: Res) -> List<&2, Ev>:
  match r:
    case Res{e, o}:
      e

def ctx_n(ctx: Ctx) -> Nat:
  match ctx:
    case TCtx{phs, N}:
      N
    case GCtx{KT, N}:
      N

def ctx_phs(ctx: Ctx) -> List<&2, Ph>:
  match ctx:
    case TCtx{phs, N}:
      phs
    case GCtx{KT, N}:
      Nil{}

def ctx_kt(ctx: Ctx) -> Nat:
  match ctx:
    case TCtx{phs, N}:
      0n
    case GCtx{KT, N}:
      KT

# Stream length of a phase list (n_tot).
def total(phs: List<&2, Ph>) -> Nat:
  match phs:
    case Nil{}:
      0n
    case p <> rest:
      match p:
        case Ph{s, n, kt}:
          Nat.add(n, total(rest))

# ---- per-iteration bookkeeping, DIET = false ----

# M:632 / T:500 / G:350: slot = slot == PF - 1 ? 0 : slot + 1
def nxt(+c: Nat, +pf: Nat) -> Nat:
  sel(Nat.is_eq(c, Nat.sub(pf, 1n)), 0n, 1n+c)

# M:625-628: if ((j & (XR - 1)) == 0) { if (j > 0) __syncthreads(); issue_x_chunk(j / XR + 1); }
def rchunk(+j: Nat, +xr: Nat) -> XE:
  xsel(Nat.is_eq(Nat.mod(j, xr), 0n), Chunk{Nat.add(Nat.div(j, xr), 1n), Nat.is_lt(0n, j)})

# M:636: ldmatrix piece ((j / XR) & 1) * XR + (j & (XR - 1)) (times X_ITER at the call)
def rpiece(+j: Nat, +xr: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mod(Nat.div(j, xr), 2n), xr), Nat.mod(j, xr))

# M:640: if ((j & (FOLD - 1)) == FOLD - 1) fold();
def rfold(+j: Nat, +fo: Nat) -> Bool:
  Nat.is_eq(Nat.mod(j, fo), Nat.sub(fo, 1n))

# ---- weight issue cursor, DIET = false ----

# M:297-320 / T:163-195 iss_seek, run length only: tile i (relative to this list's first phase) of
# the stream lies in phase Ph{s, n, KT} at iteration it = s + i; iss_rem = min(KT - it % KT, n - i).
def seek(phs: List<&2, Ph>, +i: Nat) -> Nat:
  match phs:
    case Nil{}:
      0n
    case p <> rest:
      match p:
        case Ph{+s, +n, +kt}:
          sel(Nat.is_lt(i, n), Nat.min(Nat.sub(kt, Nat.mod(Nat.add(s, i), kt)), Nat.sub(n, i)),
            seek(rest, Nat.sub(i, n)))

# The source pointer after a seek at cursor j1 is (j1, 0) (iss_seek derives it from the cursor alone).
def rt_seek(c: Bool, +ctx: Ctx, +j1: Nat, +r1: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      RT{j1, seek(ctx_phs(ctx), j1), j1, 0n}
    case False{}:
      RT{j1, r1, run, k}

# M:321-330 issue_w after the copy: iss_j++; if (--iss_rem == 0) { if (iss_j < n_tot) iss_seek(); }
# else iss_ptr += iss_row;
def rt_iss(c: Bool, +ctx: Ctx, +j1: Nat, +r1: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      rt_seek(Nat.is_lt(j1, ctx_n(ctx)), ctx, j1, r1, run, k)
    case False{}:
      RT{j1, r1, run, 1n+k}

# M:631: if (iss_j < n_tot) issue_w(iss_slot);
def rt_step(c: Bool, +ctx: Ctx, +ij: Nat, +rem: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      rt_iss(Nat.is_eq(Nat.sub(rem, 1n), 0n), ctx, 1n+ij, Nat.sub(rem, 1n), run, k)
    case False{}:
      RT{ij, rem, run, k}

# G:169: if (iss_j < n_iter) iss_ptr = w_src(iss_g);  (pointer (g, 0))
def rg_src(c: Bool, +j1: Nat, +g1: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      RG{j1, 0n, g1, g1, 0n}
    case False{}:
      RG{j1, 0n, g1, run, k}

# G:164-171 issue_w after the copy: iss_j++; if (++iss_kt == KT) { iss_kt = 0; iss_g++; ... }
# else iss_ptr += row_bytes;
def rg_wrap(c: Bool, +ctx: Ctx, +j1: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      rg_src(Nat.is_lt(j1, ctx_n(ctx)), j1, 1n+g, run, k)
    case False{}:
      RG{j1, 1n+kt, g, run, 1n+k}

# G:349: if (iss_j < n_iter) issue_w(iss_slot);
def rg_step(c: Bool, +ctx: Ctx, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat) -> RIM:
  match c:
    case True{}:
      rg_wrap(Nat.is_eq(1n+kt, ctx_kt(ctx)), ctx, 1n+ij, kt, g, run, k)
    case False{}:
      RG{ij, kt, g, run, k}

# The weight copy an iteration (or a prologue step) issues into ring slot `slot`.
def r_we(+slot: Nat, +ws: Nat, +ctx: Ctx, rim: RIM) -> WE:
  match rim:
    case RT{ij, rem, run, k}:
      wsel(Nat.is_lt(ij, ctx_n(ctx)), Iss{Nat.mul(slot, ws), run, k})
    case RG{ij, kt, g, run, k}:
      wsel(Nat.is_lt(ij, ctx_n(ctx)), Iss{Nat.mul(slot, ws), run, k})

# The cursor after `if (iss_j < N) issue_w(...)`.
def r_next(+ctx: Ctx, rim: RIM) -> RIM:
  match rim:
    case RT{+ij, +rem, +run, +k}:
      rt_step(Nat.is_lt(ij, ctx_n(ctx)), ctx, ij, rem, run, k)
    case RG{+ij, +kt, +g, +run, +k}:
      rg_step(Nat.is_lt(ij, ctx_n(ctx)), ctx, ij, kt, g, run, k)

# After the main loop: the tail / 8201 cursor and slots flow on; m16g ends.
def r_exit(+cs: Nat, +qs: Nat, rim: RIM) -> Out:
  match rim:
    case RT{ij, rem, run, k}:
      Cont{St{cs, qs, ij, rem, run, k}}
    case RG{ij, kt, g, run, k}:
      End{}

# ---- the prologue (both DIET modes run it: M:394-398, T:, G:207-211) ----

# for (d = 0; d < PF - 1; ++d) { if (iss_j < N) issue_w(d); cp_async_fence(); }, t steps left.
def pro(t: Nat, +d: Nat, +ws: Nat, +ctx: Ctx, +rim: RIM) -> List<&2, Ev>:
  match t:
    case 0n:
      Nil{}
    case 1n+u:
      Pro{r_we(d, ws, ctx, rim)} <> pro(u, 1n+d, ws, ctx, r_next(ctx, rim))

# The cursor after t prologue steps.
def pro_state(t: Nat, +ctx: Ctx, rim: RIM) -> RIM:
  match t:
    case 0n:
      rim
    case 1n+u:
      pro_state(u, ctx, r_next(ctx, rim))

# ---- the main loop, DIET = false ----

# The loop body over the skeleton events of one phase (M:621-641, T:489-509, G:340-358); j = it - s.
def rwalk(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Ctx,
    +cs: Nat, +qs: Nat, +rim: RIM) -> Res:
  match evs:
    case Nil{}:
      Res{Nil{}, r_exit(cs, qs, rim)}
    case ev <> rest:
      match ev:
        case PSpec.Tile{g, it}:
          +j = Nat.sub(it, s)
          cons(It{rchunk(j, xr), r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(rpiece(j, xr), xi),
              rfold(j, fo)},
            rwalk(rest, s, pf, xr, fo, ws, xi, ctx, nxt(cs, pf), nxt(qs, pf), r_next(ctx, rim)))
        case PSpec.Flush{g}:
          cons(Seg{g}, rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim))

# M:553 / T:421 run_phase(ph), DIET = false: v2's loop over [s, s + n) from the entry state.
def ref_phase(+ph: Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Ctx, +st: St) -> Res:
  match ph:
    case Ph{s, n, kt}:
      match st:
        case St{cs, qs, ij, rem, run, k}:
          rwalk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, RT{ij, rem, run, k})

# ---- kernel compositions (shared by both DIET modes; only the run_phase body differs) ----

# The initial tail / 8201 cursor: iss_j = 0, iss_rem = 0; if (n_tot > 0) iss_seek(); (M:293-331).
def t_init(+phs: List<&2, Ph>) -> RIM:
  RT{0n, sel(Nat.is_lt(0n, total(phs)), seek(phs, 0n), 0n), 0n, 0n}

def t_ctx(+phs: List<&2, Ph>) -> Ctx:
  TCtx{phs, total(phs)}

# cur_slot = 0, iss_slot = PF - 1 after the prologue (M:551-552).
def st_of(+cs: Nat, +qs: Nat, rim: RIM) -> St:
  match rim:
    case RT{ij, rem, run, k}:
      St{cs, qs, ij, rem, run, k}
    case RG{ij, kt, g, run, k}:
      St{cs, qs, 0n, 0n, 0n, 0n}

# `cur_slot = ringX;` before a later phase (M:759, T:671, T:762).
def set_cs(+r: Nat, st: St) -> St:
  match st:
    case St{cs, qs, ij, rem, run, k}:
      St{r, qs, ij, rem, run, k}

def out_evs(o: Out) -> List<&2, Ev>:
  match o:
    case Cont{st}:
      [Exit{st}]
    case End{}:
      Nil{}

def out_st(o: Out) -> St:
  match o:
    case Cont{st}:
      st
    case End{}:
      St{0n, 0n, 0n, 0n, 0n, 0n}

# m16g: initial cursor iss_j = 0, iss_g = s / KT, iss_kt = s - iss_g * KT, pointer w_src(g) + kt rows
# (G:154-158).
def g_init(+s: Nat, +KT: Nat) -> RIM:
  RG{0n, Nat.mod(s, KT), Nat.div(s, KT), Nat.div(s, KT), Nat.mod(s, KT)}

def res_all(r: Res) -> List<&2, Ev>:
  match r:
    case Res{e, o}:
      List.append(&2, Ev, e, out_evs(o))

# The rest of a kernel after a phase: that phase's events and exit, then `cur_slot = cr` and the next
# phase from the exit state.
def ref_then(r: Res, +p: Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Ctx)
    -> List<&2, Ev>:
  match r:
    case Res{e, +o}:
      List.append(&2, Ev, e, List.append(&2, Ev, out_evs(o),
        res_all(ref_phase(p, pf, xr, fo, ws, xi, ctx, set_cs(cr, out_st(o))))))

def ref_then2(r: Res, +p: Ph, +cr: Nat, +q: Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat,
    +xi: Nat, +ctx: Ctx) -> List<&2, Ev>:
  match r:
    case Res{e, +o}:
      List.append(&2, Ev, e, List.append(&2, Ev, out_evs(o),
        ref_then(ref_phase(p, pf, xr, fo, ws, xi, ctx, set_cs(cr, out_st(o))), q, cq, pf, xr, fo, ws, xi,
          ctx)))

# The 8201 kernel's weight-ring bookkeeping, DIET = false: prologue, phase 1 (gate + up), exit,
# cur_slot = ring2 (M:759), phase 2 (down), exit.
def ref_mlp(+p1: Ph, +p2: Ph, +r2: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat)
    -> List<&2, Ev>:
  +phs = {[p1, p2] : List<&2, Ph>}
  List.append(&2, Ev, pro(Nat.sub(pf, 1n), 0n, ws, t_ctx(phs), t_init(phs)),
    ref_then(ref_phase(p1, pf, xr, fo, ws, xi, t_ctx(phs),
        st_of(0n, Nat.sub(pf, 1n), pro_state(Nat.sub(pf, 1n), t_ctx(phs), t_init(phs)))),
      p2, r2, pf, xr, fo, ws, xi, t_ctx(phs)))

# The tail kernel's, DIET = false: prologue, phase 0 (o_proj), exit, cur_slot = ring1 (T:671),
# phase 1, exit, cur_slot = ring2 (T:762), phase 2, exit.
def ref_tail(+p0: Ph, +p1: Ph, +p2: Ph, +r1: Nat, +r2: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat,
    +xi: Nat) -> List<&2, Ev>:
  +phs = {[p0, p1, p2] : List<&2, Ph>}
  List.append(&2, Ev, pro(Nat.sub(pf, 1n), 0n, ws, t_ctx(phs), t_init(phs)),
    ref_then2(ref_phase(p0, pf, xr, fo, ws, xi, t_ctx(phs),
        st_of(0n, Nat.sub(pf, 1n), pro_state(Nat.sub(pf, 1n), t_ctx(phs), t_init(phs)))),
      p1, r1, p2, r2, pf, xr, fo, ws, xi, t_ctx(phs)))

# The m16g kernel's, DIET = false: prologue, then v2's loop over the block slice [s, s + n) from
# cur_slot = 0, iss_slot = PF - 1.
def ref_m16g(+s: Nat, +n: Nat, +KT: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat)
    -> List<&2, Ev>:
  List.append(&2, Ev, pro(Nat.sub(pf, 1n), 0n, ws, GCtx{KT, n}, g_init(s, KT)),
    res_evs(rwalk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, GCtx{KT, n}, 0n, Nat.sub(pf, 1n),
      pro_state(Nat.sub(pf, 1n), GCtx{KT, n}, g_init(s, KT)))))
