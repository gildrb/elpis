# Ext 2106 (patch 2106-m16-diet-on8205b.patch, sha256 39da72c8...): the DIET = true main loops of the
# three decode m16 kernels (T: = exl3_tail_m16_kernel.cuh, M: = exl3_mlp_m16_kernel.cuh, G: =
# exl3_gemm_m16g_kernel.cuh; line numbers of the patched tree), transcribed over Nat:
# - loop control (`dmainloop`): per segment `int left = seg_end - j; do { ... } while (--left > 0);
#   j = seg_end;`, the iteration index rebuilt as jc = seg_end - left (M:577-619, G:222-291); it emits
#   the same skeleton events as gemm_m16_partition's mainloop (Tile{g, s + jc}, Flush{g});
# - the bookkeeping (`dwalk`), driven by those events: ring slots as byte offsets cur_off / iss_off
#   masked with PF * W_STAGE - 1, the activation piece as x_off masked with 2 * XR * X_ITER - 1, the
#   x-chunk test (x_off & (XR * X_ITER - 1)) == 0, the fold test (x_off & (FOLD * X_ITER - 1)) == 0
#   after the increment, the weight issue guarded by the run countdown (tail / 8201: iss_rem > 0 with
#   iss_j holding the run end, converted back at phase exit; m16g: iss_left);
# - loop control never reads the bookkeeping state and the bookkeeping never reads `left` except
#   through jc, so running dwalk over dmainloop's events is the fused loop.
# Masks `x & (P - 1)` are `x mod P` (P is static_asserted a power of two in all three kernels).
# The shared prologue, phase compositions and event vocabulary are m16_diet_spec.bend's; the DIET =
# false loops (rwalk) are the reference. Laws: m16_diet_laws.bend.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./m16_diet_spec.bend as Spec

# DIET = true issue cursor: DT = tail / 8201 (iss_j = end of the current run, iss_rem, pointer);
# DG = m16g (iss_j, iss_kt, iss_g frozen at the run start, iss_left, pointer).
type DIM is Data:
  DT{je: Nat, rem: Nat, run: Nat, k: Nat}
  DG{jd: Nat, ktd: Nat, gd: Nat, left: Nat, run: Nat, k: Nat}

# ---- the served configuration: Exl3M16Cfg<MT> (exl3_gemm_m16_kernel.cuh:57-69), MT = 1, 2 ----

def cfg_pf() -> Nat:
  8n

def cfg_fold() -> Nat:
  4n

def cfg_xr() -> Nat:
  16n

# EXL3_M16_TILES_W
def cfg_tiles_w() -> Nat:
  4n

# W_STAGE = EXL3_M16_TILES_W * 128
def cfg_ws() -> Nat:
  Nat.mul(cfg_tiles_w(), 128n)

# X_ITER = MT * 256
def cfg_xi(+mt: Nat) -> Nat:
  Nat.mul(mt, 256n)

# ---- loop control ----

# M:585-618: do { ... jc = seg_end - left ... } while (--left > 0); `left` counts down from the
# segment's iteration count; each iteration is Tile{g, s + jc}. (left = 0 still runs the body once:
# the do-while; the laws show left >= 1 on every entry.)
def dinner(left: Nat, +se: Nat, +s: Nat, +g: Nat, rest: List<&2, PSpec.Ev>) -> List<&2, PSpec.Ev>:
  match left:
    case 0n:
      PSpec.Tile{g, Nat.add(s, Nat.sub(se, 0n))} <> rest
    case 1n+0n:
      PSpec.Tile{g, Nat.add(s, Nat.sub(se, 1n))} <> rest
    case 1n+1n+m:
      +r = m
      PSpec.Tile{g, Nat.add(s, Nat.sub(se, 1n+1n+r))} <> dinner(1n+r, se, s, g, rest)

# M:573-620: for (g_cur = s / KT; j < n; ++g_cur) { seg_end = min(e, (g_cur + 1) * KT) - s;
# left = seg_end - j; do ... while (--left > 0); j = seg_end; fold(); flush(g_cur); }. `fuel` bounds
# the model's outer iterations only (the laws show it never cuts the loop short).
def douter(fuel: Nat, go: Bool, +s: Nat, +e: Nat, +KT: Nat, +g: Nat, +j: Nat) -> List<&2, PSpec.Ev>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match go:
        case True{}:
          +se = Part.seg_end(s, e, g, KT)
          dinner(Nat.sub(se, j), se, s, g,
            PSpec.Flush{g} <> douter(f, Nat.is_lt(se, Nat.sub(e, s)), s, e, KT, 1n+g, se))
        case False{}:
          Nil{}

# The DIET = true loop over [s, e) from j = 0.
def dmainloop(+s: Nat, +e: Nat, +KT: Nat) -> List<&2, PSpec.Ev>:
  douter(1n+Nat.sub(e, s), Nat.is_lt(0n, Nat.sub(e, s)), s, e, KT, Nat.div(s, KT), 0n)

# ---- per-iteration bookkeeping, DIET = true ----

# M:586-590: if ((x_off & (XR * X_ITER - 1)) == 0) { jc = seg_end - left; if (jc > 0)
# __syncthreads(); issue_x_chunk(jc / XR + 1); }
def dchunk(+xo: Nat, +jc: Nat, +xr: Nat, +xi: Nat) -> Spec.XE:
  Spec.xsel(Nat.is_eq(Nat.mod(xo, Nat.mul(xr, xi)), 0n), Spec.Chunk{Nat.add(Nat.div(jc, xr), 1n), Nat.is_lt(0n, jc)})

# M:612-616: x_off = (x_off + X_ITER) & XBUF_MASK; if ((x_off & (FOLD * X_ITER - 1)) == 0) fold();
def dxnext(+xo: Nat, +xr: Nat, +xi: Nat) -> Nat:
  Nat.mod(Nat.add(xo, xi), Nat.mul(Nat.mul(2n, xr), xi))

def dfold(+xo: Nat, +xr: Nat, +fo: Nat, +xi: Nat) -> Bool:
  Nat.is_eq(Nat.mod(dxnext(xo, xr, xi), Nat.mul(fo, xi)), 0n)

# M:605 / M:611: off = (off + W_STAGE) & RING_MASK
def dring(+o: Nat, +pf: Nat, +ws: Nat) -> Nat:
  Nat.mod(Nat.add(o, ws), Nat.mul(pf, ws))

# ---- weight issue, DIET = true ----

# M:597-601: if (iss_j < n_tot) { iss_seek(); iss_j += iss_rem; } (iss_j, the run end, is the cursor)
def dt_seek(c: Bool, +ctx: Spec.Ctx, +je: Nat, +r1: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      DT{Nat.add(je, Spec.seek(Spec.ctx_phs(ctx), je)), Spec.seek(Spec.ctx_phs(ctx), je), je, 0n}
    case False{}:
      DT{je, r1, run, k}

# M:594-603: if (--iss_rem == 0) { ... } else iss_ptr += iss_row;
def dt_end(c: Bool, +ctx: Spec.Ctx, +je: Nat, +r1: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      dt_seek(Nat.is_lt(je, Spec.ctx_n(ctx)), ctx, je, r1, run, k)
    case False{}:
      DT{je, r1, run, 1n+k}

# M:591: if (iss_rem > 0) { cp_async_stream(...); ... }
def dt_step(c: Bool, +ctx: Spec.Ctx, +je: Nat, +rem: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      dt_end(Nat.is_eq(Nat.sub(rem, 1n), 0n), ctx, je, Nat.sub(rem, 1n), run, k)
    case False{}:
      DT{je, rem, run, k}

# G:404-408: if (iss_j < n_iter) { iss_ptr = w_src(iss_g); iss_left = min(KT, n_iter - iss_j); }
def dg_src(c: Bool, +ctx: Spec.Ctx, +j1: Nat, +g1: Nat, +l1: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      DG{j1, 0n, g1, Nat.min(Spec.ctx_kt(ctx), Nat.sub(Spec.ctx_n(ctx), j1)), g1, 0n}
    case False{}:
      DG{j1, 0n, g1, l1, run, k}

# G:398-410: if (--iss_left == 0) { iss_j += KT - iss_kt; iss_kt = 0; iss_g++; ... }
# else iss_ptr += row_bytes;
def dg_end(c: Bool, +ctx: Spec.Ctx, +jd: Nat, +ktd: Nat, +gd: Nat, +l1: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      +j1 = Nat.add(jd, Nat.sub(Spec.ctx_kt(ctx), ktd))
      dg_src(Nat.is_lt(j1, Spec.ctx_n(ctx)), ctx, j1, 1n+gd, l1, run, k)
    case False{}:
      DG{jd, ktd, gd, l1, run, 1n+k}

# G:395: if (iss_left > 0) { cp_async_stream(...); ... }
def dg_step(c: Bool, +ctx: Spec.Ctx, +jd: Nat, +ktd: Nat, +gd: Nat, +left: Nat, +run: Nat, +k: Nat) -> DIM:
  match c:
    case True{}:
      dg_end(Nat.is_eq(Nat.sub(left, 1n), 0n), ctx, jd, ktd, gd, Nat.sub(left, 1n), run, k)
    case False{}:
      DG{jd, ktd, gd, left, run, k}

# The weight copy of an iteration into ring byte offset io (ring_lane + iss_off).
def d_we(+io: Nat, +ctx: Spec.Ctx, dim: DIM) -> Spec.WE:
  match dim:
    case DT{je, rem, run, k}:
      Spec.wsel(Nat.is_lt(0n, rem), Spec.Iss{io, run, k})
    case DG{jd, ktd, gd, left, run, k}:
      Spec.wsel(Nat.is_lt(0n, left), Spec.Iss{io, run, k})

def d_next(+ctx: Spec.Ctx, dim: DIM) -> DIM:
  match dim:
    case DT{+je, +rem, +run, +k}:
      dt_step(Nat.is_lt(0n, rem), ctx, je, rem, run, k)
    case DG{+jd, +ktd, +gd, +left, +run, +k}:
      dg_step(Nat.is_lt(0n, left), ctx, jd, ktd, gd, left, run, k)

# M:647-652: after the loop iss_j -= iss_rem; cur_slot = cur_off / W_STAGE; iss_slot = iss_off / W_STAGE.
# (m16g: nothing flows out.)
def d_exit(+co: Nat, +io: Nat, +ws: Nat, dim: DIM) -> Spec.Out:
  match dim:
    case DT{je, +rem, run, k}:
      Spec.Cont{Spec.St{Nat.div(co, ws), Nat.div(io, ws), Nat.sub(je, rem), rem, run, k}}
    case DG{jd, ktd, gd, left, run, k}:
      Spec.End{}

# ---- the main loop, DIET = true ----

# The loop body over the skeleton events (M:585-617, T:453-485, G:230-289); jc = it - s.
def dwalk(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx,
    +co: Nat, +io: Nat, +xo: Nat, +dim: DIM) -> Spec.Res:
  match evs:
    case Nil{}:
      Spec.Res{Nil{}, d_exit(co, io, ws, dim)}
    case ev <> rest:
      match ev:
        case PSpec.Tile{g, it}:
          Spec.cons(Spec.It{dchunk(xo, Nat.sub(it, s), xr, xi), d_we(io, ctx, dim), co, xo, dfold(xo, xr, fo, xi)},
            dwalk(rest, s, pf, xr, fo, ws, xi, ctx, dring(co, pf, ws), dring(io, pf, ws), dxnext(xo, xr, xi),
              d_next(ctx, dim)))
        case PSpec.Flush{g}:
          Spec.cons(Spec.Seg{g}, dwalk(rest, s, pf, xr, fo, ws, xi, ctx, co, io, xo, dim))

# M:553-653 run_phase(ph), DIET = true: cur_off = cur_slot * W_STAGE; iss_off = iss_slot * W_STAGE;
# x_off = 0; iss_j += iss_rem; then the loop.
def diet_phase(+ph: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, +st: Spec.St)
    -> Spec.Res:
  match ph:
    case Spec.Ph{s, n, kt}:
      match st:
        case Spec.St{cs, qs, ij, rem, run, k}:
          dwalk(dmainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs, ws), Nat.mul(qs, ws), 0n,
            DT{Nat.add(ij, rem), rem, run, k})

# ---- kernel compositions (the spec's, with the DIET = true run_phase) ----

def diet_then(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +ctx: Spec.Ctx) -> List<&2, Spec.Ev>:
  match r:
    case Spec.Res{e, +o}:
      List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, Spec.out_evs(o),
        Spec.res_all(diet_phase(p, pf, xr, fo, ws, xi, ctx, Spec.set_cs(cr, Spec.out_st(o))))))

def diet_then2(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +q: Spec.Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat,
    +ws: Nat, +xi: Nat, +ctx: Spec.Ctx) -> List<&2, Spec.Ev>:
  match r:
    case Spec.Res{e, +o}:
      List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, Spec.out_evs(o),
        diet_then(diet_phase(p, pf, xr, fo, ws, xi, ctx, Spec.set_cs(cr, Spec.out_st(o))), q, cq, pf, xr, fo,
          ws, xi, ctx)))

def diet_mlp(+p1: Spec.Ph, +p2: Spec.Ph, +r2: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat)
    -> List<&2, Spec.Ev>:
  +phs = {[p1, p2] : List<&2, Spec.Ph>}
  List.append(&2, Spec.Ev, Spec.pro(Nat.sub(pf, 1n), 0n, ws, Spec.t_ctx(phs), Spec.t_init(phs)),
    diet_then(diet_phase(p1, pf, xr, fo, ws, xi, Spec.t_ctx(phs),
        Spec.st_of(0n, Nat.sub(pf, 1n), Spec.pro_state(Nat.sub(pf, 1n), Spec.t_ctx(phs), Spec.t_init(phs)))),
      p2, r2, pf, xr, fo, ws, xi, Spec.t_ctx(phs)))

def diet_tail(+p0: Spec.Ph, +p1: Spec.Ph, +p2: Spec.Ph, +r1: Nat, +r2: Nat, +pf: Nat, +xr: Nat, +fo: Nat,
    +ws: Nat, +xi: Nat) -> List<&2, Spec.Ev>:
  +phs = {[p0, p1, p2] : List<&2, Spec.Ph>}
  List.append(&2, Spec.Ev, Spec.pro(Nat.sub(pf, 1n), 0n, ws, Spec.t_ctx(phs), Spec.t_init(phs)),
    diet_then2(diet_phase(p0, pf, xr, fo, ws, xi, Spec.t_ctx(phs),
        Spec.st_of(0n, Nat.sub(pf, 1n), Spec.pro_state(Nat.sub(pf, 1n), Spec.t_ctx(phs), Spec.t_init(phs)))),
      p1, r1, p2, r2, pf, xr, fo, ws, xi, Spec.t_ctx(phs)))

# G:375-378: cur_off = 0; iss_off = (PF - 1) * W_STAGE; x_off = 0;
# iss_left = min(KT - iss_kt, n_iter - iss_j) (from the prologue's cursor).
def dg_init(+KT: Nat, +N: Nat, rim: Spec.RIM) -> DIM:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      DG{0n, 0n, 0n, 0n, 0n, 0n}
    case Spec.RG{+ij, +kt, g, run, k}:
      DG{ij, kt, g, Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)), run, k}

def diet_m16g(+s: Nat, +n: Nat, +KT: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat)
    -> List<&2, Spec.Ev>:
  List.append(&2, Spec.Ev, Spec.pro(Nat.sub(pf, 1n), 0n, ws, Spec.GCtx{KT, n}, Spec.g_init(s, KT)),
    Spec.res_evs(dwalk(dmainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, Spec.GCtx{KT, n}, 0n,
      Nat.mul(Nat.sub(pf, 1n), ws), 0n,
      dg_init(KT, n, Spec.pro_state(Nat.sub(pf, 1n), Spec.GCtx{KT, n}, Spec.g_init(s, KT))))))
