# Bundle maps of the grouped swap-AB EXL3 m16 GEMM, ext patch 2102
# (2102-proj-m16-grouped-v2.patch, sha256 50f75e69ba3901e1a0c1111e1534d361493e7ee291151092ef7b45eed26f51fd),
# transcribed from the CUDA integer expressions over Nat. K = exllamav3_ext/quant/
# exl3_gemm_m16g_kernel.cuh, H = exllamav3_ext/quant/exl3_gemm_m16g.cu (new files: post-patch line
# numbers). The kernel keeps 2001 v2's core: its block partition, main loop, owner helper, split-K
# slots and distributed finish are the same C expressions over (groups, KT, total, G), so those
# defs below name the 2001 v2 model (bend/gemm_m16_partition.bend, V2) at the 2102 lines that
# repeat them; what 2102 adds is the multi-matrix column map (gbase prefix sums, matrix lookup,
# per-matrix strides), the prologue input transform and the host fit checks.
# C `int` / `size_t` arithmetic on the non-negative values used here is Nat arithmetic while no
# product overflows (the shapes are capped by shape_ok, H:98-105; the kernel widens b * total to
# int64); `>> 4` is `/ 16`. A bundle `ns` is the list of matrix widths n_i = B_i.size(1) * 16 (H:212)
# in launch order. The reference is gemm_m16_group_spec.bend; the laws are gemm_m16_group_laws.bend.
import Base
import ./gemm_m16_partition.bend as V2
import ./gemm_m16_partition_spec.bend as V2Spec
import ./gemm_m16_group_spec.bend as Spec

# ---- constants (2001 header: EXL3_M16_GW = 8 * 4 * 16, EXL3_M16_SLOT_FLOATS = 16 * GW; H:19-20)

# EXL3_M16_GW: columns per group
def gw() -> Nat:
  512n

# EXL3_M16_SLOT_FLOATS = 16 * EXL3_M16_GW: floats per split-K partial slot
def slot_floats() -> Nat:
  Nat.mul(16n, 512n)

# H:19 EXL3_M16G_SLOT_BYTES = 8 MB of slots at the start of the scratch
def slot_bytes() -> Nat:
  Nat.mul(Nat.mul(8n, 1024n), 1024n)

# H:20 EXL3_M16G_XH_BYTES = 1 MB of input-transform scratch after the slots
def xh_bytes() -> Nat:
  Nat.mul(1024n, 1024n)

# ---- column map

# H:203-227: groups = 0; for i < num_mats: { gbase[i] = groups; groups += n_i / EXL3_M16_GW; }
# then for (i = num_mats; i <= EXL3_M16G_MAX_MATS; ++i) gbase[i] = groups. gbase.go(i, ns, acc)
# is entry i of that array for the widths ns, the running `groups` in acc: entry 0 of the rest is
# acc, and past the last matrix every entry is acc.
def gbase.go(i: Nat, ns: List<&2, Nat>, acc: Nat) -> Nat:
  match i:
    case 0n:
      acc
    case 1n+j:
      match ns:
        case Nil{}:
          acc
        case n <> rest:
          gbase.go(j, rest, Nat.add(acc, Nat.div(n, 512n)))

# p.gbase[i] (K:34), read by index (K:68) or through exl3_m16g_gbase (K:53-60), i <= 4
def gbase(ns: List<&2, Nat>, +i: Nat) -> Nat:
  gbase.go(i, ns, 0n)

# H:189 num_mats = B.size()
def num_mats(ns: List<&2, Nat>) -> Nat:
  List.length(&2, Nat, ns)

# K:96 groups = exl3_m16g_gbase(p, EXL3_M16G_MAX_MATS)
def groups(ns: List<&2, Nat>) -> Nat:
  gbase(ns, 4n)

# K:95 KT = size_k >> 4
def kt(k: Nat) -> Nat:
  V2.kt(k)

# K:97 total = groups * KT; iteration x = group * KT + k-tile over all matrices (group-major)
def total(ns: List<&2, Nat>, k: Nat) -> Nat:
  Nat.mul(groups(ns), kt(k))

def mat.pick(ge: Bool, i: Nat, acc: Nat) -> Nat:
  match ge:
    case True{}:
      i
    case False{}:
      acc

# K:65-69: mat = 0; for (i = 1; i < EXL3_M16G_MAX_MATS; ++i) if (g >= p.gbase[i]) mat = i;
# `left` counts the remaining iterations.
def mat.go(left: Nat, +i: Nat, +ns: List<&2, Nat>, +g: Nat, acc: Nat) -> Nat:
  match left:
    case 0n:
      acc
    case 1n+l:
      mat.go(l, 1n+i, ns, g, mat.pick(Nat.is_ge(g, gbase(ns, i)), i, acc))

# K:63-70 exl3_m16g_mat(p, g) (K:112, K:153, K:345)
def mat(+ns: List<&2, Nat>, +g: Nat) -> Nat:
  mat.go(3n, 1n, ns, g, 0n)

# K:113 / K:346 gb = exl3_m16g_gbase(p, mat)
def gb(+ns: List<&2, Nat>, +g: Nat) -> Nat:
  gbase(ns, mat(ns, g))

# K:115 / K:348 local group g - gb of the owning matrix
def local(+ns: List<&2, Nat>, +g: Nat) -> Nat:
  Nat.sub(g, gb(ns, g))

# K:347 n_mat = (exl3_m16g_gbase(p, mat + 1) - gb) * GW: the owning matrix's width (output stride)
def nmat(+ns: List<&2, Nat>, +g: Nat) -> Nat:
  Nat.mul(Nat.sub(gbase(ns, 1n+mat(ns, g)), gb(ns, g)), 512n)

# ---- weight issue cursor (K:107-135)

# K:114 row_bytes = (gbase(mat + 1) - gb) * (GW / 16) * 128: bytes per 16-deep k-tile row of B[mat]
def row_bytes(+ns: List<&2, Nat>, +g: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.sub(gbase(ns, 1n+mat(ns, g)), gb(ns, g)), 32n), 128n)

# K:115 w_src(g) byte offset in B[mat]: (uint16_t*) B[mat] + ((g - gb) * (GW / 16) + warp *
# EXL3_M16_TILES_W) * 64 halves, then + lane * 16 bytes
def wsrc(+ns: List<&2, Nat>, +g: Nat, +warp: Nat, +lane: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(local(ns, g), 32n), Nat.mul(warp, 4n)), 128n), Nat.mul(lane, 16n))

# iss_ptr = B[mat] + off with the current row_bytes rb
type WPtr is Data:
  WPtr{mat: Nat, off: Nat, rb: Nat}

# The issue state: cursor (iss_g, iss_kt) and pointer
type Iss is Data:
  Iss{cur: V2.Cursor, ptr: WPtr}

def wsite.of(c: V2.Cursor, +ns: List<&2, Nat>, +warp: Nat, +lane: Nat) -> Iss:
  match c:
    case V2.Cursor{+g, +kt}:
      Iss{V2.Cursor{g, kt}, WPtr{mat(ns, g), Nat.add(wsrc(ns, g, warp, lane), Nat.mul(kt, row_bytes(ns, g))),
        row_bytes(ns, g)}}

# K:118-121: iss_g = s_b / KT; iss_kt = s_b - iss_g * KT; iss_ptr = w_src(iss_g) (+ lane * 16);
# iss_ptr += iss_kt * row_bytes: the cursor and pointer of iteration x computed directly
def wsite(+ns: List<&2, Nat>, +x: Nat, +KT: Nat, +warp: Nat, +lane: Nat) -> Iss:
  wsite.of(V2.decode(x, KT), ns, warp, lane)

# K:128-134 pointer update: on a group wrap (++iss_kt == KT) re-derive it with w_src(iss_g) only
# while iss_j < n_iter (`more`), else keep it; otherwise iss_ptr += row_bytes
def issue.ptr(wrap: Bool, more: Bool, +ns: List<&2, Nat>, +g1: Nat, +warp: Nat, +lane: Nat,
    p: WPtr) -> WPtr:
  match wrap:
    case True{}:
      match more:
        case True{}:
          WPtr{mat(ns, g1), wsrc(ns, g1, warp, lane), row_bytes(ns, g1)}
        case False{}:
          p
    case False{}:
      match p:
        case WPtr{m, o, +rb}:
          WPtr{m, Nat.add(o, rb), rb}

# K:124-135 issue_w with iss_j = j before the call: iss_j++; cursor step (K:128-131, 2001's);
# pointer update above with more = (j + 1 < n_iter)
def issue.step(st: Iss, +j: Nat, +n: Nat, +KT: Nat, +ns: List<&2, Nat>, +warp: Nat, +lane: Nat) -> Iss:
  match st:
    case Iss{c, p}:
      match c:
        case V2.Cursor{+g, +kt}:
          Iss{V2.advance(V2.Cursor{g, kt}, KT),
            issue.ptr(Nat.is_eq(1n+kt, KT), Nat.is_lt(1n+j, n), ns, 1n+g, warp, lane, p)}

# The issue state after j issues of a block starting at s_b = s with n_iter = n (K:117-121 start).
def issued(+j: Nat, +s: Nat, +n: Nat, +KT: Nat, +ns: List<&2, Nat>, +warp: Nat, +lane: Nat) -> Iss:
  match j:
    case 0n:
      wsite(ns, s, KT, warp, lane)
    case 1n+i:
      issue.step(issued(i, s, n, KT, ns, warp, lane), i, n, KT, ns, warp, lane)

# ---- block partition, main loop, split-K slots (2001 v2's expressions)

# K:100 s_b = (int64) b * total / G; K:101 e_b = start(b + 1)
def start(b: Nat, +total: Nat, G: Nat) -> Nat:
  V2.start(b, total, G)

# K:239 / K:334 exl3_m16_owner (2001 header, exl3_gemm_m16_kernel.cuh included at K:23); the host
# copy H:74-77 is the same expression
def owner(x: Nat, +total: Nat, +G: Nat) -> Nat:
  V2.owner(x, total, G)

# K:256-318: 2001 v2's rolled main loop (outer K:259 over g_cur from s_b / KT, seg_end K:261,
# inner K:264 over j, fold K:316, flush K:317)
def mainloop(+s: Nat, +e: Nat, +KT: Nat) -> List<&2, V2Spec.Ev>:
  V2.mainloop(s, e, KT)

# K:239 cidx base: owner(g * KT, total, G)
def b_lo(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  V2.b_lo(g, KT, total, G)

# K:334 owner((g + 1) * KT - 1, total, G)
def b_hi(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  V2.b_hi(g, KT, total, G)

# K:334 nc = owner((g + 1) * KT - 1) - owner(g * KT) + 1
def nc(+g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  V2.nc(g, KT, total, G)

# K:240 partial slot of block b for group g: g * p.max_contrib + (b - owner(g * KT)); p.max_contrib
# = H:248 max_contrib(groups, KT, G)
def address(g: Nat, +mc: Nat, b: Nat, lo: Nat) -> Nat:
  V2.address(g, mc, b, lo)

# H:80-90 max_contrib(groups, KT, G): total = groups * KT (H:82), mc = 1, running maximum of
# nc(g) over g < groups (H:84-88)
def max_contrib(+groups: Nat, +KT: Nat, +G: Nat) -> Nat:
  V2.max_contrib(groups, KT, Nat.mul(groups, KT), G)

# K:240 + K:249: float index of a flushed partial element, token row `row` (K:248), group column
# col = warp * 64 + (lane >> 2) + t * 16 + (c >> 1) * 8 (V2.col):
# (slot * EXL3_M16_SLOT_FLOATS + warp * 64 + (lane >> 2)) + row * GW + t * 16 + (c >> 1) * 8
def flush_float(slot: Nat, row: Nat, col: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(slot, slot_floats()), Nat.mul(row, 512n)), col)

# K:335 + K:339: float index read by the finishing lane: s0 = g * max_contrib * SLOT_FLOATS + r * GW
# + ch * 128, slot c at s0 + c * SLOT_FLOATS, float4 `lane` element e < 4 (K:336, K:339)
def finish_float(g: Nat, +mc: Nat, c: Nat, r: Nat, ch: Nat, lane: Nat, e: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.add(Nat.mul(Nat.mul(g, mc), slot_floats()), Nat.mul(r, 512n)),
    Nat.mul(ch, 128n)), Nat.mul(c, slot_floats())), Nat.add(Nat.mul(lane, 4n), e))

# ---- distributed finish (K:325-367)

# K:326-327 CH = GW / 128; jobs = groups * size_m * CH
def jobs(groups: Nat, m: Nat) -> Nat:
  V2.jobs(groups, m)

# K:328 for (w = warp + EXL3_M16_WARPS * b; w < jobs; w += EXL3_M16_WARPS * G)
def jobloop(+b: Nat, +w: Nat, +G: Nat, +jobs: Nat) -> List<&2, Nat>:
  V2.jobloop(b, w, G, jobs)

# Number of (block b < count, warp < 8) whose K:328 loop visits job x.
def job_hits(+count: Nat, +x: Nat, +G: Nat, +jobs: Nat) -> Nat:
  V2.job_hits(count, x, G, jobs)

# K:330-333 g = w / (size_m * CH); rem = w - g * size_m * CH; r = rem / CH; ch = rem - r * CH
def job(+x: Nat, +m: Nat) -> V2Spec.Job:
  V2.job(x, m)

# K:335-342 (after the grid.sync K:321): v = slot 0, then v += slot c for c = 1 .. nc - 1
def arrive(order: List<&2, Nat>, ws: List<&2, V2Spec.Sum>, +lo: Nat) -> List<&2, V2Spec.Sum>:
  V2.arrive(order, ws, lo)

def finish(+ws: List<&2, V2Spec.Sum>, cnt: Nat) -> V2Spec.Sum:
  V2.finish(ws, cnt)

def place.of(j: V2Spec.Job, +ns: List<&2, Nat>) -> Spec.Place:
  match j:
    case V2Spec.Job{+g, r, ch}:
      Spec.Place{mat(ns, g), r, Nat.add(Nat.mul(Nat.sub(g, gb(ns, g)), 512n), Nat.mul(ch, 128n))}

# K:345-348: job x's output task: matrix mat = exl3_m16g_mat(p, g), token row r, first column
# col0 = (g - gb) * GW + ch * 128
def place(+ns: List<&2, Nat>, +x: Nat, +m: Nat) -> Spec.Place:
  place.of(job(x, m), ns)

# K:355 / K:363 element offset of the task's first output in C[mat] (row stride n_mat, K:347)
def out_off(+ns: List<&2, Nat>, +g: Nat, r: Nat, ch: Nat) -> Nat:
  Nat.add(Nat.mul(r, nmat(ns, g)), Nat.add(Nat.mul(Nat.sub(g, gb(ns, g)), 512n), Nat.mul(ch, 128n)))

# ---- prologue input transform (K:169-189)

# K:173 per_mat = size_m * size_k / 128
def per_mat(m: Nat, k: Nat) -> Nat:
  Nat.div(Nat.mul(m, k), 128n)

# K:174 total_warps = p.num_mats * per_mat
def total_warps(nm: Nat, +m: Nat, +k: Nat) -> Nat:
  Nat.mul(nm, per_mat(m, k))

# K:175-176 warps_grid = G * EXL3_M16_WARPS; for (w = warp + EXL3_M16_WARPS * b; w < total_warps;
# w += warps_grid): the K:328 loop shape (8 * G = G * 8)
def pro_loop(+b: Nat, +w: Nat, +G: Nat, +tw: Nat) -> List<&2, Nat>:
  V2.jobloop(b, w, G, tw)

def pro_hits(+count: Nat, +x: Nat, +G: Nat, +tw: Nat) -> Nat:
  V2.job_hits(count, x, G, tw)

# K:178 mat = w / per_mat
def pro_mat(+w: Nat, +pm: Nat) -> Nat:
  Nat.div(w, pm)

# K:179 r = w - mat * per_mat
def pro_r(+w: Nat, +pm: Nat) -> Nat:
  Nat.sub(w, Nat.mul(pro_mat(w, pm), pm))

# K:183 + H:243: xh[mat] + r * 128 with xh[i] = xh + (size_t) i * size_m * size_k: element offset
# of warp job w's 128 outputs in the input-transform scratch
def pro_xh(+m: Nat, +k: Nat, +w: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mul(pro_mat(w, per_mat(m, k)), m), k), Nat.mul(pro_r(w, per_mat(m, k)), 128n))

# K:182 input A + r * 128
def pro_a(+m: Nat, +k: Nat, +w: Nat) -> Nat:
  Nat.mul(pro_r(w, per_mat(m, k)), 128n)

# K:184 suh[mat] + (r * 128) % size_k
def pro_suh(+m: Nat, +k: Nat, +w: Nat) -> Nat:
  Nat.mod(Nat.mul(pro_r(w, per_mat(m, k)), 128n), k)

# ---- host fit checks

# H:109-113 launch_fits: groups * KT >= G && groups * max_contrib(groups, KT, G) *
# EXL3_M16_SLOT_FLOATS * sizeof(float) <= EXL3_M16G_SLOT_BYTES (TORCH_CHECKed at H:240 before
# every launch, part of the route predicate H:172). The byte budget is the parameter sb; the patch
# passes sb = slot_bytes() (H:19). Keeping it a parameter makes the laws hold for any budget and
# keeps the 8 MB literal out of the checker (closed Nats are unary there).
def launch_fits(+groups: Nat, +KT: Nat, +G: Nat, +sb: Nat) -> Bool:
  Bool.and(Nat.is_ge(Nat.mul(groups, KT), G),
    Nat.is_le(Nat.mul(Nat.mul(Nat.mul(groups, max_contrib(groups, KT, G)), slot_floats()), 4n), sb))

def widths_ok(ns: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> rest:
      Bool.and(Nat.is_le(512n, n), Bool.and(Nat.is_eq(Nat.mod(n, 512n), 0n), widths_ok(rest)))

# H:98-105 shape_ok (the trellis flags K == 4, mul1, !mcg of H:101 do not enter these maps):
# 1 .. 4 matrices, 1 <= size_m <= 16, size_k >= 128 and % 128 == 0, every n >= GW and % GW == 0,
# num_mats * size_m * size_k * sizeof(half) <= xb, the patch's xb = xh_bytes() (H:20)
def shape_ok(+m: Nat, +k: Nat, +ns: List<&2, Nat>, +xb: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, num_mats(ns)),
    Bool.and(Nat.is_le(num_mats(ns), 4n),
      Bool.and(Nat.is_le(1n, m),
        Bool.and(Nat.is_le(m, 16n),
          Bool.and(Nat.is_le(128n, k),
            Bool.and(Nat.is_eq(Nat.mod(k, 128n), 0n),
              Bool.and(widths_ok(ns),
                Nat.is_le(Nat.mul(Nat.mul(Nat.mul(num_mats(ns), m), k), 2n), xb))))))))
