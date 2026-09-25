# Schedule of ext 8202, the persistent layer tail (one cooperative launch per layer): o_proj /
# out_proj as an m16 split-K GEMM (phase 0, K0 = A -> N0 = H, one matrix), finish-0 jobs (slot sums,
# residual add, per-row sum-of-squares partials), norm jobs (RMSNorm + 8201's gate/up input
# transforms), then ext 8201's fused MLP (bend/mlp_m16_sched.bend) unchanged. Nat model, generic in
# the grid G, the o_proj input width A (K0), the hidden size H (N0 = 8201's gate/up K) and the
# intermediate size I; the served instance G = 164, A = 6144, H = 5120, I = 17408, PF = 8 is fixed
# below and printed by bend/TAIL_M16_SCHED_TABLE.bend. Phase 0 reuses the patch 2001 v2 partition
# (gemm_m16_partition.bend: start, owner, nc, max_contrib, mainloop) unchanged, exactly as 8201's
# phases 1 and 2 do. Laws: tail_m16_sched_laws.bend.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./tail_m16_sched_spec.bend as Spec

# Served instance: 8201's grid (164 = 82 SMs x 2), hidden and intermediate sizes and ring depth;
# the o_proj / out_proj input width K0 = 6144.
def grid() -> Nat:
  Mlp.grid()

def kin() -> Nat:
  6144n

def hidden() -> Nat:
  Mlp.hidden()

def inter() -> Nat:
  Mlp.inter()

def pf() -> Nat:
  Mlp.pf()

# ---- phase 0: one matrix of K0 = A x N0 = H, groups of 512 output columns ----

def kt0(+A: Nat) -> Nat:
  Part.kt(A)

def ng0(+H: Nat) -> Nat:
  Part.ng(H)

def total0(+A: Nat, +H: Nat) -> Nat:
  Part.total(1n, H, A)

# Block b's slice [s0, s0 + n0) of the T0 group-major (group, k-tile) iterations.
def s0(+G: Nat, +A: Nat, +H: Nat, +b: Nat) -> Nat:
  Part.start(b, total0(A, H), G)

def e0(+G: Nat, +A: Nat, +H: Nat, +b: Nat) -> Nat:
  Part.start(1n+b, total0(A, H), G)

def n0(+G: Nat, +A: Nat, +H: Nat, +b: Nat) -> Nat:
  Nat.sub(e0(G, A, H, b), s0(G, A, H, b))

# Workspace slots per group: v2's max_contrib (host) of the phase-0 partition.
def mc0(+G: Nat, +A: Nat, +H: Nat) -> Nat:
  Part.max_contrib(Part.groups(1n, H), kt0(A), total0(A, H), G)

# Lowest contributor of group g: owner(g * KT0).
def lo0(+G: Nat, +A: Nat, +H: Nat, +g: Nat) -> Nat:
  Part.b_lo(g, kt0(A), total0(A, H), G)

# Contributor count of group g (the F0 slot-sum length).
def nc0(+G: Nat, +A: Nat, +H: Nat, +g: Nat) -> Nat:
  Part.nc(g, kt0(A), total0(A, H), G)

# Workspace address of block b's flush of group g: slot (g, b - owner(g * KT0)) = g * MC0 + b - lo.
def slot0(+G: Nat, +A: Nat, +H: Nat, +g: Nat, +b: Nat) -> Nat:
  Part.address(g, mc0(G, A, H), b, lo0(G, A, H, g))

# ---- the weight ring: one stream of n0 + n1 + n2 tiles per warp ----
# Tile i of the stream lives in slot i mod PF (8201's Mlp.slot); the prologue issues tiles
# 0 .. PF - 2, step j issues tile j + PF - 1 then consumes tile j (8201's Mlp.issue_step), straight
# across the phase boundaries. Phase 1 starts at stream tile n0, phase 2 at n0 + n1; ring1 / ring2
# are the slots of those first tiles.
def ring1(+G: Nat, +A: Nat, +H: Nat, +b: Nat) -> Nat:
  Mlp.slot(n0(G, A, H, b), pf())

def ring2(+G: Nat, +A: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Mlp.slot(Nat.add(n0(G, A, H, b), Mlp.n1(G, H, I, b)), pf())

def stream(+G: Nat, +A: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.add(n0(G, A, H, b), Mlp.n1(G, H, I, b)), Mlp.n2(G, H, I, b))

# ---- F0 and N jobs (m token rows) ----

# 128-column chunks of a row: 4 per 512-column group (NCH = 40 at H = 5120).
def nch(+H: Nat) -> Nat:
  Nat.mul(ng0(H), 4n)

# F0 jobs (group, row, chunk): NG0 * m * 4 = 40 m; N jobs (row, chunk): m * NCH = 40 m.
def jobs0(+H: Nat, +m: Nat) -> Nat:
  Part.jobs(ng0(H), m)

def jobsn(+H: Nat, +m: Nat) -> Nat:
  Nat.mul(m, nch(H))

# Owner of job x (F0 and N alike): warp x div G of block x mod G.
def job_block(+G: Nat, +x: Nat) -> Nat:
  Nat.mod(x, G)

def job_warp(+G: Nat, +x: Nat) -> Nat:
  Nat.div(x, G)

# The job index warp w of block b computes (it runs it iff it is below the job count).
def warp_job(+G: Nat, +b: Nat, +w: Nat) -> Nat:
  Nat.add(Nat.mul(w, G), b)

def warp_jobs.keep(inside: Bool, +x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match inside:
    case True{}:
      x <> rest
    case False{}:
      rest

# Jobs run by warps n - 1, ..., 0 of block b, out of J jobs.
def warp_jobs.go(+n: Nat, +G: Nat, +J: Nat, +b: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+w:
      +x = warp_job(G, b, w)
      warp_jobs.keep(Nat.is_lt(x, J), x, warp_jobs.go(w, G, J, b))

# Jobs run by the 8 warps of block b.
def warp_jobs(+G: Nat, +J: Nat, +b: Nat) -> List<&2, Nat>:
  warp_jobs.go(8n, G, J, b)

# F0 job decode: g = x div 4m, r = (x mod 4m) div 4, ch = x mod 4.
def f0_job(+x: Nat, +m: Nat) -> PSpec.Job:
  PSpec.Job{Nat.div(x, Nat.mul(m, 4n)), Nat.div(Nat.mod(x, Nat.mul(m, 4n)), 4n), Nat.mod(x, 4n)}

# The sum-of-squares partial F0 job (g, r, ch) writes: ssq[r * NCH + 4 g + ch].
def f0_psum(+H: Nat, j: PSpec.Job) -> Nat:
  match j:
    case PSpec.Job{g, r, ch}:
      Nat.add(Nat.mul(r, nch(H)), Nat.add(Nat.mul(g, 4n), ch))

# Norm job decode: row r = x div NCH, chunk c = x mod NCH (columns [128 c, 128 c + 128)).
def norm_row(+H: Nat, +x: Nat) -> Nat:
  Nat.div(x, nch(H))

def norm_col(+H: Nat, +x: Nat) -> Nat:
  Nat.mod(x, nch(H))

def norm_reads.go(left: Nat, +i: Nat) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      i <> norm_reads.go(rest, 1n+i)

# The partials a norm job of row r sums (xor butterfly over ssq[r * NCH + 0 .. NCH - 1]).
def norm_reads(+H: Nat, +r: Nat) -> List<&2, Nat>:
  norm_reads.go(nch(H), Nat.mul(r, nch(H)))

# ---- events of block b, in program order ----

def tag_work(evs: List<&2, PSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      Spec.Work{ev} <> tag_work(more, rest)

def tag_fin(xs: List<&2, Nat>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match xs:
    case Nil{}:
      rest
    case x <> more:
      Spec.Fin{x} <> tag_fin(more, rest)

def tag_norm(xs: List<&2, Nat>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match xs:
    case Nil{}:
      rest
    case x <> more:
      Spec.Norm{x} <> tag_norm(more, rest)

def tag_sync(evs: List<&2, MSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      Spec.Sync{ev} <> tag_sync(more, rest)

# Barrier S; the phase-0 main loop over [s0, e0) (flushes write workspace slots, no counters);
# barrier A; this block's F0 jobs; barrier B; its N jobs; barrier C; ext 8201's events of the block
# (counter signals and waits, unchanged); barrier D.
def events(+G: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +b: Nat) -> List<&2, Spec.Ev>:
  Spec.Bar{0n} <> tag_work(Part.mainloop(s0(G, A, H, b), e0(G, A, H, b), kt0(A)),
    Spec.Bar{1n} <> tag_fin(warp_jobs(G, jobs0(H, m), b),
      Spec.Bar{2n} <> tag_norm(warp_jobs(G, jobsn(H, m), b),
        Spec.Bar{3n} <> tag_sync(Mlp.events(G, H, I, b), [Spec.Bar{4n}]))))
