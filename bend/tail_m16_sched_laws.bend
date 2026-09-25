# Semantic obligations for the ext 8202 layer-tail schedule model bend/tail_m16_sched.bend (the Nat
# model whose table bend/TAIL_M16_SCHED_TABLE.bend prints). Every law is about that Bend model; the
# CUDA kernel's conformance to it (reading the table, grid-barrier and __ldcg/cp.async memory
# ordering, fp32 values, co-residency of the G blocks, int overflow) is outside this contract.
# Generic laws hold for every grid G >= 1, o_proj input width A, hidden size H and intermediate size
# I under the stated shape preconditions, for every block, iteration, token-row count m, job,
# partial index and counter; the ring laws are generic in the stream position (and in PF where it is
# a parameter). Instance-only laws (stated with served_* hypotheses): mc0_served (MC0 = 18 at
# G = 164, A = 6144, H = 5120) and jobs_fit_served (40 m <= 8 G for m <= 8 at the served G and H).
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_sched_laws.bend as MLaws
import ./tail_m16_sched.bend as Impl
import ./tail_m16_sched_spec.bend as Spec

# Grid-wide runs of F0 job x / norm job x over the event lists of blocks 0 .. n - 1.
def fin_total(+G: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(fin_total(G, A, H, I, m, b, x), Spec.fin_hits(Impl.events(G, A, H, I, m, b), x))

def norm_total(+G: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +n: Nat, +x: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(norm_total(G, A, H, I, m, b, x), Spec.norm_hits(Impl.events(G, A, H, I, m, b), x))

# F0 jobs x < n writing sum-of-squares partial i.
def psum_writers(+H: Nat, +m: Nat, +n: Nat, +i: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+x:
      Nat.add(psum_writers(H, m, x, i),
        PSpec.bit(Nat.is_eq(Impl.f0_psum(H, Impl.f0_job(x, m)), i)))

# F0 jobs x < n of token row r writing partial i.
def row_writers(+H: Nat, +m: Nat, +n: Nat, +r: Nat, +i: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+x:
      Nat.add(row_writers(H, m, x, r, i),
        PSpec.bit(Bool.and(Nat.is_eq(Spec.job_row(Impl.f0_job(x, m)), r),
          Nat.is_eq(Impl.f0_psum(H, Impl.f0_job(x, m)), i))))

# Norm jobs x < n handling (row r, chunk c).
def norm_cells(+H: Nat, +n: Nat, +r: Nat, +c: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+x:
      Nat.add(norm_cells(H, x, r, c),
        PSpec.bit(Bool.and(Nat.is_eq(Impl.norm_row(H, x), r), Nat.is_eq(Impl.norm_col(H, x), c))))

# ---- (1) phase 0: exactly-once coverage, split-K order equals v2 ----

# Block b's table slice [s0, s0 + n0) is the set of o_proj iterations it owns in the v2 partition of
# T0; with phase0_exactly_once every iteration x < T0 lies in exactly one block's slice.
law phase0_slice_owned:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +b: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s0(G, A, H, b), x),
      Nat.is_lt(x, Nat.add(Impl.s0(G, A, H, b), Impl.n0(G, A, H, b)))) ==
    PSpec.owns(b, x, Impl.total0(A, H), G) : Bool}

law phase0_exactly_once:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total0(A, H)) == True{} : Bool}
  {PSpec.owners(G, x, Impl.total0(A, H), G) == 1n : Nat}

# The slice is v2's block range [start(b), start(b + 1)), and the phase-0 loop over it consumes the
# slice's iterations in ascending order and flushes each group after its last one, exactly as v2's
# mainloop_trace; gemm_m16_partition's slot / reduction_order laws then apply at mats = 1.
law phase0_v2:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  {Nat.add(Impl.s0(G, A, H, b), Impl.n0(G, A, H, b)) == Part.start(1n+b, Impl.total0(A, H), G)
    : Nat} &
  {Part.mainloop(Impl.s0(G, A, H, b), Nat.add(Impl.s0(G, A, H, b), Impl.n0(G, A, H, b)),
      Impl.kt0(A)) ==
    PSpec.trace(Impl.n0(G, A, H, b), Impl.s0(G, A, H, b),
      Nat.add(Impl.s0(G, A, H, b), Impl.n0(G, A, H, b)), Impl.kt0(A)) : List<&2, PSpec.Ev>}

# The phase-0 events of block b's event list (all m, all I) are exactly v2's trace of its slice.
law phase0_events:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  {Spec.works(Impl.events(G, A, H, I, m, b)) ==
    PSpec.trace(Impl.n0(G, A, H, b), Impl.s0(G, A, H, b), Impl.e0(G, A, H, b), Impl.kt0(A))
    : List<&2, PSpec.Ev>}

# ---- (2) phase-0 workspace ----

# A contributor's slot b - owner(g * KT0) is below the group's contributor count nc, nc fits MC0, and
# the address g * MC0 + slot fits the NG0 * MC0 phase-0 slots ...
law phase0_slots:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for contributor: {PSpec.touches(b, g, Impl.kt0(A), Impl.total0(A, H), G) == True{} : Bool}
  {Nat.is_lt(Nat.sub(b, Impl.lo0(G, A, H, g)), Impl.nc0(G, A, H, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc0(G, A, H, g), Impl.mc0(G, A, H)) == True{} : Bool} &
  {Nat.is_lt(Impl.slot0(G, A, H, g, b), Nat.mul(Part.groups(1n, H), Impl.mc0(G, A, H))) == True{}
    : Bool}

# ... no two (group, contributor) flushes share an address ...
law phase0_slot_injective:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +g: Nat
  for +b: Nat
  for +h: Nat
  for +c: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  for group_g: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for group_h: {Nat.is_lt(h, Part.groups(1n, H)) == True{} : Bool}
  for touch_b: {PSpec.touches(b, g, Impl.kt0(A), Impl.total0(A, H), G) == True{} : Bool}
  for touch_c: {PSpec.touches(c, h, Impl.kt0(A), Impl.total0(A, H), G) == True{} : Bool}
  for same: {Impl.slot0(G, A, H, g, b) == Impl.slot0(G, A, H, h, c) : Nat}
  {g == h : Nat} & {b == c : Nat}

# ... and at the served instance MC0 is 18 (10 x 18 slots per token row block of the workspace).
law mc0_served:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for served_g: {G == Impl.grid() : Nat}
  for served_a: {A == Impl.kin() : Nat}
  for served_h: {H == Impl.hidden() : Nat}
  {Impl.mc0(G, A, H) == 18n : Nat}

# ---- (3) the weight ring over the n0 + n1 + n2 stream ----

# ring1 / ring2 are the slots of stream tiles n0 and n0 + n1, the first tiles of phases 1 and 2:
# a phase-local cursor started at ring_k meets tile t of phase k in the slot the stream put it in.
law ring_slots:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +t: Nat
  {Mlp.slot(Nat.add(Impl.ring1(G, A, H, b), t), Impl.pf()) ==
    Mlp.slot(Nat.add(Impl.n0(G, A, H, b), t), Impl.pf()) : Nat} &
  {Mlp.slot(Nat.add(Impl.ring2(G, A, H, I, b), t), Impl.pf()) ==
    Mlp.slot(Nat.add(Nat.add(Impl.n0(G, A, H, b), Mlp.n1(G, H, I, b)), t), Impl.pf()) : Nat}

# Every stream tile i (of any phase) is issued no later than the step that consumes it, and the
# next tile of its slot, i + PF, is issued at step i + 1, strictly after tile i was consumed.
law ring_stream:
  for +i: Nat
  {Nat.is_le(Mlp.issue_step(i, Impl.pf()), i) == True{} : Bool} &
  {Mlp.slot(Nat.add(i, Impl.pf()), Impl.pf()) == Mlp.slot(i, Impl.pf()) : Nat} &
  {Mlp.issue_step(Nat.add(i, Impl.pf()), Impl.pf()) == 1n+i : Nat}

# No two tiles in flight together (i and i + d, 0 < d < PF) share a slot.
law ring_in_flight_distinct:
  for +i: Nat
  for +d: Nat
  for +pf: Nat
  for pos: {Nat.is_lt(0n, d) == True{} : Bool}
  for near: {Nat.is_lt(d, pf) == True{} : Bool}
  {Nat.is_eq(Mlp.slot(Nat.add(i, d), pf), Mlp.slot(i, pf)) == False{} : Bool}

# The first PF - 1 tiles of phase 1 are issued during phase-0 steps (before barrier A), and the
# first PF - 1 tiles of phase 2 during phase-0 / phase-1 steps.
law ring_prefetch:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +t: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total0(A, H)) == True{} : Bool}
  for early: {Nat.is_lt(1n+t, Impl.pf()) == True{} : Bool}
  {Nat.is_lt(Mlp.issue_step(Nat.add(Impl.n0(G, A, H, b), t), Impl.pf()), Impl.n0(G, A, H, b)) ==
    True{} : Bool} &
  {Nat.is_lt(Mlp.issue_step(Nat.add(Nat.add(Impl.n0(G, A, H, b), Mlp.n1(G, H, I, b)), t),
      Impl.pf()), Nat.add(Impl.n0(G, A, H, b), Mlp.n1(G, H, I, b))) == True{} : Bool}

# ---- (4) F0 and N jobs ----

# At the served G and H, 40 m F0 jobs and 40 m N jobs fit the 8 G warps for every m <= 8.
law jobs_fit_served:
  for +G: Nat
  for +H: Nat
  for +m: Nat
  for served_g: {G == Impl.grid() : Nat}
  for served_h: {H == Impl.hidden() : Nat}
  for rows: {Nat.is_le(m, 8n) == True{} : Bool}
  {Nat.is_le(Impl.jobs0(H, m), Nat.mul(8n, G)) == True{} : Bool} &
  {Nat.is_le(Impl.jobsn(H, m), Nat.mul(8n, G)) == True{} : Bool}

# The owner of job x < J <= 8 G (block x mod G, warp x div G) is a warp of the grid, and it is the
# warp whose job index is x.
law job_owner:
  for +G: Nat
  for +J: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(J, Nat.mul(8n, G)) == True{} : Bool}
  for inside: {Nat.is_lt(x, J) == True{} : Bool}
  {Nat.is_lt(Impl.job_block(G, x), G) == True{} : Bool} &
  {Nat.is_lt(Impl.job_warp(G, x), 8n) == True{} : Bool} &
  {Impl.warp_job(G, Impl.job_block(G, x), Impl.job_warp(G, x)) == x : Nat}

# Over the whole grid's event lists every F0 job x < 40 m (every norm job x < 40 m) runs exactly
# once, and no job past the end runs.
law fin_exactly_once:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(Impl.jobs0(H, m), Nat.mul(8n, G)) == True{} : Bool}
  {fin_total(G, A, H, I, m, G, x) == PSpec.bit(Nat.is_lt(x, Impl.jobs0(H, m))) : Nat}

law norm_exactly_once:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(Impl.jobsn(H, m), Nat.mul(8n, G)) == True{} : Bool}
  {norm_total(G, A, H, I, m, G, x) == PSpec.bit(Nat.is_lt(x, Impl.jobsn(H, m))) : Nat}

# F0 decode is a bijection from [0, NG0 * m * 4) onto (group < NG0, row < m, chunk < 4): every job
# decodes in range and back to itself ...
law f0_decode:
  for +H: Nat
  for +m: Nat
  for +x: Nat
  for inside: {Nat.is_lt(x, Impl.jobs0(H, m)) == True{} : Bool}
  {PSpec.job_ok(Impl.f0_job(x, m), Impl.ng0(H), m) == True{} : Bool} &
  {PSpec.encode(Impl.f0_job(x, m), m) == x : Nat}

# ... and every (group, row, chunk) in range is the decode of its own job number.
law f0_encode:
  for +H: Nat
  for +m: Nat
  for +j: PSpec.Job
  for ok: {PSpec.job_ok(j, Impl.ng0(H), m) == True{} : Bool}
  {Impl.f0_job(PSpec.encode(j, m), m) == j : PSpec.Job} &
  {Nat.is_lt(PSpec.encode(j, m), Impl.jobs0(H, m)) == True{} : Bool}

# Every sum-of-squares partial i < m * NCH is written by exactly one F0 job, and no other index is
# written.
law f0_partials_once:
  for +H: Nat
  for +m: Nat
  for +i: Nat
  for shaped: {Nat.is_le(512n, H) == True{} : Bool}
  {psum_writers(H, m, Impl.jobs0(H, m), i) == PSpec.bit(Nat.is_lt(i, Impl.jobsn(H, m))) : Nat}

# The partials a norm job of row r < m reads are exactly the ones written by row r's F0 jobs, each
# written once: an index the norm job reads has one row-r writer, any other index has none.
law norm_reads_partials:
  for +H: Nat
  for +m: Nat
  for +r: Nat
  for +i: Nat
  for shaped: {Nat.is_le(512n, H) == True{} : Bool}
  for row: {Nat.is_lt(r, m) == True{} : Bool}
  {row_writers(H, m, Impl.jobs0(H, m), r, i) ==
    PSpec.bit(MSpec.member(Impl.norm_reads(H, r), i)) : Nat}

# Every (row r < m, chunk c < NCH) is handled by exactly one norm job, and nothing else is.
law norm_cells_once:
  for +H: Nat
  for +m: Nat
  for +r: Nat
  for +c: Nat
  for shaped: {Nat.is_le(512n, H) == True{} : Bool}
  {norm_cells(H, Impl.jobsn(H, m), r, c) ==
    PSpec.bit(Bool.and(Nat.is_lt(r, m), Nat.is_lt(c, Impl.nch(H)))) : Nat}

# The NCH chunks of 128 columns tile a row of H columns exactly (H a multiple of 512).
law nch_covers:
  for +H: Nat
  for groups: {Nat.mod(H, 512n) == 0n : Nat}
  {Nat.mul(Impl.nch(H), 128n) == H : Nat}

# ---- (5) deadlock freedom given co-residency ----

# Every block runs the same grid-barrier sequence S, A, B, C, D ...
law same_barriers:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  {Spec.bars(Impl.events(G, A, H, I, m, b)) == Spec.bar_seq() : List<&2, Nat>}

# ... with its phase-0 work between S and A, F0 jobs between A and B, N jobs between B and C, and
# every counter signal / wait strictly between C and D ...
law staged:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  {Spec.staged(Impl.events(G, A, H, I, m, b), 0n) == True{} : Bool}

# ... and its counter events are exactly ext 8201's event list of the block, unchanged ...
law embeds_8201:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  {Spec.syncs(Impl.events(G, A, H, I, m, b)) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>}

# ... so 8201's stratification carries over: levels never decrease in a block, every signal of any
# block d on counter c lies below gate_level(c) and every wait of any block b on c at or above it.
law sync_levels:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  for +d: Nat
  for +c: MSpec.Ctr
  {MSpec.ordered(Spec.syncs(Impl.events(G, A, H, I, m, b)), 0n) == True{} : Bool} &
  {MSpec.sigs_below(Spec.syncs(Impl.events(G, A, H, I, m, d)), c, MLaws.gate_level(c)) == True{}
    : Bool} &
  {MSpec.waits_from(Spec.syncs(Impl.events(G, A, H, I, m, b)), c, MLaws.gate_level(c)) == True{}
    : Bool}
