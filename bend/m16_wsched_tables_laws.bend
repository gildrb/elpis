# Table obligations for ext 8205's slot-weighted 8201 / 8202 schedule (bend/m16_wsched.bend; the flat
# table bend/M16_WSCHED_TABLE.bend prints and exl3_m16_wsched.h / gen_sched.py build), complementing
# m16_wsched_laws.bend (coverage, slots, counters, levels, wait lists, finishers, program order):
#   (1) per phase, the block slices partition [0, T): start 0, contiguous, every slice non-empty,
#       the last one ends at T;
#   (2) per phase, the table's first-contributor / contributor-count fields (fc, nc) are exactly the
#       blocks whose slice meets the group, 1 <= nc <= mc;
#   (3) the ring offsets are the ring slots of the stream tile that starts each phase, below PF;
#   (4) every partial slot lies in its phase's region of the m16 workspace, and under the host's
#       workspace check every byte of it lies below the workspace size;
#   (5) equal weights reproduce the ext 8201 / 8202 tables and the 8202 tail program;
#   (6) the tail program's split boundaries, barriers and counter events do not depend on the token-row
#       count m (row invariance), only on the block, the shapes and the weights.
# Generic in G, nsm, the shapes (A = o_proj K0, H, I), the weights and every block / group / pair /
# stream position, for both table kinds (0 = standalone 8201 MLP, 1 = tail), under the host guard
# Wp.weights_valid of each phase used (the extension refuses other weights) and the shape hypotheses
# of the 8201 laws. Every law is about the Bend model; the kernel's conformance to the table it reads,
# int overflow and the memory model are outside this contract.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./tail_m16_sched.bend as Tail
import ./tail_m16_sched_spec.bend as TSpec
import ./m16_wsched.bend as Impl
import ./m16_wsched_spec.bend as Spec

# ---- (1) the slices partition [0, T) ----

law wslices0:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +a0: Nat
  for +b0: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Impl.s0(G, nsm, A, H, a0, b0, 0n) == 0n : Nat} &
  {Impl.e0(G, nsm, A, H, a0, b0, b) == Impl.s0(G, nsm, A, H, a0, b0, 1n+b) : Nat} &
  {Nat.add(Impl.s0(G, nsm, A, H, a0, b0, b), Impl.n0(G, nsm, A, H, a0, b0, b)) ==
    Impl.e0(G, nsm, A, H, a0, b0, b) : Nat} &
  {Nat.is_lt(0n, Impl.n0(G, nsm, A, H, a0, b0, b)) == True{} : Bool} &
  {Impl.s0(G, nsm, A, H, a0, b0, G) == Tail.total0(A, H) : Nat}

law wslices1:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Impl.s1(G, nsm, H, I, a1, b1, 0n) == 0n : Nat} &
  {Impl.e1(G, nsm, H, I, a1, b1, b) == Impl.s1(G, nsm, H, I, a1, b1, 1n+b) : Nat} &
  {Nat.add(Impl.s1(G, nsm, H, I, a1, b1, b), Impl.n1(G, nsm, H, I, a1, b1, b)) ==
    Impl.e1(G, nsm, H, I, a1, b1, b) : Nat} &
  {Nat.is_lt(0n, Impl.n1(G, nsm, H, I, a1, b1, b)) == True{} : Bool} &
  {Impl.s1(G, nsm, H, I, a1, b1, G) == Mlp.total1(H, I) : Nat}

law wslices2:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Impl.s2(G, nsm, H, I, a2, b2, 0n) == 0n : Nat} &
  {Impl.e2(G, nsm, H, I, a2, b2, b) == Impl.s2(G, nsm, H, I, a2, b2, 1n+b) : Nat} &
  {Nat.add(Impl.s2(G, nsm, H, I, a2, b2, b), Impl.n2(G, nsm, H, I, a2, b2, b)) ==
    Impl.e2(G, nsm, H, I, a2, b2, b) : Nat} &
  {Nat.is_lt(0n, Impl.n2(G, nsm, H, I, a2, b2, b)) == True{} : Bool} &
  {Impl.s2(G, nsm, H, I, a2, b2, G) == Mlp.total2(H, I) : Nat}

# ---- (2) the fc / nc table fields are the contributors of each group ----

law wcontrib0:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +a0: Nat
  for +b0: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {WSpec.touches(b, g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0) ==
    Spec.in_range(b, Impl.fc0(G, nsm, A, H, a0, b0, g), Impl.nc0(G, nsm, A, H, a0, b0, g)) : Bool} &
  {WSpec.touch_count(G, g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0) ==
    Impl.nc0(G, nsm, A, H, a0, b0, g) : Nat} &
  {Nat.is_le(1n, Impl.nc0(G, nsm, A, H, a0, b0, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc0(G, nsm, A, H, a0, b0, g), Impl.mc0(G, nsm, A, H, a0, b0)) == True{} : Bool}

law wcontrib1:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {WSpec.touches(b, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1) ==
    Spec.in_range(b, Impl.fc1(G, nsm, H, I, a1, b1, g), Impl.nc1(G, nsm, H, I, a1, b1, g)) : Bool} &
  {WSpec.touch_count(G, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1) ==
    Impl.nc1(G, nsm, H, I, a1, b1, g) : Nat} &
  {Nat.is_le(1n, Impl.nc1(G, nsm, H, I, a1, b1, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc1(G, nsm, H, I, a1, b1, g), Impl.mc1(G, nsm, H, I, a1, b1)) == True{} : Bool}

law wcontrib2:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {WSpec.touches(b, g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2) ==
    Spec.in_range(b, Impl.fc2(G, nsm, H, I, a2, b2, g), Impl.nc2(G, nsm, H, I, a2, b2, g)) : Bool} &
  {WSpec.touch_count(G, g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2) ==
    Impl.nc2(G, nsm, H, I, a2, b2, g) : Nat} &
  {Nat.is_le(1n, Impl.nc2(G, nsm, H, I, a2, b2, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc2(G, nsm, H, I, a2, b2, g), Impl.mc2(G, nsm, H, I, a2, b2)) == True{} : Bool}

# ---- (3) ring offsets: the slot of the stream tile that starts each phase, below PF ----

# 8201: the phase-2 stream starts at tile n1; the tail: phase 1 at tile n0, phase 2 at n0 + n1.
law wring:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +a0: Nat
  for +b0: Nat
  for +a1: Nat
  for +b1: Nat
  for +b: Nat
  for +t: Nat
  {Nat.is_lt(Impl.ring2(G, nsm, H, I, a1, b1, b), Mlp.pf()) == True{} : Bool} &
  {Mlp.slot(Nat.add(Impl.ring2(G, nsm, H, I, a1, b1, b), t), Mlp.pf()) ==
    Mlp.slot(Nat.add(Impl.n1(G, nsm, H, I, a1, b1, b), t), Mlp.pf()) : Nat} &
  {Nat.is_lt(Impl.ring1(G, nsm, A, H, a0, b0, b), Mlp.pf()) == True{} : Bool} &
  {Mlp.slot(Nat.add(Impl.ring1(G, nsm, A, H, a0, b0, b), t), Mlp.pf()) ==
    Mlp.slot(Nat.add(Impl.n0(G, nsm, A, H, a0, b0, b), t), Mlp.pf()) : Nat} &
  {Nat.is_lt(Impl.tring2(G, nsm, A, H, I, a0, b0, a1, b1, b), Mlp.pf()) == True{} : Bool} &
  {Mlp.slot(Nat.add(Impl.tring2(G, nsm, A, H, I, a0, b0, a1, b1, b), t), Mlp.pf()) ==
    Mlp.slot(Nat.add(Nat.add(Impl.n0(G, nsm, A, H, a0, b0, b), Impl.n1(G, nsm, H, I, a1, b1, b)), t),
      Mlp.pf()) : Nat}

# ---- (4) workspace: each contributor's partial slot is inside its phase region and the workspace ----

# Phase 1 (both kinds): region [0, base2); the host check ws_bytes <= cap bounds every byte of it.
law wws1:
  for +kind: Nat
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +a0: Nat
  for +b0: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +g: Nat
  for +b: Nat
  for +cap: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for fits: {Nat.is_le(Impl.ws_bytes(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2), cap) == True{} : Bool}
  {Spec.in_range(Impl.slot1(G, nsm, H, I, a1, b1, g, b), 0n, Impl.base2(G, nsm, H, I, a1, b1)) ==
    True{} : Bool} &
  {Nat.is_le(Spec.slot_end(Impl.slot1(G, nsm, H, I, a1, b1, g, b), Wp.slot_floats()), cap) == True{} : Bool}

# Phase 2 (both kinds): region [base2, base0).
law wws2:
  for +kind: Nat
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +a0: Nat
  for +b0: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +g: Nat
  for +b: Nat
  for +cap: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for fits: {Nat.is_le(Impl.ws_bytes(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2), cap) == True{} : Bool}
  {Spec.in_range(Impl.slot2(G, nsm, H, I, a1, b1, a2, b2, g, b), Impl.base2(G, nsm, H, I, a1, b1),
    Nat.mul(Part.groups(1n, H), Impl.mc2(G, nsm, H, I, a2, b2))) == True{} : Bool} &
  {Nat.is_le(Spec.slot_end(Impl.slot2(G, nsm, H, I, a1, b1, a2, b2, g, b), Wp.slot_floats()), cap) ==
    True{} : Bool}

# Phase 0 (tail, kind 1): region [base0, ws_slots).
law wws0:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +a0: Nat
  for +b0: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +g: Nat
  for +b: Nat
  for +cap: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for fits: {Nat.is_le(Impl.ws_bytes(1n, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2), cap) == True{} : Bool}
  {Spec.in_range(Impl.slot0(G, nsm, A, H, I, a0, b0, a1, b1, a2, b2, g, b),
    Impl.base0(G, nsm, H, I, a1, b1, a2, b2),
    Nat.mul(Part.groups(1n, H), Impl.mc0(G, nsm, A, H, a0, b0))) == True{} : Bool} &
  {Nat.is_le(Spec.slot_end(Impl.slot0(G, nsm, A, H, I, a0, b0, a1, b1, a2, b2, g, b), Wp.slot_floats()),
    cap) == True{} : Bool}

# ---- (5) equal weights reproduce the ext 8201 / 8202 tables ----

# Phase 1 at (w, w): the block fields n1 / ring2, the pair targets and MC1 are 8201's.
law wuniform1:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +w: Nat
  for +b: Nat
  for +p: Nat
  for wpos: {Nat.is_lt(0n, w) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.n1(G, nsm, H, I, w, w, b) == Mlp.n1(G, H, I, b) : Nat} &
  {Impl.ring2(G, nsm, H, I, w, w, b) == Mlp.ring2(G, H, I, b) : Nat} &
  {Impl.exp_gate(G, nsm, H, I, w, w, p) == Mlp.exp_gate(G, H, I, p) : Nat} &
  {Impl.exp_up(G, nsm, H, I, w, w, p) == Mlp.exp_up(G, H, I, p) : Nat} &
  {Impl.mc1(G, nsm, H, I, w, w) == Mlp.mc1(G, H, I) : Nat}

# Phase 2 at (v, v): the block fields n2 / finish pair / rank / count / wait list / offset, the pair
# counts, first contributors and MC2 are 8201's.
law wuniform2:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +v: Nat
  for +b: Nat
  for +p: Nat
  for +g: Nat
  for vpos: {Nat.is_lt(0n, v) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.n2(G, nsm, H, I, v, v, b) == Mlp.n2(G, H, I, b) : Nat} &
  {Impl.fin_pair(G, nsm, H, I, v, v, b) == Mlp.fin_pair(G, H, I, b) : Nat} &
  {Impl.fin_rank(G, nsm, H, I, v, v, b) == Mlp.fin_rank(G, H, I, b) : Nat} &
  {Impl.fin_cnt(G, nsm, H, I, v, v, b) == Mlp.fin_cnt(G, H, I, b) : Nat} &
  {Impl.waits(G, nsm, H, I, v, v, b) == Mlp.waits(G, H, I, b) : List<&2, Nat>} &
  {Impl.wait_cnt(G, nsm, H, I, v, v, b) == Mlp.wait_cnt(G, H, I, b) : Nat} &
  {Impl.wait_off(G, nsm, H, I, v, v, b) == Mlp.wait_off(G, H, I, b) : Nat} &
  {Impl.fin_warps(G, nsm, H, I, v, v, p) == Mlp.fin_warps(G, H, I, p) : Nat} &
  {Impl.wait2(G, nsm, H, I, v, v, p) == Mlp.wait2(G, H, I, p) : Nat} &
  {Impl.fc2(G, nsm, H, I, v, v, g) == Part.b_lo(g, Mlp.kt2(I), Mlp.total2(H, I), G) : Nat} &
  {Impl.mc2(G, nsm, H, I, v, v) == Mlp.mc2(G, H, I) : Nat}

# Phase 0 at (u, u) (tail with (w, w) phase 1): the tail block fields n0 / ring1 / ring2, the phase-0
# first contributors and MC0 are 8202's, and so is the whole tail program of every block for every m.
law wuniform0:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +u: Nat
  for +w: Nat
  for +v: Nat
  for +b: Nat
  for +g: Nat
  for upos: {Nat.is_lt(0n, u) == True{} : Bool}
  for wpos: {Nat.is_lt(0n, w) == True{} : Bool}
  for vpos: {Nat.is_lt(0n, v) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.n0(G, nsm, A, H, u, u, b) == Tail.n0(G, A, H, b) : Nat} &
  {Impl.ring1(G, nsm, A, H, u, u, b) == Tail.ring1(G, A, H, b) : Nat} &
  {Impl.tring2(G, nsm, A, H, I, u, u, w, w, b) == Tail.ring2(G, A, H, I, b) : Nat} &
  {Impl.fc0(G, nsm, A, H, u, u, g) == Tail.lo0(G, A, H, g) : Nat} &
  {Impl.mc0(G, nsm, A, H, u, u) == Tail.mc0(G, A, H) : Nat} &
  {Impl.tevents(G, nsm, A, H, I, m, u, u, w, w, v, v, b) == Tail.events(G, A, H, I, m, b)
    : List<&2, TSpec.Ev>}

# ---- (6) row invariance: the tail program's split boundaries do not depend on m ----

# For any two token-row counts m1, m2, block b runs the same barriers, the same phase-0 split-K main
# loop (its slice [s0, e0) of the weighted partition) and the same counter events (the weighted 8201
# events); only its F0 / N job lists depend on m.
law wtail_rows:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m1: Nat
  for +m2: Nat
  for +a0: Nat
  for +b0: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  {TSpec.bars(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) ==
    TSpec.bars(Impl.tevents(G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2, b)) : List<&2, Nat>} &
  {TSpec.works(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) ==
    TSpec.works(Impl.tevents(G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2, b)) : List<&2, PSpec.Ev>} &
  {TSpec.syncs(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) ==
    TSpec.syncs(Impl.tevents(G, nsm, A, H, I, m2, a0, b0, a1, b1, a2, b2, b)) : List<&2, MSpec.Ev>} &
  {TSpec.bars(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) == TSpec.bar_seq()
    : List<&2, Nat>} &
  {TSpec.works(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) ==
    Part.mainloop(Impl.s0(G, nsm, A, H, a0, b0, b), Impl.e0(G, nsm, A, H, a0, b0, b), Tail.kt0(A))
    : List<&2, PSpec.Ev>} &
  {TSpec.syncs(Impl.tevents(G, nsm, A, H, I, m1, a0, b0, a1, b1, a2, b2, b)) ==
    Impl.events(G, nsm, H, I, a1, b1, a2, b2, b) : List<&2, MSpec.Ev>}
