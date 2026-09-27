# Obligations for ext 2113's split-K slot discard over the Nat model m16_discard.bend against m16_discard_spec.bend.
# Together: a finish job discards only lines of its own chunk in the slots it summed (1), every line it loads is one of
# those (2), no other job's line is one of them (3), and every cell such a line holds is stored again by the next
# launch's contributors before that launch's finish loads it (4); in every launch the loads come before the warp
# barrier and the discard, and each load observes its own launch's store (or its own slot-0 sum), with the switch on
# or off (5). So a discarded line's last load precedes its discard, the next load of it follows a store, and the
# discard is unobservable to the kernels' results. The switch parses to 0 / 1, default 1 (6).
# Domains: symbolic group g, max contributors mc, row r, chunk ch, contributor count nc, discard index i, lane, float
# element e, column col, launch n; rows r < 16 and chunks ch < 4 where the geometry needs them (size_m <= 16, 4 chunks
# per 512-column group).
# Out of scope (premises, not modelled): the kernel's synchronisation (grid.sync, the cnt1 counter release/acquire,
# __syncwarp, stream order between launches) orders the steps as m16_discard.bend lists them; PTX discard.global.L2
# semantics (an L2 line becomes undefined, never another address); the 128-byte alignment of the workspace (the host
# TORCH_CHECK); which contributors flush which slots and nc <= mc (gemm_m16_partition / m16_wsched / tail_m16_sched).
import Base
import ./m16_discard.bend as Impl
import ./m16_discard_spec.bend as Spec

# (1) Every active discard (i < 4 * nc) hits line (i % 4) of the job's chunk in slot g * mc + i / 4, with i / 4 < nc:
# the discarded address is 128-byte aligned (32 times the line number).
law disc_lines:
  for +g: Nat
  for +mc: Nat
  for +r: Nat
  for +ch: Nat
  for +nc: Nat
  for +i: Nat
  for act: {Impl.disc_active(nc, i) == True{} : Bool}
  {Nat.is_lt(Nat.div(i, 4n), nc) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(i, 4n), 4n) == True{} : Bool} &
  {Nat.add(Impl.chunk(g, mc, r, ch), Impl.disc_off(i)) ==
    Nat.mul(Spec.jline(Spec.slot_of(g, mc, Nat.div(i, 4n)), r, ch, Nat.mod(i, 4n)), 32n) : Nat}

# (1) Every line q < 4 of every summed slot c < nc is discarded: i = 4 c + q is lane i % 32's iteration i / 32 of the
# discard loop, active, and decodes back to (c, q).
law disc_covers:
  for +nc: Nat
  for +c: Nat
  for +q: Nat
  for cn: {Nat.is_lt(c, nc) == True{} : Bool}
  for q4: {Nat.is_lt(q, 4n) == True{} : Bool}
  {Impl.disc_i(Nat.mod(Nat.add(Nat.mul(c, 4n), q), 32n), Nat.div(Nat.add(Nat.mul(c, 4n), q), 32n)) ==
    Nat.add(Nat.mul(c, 4n), q) : Nat} &
  {Nat.is_lt(Nat.mod(Nat.add(Nat.mul(c, 4n), q), 32n), 32n) == True{} : Bool} &
  {Impl.disc_active(nc, Nat.add(Nat.mul(c, 4n), q)) == True{} : Bool} &
  {Nat.div(Nat.add(Nat.mul(c, 4n), q), 4n) == c : Nat} &
  {Nat.mod(Nat.add(Nat.mul(c, 4n), q), 4n) == q : Nat}

# (1) No two (lane < 32, iteration) pairs of the loop share an i.
law disc_lanes_once:
  for +l1: Nat
  for +k1: Nat
  for +l2: Nat
  for +k2: Nat
  for s1: {Nat.is_lt(l1, 32n) == True{} : Bool}
  for s2: {Nat.is_lt(l2, 32n) == True{} : Bool}
  for same: {Impl.disc_i(l1, k1) == Impl.disc_i(l2, k2) : Nat}
  {k1 == k2 : Nat} & {l1 == l2 : Nat}

# (2) Every element a finish loads (lane < 32 of slot c, element e < 4; slot 0 also by the output Hadamard) lies in
# line lane / 8 < 4 of its own chunk in slot g * mc + c.
law read_lines:
  for +g: Nat
  for +mc: Nat
  for +r: Nat
  for +ch: Nat
  for +c: Nat
  for +lane: Nat
  for +e: Nat
  for l32: {Nat.is_lt(lane, 32n) == True{} : Bool}
  for e4: {Nat.is_lt(e, 4n) == True{} : Bool}
  {Nat.is_lt(Nat.div(lane, 8n), 4n) == True{} : Bool} &
  {Spec.line_of(Nat.add(Impl.chunk(g, mc, r, ch), Impl.read_off(c, lane, e))) ==
    Spec.jline(Spec.slot_of(g, mc, c), r, ch, Nat.div(lane, 8n)) : Nat}

# (3) A line names its slot, row (< 16), chunk (< 4) and line (< 4) ...
law jline_injective:
  for +s1: Nat
  for +r1: Nat
  for +ch1: Nat
  for +q1: Nat
  for +s2: Nat
  for +r2: Nat
  for +ch2: Nat
  for +q2: Nat
  for rr1: {Nat.is_lt(r1, 16n) == True{} : Bool}
  for rr2: {Nat.is_lt(r2, 16n) == True{} : Bool}
  for cc1: {Nat.is_lt(ch1, 4n) == True{} : Bool}
  for cc2: {Nat.is_lt(ch2, 4n) == True{} : Bool}
  for qq1: {Nat.is_lt(q1, 4n) == True{} : Bool}
  for qq2: {Nat.is_lt(q2, 4n) == True{} : Bool}
  for same: {Spec.jline(s1, r1, ch1, q1) == Spec.jline(s2, r2, ch2, q2) : Nat}
  {s1 == s2 : Nat} & {r1 == r2 : Nat} & {ch1 == ch2 : Nat} & {q1 == q2 : Nat}

# (3) ... and a slot its group and contributor (c < mc): so the only finish job that loads a line another job's
# discard hits is that job itself, in the same slot.
law slot_of_injective:
  for +g1: Nat
  for +c1: Nat
  for +g2: Nat
  for +c2: Nat
  for +mc: Nat
  for cm1: {Nat.is_lt(c1, mc) == True{} : Bool}
  for cm2: {Nat.is_lt(c2, mc) == True{} : Bool}
  for same: {Spec.slot_of(g1, mc, c1) == Spec.slot_of(g2, mc, c2) : Nat}
  {g1 == g2 : Nat} & {c1 == c2 : Nat}

# (3) The workspaces of one launch (8201: gate+up at 0, down after 2 * pairs * mc1 slots; tail: then o_proj after
# the down slots) are disjoint: a group g < G of a workspace with mc slots per group stays below G * mc ...
law region_bound:
  for +g: Nat
  for +c: Nat
  for +G: Nat
  for +mc: Nat
  for gG: {Nat.is_lt(g, G) == True{} : Bool}
  for cm: {Nat.is_lt(c, mc) == True{} : Bool}
  {Nat.is_lt(Spec.slot_of(g, mc, c), Nat.mul(G, mc)) == True{} : Bool}

# (3) ... so it never meets a slot of the workspace laid out after it.
law region_apart:
  for +x: Nat
  for +A: Nat
  for +y: Nat
  for xa: {Nat.is_lt(x, A) == True{} : Bool}
  {Nat.is_eq(x, Nat.add(A, y)) == False{} : Bool}

# (4) The MLP / tail slot base (ws + g * mc * SLOT, then + cidx * SLOT) is the m16g one ((g * mc + cidx) * SLOT).
law slot_base_forms:
  for +g: Nat
  for +mc: Nat
  for +c: Nat
  {Impl.slot_base_mlp(g, mc, c) == Impl.slot_base(g, mc, c) : Nat}

# (4) Every cell of a summed slot (row r < 8 MT, column col < 512) is stored by contributor c's thread (warp col / 64,
# n-tile col % 64 / 16, c >> 1 = col % 16 / 8, lane >> 2 = col % 8, token tile r / 8, lane & 3 = r % 8 / 2,
# c & 1 = r % 2), all in range.
law cells_written:
  for +g: Nat
  for +mc: Nat
  for +c: Nat
  for +r: Nat
  for +col: Nat
  for +MT: Nat
  for colw: {Nat.is_lt(col, 512n) == True{} : Bool}
  for rows: {Nat.is_lt(r, Nat.mul(MT, 8n)) == True{} : Bool}
  {Impl.write_addr(g, mc, c, Nat.div(col, 64n), Nat.div(Nat.mod(col, 64n), 16n), Nat.div(Nat.mod(col, 16n), 8n),
    Nat.mod(col, 8n), Nat.div(r, 8n), Nat.div(Nat.mod(r, 8n), 2n), Nat.mod(r, 2n)) ==
    Spec.cell(Spec.slot_of(g, mc, c), r, col) : Nat} &
  {Nat.is_lt(Nat.div(col, 64n), 8n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(col, 64n), 16n), 4n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(col, 16n), 8n), 2n) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(col, 8n), 8n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(r, 8n), MT) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(r, 8n), 2n), 4n) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(r, 2n), 2n) == True{} : Bool}

# (4) The 32 floats of line q of chunk ch are the cells of that row at columns 128 ch + 32 q + j < 512.
law line_cells:
  for +s: Nat
  for +r: Nat
  for +ch: Nat
  for +q: Nat
  for +j: Nat
  for c4: {Nat.is_lt(ch, 4n) == True{} : Bool}
  for q4: {Nat.is_lt(q, 4n) == True{} : Bool}
  for j32: {Nat.is_lt(j, 32n) == True{} : Bool}
  {Nat.add(Nat.mul(Spec.jline(s, r, ch, q), 32n), j) ==
    Spec.cell(s, r, Nat.add(Nat.add(Nat.mul(ch, 128n), Nat.mul(q, 32n)), j)) : Nat} &
  {Nat.is_lt(Nat.add(Nat.add(Nat.mul(ch, 128n), Nat.mul(q, 32n)), j), 512n) == True{} : Bool}

# (5) In every launch the finish's loads (slot loads, Hadamard re-read) precede the warp barrier, which precedes the
# discard.
law reads_before_discard:
  {Nat.is_lt(Impl.st_load(), Impl.st_bar()) == True{} : Bool} &
  {Nat.is_lt(Impl.st_reload(), Impl.st_bar()) == True{} : Bool} &
  {Nat.is_lt(Impl.st_bar(), Impl.st_disc()) == True{} : Bool}

# (5) A load at step 1 + k (k < 7) of launch n observes launch n's store (slot 0 after step 3: the finish's own sum),
# for every launch history, with discards on or off: the discard of launch n - 1 is never observed.
law load_sees_launch:
  for +on: Bool
  for +zero: Bool
  for +n: Nat
  for +k: Nat
  for k7: {Nat.is_lt(k, 7n) == True{} : Bool}
  {Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+k)) == Spec.want(zero, n, 1n+k) : Impl.Ev}

# (6) EXL3_SPLITK_DISCARD: unset or empty = 1, "0" = 0, "1" = 1; other characters and longer strings refused.
law discard_knob:
  for +c1: Nat
  {Impl.knob(Impl.Unset{}) == Impl.Ok{1n} : Impl.Knob} &
  {Impl.knob(Impl.Str{0n, c1}) == Impl.Ok{1n} : Impl.Knob} &
  {Impl.knob(Impl.Str{48n, 0n}) == Impl.Ok{0n} : Impl.Knob} &
  {Impl.knob(Impl.Str{49n, 0n}) == Impl.Ok{1n} : Impl.Knob} &
  {Impl.knob(Impl.Str{50n, 0n}) == Impl.Refused{} : Impl.Knob} &
  {Impl.knob(Impl.Str{48n, 49n}) == Impl.Refused{} : Impl.Knob} &
  {Impl.knob(Impl.Str{49n, 48n}) == Impl.Refused{} : Impl.Knob}

# (6) Every accepted value is 0 or 1.
law discard_knob_range:
  for +c0: Nat
  for +c1: Nat
  {Spec.knob_ok(Impl.knob(Impl.Str{c0, c1})) == True{} : Bool}

# (6) discard(set) keeps the mode in 0..1 (a query leaves it), and the finishes discard exactly in mode 1: the
# default (1) discards.
law discard_mode:
  for +m: Nat
  for +v: Nat
  {Nat.is_le(Impl.set_mode(m, Impl.Set{v}), 1n) == True{} : Bool} &
  {Impl.set_mode(m, Impl.Query{}) == m : Nat} &
  {Impl.issues(0n) == False{} : Bool} &
  {Impl.issues(1n) == True{} : Bool}
