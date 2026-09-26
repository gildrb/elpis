# Proofs of ext 8205's table laws (m16_wsched_tables_laws.bend) about the Bend model m16_wsched.bend.
# Structural evidence only: no unsafe definitions, axioms, holes or foreign proof code. The partition
# facts come from the proven gemm_m16_wpart laws, the arithmetic from gemm_m16_partition_proof's ar_*
# lemmas, the ring and event-projection lemmas from tail_m16_sched_proof. Every def precedes its uses.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_laws.bend as PLaws
import ./gemm_m16_partition_proof.bend as PP
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./gemm_m16_wpart_laws.bend as WLaws
import ./gemm_m16_wpart_proof.bend as WPP
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./tail_m16_sched.bend as Tail
import ./tail_m16_sched_spec.bend as TSpec
import ./tail_m16_sched_proof.bend as TP
import ./m16_wsched.bend as Impl
import ./m16_wsched_spec.bend as Spec
import ./m16_wsched_tables_laws.bend as Laws

# ==== the host guard's positivity consequences (gemm_m16_wpart valid_domain) ====

def tv_w0(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(0n, w0) == True{} : Bool}:
  -P0 = {Nat.is_lt(0n, w0) == True{} : Bool}
  -P1 = {Nat.is_lt(0n, w1) == True{} : Bool}
  -PG = {Nat.is_lt(0n, G) == True{} : Bool}
  -PT = {Nat.is_lt(0n, T) == True{} : Bool}
  PP.ard_fst(P0, P1 & PG & PT, WLaws.valid_domain(T, G, nsm, w0, w1, valid))

def tv_w1(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(0n, w1) == True{} : Bool}:
  -P0 = {Nat.is_lt(0n, w0) == True{} : Bool}
  -P1 = {Nat.is_lt(0n, w1) == True{} : Bool}
  -PG = {Nat.is_lt(0n, G) == True{} : Bool}
  -PT = {Nat.is_lt(0n, T) == True{} : Bool}
  PP.ard_fst(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, WLaws.valid_domain(T, G, nsm, w0, w1, valid)))

def tv_g(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(0n, G) == True{} : Bool}:
  -P0 = {Nat.is_lt(0n, w0) == True{} : Bool}
  -P1 = {Nat.is_lt(0n, w1) == True{} : Bool}
  -PG = {Nat.is_lt(0n, G) == True{} : Bool}
  -PT = {Nat.is_lt(0n, T) == True{} : Bool}
  PP.ard_fst(PG, PT, PP.ard_snd(P1, PG & PT,
    PP.ard_snd(P0, P1 & PG & PT, WLaws.valid_domain(T, G, nsm, w0, w1, valid))))

# ==== (1) the slices partition [0, T) ====

# s < e gives 0 < e - s.
def t_pos_sub(+s: Nat, +e: Nat, h: {Nat.is_lt(s, e) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.sub(e, s)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(0n, Nat.sub(e, s)), Nat.is_lt(Nat.add(s, 0n), e), PP.ar_lt_sub_iff(e, s, 0n))
    : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(s, 0n), s, PP.ar_add_zero_r(s)) : {Nat.is_lt(_, e) == True{} : Bool}
  h

# The five slice facts for block c of the weighted partition of T: start 0, contiguity (by
# definition), s + n = e, n > 0 for c < G, start(G) = T.
def t_slices(+T: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +c: Nat,
    +valid: {Wp.weights_valid(T, G, nsm, w0, w1) == True{} : Bool},
    +block: {Nat.is_lt(c, G) == True{} : Bool})
  -> {Wp.start(0n, T, G, nsm, w0, w1) == 0n : Nat} &
    {Wp.start(1n+c, T, G, nsm, w0, w1) == Wp.start(1n+c, T, G, nsm, w0, w1) : Nat} &
    {Nat.add(Wp.start(c, T, G, nsm, w0, w1),
      Nat.sub(Wp.start(1n+c, T, G, nsm, w0, w1), Wp.start(c, T, G, nsm, w0, w1))) ==
      Wp.start(1n+c, T, G, nsm, w0, w1) : Nat} &
    {Nat.is_lt(0n, Nat.sub(Wp.start(1n+c, T, G, nsm, w0, w1), Wp.start(c, T, G, nsm, w0, w1))) ==
      True{} : Bool} &
    {Wp.start(G, T, G, nsm, w0, w1) == T : Nat}:
  +s = Wp.start(c, T, G, nsm, w0, w1)
  +e = Wp.start(1n+c, T, G, nsm, w0, w1)
  +w0p = tv_w0(T, G, nsm, w0, w1, valid)
  +w1p = tv_w1(T, G, nsm, w0, w1, valid)
  +gp = tv_g(T, G, nsm, w0, w1, valid)
  +ne = WLaws.valid_nonempty(T, G, nsm, w0, w1, c, valid, block)
  (WLaws.start_zero(T, G, nsm, w0, w1),
    {==},
    PP.ar_sub_add(e, s, PP.ar_lt_le(s, e, ne)),
    t_pos_sub(s, e, ne),
    WLaws.start_full(T, G, nsm, w0, w1, w0p, w1p, gp))

def Laws.wslices0(G, nsm, A, H, a0, b0, b, valid, block):
  t_slices(Tail.total0(A, H), G, nsm, a0, b0, b, valid, block)

def Laws.wslices1(G, nsm, H, I, a1, b1, b, valid, block):
  t_slices(Mlp.total1(H, I), G, nsm, a1, b1, b, valid, block)

def Laws.wslices2(G, nsm, H, I, a2, b2, b, valid, block):
  t_slices(Mlp.total2(H, I), G, nsm, a2, b2, b, valid, block)

# ==== (2) fc / nc are the contributors ====

# fc <= lc gives fc + ((lc - fc) + 1) = 1 + lc.
def t_fc_nc(+fc: Nat, +lc: Nat, le: {Nat.is_le(fc, lc) == True{} : Bool})
  -> {Nat.add(fc, Nat.add(Nat.sub(lc, fc), 1n)) == 1n+lc : Nat}:
  +d = Nat.sub(lc, fc)
  Equal.trans(Nat, Nat.add(fc, Nat.add(d, 1n)), Nat.add(Nat.add(fc, d), 1n), 1n+lc,
    Equal.sym(Nat, Nat.add(Nat.add(fc, d), 1n), Nat.add(fc, Nat.add(d, 1n)), PP.ar_add_assoc(fc, d, 1n)),
    (%Equal.sym(Nat, Nat.add(fc, d), lc, PP.ar_sub_add(lc, fc, le)) : {Nat.add(_, 1n) == 1n+lc : Nat}
      Equal.trans(Nat, Nat.add(lc, 1n), 1n+Nat.add(lc, 0n), 1n+lc, PP.ar_add_succ_r(lc, 0n),
        Equal.cong(Nat, Nat, t => 1n+t, Nat.add(lc, 0n), lc, PP.ar_add_zero_r(lc)))))

def t_contrib(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +b: Nat,
    +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool},
    +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +block: {Nat.is_lt(b, G) == True{} : Bool})
  -> {WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) ==
      Spec.in_range(b, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
        Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : Bool} &
    {WSpec.touch_count(G, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) ==
      Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) : Nat} &
    {Nat.is_le(1n, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
    {Nat.is_le(Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
      Wp.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  +T = Nat.mul(groups, KT)
  +fc = Wp.first_contrib(g, KT, T, G, nsm, w0, w1)
  +lc = Wp.last_contrib(g, KT, T, G, nsm, w0, w1)
  +n = Wp.nc(g, KT, T, G, nsm, w0, w1)
  +mc = Wp.max_contrib(groups, KT, G, nsm, w0, w1)
  +w0p = tv_w0(T, G, nsm, w0, w1, valid)
  +w1p = tv_w1(T, G, nsm, w0, w1, valid)
  +gp = tv_g(T, G, nsm, w0, w1, valid)
  -A2 = {Nat.is_le(fc, lc) == True{} : Bool}
  -B2 = {Nat.is_lt(lc, G) == True{} : Bool}
  -C2 = {Nat.is_le(1n, n) == True{} : Bool}
  -D2 = {Nat.is_le(n, mc) == True{} : Bool}
  +le = PP.ard_fst(A2, B2 & C2 & D2,
    WLaws.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0p, w1p, gp, tiles, group))
  (%Equal.sym(Nat, Nat.add(fc, n), 1n+lc, t_fc_nc(fc, lc, le))
      : {WSpec.touches(b, g, KT, T, G, nsm, w0, w1) == Bool.and(Nat.is_le(fc, b), Nat.is_lt(b, _)) : Bool}
    %Equal.sym(Bool, Nat.is_lt(b, 1n+lc), Nat.is_le(1n+b, 1n+lc), PP.ar_lt_succ_le(b, 1n+lc))
      : {WSpec.touches(b, g, KT, T, G, nsm, w0, w1) == Bool.and(Nat.is_le(fc, b), _) : Bool}
    WLaws.contributors_contiguous(groups, KT, G, nsm, w0, w1, g, b, valid, tiles, group, block),
    WLaws.touch_count_is_nc(groups, KT, G, nsm, w0, w1, g, valid, tiles, group),
    PP.ard_fst(C2, D2, PP.ard_snd(B2, C2 & D2, PP.ard_snd(A2, B2 & C2 & D2,
      WLaws.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0p, w1p, gp, tiles, group)))),
    PP.ard_snd(C2, D2, PP.ard_snd(B2, C2 & D2, PP.ard_snd(A2, B2 & C2 & D2,
      WLaws.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0p, w1p, gp, tiles, group)))))

def Laws.wcontrib0(G, nsm, A, H, a0, b0, g, b, valid, shaped, group, block):
  t_contrib(Part.groups(1n, H), Tail.kt0(A), G, nsm, a0, b0, g, b, valid, PP.p2_kt_pos(A, shaped), group,
    block)

def Laws.wcontrib1(G, nsm, H, I, a1, b1, g, b, valid, shaped, group, block):
  t_contrib(Part.groups(2n, I), Mlp.kt1(H), G, nsm, a1, b1, g, b, valid, PP.p2_kt_pos(H, shaped), group,
    block)

def Laws.wcontrib2(G, nsm, H, I, a2, b2, g, b, valid, shaped, group, block):
  t_contrib(Part.groups(1n, H), Mlp.kt2(I), G, nsm, a2, b2, g, b, valid, PP.p2_kt_pos(I, shaped), group,
    block)

# ==== (3) ring offsets ====

def Laws.wring(G, nsm, A, H, I, a0, b0, a1, b1, b, t):
  +n1 = Impl.n1(G, nsm, H, I, a1, b1, b)
  +n0 = Impl.n0(G, nsm, A, H, a0, b0, b)
  (PP.ard_dm_lt(n1, 8n, {==}), TP.mod_shift(n1, t, 8n, {==}),
    PP.ard_dm_lt(n0, 8n, {==}), TP.mod_shift(n0, t, 8n, {==}),
    PP.ard_dm_lt(Nat.add(n0, n1), 8n, {==}), TP.mod_shift(Nat.add(n0, n1), t, 8n, {==}))

# ==== (4) workspace ====

# A contributor's in-phase address g * mc + (b - fc(g)) is below groups * mc (gemm_m16_wpart
# slot_in_range, last conjunct).
def t_addr_lt(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +b: Nat,
    +valid: {Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool},
    +tiles: {Nat.is_lt(0n, KT) == True{} : Bool}, +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +contributor: {WSpec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(Wp.address(g, Wp.max_contrib(groups, KT, G, nsm, w0, w1), b,
      Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
    Nat.mul(groups, Wp.max_contrib(groups, KT, G, nsm, w0, w1))) == True{} : Bool}:
  +T = Nat.mul(groups, KT)
  +lo = Wp.first_contrib(g, KT, T, G, nsm, w0, w1)
  +n = Wp.nc(g, KT, T, G, nsm, w0, w1)
  +mc = Wp.max_contrib(groups, KT, G, nsm, w0, w1)
  -A = {Nat.is_le(lo, b) == True{} : Bool}
  -B = {Nat.is_lt(Nat.sub(b, lo), n) == True{} : Bool}
  -C = {Nat.is_lt(Nat.sub(b, lo), mc) == True{} : Bool}
  -D = {Nat.is_lt(Wp.address(g, mc, b, lo), Nat.mul(groups, mc)) == True{} : Bool}
  PP.ard_snd(C, D, PP.ard_snd(B, C & D, PP.ard_snd(A, B & C & D,
    WLaws.slot_in_range(groups, KT, G, nsm, w0, w1, g, b, tv_w0(T, G, nsm, w0, w1, valid),
      tv_w1(T, G, nsm, w0, w1, valid), tv_g(T, G, nsm, w0, w1, valid), tiles, group, contributor))))

# Slot s below a W-slot workspace whose bytes fit cap ends at or below cap.
def t_bytes(+s: Nat, +W: Nat, +cap: Nat, lt: {Nat.is_lt(s, W) == True{} : Bool},
    fits: {Nat.is_le(Nat.mul(Nat.mul(W, Wp.slot_floats()), 4n), cap) == True{} : Bool})
  -> {Nat.is_le(Spec.slot_end(s, Wp.slot_floats()), cap) == True{} : Bool}:
  +sf = Wp.slot_floats()
  +le = PP.ard_rt(Nat.is_lt(s, W), Nat.is_le(1n+s, W), PP.ar_lt_succ_le(s, W), lt)
  PP.ar_le_trans(Nat.mul(Nat.mul(1n+s, sf), 4n), Nat.mul(Nat.mul(W, sf), 4n), cap,
    PP.ar_le_mul_mono(Nat.mul(1n+s, sf), Nat.mul(W, sf), 4n, PP.ar_le_mul_mono(1n+s, W, sf, le)), fits)

# base + a < base + len from a < len.
def t_shift_lt(+base: Nat, +a: Nat, +len: Nat, h: {Nat.is_lt(a, len) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(base, a), Nat.add(base, len)) == True{} : Bool}:
  PP.ard_tr(Nat.is_lt(Nat.add(base, a), Nat.add(base, len)), Nat.is_lt(a, len),
    PP.ar_lt_add_cancel(base, a, len), h)

def Laws.wws1(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2, g, b, cap, valid, shaped, group, contributor,
    fits):
  +s = Impl.slot1(G, nsm, H, I, a1, b1, g, b)
  +B2 = Impl.base2(G, nsm, H, I, a1, b1)
  +B0 = Impl.base0(G, nsm, H, I, a1, b1, a2, b2)
  +W = Impl.ws_slots(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2)
  +lt = t_addr_lt(Part.groups(2n, I), Mlp.kt1(H), G, nsm, a1, b1, g, b, valid, PP.p2_kt_pos(H, shaped), group,
    contributor)
  (PP.ar_and_intro(Nat.is_le(0n, s), Nat.is_lt(s, B2), PP.ar_h_le_zero(s), lt),
    t_bytes(s, W, cap,
      PP.ar_lt_le_trans(s, B2, W, lt,
        PP.ar_le_trans(B2, B0, W,
          PP.ar_le_add_r(B2, Nat.mul(Part.groups(1n, H), Impl.mc2(G, nsm, H, I, a2, b2))),
          PP.ar_le_add_r(B0, Nat.mul(Part.groups(1n, H), Impl.mc0_of(kind, G, nsm, A, H, a0, b0))))),
      fits))

def Laws.wws2(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2, g, b, cap, valid, shaped, group, contributor,
    fits):
  +B2 = Impl.base2(G, nsm, H, I, a1, b1)
  +L = Nat.mul(Part.groups(1n, H), Impl.mc2(G, nsm, H, I, a2, b2))
  +a = Wp.address(g, Impl.mc2(G, nsm, H, I, a2, b2), b, Impl.fc2(G, nsm, H, I, a2, b2, g))
  +B0 = Impl.base0(G, nsm, H, I, a1, b1, a2, b2)
  +W = Impl.ws_slots(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2)
  +lt = t_shift_lt(B2, a, L,
    t_addr_lt(Part.groups(1n, H), Mlp.kt2(I), G, nsm, a2, b2, g, b, valid, PP.p2_kt_pos(I, shaped), group,
      contributor))
  (PP.ar_and_intro(Nat.is_le(B2, Nat.add(B2, a)), Nat.is_lt(Nat.add(B2, a), Nat.add(B2, L)),
      PP.ar_le_add_r(B2, a), lt),
    t_bytes(Nat.add(B2, a), W, cap,
      PP.ar_lt_le_trans(Nat.add(B2, a), B0, W, lt,
        PP.ar_le_add_r(B0, Nat.mul(Part.groups(1n, H), Impl.mc0_of(kind, G, nsm, A, H, a0, b0)))),
      fits))

def Laws.wws0(G, nsm, A, H, I, a0, b0, a1, b1, a2, b2, g, b, cap, valid, shaped, group, contributor, fits):
  +B0 = Impl.base0(G, nsm, H, I, a1, b1, a2, b2)
  +L = Nat.mul(Part.groups(1n, H), Impl.mc0(G, nsm, A, H, a0, b0))
  +a = Wp.address(g, Impl.mc0(G, nsm, A, H, a0, b0), b, Impl.fc0(G, nsm, A, H, a0, b0, g))
  +lt = t_shift_lt(B0, a, L,
    t_addr_lt(Part.groups(1n, H), Tail.kt0(A), G, nsm, a0, b0, g, b, valid, PP.p2_kt_pos(A, shaped), group,
      contributor))
  (PP.ar_and_intro(Nat.is_le(B0, Nat.add(B0, a)), Nat.is_lt(Nat.add(B0, a), Nat.add(B0, L)),
      PP.ar_le_add_r(B0, a), lt),
    t_bytes(Nat.add(B0, a), Nat.add(B0, L), cap, lt, fits))

# ==== (5) equal weights are the uniform (ext 8201 / 8202) tables ====

def t_div0(x: Nat) -> {Nat.div(0n, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+y:
      {==}

def t_sub0(y: Nat) -> {Nat.sub(0n, y) == 0n : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+z:
      {==}

# (w, w) start is v2's start for every total (total 0 by computation, else equal_weights_is_v2).
def t_start(+b: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w: Nat, +wpos: {Nat.is_lt(0n, w) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Wp.start(b, T, G, nsm, w, w) == Part.start(b, T, G) : Nat}:
  match T:
    case 0n:
      %Equal.sym(Nat, Nat.mul(b, 0n), 0n, PP.ar_mul_zero_r(b))
        : {Nat.div(0n, Wp.wpre(G, nsm, w, w)) == Nat.div(_, G) : Nat}
      Equal.trans(Nat, Nat.div(0n, Wp.wpre(G, nsm, w, w)), 0n, Nat.div(0n, G), t_div0(Wp.wpre(G, nsm, w, w)),
        Equal.sym(Nat, Nat.div(0n, G), 0n, t_div0(G)))
    case 1n+t:
      PP.ard_fst({Wp.start(b, 1n+t, G, nsm, w, w) == Part.start(b, 1n+t, G) : Nat},
        {Wp.owner(0n, 1n+t, G, nsm, w, w) == Part.owner(0n, 1n+t, G) : Nat},
        WLaws.equal_weights_is_v2(1n+t, G, nsm, w, b, 0n, wpos, gp, {==}))

def t_pick_zero(c: Bool, +w: Nat) -> {Wp.owner.pick(c, 0n, 0n, w, w) == 0n : Nat}:
  match c:
    case True{}:
      t_div0(w)
    case False{}:
      %Equal.sym(Nat, Nat.sub(0n, Nat.mul(w, 0n)), 0n, t_sub0(Nat.mul(w, 0n))) : {Nat.div(_, w) == 0n : Nat}
      t_div0(w)

# At total 0 the weighted owner is block 0 (as v2's).
def t_own0(+nsm: Nat, +w: Nat, wpos: {Nat.is_lt(0n, w) == True{} : Bool})
  -> {Wp.owner.pick(Nat.is_lt(0n, Nat.mul(w, nsm)), 0n, nsm, w, w) == 0n : Nat}:
  match nsm:
    case 0n:
      t_pick_zero(Nat.is_lt(0n, Nat.mul(w, 0n)), w)
    case 1n+n:
      match w:
        case 0n:
          Empty.absurd({Wp.owner.pick(Nat.is_lt(0n, Nat.mul(0n, 1n+n)), 0n, 1n+n, 0n, 0n) == 0n : Nat},
            PP.ar_false_true(wpos))
        case 1n+v:
          t_div0(1n+v)

def t_owner(+x: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w: Nat, +wpos: {Nat.is_lt(0n, w) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Wp.owner(x, T, G, nsm, w, w) == Part.owner(x, T, G) : Nat}:
  match T:
    case 0n:
      t_own0(nsm, w, wpos)
    case 1n+t:
      PP.ard_snd({Wp.start(0n, 1n+t, G, nsm, w, w) == Part.start(0n, 1n+t, G) : Nat},
        {Wp.owner(x, 1n+t, G, nsm, w, w) == Part.owner(x, 1n+t, G) : Nat},
        WLaws.equal_weights_is_v2(1n+t, G, nsm, w, 0n, x, wpos, gp, {==}))

def t_nc(+g: Nat, +KT: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w: Nat,
    +wpos: {Nat.is_lt(0n, w) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Wp.nc(g, KT, T, G, nsm, w, w) == Part.nc(g, KT, T, G) : Nat}:
  +xl = Nat.sub(Nat.mul(1n+g, KT), 1n)
  +xf = Nat.mul(g, KT)
  %t_owner(xf, T, G, nsm, w, wpos, gp)
    : {Wp.nc(g, KT, T, G, nsm, w, w) == Nat.add(Nat.sub(Part.owner(xl, T, G), _), 1n) : Nat}
  %t_owner(xl, T, G, nsm, w, wpos, gp)
    : {Wp.nc(g, KT, T, G, nsm, w, w) == Nat.add(Nat.sub(_, Wp.owner(xf, T, G, nsm, w, w)), 1n) : Nat}
  {==}

# The running maximum over groups g .. g + left - 1 is v2's.
def t_mc_go(left: Nat, +g: Nat, +KT: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w: Nat, +mc: Nat,
    +wpos: {Nat.is_lt(0n, w) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Wp.max_contrib.go(left, g, KT, T, G, nsm, w, w, mc) == Part.max_contrib.go(left, g, KT, T, G, mc) : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+rest:
      +N = Part.nc(g, KT, T, G)
      +M = Part.max_contrib.pick(Nat.is_gt(N, mc), N, mc)
      %Equal.sym(Nat, Wp.nc(g, KT, T, G, nsm, w, w), N, t_nc(g, KT, T, G, nsm, w, wpos, gp))
        : {Wp.max_contrib.go(rest, 1n+g, KT, T, G, nsm, w, w, Part.max_contrib.pick(Nat.is_gt(_, mc), _, mc)) ==
          Part.max_contrib.go(rest, 1n+g, KT, T, G, M) : Nat}
      t_mc_go(rest, 1n+g, KT, T, G, nsm, w, M, wpos, gp)

# e - s over the (w, w) partition is v2's.
def t_len(+b: Nat, +T: Nat, +G: Nat, +nsm: Nat, +w: Nat, +wpos: {Nat.is_lt(0n, w) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.sub(Wp.start(1n+b, T, G, nsm, w, w), Wp.start(b, T, G, nsm, w, w)) ==
    Nat.sub(Part.start(1n+b, T, G), Part.start(b, T, G)) : Nat}:
  +We = Wp.start(1n+b, T, G, nsm, w, w)
  +Ws = Wp.start(b, T, G, nsm, w, w)
  %t_start(b, T, G, nsm, w, wpos, gp) : {Nat.sub(We, Ws) == Nat.sub(Part.start(1n+b, T, G), _) : Nat}
  %t_start(1n+b, T, G, nsm, w, wpos, gp) : {Nat.sub(We, Ws) == Nat.sub(_, Ws) : Nat}
  {==}

def Laws.wuniform1(G, nsm, H, I, w, b, p, wpos, grid):
  +wp = wpos
  +gp = grid
  +T1 = Mlp.total1(H, I)
  +n1eq = t_len(b, T1, G, nsm, w, wp, gp)
  (n1eq,
    Equal.cong(Nat, Nat, x => Mlp.slot(x, Mlp.pf()), Impl.n1(G, nsm, H, I, w, w, b), Mlp.n1(G, H, I, b), n1eq),
    Equal.cong(Nat, Nat, x => Nat.mul(8n, x), Wp.nc(p, Mlp.kt1(H), T1, G, nsm, w, w),
      Part.nc(p, Mlp.kt1(H), T1, G), t_nc(p, Mlp.kt1(H), T1, G, nsm, w, wp, gp)),
    Equal.cong(Nat, Nat, x => Nat.mul(8n, x), Wp.nc(Nat.add(Mlp.pairs(I), p), Mlp.kt1(H), T1, G, nsm, w, w),
      Part.nc(Nat.add(Mlp.pairs(I), p), Mlp.kt1(H), T1, G),
      t_nc(Nat.add(Mlp.pairs(I), p), Mlp.kt1(H), T1, G, nsm, w, wp, gp)),
    t_mc_go(Part.groups(2n, I), 0n, Mlp.kt1(H), T1, G, nsm, w, 1n, wp, gp))

# ---- phase 2 at (v, v): finish pairs, ranks, wait lists, pair counts ----

def t_fin_pair(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +b: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.fin_pair(G, nsm, H, I, v, v, b) == Mlp.fin_pair(G, H, I, b) : Nat}:
  Equal.cong(Nat, Nat, x => Mlp.pair_of(I, x), Wp.start(b, Mlp.total2(H, I), G, nsm, v, v),
    Part.start(b, Mlp.total2(H, I), G), t_start(b, Mlp.total2(H, I), G, nsm, v, vpos, gp))

def t_fin_count(+n: Nat, +G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +p: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.fin_count(G, nsm, H, I, v, v, n, p) == Mlp.fin_count(G, H, I, n, p) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      +IC = Impl.fin_count(G, nsm, H, I, v, v, b, p)
      +IP = Impl.fin_pair(G, nsm, H, I, v, v, b)
      %t_fin_count(b, G, nsm, H, I, v, p, vpos, gp)
        : {Nat.add(IC, MSpec.bit(Nat.is_eq(IP, p))) ==
          Nat.add(_, MSpec.bit(Nat.is_eq(Mlp.fin_pair(G, H, I, b), p))) : Nat}
      %t_fin_pair(G, nsm, H, I, v, b, vpos, gp)
        : {Nat.add(IC, MSpec.bit(Nat.is_eq(IP, p))) == Nat.add(IC, MSpec.bit(Nat.is_eq(_, p))) : Nat}
      {==}

# fin_count over n blocks of block b's finish pair.
def t_fin_of(+n: Nat, +G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +b: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.fin_count(G, nsm, H, I, v, v, n, Impl.fin_pair(G, nsm, H, I, v, v, b)) ==
    Mlp.fin_count(G, H, I, n, Mlp.fin_pair(G, H, I, b)) : Nat}:
  +IP = Impl.fin_pair(G, nsm, H, I, v, v, b)
  %t_fin_pair(G, nsm, H, I, v, b, vpos, gp)
    : {Impl.fin_count(G, nsm, H, I, v, v, n, IP) == Mlp.fin_count(G, H, I, n, _) : Nat}
  t_fin_count(n, G, nsm, H, I, v, IP, vpos, gp)

def t_waits(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +b: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.waits(G, nsm, H, I, v, v, b) == Mlp.waits(G, H, I, b) : List<&2, Nat>}:
  +T2 = Mlp.total2(H, I)
  +In = Impl.n2(G, nsm, H, I, v, v, b)
  +Is = Impl.s2(G, nsm, H, I, v, v, b)
  %t_len(b, T2, G, nsm, v, vpos, gp)
    : {Mlp.waits.go(I, In, Is, Nil{}) == Mlp.waits.go(I, _, Part.start(b, T2, G), Nil{}) : List<&2, Nat>}
  %t_start(b, T2, G, nsm, v, vpos, gp)
    : {Mlp.waits.go(I, In, Is, Nil{}) == Mlp.waits.go(I, In, _, Nil{}) : List<&2, Nat>}
  {==}

def t_wait_cnt(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +b: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.wait_cnt(G, nsm, H, I, v, v, b) == Mlp.wait_cnt(G, H, I, b) : Nat}:
  Equal.cong(List<&2, Nat>, Nat, x => List.length(&2, Nat, x), Impl.waits(G, nsm, H, I, v, v, b),
    Mlp.waits(G, H, I, b), t_waits(G, nsm, H, I, v, b, vpos, gp))

def t_wait_off(+b: Nat, +G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.wait_off(G, nsm, H, I, v, v, b) == Mlp.wait_off(G, H, I, b) : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+c:
      +IO = Impl.wait_off(G, nsm, H, I, v, v, c)
      +IW = Impl.wait_cnt(G, nsm, H, I, v, v, c)
      %t_wait_off(c, G, nsm, H, I, v, vpos, gp) : {Nat.add(IO, IW) == Nat.add(_, Mlp.wait_cnt(G, H, I, c)) : Nat}
      %t_wait_cnt(G, nsm, H, I, v, c, vpos, gp) : {Nat.add(IO, IW) == Nat.add(IO, _) : Nat}
      {==}

def t_wait_blocks(+n: Nat, +G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +v: Nat, +p: Nat,
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.wait_blocks(G, nsm, H, I, v, v, n, p) == Mlp.wait_blocks(G, H, I, n, p) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      +IB = Impl.wait_blocks(G, nsm, H, I, v, v, b, p)
      +IW = Impl.waits(G, nsm, H, I, v, v, b)
      %t_wait_blocks(b, G, nsm, H, I, v, p, vpos, gp)
        : {Nat.add(IB, MSpec.bit(MSpec.member(IW, p))) ==
          Nat.add(_, MSpec.bit(MSpec.member(Mlp.waits(G, H, I, b), p))) : Nat}
      %t_waits(G, nsm, H, I, v, b, vpos, gp)
        : {Nat.add(IB, MSpec.bit(MSpec.member(IW, p))) == Nat.add(IB, MSpec.bit(MSpec.member(_, p))) : Nat}
      {==}

def Laws.wuniform2(G, nsm, H, I, v, b, p, g, vpos, grid):
  +vp = vpos
  +gp = grid
  +T2 = Mlp.total2(H, I)
  (t_len(b, T2, G, nsm, v, vp, gp),
    t_fin_pair(G, nsm, H, I, v, b, vp, gp),
    t_fin_of(b, G, nsm, H, I, v, b, vp, gp),
    t_fin_of(G, G, nsm, H, I, v, b, vp, gp),
    t_waits(G, nsm, H, I, v, b, vp, gp),
    t_wait_cnt(G, nsm, H, I, v, b, vp, gp),
    t_wait_off(b, G, nsm, H, I, v, vp, gp),
    Equal.cong(Nat, Nat, x => Nat.mul(8n, x), Impl.fin_count(G, nsm, H, I, v, v, G, p),
      Mlp.fin_count(G, H, I, G, p), t_fin_count(G, G, nsm, H, I, v, p, vp, gp)),
    t_wait_blocks(G, G, nsm, H, I, v, p, vp, gp),
    t_owner(Nat.mul(g, Mlp.kt2(I)), T2, G, nsm, v, vp, gp),
    t_mc_go(Part.groups(1n, H), 0n, Mlp.kt2(I), T2, G, nsm, v, 1n, vp, gp))

# ---- phase 0 and the tail program at (u, u) ----

# A block's 8201 counter events from its slice bounds.
def t_ev_of(+H: Nat, +I: Nat, +s1: Nat, +e1: Nat, +s2: Nat, +e2: Nat) -> List<&2, MSpec.Ev>:
  Mlp.sigs1(Part.mainloop(s1, e1, Mlp.kt1(H)),
    Mlp.finish(Mlp.pairs(I), Mlp.pair_of(I, s2),
      Mlp.waits2(Mlp.waits.go(I, Nat.sub(e2, s2), s2, Nil{}))))

def t_events(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +w: Nat, +v: Nat, +b: Nat,
    +wpos: {Nat.is_lt(0n, w) == True{} : Bool}, +vpos: {Nat.is_lt(0n, v) == True{} : Bool},
    +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.events(G, nsm, H, I, w, w, v, v, b) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>}:
  +T1 = Mlp.total1(H, I)
  +T2 = Mlp.total2(H, I)
  +W1 = Wp.start(b, T1, G, nsm, w, w)
  +W1e = Wp.start(1n+b, T1, G, nsm, w, w)
  +W2 = Wp.start(b, T2, G, nsm, v, v)
  +W2e = Wp.start(1n+b, T2, G, nsm, v, v)
  +P1e = Part.start(1n+b, T1, G)
  +P2 = Part.start(b, T2, G)
  +P2e = Part.start(1n+b, T2, G)
  %t_start(b, T1, G, nsm, w, wpos, gp)
    : {t_ev_of(H, I, W1, W1e, W2, W2e) == t_ev_of(H, I, _, P1e, P2, P2e) : List<&2, MSpec.Ev>}
  %t_start(1n+b, T1, G, nsm, w, wpos, gp)
    : {t_ev_of(H, I, W1, W1e, W2, W2e) == t_ev_of(H, I, W1, _, P2, P2e) : List<&2, MSpec.Ev>}
  %t_start(b, T2, G, nsm, v, vpos, gp)
    : {t_ev_of(H, I, W1, W1e, W2, W2e) == t_ev_of(H, I, W1, W1e, _, P2e) : List<&2, MSpec.Ev>}
  %t_start(1n+b, T2, G, nsm, v, vpos, gp)
    : {t_ev_of(H, I, W1, W1e, W2, W2e) == t_ev_of(H, I, W1, W1e, W2, _) : List<&2, MSpec.Ev>}
  {==}

# The tail program of block b for m rows from its phase-0 main loop ML and its counter events EV.
def t_tail(+G: Nat, +H: Nat, +m: Nat, +b: Nat, +ML: List<&2, PSpec.Ev>, +EV: List<&2, MSpec.Ev>)
    -> List<&2, TSpec.Ev>:
  TSpec.Bar{0n} <> Tail.tag_work(ML,
    TSpec.Bar{1n} <> Tail.tag_fin(Tail.warp_jobs(G, Tail.jobs0(H, m), b),
      TSpec.Bar{2n} <> Tail.tag_norm(Tail.warp_jobs(G, Tail.jobsn(H, m), b),
        TSpec.Bar{3n} <> Tail.tag_sync(EV, [TSpec.Bar{4n}]))))

def t_tevents(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +u: Nat, +w: Nat, +v: Nat, +b: Nat,
    +upos: {Nat.is_lt(0n, u) == True{} : Bool}, +wpos: {Nat.is_lt(0n, w) == True{} : Bool},
    +vpos: {Nat.is_lt(0n, v) == True{} : Bool}, +gp: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.tevents(G, nsm, A, H, I, m, u, u, w, w, v, v, b) == Tail.events(G, A, H, I, m, b)
    : List<&2, TSpec.Ev>}:
  +T0 = Tail.total0(A, H)
  +K = Tail.kt0(A)
  +S = Wp.start(b, T0, G, nsm, u, u)
  +E = Wp.start(1n+b, T0, G, nsm, u, u)
  +EV = Impl.events(G, nsm, H, I, w, w, v, v, b)
  %t_start(b, T0, G, nsm, u, upos, gp)
    : {t_tail(G, H, m, b, Part.mainloop(S, E, K), EV) ==
      t_tail(G, H, m, b, Part.mainloop(_, Part.start(1n+b, T0, G), K), Mlp.events(G, H, I, b))
      : List<&2, TSpec.Ev>}
  %t_start(1n+b, T0, G, nsm, u, upos, gp)
    : {t_tail(G, H, m, b, Part.mainloop(S, E, K), EV) ==
      t_tail(G, H, m, b, Part.mainloop(S, _, K), Mlp.events(G, H, I, b)) : List<&2, TSpec.Ev>}
  %t_events(G, nsm, H, I, w, v, b, wpos, vpos, gp)
    : {t_tail(G, H, m, b, Part.mainloop(S, E, K), EV) == t_tail(G, H, m, b, Part.mainloop(S, E, K), _)
      : List<&2, TSpec.Ev>}
  {==}

def Laws.wuniform0(G, nsm, A, H, I, m, u, w, v, b, g, upos, wpos, vpos, grid):
  +up = upos
  +wp = wpos
  +vp = vpos
  +gp = grid
  +T0 = Tail.total0(A, H)
  +n0eq = t_len(b, T0, G, nsm, u, up, gp)
  +In0 = Impl.n0(G, nsm, A, H, u, u, b)
  +In1 = Impl.n1(G, nsm, H, I, w, w, b)
  (n0eq,
    Equal.cong(Nat, Nat, x => Mlp.slot(x, Mlp.pf()), In0, Tail.n0(G, A, H, b), n0eq),
    (%n0eq : {Mlp.slot(Nat.add(In0, In1), Mlp.pf()) == Mlp.slot(Nat.add(_, Mlp.n1(G, H, I, b)), Mlp.pf()) : Nat}
      %t_len(b, Mlp.total1(H, I), G, nsm, w, wp, gp)
        : {Mlp.slot(Nat.add(In0, In1), Mlp.pf()) == Mlp.slot(Nat.add(In0, _), Mlp.pf()) : Nat}
      {==}),
    t_owner(Nat.mul(g, Tail.kt0(A)), T0, G, nsm, u, up, gp),
    t_mc_go(Part.groups(1n, H), 0n, Tail.kt0(A), T0, G, nsm, u, 1n, up, gp),
    t_tevents(G, nsm, A, H, I, m, u, w, v, b, up, wp, vp, gp))

# ==== (6) the tail program's barriers, split boundaries and counter events do not depend on m ====

def t_bars(+G: Nat, +H: Nat, +m: Nat, +b: Nat, +ML: List<&2, PSpec.Ev>, +EV: List<&2, MSpec.Ev>)
  -> {TSpec.bars(t_tail(G, H, m, b, ML, EV)) == TSpec.bar_seq() : List<&2, Nat>}:
  +FJ = Tail.warp_jobs(G, Tail.jobs0(H, m), b)
  +NJ = Tail.warp_jobs(G, Tail.jobsn(H, m), b)
  +R4 = {[TSpec.Bar{4n}] : List<&2, TSpec.Ev>}
  +R3 = {TSpec.Bar{3n} <> Tail.tag_sync(EV, R4) : List<&2, TSpec.Ev>}
  +R2 = {TSpec.Bar{2n} <> Tail.tag_norm(NJ, R3) : List<&2, TSpec.Ev>}
  +R1 = {TSpec.Bar{1n} <> Tail.tag_fin(FJ, R2) : List<&2, TSpec.Ev>}
  %TP.bars_work(ML, R1) : {0n <> _ == TSpec.bar_seq() : List<&2, Nat>}
  %TP.bars_fin(FJ, R2) : {0n <> 1n <> _ == TSpec.bar_seq() : List<&2, Nat>}
  %TP.bars_norm(NJ, R3) : {0n <> 1n <> 2n <> _ == TSpec.bar_seq() : List<&2, Nat>}
  %TP.bars_sync(EV, R4) : {0n <> 1n <> 2n <> 3n <> _ == TSpec.bar_seq() : List<&2, Nat>}
  {==}

def t_works(+G: Nat, +H: Nat, +m: Nat, +b: Nat, +ML: List<&2, PSpec.Ev>, +EV: List<&2, MSpec.Ev>)
  -> {TSpec.works(t_tail(G, H, m, b, ML, EV)) == ML : List<&2, PSpec.Ev>}:
  +FJ = Tail.warp_jobs(G, Tail.jobs0(H, m), b)
  +NJ = Tail.warp_jobs(G, Tail.jobsn(H, m), b)
  +R4 = {[TSpec.Bar{4n}] : List<&2, TSpec.Ev>}
  +R3 = {TSpec.Bar{3n} <> Tail.tag_sync(EV, R4) : List<&2, TSpec.Ev>}
  +R2 = {TSpec.Bar{2n} <> Tail.tag_norm(NJ, R3) : List<&2, TSpec.Ev>}
  +R1 = {TSpec.Bar{1n} <> Tail.tag_fin(FJ, R2) : List<&2, TSpec.Ev>}
  TP.wk_work(ML, R1,
    (%TP.wk_fin(FJ, R2) : {_ == Nil{} : List<&2, PSpec.Ev>}
      %TP.wk_norm(NJ, R3) : {_ == Nil{} : List<&2, PSpec.Ev>}
      %TP.wk_sync(EV, R4) : {_ == Nil{} : List<&2, PSpec.Ev>}
      {==}))

def t_syncs(+G: Nat, +H: Nat, +m: Nat, +b: Nat, +ML: List<&2, PSpec.Ev>, +EV: List<&2, MSpec.Ev>)
  -> {TSpec.syncs(t_tail(G, H, m, b, ML, EV)) == EV : List<&2, MSpec.Ev>}:
  +FJ = Tail.warp_jobs(G, Tail.jobs0(H, m), b)
  +NJ = Tail.warp_jobs(G, Tail.jobsn(H, m), b)
  +R4 = {[TSpec.Bar{4n}] : List<&2, TSpec.Ev>}
  +R3 = {TSpec.Bar{3n} <> Tail.tag_sync(EV, R4) : List<&2, TSpec.Ev>}
  +R2 = {TSpec.Bar{2n} <> Tail.tag_norm(NJ, R3) : List<&2, TSpec.Ev>}
  +R1 = {TSpec.Bar{1n} <> Tail.tag_fin(FJ, R2) : List<&2, TSpec.Ev>}
  %TP.sy_work(ML, R1) : {_ == EV : List<&2, MSpec.Ev>}
  %TP.sy_fin(FJ, R2) : {_ == EV : List<&2, MSpec.Ev>}
  %TP.sy_norm(NJ, R3) : {_ == EV : List<&2, MSpec.Ev>}
  TP.sy_sync(EV)

def Laws.wtail_rows(G, nsm, A, H, I, m1, m2, a0, b0, a1, b1, a2, b2, b):
  +ML = Part.mainloop(Impl.s0(G, nsm, A, H, a0, b0, b), Impl.e0(G, nsm, A, H, a0, b0, b), Tail.kt0(A))
  +EV = Impl.events(G, nsm, H, I, a1, b1, a2, b2, b)
  (Equal.trans(List<&2, Nat>, TSpec.bars(t_tail(G, H, m1, b, ML, EV)), TSpec.bar_seq(),
      TSpec.bars(t_tail(G, H, m2, b, ML, EV)), t_bars(G, H, m1, b, ML, EV),
      Equal.sym(List<&2, Nat>, TSpec.bars(t_tail(G, H, m2, b, ML, EV)), TSpec.bar_seq(),
        t_bars(G, H, m2, b, ML, EV))),
    Equal.trans(List<&2, PSpec.Ev>, TSpec.works(t_tail(G, H, m1, b, ML, EV)), ML,
      TSpec.works(t_tail(G, H, m2, b, ML, EV)), t_works(G, H, m1, b, ML, EV),
      Equal.sym(List<&2, PSpec.Ev>, TSpec.works(t_tail(G, H, m2, b, ML, EV)), ML, t_works(G, H, m2, b, ML, EV))),
    Equal.trans(List<&2, MSpec.Ev>, TSpec.syncs(t_tail(G, H, m1, b, ML, EV)), EV,
      TSpec.syncs(t_tail(G, H, m2, b, ML, EV)), t_syncs(G, H, m1, b, ML, EV),
      Equal.sym(List<&2, MSpec.Ev>, TSpec.syncs(t_tail(G, H, m2, b, ML, EV)), EV, t_syncs(G, H, m2, b, ML, EV))),
    t_bars(G, H, m1, b, ML, EV),
    t_works(G, H, m1, b, ML, EV),
    t_syncs(G, H, m1, b, ML, EV))
