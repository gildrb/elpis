# Proofs of ext 2107's laws (m16_diet2_laws.bend) about bend/m16_diet2.bend against
# bend/m16_diet2_spec.bend. Structural evidence only: no unsafe definitions, axioms, holes or foreign
# proof code. Arithmetic from gemm_m16_partition_proof's ar_* / ard_* lemmas and m16_diet_proof's dv.
# Every def precedes its uses.
import Base
import ./gemm_m16_partition_proof.bend as PP
import ./m16_diet_spec.bend as DSpec
import ./m16_diet.bend as DImpl
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./m16_diet_laws.bend as DL
import ./m16_diet_proof.bend as DP
import ./m16_diet2_spec.bend as Spec
import ./m16_diet2.bend as Impl
import ./m16_diet2_laws.bend as Laws

# ==== (1) extraction: both sides reduce to the same nibbles ====

def Laws.diet2_extract(a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7):
  ({==}, {==})

# The two extractions agree on every pair of read words.
def x_eq(+A: List<&2, Nat>, +B: List<&2, Nat>)
  -> {Impl.diet_windows(Spec.w8(A), Spec.w8(B)) == Spec.ref_windows(Spec.w8(A), Spec.w8(B)) : Spec.Win8}:
  +W = Spec.windows(Spec.w8(A), Spec.w8(B))
  -P = {Spec.ref_windows(Spec.w8(A), Spec.w8(B)) == W : Spec.Win8}
  -Q = {Impl.diet_windows(Spec.w8(A), Spec.w8(B)) == W : Spec.Win8}
  +a = Spec.w8(A)
  +b = Spec.w8(B)
  Equal.trans(Spec.Win8, Impl.diet_windows(a, b), W, Spec.ref_windows(a, b),
    PP.ard_snd(P, Q, Laws.diet2_extract(Spec.nth(0n, A), Spec.nth(1n, A), Spec.nth(2n, A), Spec.nth(3n, A), Spec.nth(4n, A),
      Spec.nth(5n, A), Spec.nth(6n, A), Spec.nth(7n, A), Spec.nth(0n, B), Spec.nth(1n, B), Spec.nth(2n, B), Spec.nth(3n, B),
      Spec.nth(4n, B), Spec.nth(5n, B), Spec.nth(6n, B), Spec.nth(7n, B))),
    Equal.sym(Spec.Win8, Spec.ref_windows(a, b), W,
      PP.ard_fst(P, Q, Laws.diet2_extract(Spec.nth(0n, A), Spec.nth(1n, A), Spec.nth(2n, A), Spec.nth(3n, A), Spec.nth(4n, A),
        Spec.nth(5n, A), Spec.nth(6n, A), Spec.nth(7n, A), Spec.nth(0n, B), Spec.nth(1n, B), Spec.nth(2n, B), Spec.nth(3n, B),
        Spec.nth(4n, B), Spec.nth(5n, B), Spec.nth(6n, B), Spec.nth(7n, B)))))

# ==== (2) addresses ====

# ((a + I 4) + C) + T == a + ((C + T) + 4 I)
def sum4(+a: Nat, +I: Nat, +C: Nat, +T: Nat)
  -> {Nat.add(Nat.add(Nat.add(a, Nat.mul(I, 4n)), C), T) == Nat.add(a, Nat.add(Nat.add(C, T), Nat.mul(4n, I))) : Nat}:
  +X = Nat.mul(4n, I)
  %Equal.sym(Nat, Nat.mul(I, 4n), X, PP.ar_mul_comm(I, 4n))
    : {Nat.add(Nat.add(Nat.add(a, _), C), T) == Nat.add(a, Nat.add(Nat.add(C, T), X)) : Nat}
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, X), C), T), Nat.add(Nat.add(a, X), Nat.add(C, T)),
    Nat.add(a, Nat.add(Nat.add(C, T), X)), PP.ar_add_assoc(Nat.add(a, X), C, T),
    Equal.trans(Nat, Nat.add(Nat.add(a, X), Nat.add(C, T)), Nat.add(a, Nat.add(X, Nat.add(C, T))),
      Nat.add(a, Nat.add(Nat.add(C, T), X)), PP.ar_add_assoc(a, X, Nat.add(C, T)),
      Equal.cong(Nat, Nat, y => Nat.add(a, y), Nat.add(X, Nat.add(C, T)), Nat.add(Nat.add(C, T), X), PP.ar_add_comm(X, Nat.add(C, T)))))

# i1 = (lane * 8) >> 3 == lane
def i1_eq(+lane: Nat) -> {Spec.ref_i1(lane) == lane : Nat}:
  DP.dv(lane, 8n, {==})

def a0_eq(+rs: Nat, +co: Nat, +lane: Nat, +t: Nat)
  -> {Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), co), t) == Spec.ref_addr(rs, co, t, Spec.ref_i0(lane)) : Nat}:
  +I = Nat.mod(Nat.add(lane, 31n), 32n)
  +L = Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), co), t)
  %Equal.sym(Nat, Spec.ref_i1(lane), lane, i1_eq(lane))
    : {L == Nat.add(rs, Nat.add(Nat.add(co, Nat.mul(t, 128n)), Nat.mul(4n, Nat.mod(Nat.add(_, 31n), 32n)))) : Nat}
  sum4(rs, I, co, Nat.mul(t, 128n))

def a1_eq(+rs: Nat, +co: Nat, +lane: Nat, +t: Nat)
  -> {Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t) == Spec.ref_addr(rs, co, t, Spec.ref_i1(lane)) : Nat}:
  +L = Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t)
  %Equal.sym(Nat, Spec.ref_i1(lane), lane, i1_eq(lane))
    : {L == Nat.add(rs, Nat.add(Nat.add(co, Nat.mul(t, 128n)), Nat.mul(4n, _))) : Nat}
  sum4(rs, lane, co, Nat.mul(t, 128n))

def Laws.diet2_lds_addr(rs, co, lane, t):
  (a0_eq(rs, co, lane, t), a1_eq(rs, co, lane, t))

# ---- in the slot ----

def tile_off_go(t: Nat, +i: Nat, ht: {Nat.is_lt(t, 4n) == True{} : Bool}, +x4: {Nat.is_lt(Nat.mul(4n, i), 128n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(t, 128n), Nat.mul(4n, i)), 512n) == True{} : Bool}:
  match t:
    case 0n:
      PP.ar_lt_trans(Nat.mul(4n, i), 128n, 512n, x4, {==})
    case 1n+t1:
      match t1:
        case 0n:
          PP.ard_tr(Nat.is_lt(Nat.add(128n, Nat.mul(4n, i)), Nat.add(128n, 384n)), Nat.is_lt(Nat.mul(4n, i), 384n),
            PP.ar_lt_add_cancel(128n, Nat.mul(4n, i), 384n), PP.ar_lt_trans(Nat.mul(4n, i), 128n, 384n, x4, {==}))
        case 1n+t2:
          match t2:
            case 0n:
              PP.ard_tr(Nat.is_lt(Nat.add(256n, Nat.mul(4n, i)), Nat.add(256n, 256n)), Nat.is_lt(Nat.mul(4n, i), 256n),
                PP.ar_lt_add_cancel(256n, Nat.mul(4n, i), 256n), PP.ar_lt_trans(Nat.mul(4n, i), 128n, 256n, x4, {==}))
            case 1n+t3:
              match t3:
                case 0n:
                  PP.ard_tr(Nat.is_lt(Nat.add(384n, Nat.mul(4n, i)), Nat.add(384n, 128n)), Nat.is_lt(Nat.mul(4n, i), 128n),
                    PP.ar_lt_add_cancel(384n, Nat.mul(4n, i), 128n), x4)
                case 1n+t4:
                  Empty.absurd({Nat.is_lt(Nat.add(Nat.mul(4n+t4, 128n), Nat.mul(4n, i)), 512n) == True{} : Bool}, PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(t4, 0n), True{},
                    Equal.sym(Bool, Nat.is_lt(t4, 0n), False{}, PP.ar_h_lt_zero(t4)), ht)))

# t 128 + 4 i < 512 for t < 4, i < 32
def tile_off(t: Nat, +i: Nat, ht: {Nat.is_lt(t, 4n) == True{} : Bool}, +hi: {Nat.is_lt(i, 32n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(t, 128n), Nat.mul(4n, i)), 512n) == True{} : Bool}:
  +x4 = {(%PP.ar_mul_comm(i, 4n) : {Nat.is_lt(_, 128n) == True{} : Bool}
      PP.ard_tr(Nat.is_lt(Nat.mul(i, 4n), Nat.mul(32n, 4n)), Nat.is_lt(i, 32n), PP.ar_mul_lt_cancel(i, 32n, 4n, {==}), hi))
    : {Nat.is_lt(Nat.mul(4n, i), 128n) == True{} : Bool}}
  tile_off_go(t, i, ht, x4)

# rs + C <= rs + ((C + T) + X) and rs + ((C + T) + X) < rs + (512 + C) for T + X < 512
def in_slot(+rs: Nat, +C: Nat, +T: Nat, +X: Nat, +h: {Nat.is_lt(Nat.add(T, X), 512n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(rs, C), Nat.add(rs, Nat.add(Nat.add(C, T), X))) == True{} : Bool} &
    {Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(C, T), X)), Nat.add(rs, Nat.add(512n, C))) == True{} : Bool}:
  +lo = PP.ard_rt(Nat.is_le(C, Nat.add(Nat.add(C, T), X)), Nat.is_le(Nat.add(rs, C), Nat.add(rs, Nat.add(Nat.add(C, T), X))),
    Equal.sym(Bool, Nat.is_le(Nat.add(rs, C), Nat.add(rs, Nat.add(Nat.add(C, T), X))), Nat.is_le(C, Nat.add(Nat.add(C, T), X)),
      PP.ar_le_add_cancel(rs, C, Nat.add(Nat.add(C, T), X))),
    PP.ar_le_trans(C, Nat.add(C, T), Nat.add(Nat.add(C, T), X), PP.ar_le_add_r(C, T), PP.ar_le_add_r(Nat.add(C, T), X)))
  +mid = {(%Equal.sym(Nat, Nat.add(Nat.add(C, T), X), Nat.add(C, Nat.add(T, X)), PP.ar_add_assoc(C, T, X))
        : {Nat.is_lt(_, Nat.add(C, 512n)) == True{} : Bool}
      PP.ard_rt(Nat.is_lt(Nat.add(T, X), 512n), Nat.is_lt(Nat.add(C, Nat.add(T, X)), Nat.add(C, 512n)),
        Equal.sym(Bool, Nat.is_lt(Nat.add(C, Nat.add(T, X)), Nat.add(C, 512n)), Nat.is_lt(Nat.add(T, X), 512n),
          PP.ar_lt_add_cancel(C, Nat.add(T, X), 512n)), h))
    : {Nat.is_lt(Nat.add(Nat.add(C, T), X), Nat.add(C, 512n)) == True{} : Bool}}
  +mid2 = {(%PP.ar_add_comm(C, 512n) : {Nat.is_lt(Nat.add(Nat.add(C, T), X), _) == True{} : Bool}
      mid) : {Nat.is_lt(Nat.add(Nat.add(C, T), X), Nat.add(512n, C)) == True{} : Bool}}
  (lo, PP.ard_rt(Nat.is_lt(Nat.add(Nat.add(C, T), X), Nat.add(512n, C)),
    Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(C, T), X)), Nat.add(rs, Nat.add(512n, C))),
    Equal.sym(Bool, Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(C, T), X)), Nat.add(rs, Nat.add(512n, C))),
      Nat.is_lt(Nat.add(Nat.add(C, T), X), Nat.add(512n, C)), PP.ar_lt_add_cancel(rs, Nat.add(Nat.add(C, T), X), Nat.add(512n, C))),
    mid2))

def Laws.diet2_lds_in_slot(rs, c, pf, lane, t, lanes, tiles, slot):
  +ln = lanes
  +tl = tiles
  +C = Nat.mul(c, 512n)
  +T = Nat.mul(t, 128n)
  +I0 = Spec.ref_i0(lane)
  +I1 = Spec.ref_i1(lane)
  +h0 = {PP.ard_dm_lt(Nat.add(Spec.ref_i1(lane), 31n), 32n, {==}) : {Nat.is_lt(I0, 32n) == True{} : Bool}}
  +h1 = {(%Equal.sym(Nat, I1, lane, i1_eq(lane)) : {Nat.is_lt(_, 32n) == True{} : Bool}
      ln) : {Nat.is_lt(I1, 32n) == True{} : Bool}}
  -A0 = {Nat.is_le(Nat.add(rs, C), Nat.add(rs, Nat.add(Nat.add(C, T), Nat.mul(4n, I0)))) == True{} : Bool}
  -B0 = {Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(C, T), Nat.mul(4n, I0))), Nat.add(rs, Nat.add(512n, C))) == True{} : Bool}
  -A1 = {Nat.is_le(Nat.add(rs, C), Nat.add(rs, Nat.add(Nat.add(C, T), Nat.mul(4n, I1)))) == True{} : Bool}
  -B1 = {Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(C, T), Nat.mul(4n, I1))), Nat.add(rs, Nat.add(512n, C))) == True{} : Bool}
  (h0, (h1, (PP.ard_fst(A0, B0, in_slot(rs, C, T, Nat.mul(4n, I0), tile_off(t, I0, tl, h0))),
    (PP.ard_snd(A0, B0, in_slot(rs, C, T, Nat.mul(4n, I0), tile_off(t, I0, tl, h0))),
      (PP.ard_fst(A1, B1, in_slot(rs, C, T, Nat.mul(4n, I1), tile_off(t, I1, tl, h1))),
        (PP.ard_snd(A1, B1, in_slot(rs, C, T, Nat.mul(4n, I1), tile_off(t, I1, tl, h1))),
          PP.ar_le_mul_mono(1n+c, pf, 512n, PP.ard_rt(Nat.is_lt(c, pf), Nat.is_le(1n+c, pf), PP.ar_lt_succ_le(c, pf), slot))))))))

# ==== (3) the tile step ====

def mmas_cong(+MT: Nat, +t: Nat, +w1: Spec.Win8, +w2: Spec.Win8, +r1: List<&2, Spec.TE>, +r2: List<&2, Spec.TE>,
    +ew: {w1 == w2 : Spec.Win8}, +er: {r1 == r2 : List<&2, Spec.TE>})
  -> {Spec.mmas(MT, 0n, t, w1, r1) == Spec.mmas(MT, 0n, t, w2, r2) : List<&2, Spec.TE>}:
  Equal.trans(List<&2, Spec.TE>, Spec.mmas(MT, 0n, t, w1, r1), Spec.mmas(MT, 0n, t, w2, r1), Spec.mmas(MT, 0n, t, w2, r2),
    Equal.cong(Spec.Win8, List<&2, Spec.TE>, y => Spec.mmas(MT, 0n, t, y, r1), w1, w2, ew),
    Equal.cong(List<&2, Spec.TE>, List<&2, Spec.TE>, y => Spec.mmas(MT, 0n, t, w2, y), r1, r2, er))

# The mode-2 windows of tile t are the reference windows of tile t.
def tw_eq(+mem: List<&2, Spec.Cell>, +rs: Nat, +co: Nat, +lane: Nat, +t: Nat)
  -> {Impl.diet_windows(Spec.rd(mem, Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), co), t)), Spec.rd(mem, Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t)))
    == Spec.ref_windows(Spec.rd(mem, Spec.ref_addr(rs, co, t, Spec.ref_i0(lane))), Spec.rd(mem, Spec.ref_addr(rs, co, t, Spec.ref_i1(lane))))
    : Spec.Win8}:
  +R0 = Spec.ref_addr(rs, co, t, Spec.ref_i0(lane))
  +R1 = Spec.ref_addr(rs, co, t, Spec.ref_i1(lane))
  %Equal.sym(Nat, Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), co), t), R0, a0_eq(rs, co, lane, t))
    : {Impl.diet_windows(Spec.rd(mem, _), Spec.rd(mem, Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t))) ==
      Spec.ref_windows(Spec.rd(mem, R0), Spec.rd(mem, R1)) : Spec.Win8}
  %Equal.sym(Nat, Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), co), t), R1, a1_eq(rs, co, lane, t))
    : {Impl.diet_windows(Spec.rd(mem, R0), Spec.rd(mem, _)) == Spec.ref_windows(Spec.rd(mem, R0), Spec.rd(mem, R1)) : Spec.Win8}
  x_eq(Spec.raw(mem, R0), Spec.raw(mem, R1))

def tiles_eq(n: Nat, +t: Nat, +mem: List<&2, Spec.Cell>, +rs: Nat, +co: Nat, +lane: Nat, +MT: Nat)
  -> {Impl.dtiles(Impl.loads(n, t, mem, Nat.add(Impl.dw0(rs, lane), co), Nat.add(Impl.dw1(rs, lane), co)), t, MT) ==
    Spec.ref_tiles(n, t, mem, rs, co, lane, MT) : List<&2, Spec.TE>}:
  match n:
    case 0n:
      {==}
    case 1n+m0:
      +m = m0
      +W0 = Nat.add(Impl.dw0(rs, lane), co)
      +W1 = Nat.add(Impl.dw1(rs, lane), co)
      mmas_cong(MT, t, Impl.diet_windows(Spec.rd(mem, Impl.lds_addr(W0, t)), Spec.rd(mem, Impl.lds_addr(W1, t))),
        Spec.ref_windows(Spec.rd(mem, Spec.ref_addr(rs, co, t, Spec.ref_i0(lane))), Spec.rd(mem, Spec.ref_addr(rs, co, t, Spec.ref_i1(lane)))),
        Impl.dtiles(Impl.loads(m, 1n+t, mem, W0, W1), 1n+t, MT), Spec.ref_tiles(m, 1n+t, mem, rs, co, lane, MT),
        tw_eq(mem, rs, co, lane, t), tiles_eq(m, 1n+t, mem, rs, co, lane, MT))

def Laws.diet2_tile(mem, rs, lane, xsa, co, xo, MT):
  Equal.cong(List<&2, Spec.TE>, List<&2, Spec.TE>, y => Spec.Ldsm{Nat.add(xsa, xo)} <> y,
    Impl.dtiles(Impl.loads(4n, 0n, mem, Nat.add(Impl.dw0(rs, lane), co), Nat.add(Impl.dw1(rs, lane), co)), 0n, MT),
    Spec.ref_tiles(4n, 0n, mem, rs, co, lane, MT), tiles_eq(4n, 0n, mem, rs, co, lane, MT))

def trace_eq(evs: List<&2, DSpec.Ev>, +mem: List<&2, Spec.Cell>, +rs: Nat, +lane: Nat, +xsa: Nat, +MT: Nat)
  -> {Laws.iters_diet(evs, mem, rs, lane, xsa, MT) == Laws.iters_ref(evs, mem, rs, lane, xsa, MT) : List<&2, Spec.TE>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case DSpec.It{x, w, +ring, +xoff, fold}:
          +rest = rest0
          +D = Impl.diet_iter(mem, rs, lane, xsa, ring, xoff, MT)
          +R = Spec.ref_iter(mem, rs, lane, xsa, ring, xoff, MT)
          +DI = Laws.iters_diet(rest, mem, rs, lane, xsa, MT)
          +RI = Laws.iters_ref(rest, mem, rs, lane, xsa, MT)
          Equal.trans(List<&2, Spec.TE>, List.append(&2, Spec.TE, D, DI), List.append(&2, Spec.TE, R, DI), List.append(&2, Spec.TE, R, RI),
            Equal.cong(List<&2, Spec.TE>, List<&2, Spec.TE>, y => List.append(&2, Spec.TE, y, DI), D, R,
              Laws.diet2_tile(mem, rs, lane, xsa, ring, xoff, MT)),
            Equal.cong(List<&2, Spec.TE>, List<&2, Spec.TE>, y => List.append(&2, Spec.TE, R, y), DI, RI,
              trace_eq(rest, mem, rs, lane, xsa, MT)))
        case DSpec.Seg{g}:
          trace_eq(rest0, mem, rs, lane, xsa, MT)
        case DSpec.Pro{w}:
          trace_eq(rest0, mem, rs, lane, xsa, MT)
        case DSpec.Exit{st}:
          trace_eq(rest0, mem, rs, lane, xsa, MT)

def Laws.diet2_trace(evs, mem, rs, lane, xsa, MT):
  trace_eq(evs, mem, rs, lane, xsa, MT)

# ==== (3b) every word read of every iteration inside the ring ====

# fit: every iteration's MMA ring offset leaves a whole stage below rl (ring + ws <= rl).
def fit(evs: List<&2, DSpec.Ev>, +ws: Nat, +rl: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, ring, xoff, fold}:
          Bool.and(Nat.is_le(Nat.add(ring, ws), rl), fit(rest, ws, rl))
        case DSpec.Seg{g}:
          fit(rest, ws, rl)
        case DSpec.Pro{w}:
          fit(rest, ws, rl)
        case DSpec.Exit{st}:
          fit(rest, ws, rl)

def ft_app(a: List<&2, DSpec.Ev>, +b: List<&2, DSpec.Ev>, +ws: Nat, +rl: Nat, +ha: {fit(a, ws, rl) == True{} : Bool},
    +hb: {fit(b, ws, rl) == True{} : Bool})
  -> {fit(List.append(&2, DSpec.Ev, a, b), ws, rl) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case ev <> rest0:
      match ev:
        case DSpec.It{x, w, +ring, xoff, fold}:
          +rest = rest0
          +R = Nat.is_le(Nat.add(ring, ws), rl)
          PP.ar_and_intro(R, fit(List.append(&2, DSpec.Ev, rest, b), ws, rl), PP.ar_and_l(R, fit(rest, ws, rl), ha),
            ft_app(rest, b, ws, rl, PP.ar_and_r(R, fit(rest, ws, rl), ha), hb))
        case DSpec.Seg{g}:
          ft_app(rest0, b, ws, rl, ha, hb)
        case DSpec.Pro{w}:
          ft_app(rest0, b, ws, rl, ha, hb)
        case DSpec.Exit{st}:
          ft_app(rest0, b, ws, rl, ha, hb)

def ft_pro(t: Nat, +d: Nat, +ws: Nat, +ctx: DSpec.Ctx, +rim: DSpec.RIM, +rl: Nat)
  -> {fit(DSpec.pro(t, d, ws, ctx, rim), ws, rl) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+u:
      ft_pro(u, 1n+d, ws, ctx, DSpec.r_next(ctx, rim), rl)

def ft_out(o: DSpec.Out, +ws: Nat, +rl: Nat) -> {fit(DSpec.out_evs(o), ws, rl) == True{} : Bool}:
  match o:
    case DSpec.Cont{st}:
      {==}
    case DSpec.End{}:
      {==}

def ft_all(r: DSpec.Res, +ws: Nat, +rl: Nat, +h: {fit(DSpec.res_evs(r), ws, rl) == True{} : Bool})
  -> {fit(DSpec.res_all(r), ws, rl) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, +o}:
      ft_app(e, DSpec.out_evs(o), ws, rl, h, ft_out(o, ws, rl))

# cs W + W <= PF W for cs < PF
def ft_slot(+cs: Nat, +pf: Nat, +ws: Nat, +h: {Nat.is_lt(cs, pf) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(cs, ws), ws), Nat.mul(pf, ws)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.mul(cs, ws), ws), Nat.mul(1n+cs, ws), DP.da_mul_succ(cs, ws)) : {Nat.is_le(_, Nat.mul(pf, ws)) == True{} : Bool}
  PP.ar_le_mul_mono(1n+cs, pf, ws, PP.ard_rt(Nat.is_lt(cs, pf), Nat.is_le(1n+cs, pf), PP.ar_lt_succ_le(cs, pf), h))

def ft_walk(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +cs: Nat, +qs: Nat, +rim: DSpec.RIM, +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {fit(DSpec.res_evs(DSpec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), ws, Nat.mul(pf, ws)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case PSpec.Tile{g, it}:
          +rest = rest0
          +j = Nat.sub(it, s)
          +rl = Nat.mul(pf, ws)
          -RA = {DImpl.dring(Nat.mul(cs, ws), pf, ws) == Nat.mul(DSpec.nxt(cs, pf), ws) : Nat}
          -RB = {Nat.is_lt(DSpec.nxt(cs, pf), pf) == True{} : Bool}
          +IT = {DSpec.It{DSpec.rchunk(j, xr), DSpec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(DSpec.rpiece(j, xr), xi),
            DSpec.rfold(j, fo)} : DSpec.Ev}
          +X = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim))
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(IT, X)), IT <> DSpec.res_evs(X), DP.res_evs_cons(IT, X))
            : {fit(_, ws, rl) == True{} : Bool}
          PP.ar_and_intro(Nat.is_le(Nat.add(Nat.mul(cs, ws), ws), rl), fit(DSpec.res_evs(X), ws, rl), ft_slot(cs, pf, ws, hcs),
            ft_walk(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim),
              PP.ard_snd(RA, RB, DP.da_ring(cs, pf, ws, hcs, wspos)), wspos))
        case PSpec.Flush{g}:
          +rest = rest0
          +X = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(DSpec.Seg{g}, X)), DSpec.Seg{g} <> DSpec.res_evs(X), DP.res_evs_cons(DSpec.Seg{g}, X))
            : {fit(_, ws, Nat.mul(pf, ws)) == True{} : Bool}
          ft_walk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim, hcs, wspos)

def ft_phase(+p: DSpec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx, +cs: Nat, +qs: Nat, rim: DSpec.RIM,
    +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {fit(DSpec.res_evs(DSpec.ref_phase(p, pf, xr, fo, ws, xi, ctx, DSpec.st_of(cs, qs, rim))), ws, Nat.mul(pf, ws)) == True{} : Bool}:
  match p:
    case DSpec.Ph{+s, +n, +kt}:
      match rim:
        case DSpec.RT{+ij, +rem, +run, +k}:
          ft_walk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, DSpec.RT{ij, rem, run, k}, hcs, wspos)
        case DSpec.RG{ij, kt2, g, run, k}:
          ft_walk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, DSpec.RT{0n, 0n, 0n, 0n}, hcs, wspos)

def ft_then(r: DSpec.Res, +p: DSpec.Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +he: {fit(DSpec.res_evs(r), ws, Nat.mul(pf, ws)) == True{} : Bool}, +hcr: {Nat.is_lt(cr, pf) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {fit(DSpec.ref_then(r, p, cr, pf, xr, fo, ws, xi, ctx), ws, Nat.mul(pf, ws)) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, o}:
      match o:
        case DSpec.Cont{st}:
          match st:
            case DSpec.St{+cs, +qs, +ij, +rem, +run, +k}:
              +rl = Nat.mul(pf, ws)
              +RP = DSpec.ref_phase(p, pf, xr, fo, ws, xi, ctx, DSpec.St{cr, qs, ij, rem, run, k})
              ft_app(e, List.append(&2, DSpec.Ev, [DSpec.Exit{DSpec.St{cs, qs, ij, rem, run, k}}], DSpec.res_all(RP)), ws, rl, he,
                ft_all(RP, ws, rl, ft_phase(p, pf, xr, fo, ws, xi, ctx, cr, qs, DSpec.RT{ij, rem, run, k}, hcr, wspos)))
        case DSpec.End{}:
          +rl = Nat.mul(pf, ws)
          +RP = DSpec.ref_phase(p, pf, xr, fo, ws, xi, ctx, DSpec.St{cr, 0n, 0n, 0n, 0n, 0n})
          ft_app(e, DSpec.res_all(RP), ws, rl, he,
            ft_all(RP, ws, rl, ft_phase(p, pf, xr, fo, ws, xi, ctx, cr, 0n, DSpec.RT{0n, 0n, 0n, 0n}, hcr, wspos)))

def ft_then2(r: DSpec.Res, +p: DSpec.Ph, +cr: Nat, +q: DSpec.Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +ctx: DSpec.Ctx, +he: {fit(DSpec.res_evs(r), ws, Nat.mul(pf, ws)) == True{} : Bool}, +hcr: {Nat.is_lt(cr, pf) == True{} : Bool},
    +hcq: {Nat.is_lt(cq, pf) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {fit(DSpec.ref_then2(r, p, cr, q, cq, pf, xr, fo, ws, xi, ctx), ws, Nat.mul(pf, ws)) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, o}:
      match o:
        case DSpec.Cont{st}:
          match st:
            case DSpec.St{+cs, +qs, +ij, +rem, +run, +k}:
              +rl = Nat.mul(pf, ws)
              +RP = DSpec.ref_phase(p, pf, xr, fo, ws, xi, ctx, DSpec.St{cr, qs, ij, rem, run, k})
              +TH = DSpec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, ctx)
              ft_app(e, List.append(&2, DSpec.Ev, [DSpec.Exit{DSpec.St{cs, qs, ij, rem, run, k}}], TH), ws, rl, he,
                ft_then(RP, q, cq, pf, xr, fo, ws, xi, ctx, ft_phase(p, pf, xr, fo, ws, xi, ctx, cr, qs, DSpec.RT{ij, rem, run, k}, hcr, wspos),
                  hcq, wspos))
        case DSpec.End{}:
          +rl = Nat.mul(pf, ws)
          +RP = DSpec.ref_phase(p, pf, xr, fo, ws, xi, ctx, DSpec.St{cr, 0n, 0n, 0n, 0n, 0n})
          +TH = DSpec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, ctx)
          ft_app(e, TH, ws, rl, he,
            ft_then(RP, q, cq, pf, xr, fo, ws, xi, ctx, ft_phase(p, pf, xr, fo, ws, xi, ctx, cr, 0n, DSpec.RT{0n, 0n, 0n, 0n}, hcr, wspos),
              hcq, wspos))

# ---- from fit to the 8 reads ----

# rs + ((ring + T) + X) < rs + rl for T + X < 512 and ring + 512 <= rl
def rd_lt(+rs: Nat, +ring: Nat, +T: Nat, +X: Nat, +rl: Nat, +hTX: {Nat.is_lt(Nat.add(T, X), 512n) == True{} : Bool},
    +hf: {Nat.is_le(Nat.add(ring, 512n), rl) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(ring, T), X)), Nat.add(rs, rl)) == True{} : Bool}:
  +m1 = {(%Equal.sym(Nat, Nat.add(Nat.add(ring, T), X), Nat.add(ring, Nat.add(T, X)), PP.ar_add_assoc(ring, T, X))
        : {Nat.is_lt(_, Nat.add(ring, 512n)) == True{} : Bool}
      PP.ard_rt(Nat.is_lt(Nat.add(T, X), 512n), Nat.is_lt(Nat.add(ring, Nat.add(T, X)), Nat.add(ring, 512n)),
        Equal.sym(Bool, Nat.is_lt(Nat.add(ring, Nat.add(T, X)), Nat.add(ring, 512n)), Nat.is_lt(Nat.add(T, X), 512n),
          PP.ar_lt_add_cancel(ring, Nat.add(T, X), 512n)), hTX))
    : {Nat.is_lt(Nat.add(Nat.add(ring, T), X), Nat.add(ring, 512n)) == True{} : Bool}}
  +m2 = PP.ar_lt_le_trans(Nat.add(Nat.add(ring, T), X), Nat.add(ring, 512n), rl, m1, hf)
  PP.ard_rt(Nat.is_lt(Nat.add(Nat.add(ring, T), X), rl), Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(ring, T), X)), Nat.add(rs, rl)),
    Equal.sym(Bool, Nat.is_lt(Nat.add(rs, Nat.add(Nat.add(ring, T), X)), Nat.add(rs, rl)), Nat.is_lt(Nat.add(Nat.add(ring, T), X), rl),
      PP.ar_lt_add_cancel(rs, Nat.add(Nat.add(ring, T), X), rl)), m2)

# Both reads of tile t < 4 lie below rs + rl.
def rd_two(+rs: Nat, +lane: Nat, +ring: Nat, +rl: Nat, +t: Nat, +lanes: {Nat.is_lt(lane, 32n) == True{} : Bool},
    +ht: {Nat.is_lt(t, 4n) == True{} : Bool}, +hf: {Nat.is_le(Nat.add(ring, 512n), rl) == True{} : Bool})
  -> {Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), ring), t), Nat.add(rs, rl)) == True{} : Bool} &
    {Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), ring), t), Nat.add(rs, rl)) == True{} : Bool}:
  +I0 = Spec.ref_i0(lane)
  +I1 = Spec.ref_i1(lane)
  +h0 = {PP.ard_dm_lt(Nat.add(Spec.ref_i1(lane), 31n), 32n, {==}) : {Nat.is_lt(I0, 32n) == True{} : Bool}}
  +h1 = {(%Equal.sym(Nat, I1, lane, i1_eq(lane)) : {Nat.is_lt(_, 32n) == True{} : Bool}
      lanes) : {Nat.is_lt(I1, 32n) == True{} : Bool}}
  +L = Nat.add(rs, rl)
  ((%Equal.sym(Nat, Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), ring), t), Spec.ref_addr(rs, ring, t, I0), a0_eq(rs, ring, lane, t))
      : {Nat.is_lt(_, L) == True{} : Bool}
    rd_lt(rs, ring, Nat.mul(t, 128n), Nat.mul(4n, I0), rl, tile_off(t, I0, ht, h0), hf)),
   (%Equal.sym(Nat, Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), ring), t), Spec.ref_addr(rs, ring, t, I1), a1_eq(rs, ring, lane, t))
      : {Nat.is_lt(_, L) == True{} : Bool}
    rd_lt(rs, ring, Nat.mul(t, 128n), Nat.mul(4n, I1), rl, tile_off(t, I1, ht, h1), hf)))

def rd_t(+rs: Nat, +lane: Nat, +ring: Nat, +rl: Nat, +t: Nat, +rest: Bool, +lanes: {Nat.is_lt(lane, 32n) == True{} : Bool},
    +ht: {Nat.is_lt(t, 4n) == True{} : Bool}, +hf: {Nat.is_le(Nat.add(ring, 512n), rl) == True{} : Bool},
    +hr: {rest == True{} : Bool})
  -> {Bool.and(Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), ring), t), Nat.add(rs, rl)),
      Bool.and(Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), ring), t), Nat.add(rs, rl)), rest)) == True{} : Bool}:
  +A = Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw0(rs, lane), ring), t), Nat.add(rs, rl))
  +B = Nat.is_lt(Impl.lds_addr(Nat.add(Impl.dw1(rs, lane), ring), t), Nat.add(rs, rl))
  -PA = {A == True{} : Bool}
  -PB = {B == True{} : Bool}
  PP.ar_and_intro(A, Bool.and(B, rest), PP.ard_fst(PA, PB, rd_two(rs, lane, ring, rl, t, lanes, ht, hf)),
    PP.ar_and_intro(B, rest, PP.ard_snd(PA, PB, rd_two(rs, lane, ring, rl, t, lanes, ht, hf)), hr))

def rd_iter(+rs: Nat, +lane: Nat, +ring: Nat, +rl: Nat, +lanes: {Nat.is_lt(lane, 32n) == True{} : Bool},
    +hf: {Nat.is_le(Nat.add(ring, 512n), rl) == True{} : Bool})
  -> {Laws.lds_t(4n, 0n, rs, lane, ring, Nat.add(rs, rl)) == True{} : Bool}:
  +L = Nat.add(rs, rl)
  rd_t(rs, lane, ring, rl, 0n, Laws.lds_t(3n, 1n, rs, lane, ring, L), lanes, {==}, hf,
    rd_t(rs, lane, ring, rl, 1n, Laws.lds_t(2n, 2n, rs, lane, ring, L), lanes, {==}, hf,
      rd_t(rs, lane, ring, rl, 2n, Laws.lds_t(1n, 3n, rs, lane, ring, L), lanes, {==}, hf,
        rd_t(rs, lane, ring, rl, 3n, True{}, lanes, {==}, hf, {==}))))

def lf(evs: List<&2, DSpec.Ev>, +rs: Nat, +lane: Nat, +rl: Nat, +lanes: {Nat.is_lt(lane, 32n) == True{} : Bool},
    +h: {fit(evs, 512n, rl) == True{} : Bool})
  -> {Laws.lds_ok(evs, rs, lane, Nat.add(rs, rl)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case DSpec.It{x, w, +ring, xoff, fold}:
          +rest = rest0
          +R = Nat.is_le(Nat.add(ring, 512n), rl)
          PP.ar_and_intro(Laws.lds_t(4n, 0n, rs, lane, ring, Nat.add(rs, rl)), Laws.lds_ok(rest, rs, lane, Nat.add(rs, rl)),
            rd_iter(rs, lane, ring, rl, lanes, PP.ar_and_l(R, fit(rest, 512n, rl), h)),
            lf(rest, rs, lane, rl, lanes, PP.ar_and_r(R, fit(rest, 512n, rl), h)))
        case DSpec.Seg{g}:
          lf(rest0, rs, lane, rl, lanes, h)
        case DSpec.Pro{w}:
          lf(rest0, rs, lane, rl, lanes, h)
        case DSpec.Exit{st}:
          lf(rest0, rs, lane, rl, lanes, h)

def Laws.diet2_mlp_lds(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, xi, rs, lane, kt1, kt2, pfpos, xrpos, fopos, xipos, cadence, ring2,
    lanes):
  +pp = pfpos
  +r2p = ring2
  +ws = DImpl.cfg_ws()
  +p1 = {DSpec.Ph{s1, n1, k1} : DSpec.Ph}
  +p2 = {DSpec.Ph{s2, n2, k2} : DSpec.Ph}
  +phs = {[p1, p2] : List<&2, DSpec.Ph>}
  +ctx = DSpec.t_ctx(phs)
  +R0 = DSpec.pro_state(Nat.sub(pf, 1n), ctx, DSpec.t_init(phs))
  +rl = Nat.mul(pf, ws)
  +RP = DSpec.ref_phase(p1, pf, xr, fo, ws, xi, ctx, DSpec.st_of(0n, Nat.sub(pf, 1n), R0))
  +REF = DSpec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi)
  %Equal.sym(List<&2, DSpec.Ev>, DImpl.diet_mlp(p1, p2, r2, pf, xr, fo, ws, xi), REF,
      DL.diet_mlp(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, kt1, kt2, pp, xrpos, fopos, {==}, xipos, cadence, r2p))
    : {Laws.lds_ok(_, rs, lane, Nat.add(rs, rl)) == True{} : Bool}
  lf(REF, rs, lane, rl, lanes,
    ft_app(DSpec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.t_init(phs)), DSpec.ref_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx), ws, rl,
      ft_pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.t_init(phs), rl),
      ft_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx, ft_phase(p1, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, {==}), r2p, {==})))

def Laws.diet2_tail_lds(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, xi, rs, lane, kt0, kt1, kt2, pfpos, xrpos, fopos,
    xipos, cadence, ring2, lanes, ring1):
  +pp = pfpos
  +r1p = ring1
  +r2p = ring2
  +ws = DImpl.cfg_ws()
  +p0 = {DSpec.Ph{s0, n0, k0} : DSpec.Ph}
  +p1 = {DSpec.Ph{s1, n1, k1} : DSpec.Ph}
  +p2 = {DSpec.Ph{s2, n2, k2} : DSpec.Ph}
  +phs = {[p0, p1, p2] : List<&2, DSpec.Ph>}
  +ctx = DSpec.t_ctx(phs)
  +R0 = DSpec.pro_state(Nat.sub(pf, 1n), ctx, DSpec.t_init(phs))
  +rl = Nat.mul(pf, ws)
  +RP = DSpec.ref_phase(p0, pf, xr, fo, ws, xi, ctx, DSpec.st_of(0n, Nat.sub(pf, 1n), R0))
  +REF = DSpec.ref_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi)
  %Equal.sym(List<&2, DSpec.Ev>, DImpl.diet_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi), REF,
      DL.diet_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, kt0, kt1, kt2, pp, xrpos, fopos, {==}, xipos, cadence,
        r1p, r2p))
    : {Laws.lds_ok(_, rs, lane, Nat.add(rs, rl)) == True{} : Bool}
  lf(REF, rs, lane, rl, lanes,
    ft_app(DSpec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.t_init(phs)), DSpec.ref_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx), ws, rl,
      ft_pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.t_init(phs), rl),
      ft_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx, ft_phase(p0, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, {==}),
        r1p, r2p, {==})))

def Laws.diet2_m16g_lds(s, n, KT, pf, xr, fo, xi, rs, lane, tiles, pfpos, xrpos, fopos, xipos, cadence, lanes):
  +pp = pfpos
  +ws = DImpl.cfg_ws()
  +ctx = {DSpec.GCtx{KT, n} : DSpec.Ctx}
  +rl = Nat.mul(pf, ws)
  +R0 = DSpec.pro_state(Nat.sub(pf, 1n), ctx, DSpec.g_init(s, KT))
  +REF = DSpec.ref_m16g(s, n, KT, pf, xr, fo, ws, xi)
  %Equal.sym(List<&2, DSpec.Ev>, DImpl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi), REF,
      DL.diet_m16g(s, n, KT, pf, xr, fo, ws, xi, tiles, pp, xrpos, fopos, {==}, xipos, cadence))
    : {Laws.lds_ok(_, rs, lane, Nat.add(rs, rl)) == True{} : Bool}
  lf(REF, rs, lane, rl, lanes,
    ft_app(DSpec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.g_init(s, KT)),
      DSpec.res_evs(DSpec.rwalk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0)), ws, rl,
      ft_pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.g_init(s, KT), rl),
      ft_walk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, {==})))

# ==== (4) the switch ====

def dg_ok(v: Bool, +c: Nat, +ev: {Bool.and(Nat.is_le(48n, c), Nat.is_le(c, 50n)) == v : Bool})
  -> {Laws.mode_ok(Impl.digit_ok(v, c)) == True{} : Bool}:
  match v:
    case True{}:
      +hi = PP.ar_and_r(Nat.is_le(48n, c), Nat.is_le(c, 50n), ev)
      +lo = PP.ar_and_l(Nat.is_le(48n, c), Nat.is_le(c, 50n), ev)
      # c = 48 + d with d <= 2
      +d = Nat.sub(c, 48n)
      +ec = {(PP.ar_sub_add(c, 48n, lo)) : {Nat.add(48n, d) == c : Nat}}
      +hd = {(%Equal.sym(Nat, Nat.add(48n, d), c, ec) : {Nat.is_le(_, 50n) == True{} : Bool}
          hi) : {Nat.is_le(Nat.add(48n, d), 50n) == True{} : Bool}}
      PP.ard_tr(Nat.is_lt(d, 3n), Nat.is_le(1n+d, 3n), PP.ar_lt_succ_le(d, 3n), hd)
    case False{}:
      {==}

def ps_ok(cs: List<&2, Nat>) -> {Laws.mode_ok(Impl.parse_str(cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match rest:
        case Nil{}:
          dg_ok(Bool.and(Nat.is_le(48n, c), Nat.is_le(c, 50n)), c, {==})
        case d <> more:
          {==}

def env_ok(env: Impl.Env) -> {Laws.mode_ok(Impl.parse(env)) == True{} : Bool}:
  match env:
    case Impl.Unset{}:
      {==}
    case Impl.Str{cs}:
      ps_ok(cs)

def min2(x: Nat) -> {Nat.is_lt(Nat.min(x, 2n), 3n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+x1:
      match x1:
        case 0n:
          {==}
        case 1n+x2:
          %Equal.sym(Nat, Nat.min(x2, 0n), 0n, DP.dmin0(x2)) : {Nat.is_lt(1n+1n+_, 3n) == True{} : Bool}
          {==}

def set_ok(+m: Nat, s: Impl.SetArg, +h: {Nat.is_lt(m, 3n) == True{} : Bool})
  -> {Nat.is_lt(Impl.set_mode(m, s), 3n) == True{} : Bool}:
  match s:
    case Impl.Query{}:
      h
    case Impl.Put{x}:
      min2(x)

def Laws.diet2_mode(env, m, s, range):
  ({==}, ({==}, ({==}, ({==}, ({==}, (env_ok(env), set_ok(m, s, range)))))))

def Laws.diet2_dispatch(m, range):
  match m:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+m1:
      match m1:
        case 0n:
          ({==}, ({==}, {==}))
        case 1n+m2:
          match m2:
            case 0n:
              ({==}, ({==}, {==}))
            case 1n+m3:
              Empty.absurd({Impl.inst(3n+m3) == 3n+m3 : Nat} & {Nat.is_lt(Impl.inst(3n+m3), 3n) == True{} : Bool} &
                {Spec.feat(Impl.inst(3n+m3)) == Spec.Feat{Nat.is_lt(0n, 3n+m3), Nat.is_eq(3n+m3, 2n)} : Spec.Feat},
                PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(m3, 0n), True{},
                  Equal.sym(Bool, Nat.is_lt(m3, 0n), False{}, PP.ar_h_lt_zero(m3)), range)))
