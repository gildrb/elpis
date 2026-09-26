# Proofs of ext 2106's laws (m16_diet_laws.bend) about the Bend model m16_diet.bend against the DIET =
# false reference m16_diet_spec.bend. Structural evidence only: no unsafe definitions, axioms, holes
# or foreign proof code. Arithmetic from gemm_m16_partition_proof's ar_* / p5_* / p7_* lemmas and
# tail_m16_sched_proof's mod_shift; the loop-control proof follows gemm_m16_partition_proof's
# mainloop_trace (p5_outer). Sections: (A) arithmetic, (B) loop control, (C) weight-issue cursors,
# (D) a phase, (E) tail / 8201 kernels, (F) m16g, (G) offsets inside their buffers, (H) every weight
# copy exactly once. Every def precedes its uses.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_laws.bend as PLaws
import ./gemm_m16_partition_proof.bend as PP
import ./tail_m16_sched_proof.bend as TP
import ./m16_diet_spec.bend as Spec
import ./m16_diet.bend as Impl
import ./m16_diet_laws.bend as Laws

# ==== (A) arithmetic ====

# (a x) mod (b x) == (a mod b) x   (b, x >= 1)
def da_mul_mod(+a: Nat, +b: Nat, +x: Nat, +bpos: {Nat.is_lt(0n, b) == True{} : Bool},
    +xpos: {Nat.is_lt(0n, x) == True{} : Bool})
  -> {Nat.mod(Nat.mul(a, x), Nat.mul(b, x)) == Nat.mul(Nat.mod(a, b), x) : Nat}:
  +q = Nat.div(a, b)
  +r = Nat.mod(a, b)
  +bx = Nat.mul(b, x)
  +rx = Nat.mul(r, x)
  +e1 = Equal.cong(Nat, Nat, z => Nat.mul(z, x), a, Nat.add(Nat.mul(q, b), r),
    Equal.sym(Nat, Nat.add(Nat.mul(q, b), r), a, PP.ard_dm_eq(a, b, bpos)))
  +e2 = PP.ar_mul_add_l(Nat.mul(q, b), r, x)
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(z, rx), Nat.mul(Nat.mul(q, b), x), Nat.mul(q, bx),
    PP.ar_mul_assoc(q, b, x))
  +eq = Equal.trans(Nat, Nat.mul(a, x), Nat.mul(Nat.add(Nat.mul(q, b), r), x), Nat.add(Nat.mul(q, bx), rx), e1,
    Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(q, b), r), x), Nat.add(Nat.mul(Nat.mul(q, b), x), rx),
      Nat.add(Nat.mul(q, bx), rx), e2, e3))
  +small = PP.ard_rt(Nat.is_lt(r, b), Nat.is_lt(rx, bx),
    Equal.sym(Bool, Nat.is_lt(rx, bx), Nat.is_lt(r, b), PP.ar_mul_lt_cancel(r, b, x, xpos)),
    PP.ard_dm_lt(a, b, bpos))
  %Equal.sym(Nat, Nat.mul(a, x), Nat.add(Nat.mul(q, bx), rx), eq) : {Nat.mod(_, bx) == rx : Nat}
  PP.p7_mod_r(q, rx, bx, small)

# r x + x == (1 + r) x
def da_mul_succ(+r: Nat, +x: Nat) -> {Nat.add(Nat.mul(r, x), x) == Nat.mul(1n+r, x) : Nat}:
  PP.ar_add_comm(Nat.mul(r, x), x)

# add(a, 1) == 1 + a
def da_add1(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  PP.ar_add_comm(a, 1n)

# r mod M == r for r < M
def da_mod_small(+r: Nat, +M: Nat, h: {Nat.is_lt(r, M) == True{} : Bool}) -> {Nat.mod(r, M) == r : Nat}:
  PP.p7_mod_r(0n, r, M, h)

# M mod M == 0 for M >= 1
def da_mod_self(+M: Nat, +pos: {Nat.is_lt(0n, M) == True{} : Bool}) -> {Nat.mod(M, M) == 0n : Nat}:
  +e = Equal.trans(Nat, Nat.add(Nat.mul(1n, M), 0n), Nat.mul(1n, M), M, PP.ar_add_zero_r(Nat.mul(1n, M)),
    PP.ar_add_zero_r(M))
  %e : {Nat.mod(_, M) == 0n : Nat}
  PP.p7_mod_r(1n, 0n, M, pos)

# ((j mod M) x + x) mod (M x) == ((1 + j) mod M) x   (M, x >= 1)
def da_xstep(+j: Nat, +M: Nat, +x: Nat, +mpos: {Nat.is_lt(0n, M) == True{} : Bool},
    +xpos: {Nat.is_lt(0n, x) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(Nat.mod(j, M), x), x), Nat.mul(M, x)) == Nat.mul(Nat.mod(1n+j, M), x) : Nat}:
  +r = Nat.mod(j, M)
  +R = Nat.mul(Nat.mod(1n+j, M), x)
  %Equal.sym(Nat, Nat.add(Nat.mul(r, x), x), Nat.mul(1n+r, x), da_mul_succ(r, x))
    : {Nat.mod(_, Nat.mul(M, x)) == R : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.mul(1n+r, x), Nat.mul(M, x)), Nat.mul(Nat.mod(1n+r, M), x),
      da_mul_mod(1n+r, M, x, mpos, xpos))
    : {_ == R : Nat}
  %da_add1(r) : {Nat.mul(Nat.mod(_, M), x) == R : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(r, 1n), M), Nat.mod(Nat.add(j, 1n), M), TP.mod_shift(j, 1n, M, mpos))
    : {Nat.mul(_, x) == R : Nat}
  %Equal.sym(Nat, Nat.add(j, 1n), 1n+j, da_add1(j)) : {Nat.mul(Nat.mod(_, M), x) == R : Nat}
  {==}

# y x == 0 iff y == 0   (x >= 1)
def da_eq0_mul(y: Nat, x: Nat, xpos: {Nat.is_lt(0n, x) == True{} : Bool})
  -> {Nat.is_eq(Nat.mul(y, x), 0n) == Nat.is_eq(y, 0n) : Bool}:
  match y x:
    case 0n _:
      {==}
    case 1n+yp 0n:
      Empty.absurd({Nat.is_eq(Nat.mul(1n+yp, 0n), 0n) == Nat.is_eq(1n+yp, 0n) : Bool}, PP.ar_false_true(xpos))
    case 1n+yp 1n+xp:
      {==}

# 2 XR >= 1
def da_2pos(+xr: Nat, +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.mul(2n, xr)) == True{} : Bool}:
  PP.ar_lt_le_trans(0n, xr, Nat.mul(2n, xr), xrpos, PP.ar_le_add_r(xr, Nat.add(xr, 0n)))

# a b >= 1 for a, b >= 1
def da_mulpos(a: Nat, +b: Nat, apos: {Nat.is_lt(0n, a) == True{} : Bool}, bpos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, b)) == True{} : Bool}, PP.ar_false_true(apos))
    case 1n+a0:
      +ap = a0
      PP.ar_lt_le_trans(0n, b, Nat.add(b, Nat.mul(ap, b)), bpos, PP.ar_le_add_r(b, Nat.mul(ap, b)))

# ---- ring slots ----

# a <= b and a != b give a < b.
def da_lt_ne(a: Nat, b: Nat, le: {Nat.is_le(a, b) == True{} : Bool}, ne: {Nat.is_eq(a, b) == False{} : Bool})
  -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PP.ar_true_false(ne))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, PP.ar_false_true(le))
    case 1n+ap 1n+bp:
      da_lt_ne(ap, bp, le, ne)

# is_eq(c, (1 + p) - 1) is is_eq(c, p).
def da_eq_pred(+c: Nat, +p: Nat) -> {Nat.is_eq(c, p) == Nat.is_eq(c, Nat.sub(1n+p, 1n)) : Bool}:
  %Equal.sym(Nat, Nat.sub(p, 0n), p, PP.ar_sub_zero_r(p)) : {Nat.is_eq(c, p) == Nat.is_eq(c, _) : Bool}
  {==}

def da_ring_go(v: Bool, +c: Nat, +p: Nat, +slot: {Nat.is_lt(c, 1n+p) == True{} : Bool},
    ev: {Nat.is_eq(c, Nat.sub(1n+p, 1n)) == v : Bool})
  -> {Nat.mod(1n+c, 1n+p) == Spec.sel(v, 0n, 1n+c) : Nat} & {Nat.is_lt(Spec.sel(v, 0n, 1n+c), 1n+p) == True{} : Bool}:
  match v:
    case True{}:
      +ce = PP.ar_eq_true(c, p, Equal.trans(Bool, Nat.is_eq(c, p), Nat.is_eq(c, Nat.sub(1n+p, 1n)), True{},
        da_eq_pred(c, p), ev))
      (%Equal.sym(Nat, c, p, ce) : {Nat.mod(1n+_, 1n+p) == 0n : Nat}
        da_mod_self(1n+p, {==}), {==})
    case False{}:
      +ne = Equal.trans(Bool, Nat.is_eq(c, p), Nat.is_eq(c, Nat.sub(1n+p, 1n)), False{}, da_eq_pred(c, p), ev)
      +lt = da_lt_ne(1n+c, 1n+p, PP.ard_rt(Nat.is_lt(c, 1n+p), Nat.is_le(1n+c, 1n+p), PP.ar_lt_succ_le(c, 1n+p), slot), ne)
      (da_mod_small(1n+c, 1n+p, lt), lt)

def da_ring(+c: Nat, pf: Nat, +ws: Nat, +slot: {Nat.is_lt(c, pf) == True{} : Bool},
    +wpos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Impl.dring(Nat.mul(c, ws), pf, ws) == Nat.mul(Spec.nxt(c, pf), ws) : Nat} &
    {Nat.is_lt(Spec.nxt(c, pf), pf) == True{} : Bool}:
  match pf:
    case 0n:
      Empty.absurd({Impl.dring(Nat.mul(c, ws), 0n, ws) == Nat.mul(Spec.nxt(c, 0n), ws) : Nat} &
        {Nat.is_lt(Spec.nxt(c, 0n), 0n) == True{} : Bool}, PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(c, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(c, 0n), False{}, PP.ar_h_lt_zero(c)), slot)))
    case 1n+p0:
      +p = p0
      -A = {Nat.mod(1n+c, 1n+p) == Spec.nxt(c, 1n+p) : Nat}
      -B = {Nat.is_lt(Spec.nxt(c, 1n+p), 1n+p) == True{} : Bool}
      +R = Nat.mul(Spec.nxt(c, 1n+p), ws)
      (%Equal.sym(Nat, Nat.add(Nat.mul(c, ws), ws), Nat.mul(1n+c, ws), da_mul_succ(c, ws))
          : {Nat.mod(_, Nat.mul(1n+p, ws)) == R : Nat}
        %Equal.sym(Nat, Nat.mod(Nat.mul(1n+c, ws), Nat.mul(1n+p, ws)), Nat.mul(Nat.mod(1n+c, 1n+p), ws),
            da_mul_mod(1n+c, 1n+p, ws, {==}, wpos))
          : {_ == R : Nat}
        Equal.cong(Nat, Nat, z => Nat.mul(z, ws), Nat.mod(1n+c, 1n+p), Spec.nxt(c, 1n+p),
          PP.ard_fst(A, B, da_ring_go(Nat.is_eq(c, Nat.sub(1n+p, 1n)), c, p, slot, {==}))),
        PP.ard_snd(A, B, da_ring_go(Nat.is_eq(c, Nat.sub(1n+p, 1n)), c, p, slot, {==})))

def Laws.diet_ring_step(c, pf, ws, slot, wpos):
  da_ring(c, pf, ws, slot, wpos)

# ---- activation piece, chunk and fold tests ----

# ((j / XR) mod 2) XR + j mod XR == j mod 2 XR
def da_piece(+j: Nat, +xr: Nat, +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool})
  -> {Spec.rpiece(j, xr) == Nat.mod(j, Nat.mul(2n, xr)) : Nat}:
  +a = Nat.div(j, xr)
  +b = Nat.mod(j, xr)
  +c = Nat.div(a, 2n)
  +d = Nat.mod(a, 2n)
  +M = Nat.mul(2n, xr)
  +Y = Nat.add(Nat.mul(d, xr), b)
  +e1 = Equal.sym(Nat, Nat.add(Nat.mul(a, xr), b), j, PP.ard_dm_eq(j, xr, xrpos))
  +e2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, xr), b), a, Nat.add(Nat.mul(c, 2n), d),
    Equal.sym(Nat, Nat.add(Nat.mul(c, 2n), d), a, PP.ard_dm_eq(a, 2n, {==})))
  +e3 = Equal.cong(Nat, Nat, z => Nat.add(z, b), Nat.mul(Nat.add(Nat.mul(c, 2n), d), xr),
    Nat.add(Nat.mul(Nat.mul(c, 2n), xr), Nat.mul(d, xr)), PP.ar_mul_add_l(Nat.mul(c, 2n), d, xr))
  +e4 = Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.mul(d, xr)), b), Nat.mul(Nat.mul(c, 2n), xr),
    Nat.mul(c, M), PP.ar_mul_assoc(c, 2n, xr))
  +e5 = PP.ar_add_assoc(Nat.mul(c, M), Nat.mul(d, xr), b)
  +eqj = Equal.trans(Nat, j, Nat.add(Nat.mul(a, xr), b), Nat.add(Nat.mul(c, M), Y), e1,
    Equal.trans(Nat, Nat.add(Nat.mul(a, xr), b), Nat.add(Nat.mul(Nat.add(Nat.mul(c, 2n), d), xr), b),
      Nat.add(Nat.mul(c, M), Y), e2,
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(c, 2n), d), xr), b),
        Nat.add(Nat.add(Nat.mul(Nat.mul(c, 2n), xr), Nat.mul(d, xr)), b), Nat.add(Nat.mul(c, M), Y), e3,
        Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(c, 2n), xr), Nat.mul(d, xr)), b),
          Nat.add(Nat.add(Nat.mul(c, M), Nat.mul(d, xr)), b), Nat.add(Nat.mul(c, M), Y), e4, e5))))
  +small = PP.p7_mr_lt(d, b, 2n, xr, PP.ard_dm_lt(a, 2n, {==}), PP.ard_dm_lt(j, xr, xrpos))
  %Equal.sym(Nat, j, Nat.add(Nat.mul(c, M), Y), eqj) : {Spec.rpiece(j, xr) == Nat.mod(_, M) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(c, M), Y), M), Y, PP.p7_mod_r(c, Y, M, small))
    : {Spec.rpiece(j, xr) == _ : Nat}
  {==}

def Laws.diet_xoff(j, xr, xi, xrpos, xipos):
  +xp = xrpos
  (da_piece(j, xr, xp), da_xstep(j, Nat.mul(2n, xr), xi, da_2pos(xr, xp), xipos))

# The x-chunk test: ((j mod 2 XR) X_ITER) mod (XR X_ITER) == 0 iff j mod XR == 0.
def da_chunk_bool(+j: Nat, +xr: Nat, +xi: Nat, +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool},
    +xipos: {Nat.is_lt(0n, xi) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), Nat.mul(xr, xi)), 0n) == Nat.is_eq(Nat.mod(j, xr), 0n) : Bool}:
  +R = Nat.mod(j, Nat.mul(2n, xr))
  +t1 = da_mul_mod(R, xr, xi, xrpos, xipos)
  +t2 = PP.p7_mod_nest(j, 2n, xr, xrpos, da_2pos(xr, xrpos))
  Equal.trans(Bool, Nat.is_eq(Nat.mod(Nat.mul(R, xi), Nat.mul(xr, xi)), 0n), Nat.is_eq(Nat.mul(Nat.mod(R, xr), xi), 0n),
    Nat.is_eq(Nat.mod(j, xr), 0n),
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(Nat.mul(R, xi), Nat.mul(xr, xi)), Nat.mul(Nat.mod(R, xr), xi), t1),
    Equal.trans(Bool, Nat.is_eq(Nat.mul(Nat.mod(R, xr), xi), 0n), Nat.is_eq(Nat.mod(R, xr), 0n), Nat.is_eq(Nat.mod(j, xr), 0n),
      da_eq0_mul(Nat.mod(R, xr), xi, xipos),
      Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(R, xr), Nat.mod(j, xr), t2)))

def Laws.diet_chunk(j, xr, xi, xrpos, xipos):
  Equal.cong(Bool, Spec.XE, z => Spec.xsel(z, Spec.Chunk{Nat.add(Nat.div(j, xr), 1n), Nat.is_lt(0n, j)}),
    Nat.is_eq(Nat.mod(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), Nat.mul(xr, xi)), 0n), Nat.is_eq(Nat.mod(j, xr), 0n),
    da_chunk_bool(j, xr, xi, xrpos, xipos))

# (r + 1) mod FOLD == 0 iff r == FOLD - 1, for r < FOLD.
def da_fr_go(v: Bool, +r: Nat, +p: Nat, +lt: {Nat.is_lt(r, 1n+p) == True{} : Bool}, ev: {Nat.is_eq(r, p) == v : Bool})
  -> {Nat.is_eq(Nat.mod(1n+r, 1n+p), 0n) == v : Bool}:
  match v:
    case True{}:
      +rp = PP.ar_eq_true(r, p, ev)
      %Equal.sym(Nat, r, p, rp) : {Nat.is_eq(Nat.mod(1n+_, 1n+p), 0n) == True{} : Bool}
      %Equal.sym(Nat, Nat.mod(1n+p, 1n+p), 0n, da_mod_self(1n+p, {==})) : {Nat.is_eq(_, 0n) == True{} : Bool}
      {==}
    case False{}:
      +small = da_lt_ne(r, p, PP.ard_rt(Nat.is_lt(r, 1n+p), Nat.is_le(1n+r, 1n+p), PP.ar_lt_succ_le(r, 1n+p), lt), ev)
      %Equal.sym(Nat, Nat.mod(1n+r, 1n+p), 1n+r, da_mod_small(1n+r, 1n+p, small)) : {Nat.is_eq(_, 0n) == False{} : Bool}
      {==}

def da_fr(+r: Nat, fo: Nat, +lt: {Nat.is_lt(r, fo) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(Nat.add(r, 1n), fo), 0n) == Nat.is_eq(r, Nat.sub(fo, 1n)) : Bool}:
  match fo:
    case 0n:
      Empty.absurd({Nat.is_eq(Nat.mod(Nat.add(r, 1n), 0n), 0n) == Nat.is_eq(r, Nat.sub(0n, 1n)) : Bool},
        PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(r, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(r, 0n), False{}, PP.ar_h_lt_zero(r)), lt)))
    case 1n+p0:
      +p = p0
      %Equal.sym(Nat, Nat.add(r, 1n), 1n+r, da_add1(r)) : {Nat.is_eq(Nat.mod(_, 1n+p), 0n) == Nat.is_eq(r, Nat.sub(1n+p, 1n)) : Bool}
      %Equal.sym(Nat, Nat.sub(p, 0n), p, PP.ar_sub_zero_r(p)) : {Nat.is_eq(Nat.mod(1n+r, 1n+p), 0n) == Nat.is_eq(r, _) : Bool}
      da_fr_go(Nat.is_eq(r, p), r, p, lt, {==})

# ((j + 1) mod FOLD == 0) iff j mod FOLD == FOLD - 1
def da_fold_r(+j: Nat, +fo: Nat, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(1n+j, fo), 0n) == Nat.is_eq(Nat.mod(j, fo), Nat.sub(fo, 1n)) : Bool}:
  +r = Nat.mod(j, fo)
  %da_add1(j) : {Nat.is_eq(Nat.mod(_, fo), 0n) == Nat.is_eq(r, Nat.sub(fo, 1n)) : Bool}
  %TP.mod_shift(j, 1n, fo, fopos) : {Nat.is_eq(_, 0n) == Nat.is_eq(r, Nat.sub(fo, 1n)) : Bool}
  da_fr(r, fo, PP.ard_dm_lt(j, fo, fopos))

# 2 XR == (2 XR / FOLD) FOLD when FOLD divides 2 XR.
def da_cad(+M: Nat, +fo: Nat, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool}, cad: {Nat.mod(M, fo) == 0n : Nat})
  -> {Nat.mul(Nat.div(M, fo), fo) == M : Nat}:
  +dm = PP.ard_dm_eq(M, fo, fopos)
  %PP.ar_add_zero_r(Nat.mul(Nat.div(M, fo), fo))
    : {_ == M : Nat}
  %cad : {Nat.add(Nat.mul(Nat.div(M, fo), fo), _) == M : Nat}
  dm

# (x mod M) mod FOLD == x mod FOLD when FOLD divides M >= 1.
def da_mod_fold(+x: Nat, +M: Nat, +fo: Nat, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool},
    +mpos: {Nat.is_lt(0n, M) == True{} : Bool}, +cad: {Nat.mod(M, fo) == 0n : Nat})
  -> {Nat.mod(Nat.mod(x, M), fo) == Nat.mod(x, fo) : Nat}:
  +k = Nat.div(M, fo)
  +kf = da_cad(M, fo, fopos, cad)
  %kf : {Nat.mod(Nat.mod(x, _), fo) == Nat.mod(x, fo) : Nat}
  PP.p7_mod_nest(x, k, fo, fopos, (%Equal.sym(Nat, Nat.mul(k, fo), M, kf) : {Nat.is_lt(0n, _) == True{} : Bool}
    mpos))

def da_fold(+j: Nat, +xr: Nat, +fo: Nat, +xi: Nat, +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool},
    +fopos: {Nat.is_lt(0n, fo) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +cad: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat})
  -> {Impl.dfold(Nat.mul(Nat.mod(j, Nat.mul(2n, xr)), xi), xr, fo, xi) == Spec.rfold(j, fo) : Bool}:
  +M = Nat.mul(2n, xr)
  +FX = Nat.mul(fo, xi)
  +XN = Impl.dxnext(Nat.mul(Nat.mod(j, M), xi), xr, xi)
  +A1 = Nat.mul(Nat.mod(1n+j, M), xi)
  +A2 = Nat.mul(Nat.mod(Nat.mod(1n+j, M), fo), xi)
  +s1 = da_xstep(j, M, xi, da_2pos(xr, xrpos), xipos)
  +s2 = da_mul_mod(Nat.mod(1n+j, M), fo, xi, fopos, xipos)
  +s3 = da_mod_fold(1n+j, M, fo, fopos, da_2pos(xr, xrpos), cad)
  Equal.trans(Bool, Nat.is_eq(Nat.mod(XN, FX), 0n), Nat.is_eq(Nat.mod(A1, FX), 0n), Spec.rfold(j, fo),
    Equal.cong(Nat, Bool, z => Nat.is_eq(Nat.mod(z, FX), 0n), XN, A1, s1),
    Equal.trans(Bool, Nat.is_eq(Nat.mod(A1, FX), 0n), Nat.is_eq(A2, 0n), Spec.rfold(j, fo),
      Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(A1, FX), A2, s2),
      Equal.trans(Bool, Nat.is_eq(A2, 0n), Nat.is_eq(Nat.mod(Nat.mod(1n+j, M), fo), 0n), Spec.rfold(j, fo),
        da_eq0_mul(Nat.mod(Nat.mod(1n+j, M), fo), xi, xipos),
        Equal.trans(Bool, Nat.is_eq(Nat.mod(Nat.mod(1n+j, M), fo), 0n), Nat.is_eq(Nat.mod(1n+j, fo), 0n), Spec.rfold(j, fo),
          Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), Nat.mod(Nat.mod(1n+j, M), fo), Nat.mod(1n+j, fo), s3),
          da_fold_r(j, fo, fopos)))))

def Laws.diet_fold(j, xr, fo, xi, xrpos, fopos, xipos, cadence):
  da_fold(j, xr, fo, xi, xrpos, fopos, xipos, cadence)

def Laws.diet_served_cfg(mt, mtpos):
  ({==}, {==}, {==}, {==}, da_mulpos(mt, 256n, mtpos, {==}), {==})

# ==== (B) loop control: the countdown loop is v2's ====

# With k + j == seg_end and k >= 1, the do-while over left = k emits v2's iterations j .. j + k - 1.
def ds_inner(k: Nat, +se: Nat, +s: Nat, +g: Nat, +j: Nat, +rest: List<&2, PSpec.Ev>,
    kpos: {Nat.is_lt(0n, k) == True{} : Bool}, +hk: {Nat.add(k, j) == se : Nat})
  -> {Impl.dinner(k, se, s, g, rest) == Part.inner(k, s, g, j, rest) : List<&2, PSpec.Ev>}:
  match k:
    case 0n:
      Empty.absurd({Impl.dinner(0n, se, s, g, rest) == Part.inner(0n, s, g, j, rest) : List<&2, PSpec.Ev>},
        PP.ar_false_true(kpos))
    case 1n+0n:
      %hk : {PSpec.Tile{g, Nat.add(s, Nat.sub(_, 1n))} <> rest == PSpec.Tile{g, Nat.add(s, j)} <> rest : List<&2, PSpec.Ev>}
      %Equal.sym(Nat, Nat.sub(j, 0n), j, PP.ar_sub_zero_r(j))
        : {PSpec.Tile{g, Nat.add(s, _)} <> rest == PSpec.Tile{g, Nat.add(s, j)} <> rest : List<&2, PSpec.Ev>}
      {==}
    case 1n+1n+k1:
      +r = k1
      +ih = ds_inner(1n+r, se, s, g, 1n+j, rest, {==},
        (%Equal.sym(Nat, Nat.add(r, 1n+j), 1n+Nat.add(r, j), PP.ar_add_succ_r(r, j)) : {1n+_ == se : Nat}
          hk))
      %hk : {PSpec.Tile{g, Nat.add(s, Nat.sub(_, 1n+1n+r))} <> Impl.dinner(1n+r, se, s, g, rest) ==
        PSpec.Tile{g, Nat.add(s, j)} <> Part.inner(1n+r, s, g, 1n+j, rest) : List<&2, PSpec.Ev>}
      %Equal.sym(Nat, Nat.sub(Nat.add(r, j), r), j, PP.ar_add_sub(r, j))
        : {PSpec.Tile{g, Nat.add(s, _)} <> Impl.dinner(1n+r, se, s, g, rest) ==
          PSpec.Tile{g, Nat.add(s, j)} <> Part.inner(1n+r, s, g, 1n+j, rest) : List<&2, PSpec.Ev>}
      %Equal.sym(List<&2, PSpec.Ev>, Impl.dinner(1n+r, se, s, g, rest), Part.inner(1n+r, s, g, 1n+j, rest), ih)
        : {PSpec.Tile{g, Nat.add(s, j)} <> _ == PSpec.Tile{g, Nat.add(s, j)} <> Part.inner(1n+r, s, g, 1n+j, rest)
          : List<&2, PSpec.Ev>}
      {==}

# The countdown outer loop is v2's outer loop, under p5_outer's invariant (j <= n, j < n puts s + j
# in group g, enough fuel).
def ds_outer(fuel: Nat, go: Bool, +s: Nat, +e: Nat, +KT: Nat, +g: Nat, +j: Nat,
    +pos: {Nat.is_lt(0n, KT) == True{} : Bool},
    +ord: {Nat.is_le(s, e) == True{} : Bool},
    +jn: {Nat.is_le(j, Nat.sub(e, s)) == True{} : Bool},
    +hgo: {Nat.is_lt(j, Nat.sub(e, s)) == go : Bool},
    hg: {Nat.is_lt(j, Nat.sub(e, s)) == True{} : Bool} -> {Nat.div(Nat.add(s, j), KT) == g : Nat},
    +hfuel: {Nat.is_lt(Nat.sub(Nat.sub(e, s), j), fuel) == True{} : Bool})
  -> {Impl.douter(fuel, go, s, e, KT, g, j) == Part.outer(fuel, go, s, e, KT, g, j) : List<&2, PSpec.Ev>}:
  match fuel go:
    case 0n _:
      {==}
    case 1n+f False{}:
      {==}
    case 1n+f True{}:
      +rf = f
      +T = Nat.min(e, Nat.mul(1n+g, KT))
      +SE = Nat.sub(T, s)
      +dq = hg(hgo)
      +hiX = PP.p5_rt(Nat.is_lt(Nat.div(Nat.add(s, j), KT), 1n+g), Nat.is_lt(Nat.add(s, j), Nat.mul(1n+g, KT)),
        PP.ar_div_lt(1n+g, Nat.add(s, j), KT, pos), PP.p5_lt_div(g, Nat.add(s, j), KT, dq))
      +hie = PP.p5_rt(Nat.is_lt(j, Nat.sub(e, s)), Nat.is_lt(Nat.add(s, j), e), PP.ar_lt_sub_iff(e, s, j), hgo)
      +hit = PP.p5_rt(Bool.and(Nat.is_lt(Nat.add(s, j), e), Nat.is_lt(Nat.add(s, j), Nat.mul(1n+g, KT))), Nat.is_lt(Nat.add(s, j), T),
        Equal.sym(Bool, Nat.is_lt(Nat.add(s, j), T), Bool.and(Nat.is_lt(Nat.add(s, j), e), Nat.is_lt(Nat.add(s, j), Nat.mul(1n+g, KT))),
          PP.ar_min_lt(Nat.add(s, j), e, Nat.mul(1n+g, KT))),
        PP.ar_and_intro(Nat.is_lt(Nat.add(s, j), e), Nat.is_lt(Nat.add(s, j), Nat.mul(1n+g, KT)), hie, hiX))
      +st = PP.ar_le_trans(s, Nat.add(s, j), T, PP.ar_le_add_r(s, j), PP.ar_lt_le(Nat.add(s, j), T, hit))
      +jse = PP.p5_rt(Nat.is_lt(Nat.add(s, j), T), Nat.is_lt(j, SE),
        Equal.sym(Bool, Nat.is_lt(j, SE), Nat.is_lt(Nat.add(s, j), T), PP.ar_lt_sub_iff(T, s, j)), hit)
      +jsele = PP.ar_lt_le(j, SE, jse)
      +sen = PP.p5_rt(Nat.is_le(T, Nat.add(s, Nat.sub(e, s))), Nat.is_le(SE, Nat.sub(e, s)),
        Equal.sym(Bool, Nat.is_le(SE, Nat.sub(e, s)), Nat.is_le(T, Nat.add(s, Nat.sub(e, s))), PP.ar_le_sub_iff(T, s, Nat.sub(e, s))),
        PP.p5_t_le(s, e, Nat.mul(1n+g, KT), ord))
      +kpos = PP.p5_rt(Nat.is_lt(Nat.add(j, 0n), SE), Nat.is_lt(0n, Nat.sub(SE, j)),
        Equal.sym(Bool, Nat.is_lt(0n, Nat.sub(SE, j)), Nat.is_lt(Nat.add(j, 0n), SE), PP.ar_lt_sub_iff(SE, j, 0n)),
        PP.p5_lt_add0(j, SE, jse))
      +nsplit = PP.p5_sub_split(Nat.sub(e, s), SE, j, jsele, sen)
      +ih = ds_outer(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE, pos, ord, sen, {==},
        h => PP.p5_next_group(s, e, KT, g, pos, st, h),
        PP.p5_fuel_step(Nat.sub(e, s), SE, j, rf, nsplit, kpos, hfuel))
      +R = Part.inner(Nat.sub(SE, j), s, g, j,
        PSpec.Flush{g} <> Part.outer(rf, Nat.is_lt(Nat.max(j, SE), Nat.sub(e, s)), s, e, KT, 1n+g, Nat.max(j, SE)))
      %Equal.sym(Nat, Nat.max(j, SE), SE, PP.p5_max_r(j, SE, jsele))
        : {Impl.dinner(Nat.sub(SE, j), SE, s, g, PSpec.Flush{g} <> Impl.douter(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE)) ==
          Part.inner(Nat.sub(SE, j), s, g, j, PSpec.Flush{g} <> Part.outer(rf, Nat.is_lt(_, Nat.sub(e, s)), s, e, KT, 1n+g, _))
          : List<&2, PSpec.Ev>}
      %Equal.sym(List<&2, PSpec.Ev>, Impl.douter(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE),
          Part.outer(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE), ih)
        : {Impl.dinner(Nat.sub(SE, j), SE, s, g, PSpec.Flush{g} <> _) ==
          Part.inner(Nat.sub(SE, j), s, g, j, PSpec.Flush{g} <> Part.outer(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE))
          : List<&2, PSpec.Ev>}
      ds_inner(Nat.sub(SE, j), SE, s, g, j,
        PSpec.Flush{g} <> Part.outer(rf, Nat.is_lt(SE, Nat.sub(e, s)), s, e, KT, 1n+g, SE), kpos,
        Equal.trans(Nat, Nat.add(Nat.sub(SE, j), j), Nat.add(j, Nat.sub(SE, j)), SE,
          PP.ar_add_comm(Nat.sub(SE, j), j), PP.ar_sub_add(SE, j, jsele)))

def Laws.diet_skeleton(s, e, KT, ordered, tiles):
  ds_outer(1n+Nat.sub(e, s), Nat.is_lt(0n, Nat.sub(e, s)), s, e, KT, Nat.div(s, KT), 0n, tiles,
    ordered, PP.ar_h_le_zero(Nat.sub(e, s)), {==}, h => PP.p5_div_add0(s, KT),
    PP.p5_fuel0(Nat.sub(e, s)))

# ==== (C) tail / 8201 weight issue: run-end cursor ====

# Under iss_j + iss_rem <= N and (iss_j < N -> iss_rem > 0): iss_rem > 0 iff iss_j < N.
def ti_live(+ij: Nat, rem: Nat, +N: Nat, fits: {Nat.is_le(Nat.add(ij, rem), N) == True{} : Bool},
    live: {Bool.or(Nat.is_le(N, ij), Nat.is_lt(0n, rem)) == True{} : Bool})
  -> {Nat.is_lt(0n, rem) == Nat.is_lt(ij, N) : Bool}:
  match rem:
    case 0n:
      Equal.sym(Bool, Nat.is_lt(ij, N), False{}, PP.p6_le_nlt(ij, N,
        Equal.trans(Bool, Nat.is_le(N, ij), Bool.or(Nat.is_le(N, ij), False{}), True{},
          Equal.sym(Bool, Bool.or(Nat.is_le(N, ij), False{}), Nat.is_le(N, ij), PP.p6_or_false(Nat.is_le(N, ij))), live)))
    case 1n+r0:
      +r = r0
      +lt = PP.ar_lt_le_trans(ij, Nat.add(ij, 1n+r), N,
        (%PP.ar_add_zero_r(ij) : {Nat.is_lt(_, Nat.add(ij, 1n+r)) == True{} : Bool}
          PP.ard_tr(Nat.is_lt(Nat.add(ij, 0n), Nat.add(ij, 1n+r)), Nat.is_lt(0n, 1n+r), PP.ar_lt_add_cancel(ij, 0n, 1n+r), {==})),
        fits)
      Equal.sym(Bool, Nat.is_lt(ij, N), True{}, lt)

def ti_seek(v: Bool, +ctx: Spec.Ctx, +j1: Nat, +run: Nat, +k: Nat)
  -> {Impl.dt_seek(v, ctx, j1, 0n, run, k) == Laws.dt_of(Spec.rt_seek(v, ctx, j1, 0n, run, k)) : Impl.DIM}:
  match v:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Nat, Nat.add(j1, 0n), j1, PP.ar_add_zero_r(j1))
        : {Impl.DT{j1, 0n, run, k} == Impl.DT{_, 0n, run, k} : Impl.DIM}
      {==}

def ti_next_go(+ctx: Spec.Ctx, +ij: Nat, rem: Nat, +run: Nat, +k: Nat)
  -> {Impl.dt_step(Nat.is_lt(0n, rem), ctx, Nat.add(ij, rem), rem, run, k) ==
    Laws.dt_of(Spec.rt_step(Nat.is_lt(0n, rem), ctx, ij, rem, run, k)) : Impl.DIM}:
  match rem:
    case 0n:
      {==}
    case 1n+0n:
      %Equal.sym(Nat, Nat.add(ij, 1n), 1n+ij, da_add1(ij))
        : {Impl.dt_seek(Nat.is_lt(_, Spec.ctx_n(ctx)), ctx, _, 0n, run, k) ==
          Laws.dt_of(Spec.rt_seek(Nat.is_lt(1n+ij, Spec.ctx_n(ctx)), ctx, 1n+ij, 0n, run, k)) : Impl.DIM}
      ti_seek(Nat.is_lt(1n+ij, Spec.ctx_n(ctx)), ctx, 1n+ij, run, k)
    case 1n+1n+r2:
      +r = r2
      %Equal.sym(Nat, Nat.add(ij, 1n+1n+r), 1n+Nat.add(ij, 1n+r), PP.ar_add_succ_r(ij, 1n+r))
        : {Impl.DT{_, 1n+r, run, 1n+k} == Impl.DT{1n+Nat.add(ij, 1n+r), 1n+r, run, 1n+k} : Impl.DIM}
      {==}

def Laws.diet_tail_issue(phs, ij, rem, run, k, q, ws, fits, live):
  +hl = ti_live(ij, rem, Spec.total(phs), fits, live)
  +W = {Spec.Iss{Nat.mul(q, ws), run, k} : Spec.WE}
  (Equal.cong(Bool, Spec.WE, b => Spec.wsel(b, W), Nat.is_lt(0n, rem), Nat.is_lt(ij, Spec.total(phs)), hl),
    %hl : {Impl.dt_step(Nat.is_lt(0n, rem), Spec.t_ctx(phs), Nat.add(ij, rem), rem, run, k) ==
      Laws.dt_of(Spec.rt_step(_, Spec.t_ctx(phs), ij, rem, run, k)) : Impl.DIM}
    ti_next_go(Spec.t_ctx(phs), ij, rem, run, k))

# ---- the DIET = false cursor invariant: iss_j + iss_rem <= N, a live cursor has iss_rem > 0 ----

# A pair whose kind is Data (reusable with `+`), unlike `A & B`.
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def InvR(+N: Nat, rim: Spec.RIM) -> Data:
  match rim:
    case Spec.RT{+ij, +rem, run, k}:
      P2({Nat.is_le(Nat.add(ij, rem), N) == True{} : Bool}, {Bool.or(Nat.is_le(N, ij), Nat.is_lt(0n, rem)) == True{} : Bool})
    case Spec.RG{ij, kt, g, run, k}:
      Empty

# 0 < b - a for a < b.
def dp_sub_pos(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(b, a)) == True{} : Bool}:
  PP.ard_tr(Nat.is_lt(0n, Nat.sub(b, a)), Nat.is_lt(Nat.add(a, 0n), b), PP.ar_lt_sub_iff(b, a, 0n),
    (%Equal.sym(Nat, Nat.add(a, 0n), a, PP.ar_add_zero_r(a)) : {Nat.is_lt(_, b) == True{} : Bool}
      h))

# A run starting at stream tile i < n_tot is non-empty and ends inside the stream.
def seek_pick(v: Bool, +s: Nat, +n: Nat, +kt: Nat, +rest: List<&2, Spec.Ph>, +i: Nat,
    +ev: {Nat.is_lt(i, n) == v : Bool}, +h: {Nat.is_lt(i, Nat.add(n, Spec.total(rest))) == True{} : Bool},
    ktpos: {Nat.is_lt(0n, kt) == True{} : Bool},
    ih1: {Nat.is_lt(Nat.sub(i, n), Spec.total(rest)) == True{} : Bool} ->
      {Nat.is_lt(0n, Spec.seek(rest, Nat.sub(i, n))) == True{} : Bool},
    ih2: {Nat.is_lt(Nat.sub(i, n), Spec.total(rest)) == True{} : Bool} ->
      {Nat.is_le(Nat.add(Nat.sub(i, n), Spec.seek(rest, Nat.sub(i, n))), Spec.total(rest)) == True{} : Bool})
  -> {Nat.is_lt(0n, Spec.sel(v, Nat.min(Nat.sub(kt, Nat.mod(Nat.add(s, i), kt)), Nat.sub(n, i)), Spec.seek(rest, Nat.sub(i, n)))) == True{} : Bool} &
    {Nat.is_le(Nat.add(i, Spec.sel(v, Nat.min(Nat.sub(kt, Nat.mod(Nat.add(s, i), kt)), Nat.sub(n, i)), Spec.seek(rest, Nat.sub(i, n)))),
      Nat.add(n, Spec.total(rest))) == True{} : Bool}:
  match v:
    case True{}:
      +m = Nat.mod(Nat.add(s, i), kt)
      +a = Nat.sub(kt, m)
      +b = Nat.sub(n, i)
      +pa = dp_sub_pos(m, kt, PP.ard_dm_lt(Nat.add(s, i), kt, ktpos))
      +pb = dp_sub_pos(i, n, ev)
      +mn = Nat.min(a, b)
      +le1 = PP.ard_tr(Nat.is_le(Nat.add(i, mn), Nat.add(i, b)), Nat.is_le(mn, b), PP.ar_le_add_cancel(i, mn, b), PP.p5_min_le_r(a, b))
      +le2 = {(%Equal.sym(Nat, Nat.add(i, b), n, PP.ar_sub_add(n, i, PP.ar_lt_le(i, n, ev)))
          : {Nat.is_le(_, Nat.add(n, Spec.total(rest))) == True{} : Bool}
        PP.ar_le_add_r(n, Spec.total(rest))) : {Nat.is_le(Nat.add(i, b), Nat.add(n, Spec.total(rest))) == True{} : Bool}}
      (PP.ard_tr(Nat.is_lt(0n, mn), Bool.and(Nat.is_lt(0n, a), Nat.is_lt(0n, b)), PP.ar_min_lt(0n, a, b),
          PP.ar_and_intro(Nat.is_lt(0n, a), Nat.is_lt(0n, b), pa, pb)),
        PP.ar_le_trans(Nat.add(i, mn), Nat.add(i, b), Nat.add(n, Spec.total(rest)), le1, le2))
    case False{}:
      +ni = PP.p6_nlt_le(i, n, ev)
      +T = Spec.total(rest)
      +d = Nat.sub(i, n)
      +ie = PP.ar_sub_add(i, n, ni)
      +hd = PP.ard_rt(Nat.is_lt(Nat.add(n, d), Nat.add(n, T)), Nat.is_lt(d, T), PP.ar_lt_add_cancel(n, d, T),
        (%Equal.sym(Nat, Nat.add(n, d), i, ie) : {Nat.is_lt(_, Nat.add(n, T)) == True{} : Bool}
          h))
      -A = {Nat.is_lt(0n, Spec.seek(rest, d)) == True{} : Bool}
      -B = {Nat.is_le(Nat.add(d, Spec.seek(rest, d)), T) == True{} : Bool}
      +S = Spec.seek(rest, d)
      (ih1(hd),
        (%ie : {Nat.is_le(Nat.add(_, S), Nat.add(n, T)) == True{} : Bool}
          %Equal.sym(Nat, Nat.add(Nat.add(n, d), S), Nat.add(n, Nat.add(d, S)), PP.ar_add_assoc(n, d, S))
            : {Nat.is_le(_, Nat.add(n, T)) == True{} : Bool}
          PP.ard_tr(Nat.is_le(Nat.add(n, Nat.add(d, S)), Nat.add(n, T)), Nat.is_le(Nat.add(d, S), T), PP.ar_le_add_cancel(n, Nat.add(d, S), T),
            ih2(hd))))

def seek_ok(phs: List<&2, Spec.Ph>, +i: Nat, +h: {Nat.is_lt(i, Spec.total(phs)) == True{} : Bool},
    +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> {Nat.is_lt(0n, Spec.seek(phs, i)) == True{} : Bool} & {Nat.is_le(Nat.add(i, Spec.seek(phs, i)), Spec.total(phs)) == True{} : Bool}:
  match phs:
    case Nil{}:
      Empty.absurd({Nat.is_lt(0n, Spec.seek(Nil{}, i)) == True{} : Bool} & {Nat.is_le(Nat.add(i, Spec.seek(Nil{}, i)), 0n) == True{} : Bool},
        PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, PP.ar_h_lt_zero(i)), h)))
    case p <> rest:
      match p:
        case Spec.Ph{+s, +n, +kt}:
          +rs = rest
          seek_pick(Nat.is_lt(i, n), s, n, kt, rs, i, {==}, h, PP.ar_and_l(Nat.is_lt(0n, kt), Laws.phases_ok(rs), ok),
            hd => PP.ard_fst({Nat.is_lt(0n, Spec.seek(rs, Nat.sub(i, n))) == True{} : Bool},
              {Nat.is_le(Nat.add(Nat.sub(i, n), Spec.seek(rs, Nat.sub(i, n))), Spec.total(rs)) == True{} : Bool},
              seek_ok(rs, Nat.sub(i, n), hd, PP.ar_and_r(Nat.is_lt(0n, kt), Laws.phases_ok(rs), ok))),
            hd => PP.ard_snd({Nat.is_lt(0n, Spec.seek(rs, Nat.sub(i, n))) == True{} : Bool},
              {Nat.is_le(Nat.add(Nat.sub(i, n), Spec.seek(rs, Nat.sub(i, n))), Spec.total(rs)) == True{} : Bool},
              seek_ok(rs, Nat.sub(i, n), hd, PP.ar_and_r(Nat.is_lt(0n, kt), Laws.phases_ok(rs), ok))))

def inv_seek(z: Bool, +phs: List<&2, Spec.Ph>, +N: Nat, +ij: Nat, +run: Nat, +k: Nat,
    +ez: {Nat.is_lt(1n+ij, N) == z : Bool}, +eN: {N == Spec.total(phs) : Nat},
    +ok: {Laws.phases_ok(phs) == True{} : Bool}, +lt: {Nat.is_lt(ij, N) == True{} : Bool})
  -> InvR(N, Spec.rt_seek(z, Spec.TCtx{phs, N}, 1n+ij, 0n, run, k)):
  match z:
    case True{}:
      -A = {Nat.is_lt(0n, Spec.seek(phs, 1n+ij)) == True{} : Bool}
      -B = {Nat.is_le(Nat.add(1n+ij, Spec.seek(phs, 1n+ij)), Spec.total(phs)) == True{} : Bool}
      ((%Equal.sym(Nat, N, Spec.total(phs), eN) : {Nat.is_le(Nat.add(1n+ij, Spec.seek(phs, 1n+ij)), _) == True{} : Bool}
          PP.ard_snd(A, B, seek_ok(phs, 1n+ij, (%eN : {Nat.is_lt(1n+ij, _) == True{} : Bool}
            ez), ok))),
        (%Equal.sym(Bool, Nat.is_lt(0n, Spec.seek(phs, 1n+ij)), True{}, PP.ard_fst(A, B, seek_ok(phs, 1n+ij, (%eN : {Nat.is_lt(1n+ij, _) == True{} : Bool}
              ez), ok)))
            : {Bool.or(Nat.is_le(N, 1n+ij), _) == True{} : Bool}
          PP.p6_or_true(Nat.is_le(N, 1n+ij))))
    case False{}:
      ((%Equal.sym(Nat, Nat.add(ij, 0n), ij, PP.ar_add_zero_r(ij)) : {Nat.is_le(1n+_, N) == True{} : Bool}
          PP.ard_rt(Nat.is_lt(ij, N), Nat.is_le(1n+ij, N), PP.ar_lt_succ_le(ij, N), lt)),
        (%Equal.sym(Bool, Nat.is_le(N, 1n+ij), True{}, PP.p6_nlt_le(1n+ij, N, ez))
            : {Bool.or(_, False{}) == True{} : Bool}
          {==}))

def inv_step(v: Bool, +phs: List<&2, Spec.Ph>, +N: Nat, +ij: Nat, rem: Nat, +run: Nat, +k: Nat,
    +ev: {Nat.is_lt(ij, N) == v : Bool}, +eN: {N == Spec.total(phs) : Nat},
    +ok: {Laws.phases_ok(phs) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(ij, rem), N) == True{} : Bool},
    +live: {Bool.or(Nat.is_le(N, ij), Nat.is_lt(0n, rem)) == True{} : Bool})
  -> InvR(N, Spec.rt_step(v, Spec.TCtx{phs, N}, ij, rem, run, k)):
  match v:
    case False{}:
      (fits, live)
    case True{}:
      match rem:
        case 0n:
          Empty.absurd(InvR(N, Spec.rt_step(True{}, Spec.TCtx{phs, N}, ij, 0n, run, k)),
            PP.ar_true_false(Equal.trans(Bool, True{}, Nat.is_lt(ij, N), False{}, Equal.sym(Bool, Nat.is_lt(ij, N), True{}, ev),
              PP.p6_le_nlt(ij, N, Equal.trans(Bool, Nat.is_le(N, ij), Bool.or(Nat.is_le(N, ij), False{}), True{},
                Equal.sym(Bool, Bool.or(Nat.is_le(N, ij), False{}), Nat.is_le(N, ij), PP.p6_or_false(Nat.is_le(N, ij))), live)))))
        case 1n+0n:
          inv_seek(Nat.is_lt(1n+ij, N), phs, N, ij, run, k, {==}, eN, ok, ev)
        case 1n+1n+r2:
          +r = r2
          ((%PP.ar_add_succ_r(ij, 1n+r) : {Nat.is_le(_, N) == True{} : Bool}
              fits),
            PP.p6_or_true(Nat.is_le(N, 1n+ij)))

# ---- the simulation relation between the DIET = true and DIET = false cursors ----

# Tail / 8201: the DIET = true cursor is the run-end form of the DIET = false one, which satisfies
# InvR over the phase stream (n_tot = total of the phase list, every KT >= 1).
def RelT(+phs: List<&2, Spec.Ph>, +N: Nat, dim: Impl.DIM, +rim: Spec.RIM) -> Data:
  P2({dim == Laws.dt_of(rim) : Impl.DIM}, P2({N == Spec.total(phs) : Nat}, P2({Laws.phases_ok(phs) == True{} : Bool}, InvR(N, rim))))

# m16g, a live cursor: iss_j - iss_kt agree (the DIET = true iss_j / iss_kt are frozen at the run
# start), same group and pointer.
def gact(b: Bool, +jd: Nat, +ktd: Nat, +gd: Nat, +drun: Nat, +dk: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat)
    -> Data:
  match b:
    case True{}:
      P2({Nat.add(jd, kt) == Nat.add(ij, ktd) : Nat}, P2({Nat.is_le(ktd, kt) == True{} : Bool}, P2({gd == g : Nat},
        P2({drun == run : Nat}, {dk == k : Nat}))))
    case False{}:
      Unit

# m16g: iss_left = min(KT - iss_kt, n_iter - iss_j) of the DIET = false cursor (0 once done), iss_kt < KT.
def RelG(+KT: Nat, +N: Nat, dim: Impl.DIM, rim: Spec.RIM) -> Data:
  match dim:
    case Impl.DG{+jd, +ktd, +gd, +left, +drun, +dk}:
      match rim:
        case Spec.RG{+ij, +kt, +g, +run, +k}:
          P2({Nat.is_lt(0n, KT) == True{} : Bool}, P2({Nat.is_lt(kt, KT) == True{} : Bool},
            P2({left == Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)) : Nat},
              gact(Nat.is_lt(ij, N), jd, ktd, gd, drun, dk, ij, kt, g, run, k))))
        case Spec.RT{ij, rem, run, k}:
          Empty
    case Impl.DT{je, rem, run, k}:
      Empty

def Rel(ctx: Spec.Ctx, dim: Impl.DIM, rim: Spec.RIM) -> Data:
  match ctx:
    case Spec.TCtx{+phs, +N}:
      RelT(phs, N, dim, rim)
    case Spec.GCtx{+KT, +N}:
      RelG(KT, N, dim, rim)

# c W / W == c
def dv(+c: Nat, +ws: Nat, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}) -> {Nat.div(Nat.mul(c, ws), ws) == c : Nat}:
  %PP.ar_add_zero_r(Nat.mul(c, ws)) : {Nat.div(_, ws) == c : Nat}
  PP.p7_div_q(c, 0n, ws, wspos)

# (a + b) - b == a
def dsub(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  %PP.ar_add_comm(b, a) : {Nat.sub(_, b) == a : Nat}
  PP.ar_add_sub(b, a)

# a <= b gives a - b == 0
def dsub_le0(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, PP.ar_false_true(h))
    case 1n+ap 1n+bp:
      dsub_le0(ap, bp, h)

# min(a, 0) == 0
def dmin0(a: Nat) -> {Nat.min(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      {==}

# m16g copy: iss_left > 0 exactly while the DIET = false cursor is live, same source then.
def g_we(v: Bool, +io: Nat, +KT: Nat, +N: Nat, +jd: Nat, +ktd: Nat, +gd: Nat, +left: Nat, +drun: Nat, +dk: Nat,
    +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat, +ev: {Nat.is_lt(ij, N) == v : Bool},
    +hkt: {Nat.is_lt(kt, KT) == True{} : Bool}, +hl: {left == Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)) : Nat},
    ha: gact(v, jd, ktd, gd, drun, dk, ij, kt, g, run, k))
  -> {Spec.wsel(Nat.is_lt(0n, left), Spec.Iss{io, drun, dk}) == Spec.wsel(v, Spec.Iss{io, run, k}) : Spec.WE}:
  match v:
    case True{}:
      (a1, r1) = ha
      (a2, r2) = r1
      (a3, r3) = r2
      (a4, a5) = r3
      +a = Nat.sub(KT, kt)
      +b = Nat.sub(N, ij)
      +lp = {(%Equal.sym(Nat, left, Nat.min(a, b), hl) : {Nat.is_lt(0n, _) == True{} : Bool}
          PP.ard_tr(Nat.is_lt(0n, Nat.min(a, b)), Bool.and(Nat.is_lt(0n, a), Nat.is_lt(0n, b)), PP.ar_min_lt(0n, a, b),
            PP.ar_and_intro(Nat.is_lt(0n, a), Nat.is_lt(0n, b), dp_sub_pos(kt, KT, hkt), dp_sub_pos(ij, N, ev))))
        : {Nat.is_lt(0n, left) == True{} : Bool}}
      %Equal.sym(Bool, Nat.is_lt(0n, left), True{}, lp) : {Spec.wsel(_, Spec.Iss{io, drun, dk}) == Spec.wsel(True{}, Spec.Iss{io, run, k}) : Spec.WE}
      %Equal.sym(Nat, drun, run, a4) : {Spec.wsel(True{}, Spec.Iss{io, _, dk}) == Spec.wsel(True{}, Spec.Iss{io, run, k}) : Spec.WE}
      %Equal.sym(Nat, dk, k, a5) : {Spec.wsel(True{}, Spec.Iss{io, run, _}) == Spec.wsel(True{}, Spec.Iss{io, run, k}) : Spec.WE}
      {==}
    case False{}:
      +l0 = {(%Equal.sym(Nat, left, Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)), hl) : {_ == 0n : Nat}
          %Equal.sym(Nat, Nat.sub(N, ij), 0n, dsub_le0(N, ij, PP.p6_nlt_le(ij, N, ev)))
            : {Nat.min(Nat.sub(KT, kt), _) == 0n : Nat}
          dmin0(Nat.sub(KT, kt))) : {left == 0n : Nat}}
      %Equal.sym(Nat, left, 0n, l0) : {Spec.wsel(Nat.is_lt(0n, _), Spec.Iss{io, drun, dk}) == Spec.NoW{} : Spec.WE}
      {==}

def im_we(+ctx: Spec.Ctx, +dim: Impl.DIM, +rim: Spec.RIM, +qs: Nat, +ws: Nat, hrel: Rel(ctx, dim, rim))
  -> {Impl.d_we(Nat.mul(qs, ws), ctx, dim) == Spec.r_we(qs, ws, ctx, rim) : Spec.WE}:
  match ctx:
    case Spec.TCtx{+phs, +N}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (e0, h1) = hrel
          (eN, h2) = h1
          (eok, h3) = h2
          (fits, live) = h3
          %Equal.sym(Impl.DIM, dim, Impl.DT{Nat.add(ij, rem), rem, run, k}, e0)
            : {Impl.d_we(Nat.mul(qs, ws), Spec.TCtx{phs, N}, _) == Spec.r_we(qs, ws, Spec.TCtx{phs, N}, Spec.RT{ij, rem, run, k}) : Spec.WE}
          Equal.cong(Bool, Spec.WE, b => Spec.wsel(b, Spec.Iss{Nat.mul(qs, ws), run, k}), Nat.is_lt(0n, rem), Nat.is_lt(ij, N),
            ti_live(ij, rem, N, fits, live))
        case Spec.RG{ij, kt, g, run, k}:
          (e0, h1) = hrel
          (eN, h2) = h1
          (eok, h3) = h2
          match h3:
    case Spec.GCtx{+KT, +N}:
      match dim:
        case Impl.DG{+jd, +ktd, +gd, +left, +drun, +dk}:
          match rim:
            case Spec.RG{+ij, +kt, +g, +run, +k}:
              (kp, h1) = hrel
              (hkt, h2) = h1
              (hl, ha) = h2
              g_we(Nat.is_lt(ij, N), Nat.mul(qs, ws), KT, N, jd, ktd, gd, left, drun, dk, ij, kt, g, run, k, {==}, hkt, hl, ha)
            case Spec.RT{ij, rem, run, k}:
              match hrel:
        case Impl.DT{je, rem, run, k}:
          match hrel:

def im_exit(+ctx: Spec.Ctx, +dim: Impl.DIM, +rim: Spec.RIM, +cs: Nat, +qs: Nat, +ws: Nat,
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, hrel: Rel(ctx, dim, rim))
  -> {Impl.d_exit(Nat.mul(cs, ws), Nat.mul(qs, ws), ws, dim) == Spec.r_exit(cs, qs, rim) : Spec.Out}:
  match ctx:
    case Spec.TCtx{+phs, +N}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (e0, h1) = hrel
          %Equal.sym(Impl.DIM, dim, Impl.DT{Nat.add(ij, rem), rem, run, k}, e0)
            : {Impl.d_exit(Nat.mul(cs, ws), Nat.mul(qs, ws), ws, _) == Spec.Cont{Spec.St{cs, qs, ij, rem, run, k}} : Spec.Out}
          %Equal.sym(Nat, Nat.div(Nat.mul(cs, ws), ws), cs, dv(cs, ws, wspos))
            : {Spec.Cont{Spec.St{_, Nat.div(Nat.mul(qs, ws), ws), Nat.sub(Nat.add(ij, rem), rem), rem, run, k}} == Spec.Cont{Spec.St{cs, qs, ij, rem, run, k}} : Spec.Out}
          %Equal.sym(Nat, Nat.div(Nat.mul(qs, ws), ws), qs, dv(qs, ws, wspos))
            : {Spec.Cont{Spec.St{cs, _, Nat.sub(Nat.add(ij, rem), rem), rem, run, k}} == Spec.Cont{Spec.St{cs, qs, ij, rem, run, k}} : Spec.Out}
          %Equal.sym(Nat, Nat.sub(Nat.add(ij, rem), rem), ij, dsub(ij, rem))
            : {Spec.Cont{Spec.St{cs, qs, _, rem, run, k}} == Spec.Cont{Spec.St{cs, qs, ij, rem, run, k}} : Spec.Out}
          {==}
        case Spec.RG{ij, kt, g, run, k}:
          (e0, h1) = hrel
          (eN, h2) = h1
          (eok, h3) = h2
          match h3:
    case Spec.GCtx{+KT, +N}:
      match dim:
        case Impl.DG{+jd, +ktd, +gd, +left, +drun, +dk}:
          match rim:
            case Spec.RG{+ij, +kt, +g, +run, +k}:
              {==}
            case Spec.RT{ij, rem, run, k}:
              match hrel:
        case Impl.DT{je, rem, run, k}:
          match hrel:

def imn_t(+phs: List<&2, Spec.Ph>, +N: Nat, +dim: Impl.DIM, +ij: Nat, +rem: Nat, +run: Nat, +k: Nat,
    +e0: {dim == Impl.DT{Nat.add(ij, rem), rem, run, k} : Impl.DIM}, +eN: {N == Spec.total(phs) : Nat},
    +eok: {Laws.phases_ok(phs) == True{} : Bool}, +fits: {Nat.is_le(Nat.add(ij, rem), N) == True{} : Bool},
    +live: {Bool.or(Nat.is_le(N, ij), Nat.is_lt(0n, rem)) == True{} : Bool})
  -> Rel(Spec.TCtx{phs, N}, Impl.d_next(Spec.TCtx{phs, N}, dim), Spec.r_next(Spec.TCtx{phs, N}, Spec.RT{ij, rem, run, k})):
  +hl = ti_live(ij, rem, N, fits, live)
  +ctx2 = {Spec.TCtx{phs, N} : Spec.Ctx}
  ((%Equal.sym(Impl.DIM, dim, Impl.DT{Nat.add(ij, rem), rem, run, k}, e0)
      : {Impl.d_next(ctx2, _) == Laws.dt_of(Spec.rt_step(Nat.is_lt(ij, N), ctx2, ij, rem, run, k)) : Impl.DIM}
    %hl : {Impl.dt_step(Nat.is_lt(0n, rem), ctx2, Nat.add(ij, rem), rem, run, k) ==
      Laws.dt_of(Spec.rt_step(_, ctx2, ij, rem, run, k)) : Impl.DIM}
    ti_next_go(ctx2, ij, rem, run, k)),
    eN, eok, inv_step(Nat.is_lt(ij, N), phs, N, ij, rem, run, k, {==}, eN, eok, fits, live))

# ---- m16g cursor step ----

# a - (1 + b) == (a - b) - 1
def g_sub_pred(a: Nat, b: Nat) -> {Nat.sub(a, 1n+b) == Nat.sub(Nat.sub(a, b), 1n) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      g_sub_pred(ap, bp)

# min(A, B) - 1 == min(A - 1, B - 1)
def g_min_pred(a: Nat, b: Nat) -> {Nat.sub(Nat.min(a, b), 1n) == Nat.min(Nat.sub(a, 1n), Nat.sub(b, 1n)) : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      +x = ap
      %Equal.sym(Nat, Nat.min(Nat.sub(x, 0n), 0n), 0n, dmin0(Nat.sub(x, 0n))) : {0n == _ : Nat}
      {==}
    case 1n+ap 1n+bp:
      +x = ap
      +y = bp
      %Equal.sym(Nat, Nat.sub(Nat.min(x, y), 0n), Nat.min(x, y), PP.ar_sub_zero_r(Nat.min(x, y)))
        : {_ == Nat.min(Nat.sub(x, 0n), Nat.sub(y, 0n)) : Nat}
      %Equal.sym(Nat, Nat.sub(x, 0n), x, PP.ar_sub_zero_r(x)) : {Nat.min(x, y) == Nat.min(_, Nat.sub(y, 0n)) : Nat}
      %Equal.sym(Nat, Nat.sub(y, 0n), y, PP.ar_sub_zero_r(y)) : {Nat.min(x, y) == Nat.min(x, _) : Nat}
      {==}

# (1 + a) - a == 1
def g_sub_succ_self(a: Nat) -> {Nat.sub(1n+a, a) == 1n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      g_sub_succ_self(ap)

# (1 + a) - b == 1 + (a - b) for b <= a
def g_sub_succ_l(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.sub(1n, 1n+bp) == 1n+Nat.sub(0n, 1n+bp) : Nat}, PP.ar_false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      g_sub_succ_l(ap, bp, h)

# x != 0 gives 0 < x
def g_ne0(x: Nat, h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PP.ar_true_false(h))
    case 1n+xp:
      {==}

# jd + kt == ij + ktd and ktd <= kt give jd + (kt - ktd) == ij
def g_jrun(+jd: Nat, +ktd: Nat, +ij: Nat, +kt: Nat, +a1: {Nat.add(jd, kt) == Nat.add(ij, ktd) : Nat},
    +a2: {Nat.is_le(ktd, kt) == True{} : Bool})
  -> {Nat.add(jd, Nat.sub(kt, ktd)) == ij : Nat}:
  +d = Nat.sub(kt, ktd)
  +x = Nat.add(jd, d)
  +e1 = {(%Equal.sym(Nat, Nat.add(ktd, d), kt, PP.ar_sub_add(kt, ktd, a2)) : {Nat.add(jd, _) == Nat.add(ij, ktd) : Nat}
      a1) : {Nat.add(jd, Nat.add(ktd, d)) == Nat.add(ij, ktd) : Nat}}
  +e2 = {Equal.trans(Nat, Nat.add(ktd, x), Nat.add(jd, Nat.add(ktd, d)), Nat.add(ktd, ij),
      Equal.trans(Nat, Nat.add(ktd, x), Nat.add(x, ktd), Nat.add(jd, Nat.add(ktd, d)), PP.ar_add_comm(ktd, x),
        Equal.trans(Nat, Nat.add(x, ktd), Nat.add(jd, Nat.add(d, ktd)), Nat.add(jd, Nat.add(ktd, d)), PP.ar_add_assoc(jd, d, ktd),
          Equal.cong(Nat, Nat, z => Nat.add(jd, z), Nat.add(d, ktd), Nat.add(ktd, d), PP.ar_add_comm(d, ktd)))),
      Equal.trans(Nat, Nat.add(jd, Nat.add(ktd, d)), Nat.add(ij, ktd), Nat.add(ktd, ij), e1, PP.ar_add_comm(ij, ktd)))
    : {Nat.add(ktd, x) == Nat.add(ktd, ij) : Nat}}
  Equal.trans(Nat, x, Nat.sub(Nat.add(ktd, x), ktd), ij, Equal.sym(Nat, Nat.sub(Nat.add(ktd, x), ktd), x, PP.ar_add_sub(ktd, x)),
    (%Equal.sym(Nat, Nat.add(ktd, x), Nat.add(ktd, ij), e2) : {Nat.sub(_, ktd) == ij : Nat}
      PP.ar_add_sub(ktd, ij)))

# left > 0 and left - 1 == 0 give left == 1
def g_one(left: Nat, lp: {Nat.is_lt(0n, left) == True{} : Bool}, h: {Nat.sub(left, 1n) == 0n : Nat}) -> {left == 1n : Nat}:
  match left:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, PP.ar_false_true(lp))
    case 1n+0n:
      {==}
    case 1n+1n+x:
      Empty.absurd({1n+1n+x == 1n : Nat}, PP.ar_zero_succ(x, Equal.sym(Nat, 1n+x, 0n, h)))

# 1 < A and min(A, B) == 1 give B <= 1
def g_le_one(a: Nat, b: Nat, ha: {Nat.is_lt(1n, a) == True{} : Bool}, hm: {Nat.min(a, b) == 1n : Nat})
  -> {Nat.is_le(b, 1n) == True{} : Bool}:
  match a b:
    case _ 0n:
      {==}
    case _ 1n+0n:
      {==}
    case 0n 1n+1n+bp:
      Empty.absurd({Nat.is_le(1n+1n+bp, 1n) == True{} : Bool}, PP.ar_false_true(ha))
    case 1n+0n 1n+1n+bp:
      Empty.absurd({Nat.is_le(1n+1n+bp, 1n) == True{} : Bool}, PP.ar_false_true(ha))
    case 1n+1n+ap 1n+1n+bp:
      Empty.absurd({Nat.is_le(1n+1n+bp, 1n) == True{} : Bool},
        PP.ar_zero_succ(Nat.min(ap, bp), Equal.sym(Nat, 1n+Nat.min(ap, bp), 0n, PP.ar_succ_inj(1n+Nat.min(ap, bp), 0n, hm))))

# After the run's last copy at a group wrap, DIET = true's pointer / left and DIET = false's agree.
def gsrc_t(z: Bool, +KT: Nat, +N: Nat, +j1: Nat, +ij: Nat, +g: Nat, +run: Nat, +k: Nat,
    +ez: {Nat.is_lt(1n+ij, N) == z : Bool}, +hj: {j1 == 1n+ij : Nat}, +kp: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> RelG(KT, N, Impl.dg_src(Nat.is_lt(j1, N), Spec.GCtx{KT, N}, j1, 1n+g, 0n, run, k), Spec.rg_src(z, 1n+ij, 1n+g, run, k)):
  match z:
    case True{}:
      %Equal.sym(Nat, j1, 1n+ij, hj)
        : RelG(KT, N, Impl.dg_src(Nat.is_lt(_, N), Spec.GCtx{KT, N}, _, 1n+g, 0n, run, k), Spec.rg_src(True{}, 1n+ij, 1n+g, run, k))
      %Equal.sym(Bool, Nat.is_lt(1n+ij, N), True{}, ez)
        : RelG(KT, N, Impl.dg_src(_, Spec.GCtx{KT, N}, 1n+ij, 1n+g, 0n, run, k), Spec.rg_src(True{}, 1n+ij, 1n+g, run, k))
      (kp, (kp, (Equal.cong(Nat, Nat, x => Nat.min(x, Nat.sub(N, 1n+ij)), KT, Nat.sub(KT, 0n),
          Equal.sym(Nat, Nat.sub(KT, 0n), KT, PP.ar_sub_zero_r(KT))),
        (%Equal.sym(Bool, Nat.is_lt(1n+ij, N), True{}, ez)
            : gact(_, 1n+ij, 0n, 1n+g, 1n+g, 0n, 1n+ij, 0n, 1n+g, 1n+g, 0n)
          ({==}, ({==}, ({==}, ({==}, {==}))))))))
    case False{}:
      %Equal.sym(Nat, j1, 1n+ij, hj)
        : RelG(KT, N, Impl.dg_src(Nat.is_lt(_, N), Spec.GCtx{KT, N}, _, 1n+g, 0n, run, k), Spec.rg_src(False{}, 1n+ij, 1n+g, run, k))
      %Equal.sym(Bool, Nat.is_lt(1n+ij, N), False{}, ez)
        : RelG(KT, N, Impl.dg_src(_, Spec.GCtx{KT, N}, 1n+ij, 1n+g, 0n, run, k), Spec.rg_src(False{}, 1n+ij, 1n+g, run, k))
      (kp, (kp, (Equal.sym(Nat, Nat.min(Nat.sub(KT, 0n), Nat.sub(N, 1n+ij)), 0n,
          (%Equal.sym(Nat, Nat.sub(N, 1n+ij), 0n, dsub_le0(N, 1n+ij, PP.p6_nlt_le(1n+ij, N, ez)))
              : {Nat.min(Nat.sub(KT, 0n), _) == 0n : Nat}
            dmin0(Nat.sub(KT, 0n)))),
        (%Equal.sym(Bool, Nat.is_lt(1n+ij, N), False{}, ez)
            : gact(_, 1n+ij, 0n, 1n+g, run, k, 1n+ij, 0n, 1n+g, run, k)
          Unit{}))))

# a <= b and c <= b give a - c <= b - c
def g_sub_mono(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +cb: {Nat.is_le(c, b) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  PP.ard_tr(Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)), Nat.is_le(a, Nat.add(c, Nat.sub(b, c))), PP.ar_le_sub_iff(a, c, Nat.sub(b, c)),
    (%Equal.sym(Nat, Nat.add(c, Nat.sub(b, c)), b, PP.ar_sub_add(b, c, cb)) : {Nat.is_le(a, _) == True{} : Bool}
      ab))

def gn2(w: Bool, u: Bool, +KT: Nat, +N: Nat, +jd: Nat, +ktd: Nat, +left: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +ew: {Nat.is_eq(Nat.sub(left, 1n), 0n) == w : Bool}, +eu: {Nat.is_eq(1n+kt, KT) == u : Bool},
    +kp: {Nat.is_lt(0n, KT) == True{} : Bool}, +hkt: {Nat.is_lt(kt, KT) == True{} : Bool},
    +hl: {left == Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)) : Nat},
    +a1: {Nat.add(jd, kt) == Nat.add(ij, ktd) : Nat}, +a2: {Nat.is_le(ktd, kt) == True{} : Bool},
    +hij: {Nat.is_lt(ij, N) == True{} : Bool}, +lp: {Nat.is_lt(0n, left) == True{} : Bool})
  -> RelG(KT, N, Impl.dg_end(w, Spec.GCtx{KT, N}, jd, ktd, g, Nat.sub(left, 1n), run, k),
    Spec.rg_wrap(u, Spec.GCtx{KT, N}, 1n+ij, kt, g, run, k)):
  match w u:
    case False{} False{}:
      +A = Nat.sub(KT, kt)
      +B = Nat.sub(N, ij)
      +X = Nat.sub(KT, 1n+kt)
      +Y = Nat.sub(N, 1n+ij)
      +J1 = Nat.add(jd, Nat.sub(KT, ktd))
      +le1kt = PP.ard_rt(Nat.is_lt(kt, KT), Nat.is_le(1n+kt, KT), PP.ar_lt_succ_le(kt, KT), hkt)
      +c2 = da_lt_ne(1n+kt, KT, le1kt, eu)
      +c3 = {Equal.trans(Nat, Nat.sub(left, 1n), Nat.sub(Nat.min(A, B), 1n), Nat.min(X, Y),
          Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), left, Nat.min(A, B), hl),
          Equal.trans(Nat, Nat.sub(Nat.min(A, B), 1n), Nat.min(Nat.sub(A, 1n), Nat.sub(B, 1n)), Nat.min(X, Y), g_min_pred(A, B),
            (%Equal.sym(Nat, X, Nat.sub(A, 1n), g_sub_pred(KT, kt)) : {Nat.min(Nat.sub(A, 1n), Nat.sub(B, 1n)) == Nat.min(_, Y) : Nat}
              %Equal.sym(Nat, Y, Nat.sub(B, 1n), g_sub_pred(N, ij)) : {Nat.min(Nat.sub(A, 1n), Nat.sub(B, 1n)) == Nat.min(Nat.sub(A, 1n), _) : Nat}
              {==})))
        : {Nat.sub(left, 1n) == Nat.min(X, Y) : Nat}}
      +lb = Equal.trans(Bool, Nat.is_lt(0n, Nat.min(X, Y)), Nat.is_lt(0n, Nat.sub(left, 1n)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(0n, z), Nat.min(X, Y), Nat.sub(left, 1n), Equal.sym(Nat, Nat.sub(left, 1n), Nat.min(X, Y), c3)),
        g_ne0(Nat.sub(left, 1n), ew))
      +y0 = PP.ar_and_r(Nat.is_lt(0n, X), Nat.is_lt(0n, Y),
        PP.ard_rt(Nat.is_lt(0n, Nat.min(X, Y)), Bool.and(Nat.is_lt(0n, X), Nat.is_lt(0n, Y)), PP.ar_min_lt(0n, X, Y), lb))
      +hij1 = {(%PP.ar_add_zero_r(1n+ij) : {Nat.is_lt(_, N) == True{} : Bool}
          PP.ard_rt(Nat.is_lt(0n, Y), Nat.is_lt(Nat.add(1n+ij, 0n), N), PP.ar_lt_sub_iff(N, 1n+ij, 0n), y0))
        : {Nat.is_lt(1n+ij, N) == True{} : Bool}}
      (kp, (c2, (c3,
        (%Equal.sym(Bool, Nat.is_lt(1n+ij, N), True{}, hij1)
            : gact(_, jd, ktd, g, run, 1n+k, 1n+ij, 1n+kt, g, run, 1n+k)
          (Equal.trans(Nat, Nat.add(jd, 1n+kt), 1n+Nat.add(jd, kt), Nat.add(1n+ij, ktd), PP.ar_add_succ_r(jd, kt),
              Equal.cong(Nat, Nat, z => 1n+z, Nat.add(jd, kt), Nat.add(ij, ktd), a1)),
            (PP.ar_le_trans(ktd, kt, 1n+kt, a2, PP.ar_h_le_succ(kt)), ({==}, ({==}, {==}))))))))
    case False{} True{}:
      +A = Nat.sub(KT, kt)
      +B = Nat.sub(N, ij)
      +X = Nat.sub(KT, 1n+kt)
      +Y = Nat.sub(N, 1n+ij)
      +J1 = Nat.add(jd, Nat.sub(KT, ktd))
      +le1kt = PP.ard_rt(Nat.is_lt(kt, KT), Nat.is_le(1n+kt, KT), PP.ar_lt_succ_le(kt, KT), hkt)
      +ke = PP.ar_eq_true(1n+kt, KT, eu)
      +a_one = {(%ke : {Nat.sub(_, kt) == 1n : Nat}
          g_sub_succ_self(kt)) : {A == 1n : Nat}}
      +le1 = {(%Equal.sym(Nat, left, Nat.min(A, B), hl) : {Nat.is_le(_, 1n) == True{} : Bool}
          Equal.trans(Bool, Nat.is_le(Nat.min(A, B), 1n), Nat.is_le(Nat.min(A, B), A), True{},
            Equal.cong(Nat, Bool, z => Nat.is_le(Nat.min(A, B), z), 1n, A, Equal.sym(Nat, A, 1n, a_one)), PP.p5_min_le_l(A, B)))
        : {Nat.is_le(left, 1n) == True{} : Bool}}
      +s0 = dsub_le0(left, 1n, le1)
      Empty.absurd(RelG(KT, N, Impl.dg_end(False{}, Spec.GCtx{KT, N}, jd, ktd, g, Nat.sub(left, 1n), run, k),
          Spec.rg_wrap(True{}, Spec.GCtx{KT, N}, 1n+ij, kt, g, run, k)),
        PP.ar_true_false(Equal.trans(Bool, True{}, Nat.is_eq(Nat.sub(left, 1n), 0n), False{},
          Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, Nat.sub(left, 1n), Equal.sym(Nat, Nat.sub(left, 1n), 0n, s0)), ew)))
    case True{} True{}:
      +A = Nat.sub(KT, kt)
      +B = Nat.sub(N, ij)
      +X = Nat.sub(KT, 1n+kt)
      +Y = Nat.sub(N, 1n+ij)
      +J1 = Nat.add(jd, Nat.sub(KT, ktd))
      +le1kt = PP.ard_rt(Nat.is_lt(kt, KT), Nat.is_le(1n+kt, KT), PP.ar_lt_succ_le(kt, KT), hkt)
      +s0 = PP.ar_eq_true(Nat.sub(left, 1n), 0n, ew)
      +ke = PP.ar_eq_true(1n+kt, KT, eu)
      +d = Nat.sub(kt, ktd)
      +hJ = {(%ke : {Nat.add(jd, Nat.sub(_, ktd)) == 1n+ij : Nat}
          %Equal.sym(Nat, Nat.sub(1n+kt, ktd), 1n+d, g_sub_succ_l(kt, ktd, a2)) : {Nat.add(jd, _) == 1n+ij : Nat}
          %Equal.sym(Nat, Nat.add(jd, 1n+d), 1n+Nat.add(jd, d), PP.ar_add_succ_r(jd, d)) : {_ == 1n+ij : Nat}
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(jd, d), ij, g_jrun(jd, ktd, ij, kt, a1, a2)))
        : {J1 == 1n+ij : Nat}}
      %Equal.sym(Nat, Nat.sub(left, 1n), 0n, s0)
        : RelG(KT, N, Impl.dg_src(Nat.is_lt(J1, N), Spec.GCtx{KT, N}, J1, 1n+g, _, run, k),
          Spec.rg_src(Nat.is_lt(1n+ij, N), 1n+ij, 1n+g, run, k))
      gsrc_t(Nat.is_lt(1n+ij, N), KT, N, J1, ij, g, run, k, {==}, hJ, kp)
    case True{} False{}:
      +A = Nat.sub(KT, kt)
      +B = Nat.sub(N, ij)
      +X = Nat.sub(KT, 1n+kt)
      +Y = Nat.sub(N, 1n+ij)
      +J1 = Nat.add(jd, Nat.sub(KT, ktd))
      +le1kt = PP.ard_rt(Nat.is_lt(kt, KT), Nat.is_le(1n+kt, KT), PP.ar_lt_succ_le(kt, KT), hkt)
      +s0 = PP.ar_eq_true(Nat.sub(left, 1n), 0n, ew)
      +l1 = g_one(left, lp, s0)
      +c2 = da_lt_ne(1n+kt, KT, le1kt, eu)
      +a2x = PP.ard_rt(Nat.is_lt(Nat.add(kt, 1n), KT), Nat.is_lt(1n, A), Equal.sym(Bool, Nat.is_lt(1n, A), Nat.is_lt(Nat.add(kt, 1n), KT), PP.ar_lt_sub_iff(KT, kt, 1n)),
        (%Equal.sym(Nat, Nat.add(kt, 1n), 1n+kt, da_add1(kt)) : {Nat.is_lt(_, KT) == True{} : Bool}
          c2))
      +hm = Equal.trans(Nat, Nat.min(A, B), left, 1n, Equal.sym(Nat, left, Nat.min(A, B), hl), l1)
      +bl = g_le_one(A, B, a2x, hm)
      +nle = {(%da_add1(ij) : {Nat.is_le(N, _) == True{} : Bool}
          PP.ard_rt(Nat.is_le(B, 1n), Nat.is_le(N, Nat.add(ij, 1n)), PP.ar_le_sub_iff(N, ij, 1n), bl))
        : {Nat.is_le(N, 1n+ij) == True{} : Bool}}
      +d = Nat.sub(kt, ktd)
      +kd = PP.ar_le_trans(ktd, kt, KT, a2, PP.ar_lt_le(kt, KT, hkt))
      +L2 = {(%g_sub_succ_l(kt, ktd, a2) : {Nat.is_le(_, Nat.sub(KT, ktd)) == True{} : Bool}
          g_sub_mono(1n+kt, KT, ktd, le1kt, kd)) : {Nat.is_le(1n+d, Nat.sub(KT, ktd)) == True{} : Bool}}
      +jge = {(%Equal.trans(Nat, Nat.add(jd, 1n+d), 1n+Nat.add(jd, d), 1n+ij, PP.ar_add_succ_r(jd, d),
            Equal.cong(Nat, Nat, z => 1n+z, Nat.add(jd, d), ij, g_jrun(jd, ktd, ij, kt, a1, a2)))
          : {Nat.is_le(_, J1) == True{} : Bool}
          PP.ard_tr(Nat.is_le(Nat.add(jd, 1n+d), J1), Nat.is_le(1n+d, Nat.sub(KT, ktd)), PP.ar_le_add_cancel(jd, 1n+d, Nat.sub(KT, ktd)), L2))
        : {Nat.is_le(1n+ij, J1) == True{} : Bool}}
      +nJ = PP.p6_le_nlt(J1, N, PP.ar_le_trans(N, 1n+ij, J1, nle, jge))
      %Equal.sym(Bool, Nat.is_lt(J1, N), False{}, nJ)
        : RelG(KT, N, Impl.dg_src(_, Spec.GCtx{KT, N}, J1, 1n+g, Nat.sub(left, 1n), run, k), Spec.RG{1n+ij, 1n+kt, g, run, 1n+k})
      %Equal.sym(Nat, Nat.sub(left, 1n), 0n, s0)
        : RelG(KT, N, Impl.dg_src(False{}, Spec.GCtx{KT, N}, J1, 1n+g, _, run, k), Spec.RG{1n+ij, 1n+kt, g, run, 1n+k})
      (kp, (c2, (Equal.sym(Nat, Nat.min(X, Y), 0n,
          (%Equal.sym(Nat, Y, 0n, dsub_le0(N, 1n+ij, nle)) : {Nat.min(X, _) == 0n : Nat}
            dmin0(X))),
        (%Equal.sym(Bool, Nat.is_lt(1n+ij, N), False{}, PP.p6_le_nlt(1n+ij, N, nle))
            : gact(_, J1, 0n, 1n+g, run, k, 1n+ij, 1n+kt, g, run, 1n+k)
          Unit{}))))

def gn(v: Bool, +KT: Nat, +N: Nat, +jd: Nat, +ktd: Nat, +gd: Nat, +left: Nat, +drun: Nat, +dk: Nat,
    +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat, +ev: {Nat.is_lt(ij, N) == v : Bool},
    +kp: {Nat.is_lt(0n, KT) == True{} : Bool}, +hkt: {Nat.is_lt(kt, KT) == True{} : Bool},
    +hl: {left == Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)) : Nat}, ha: gact(v, jd, ktd, gd, drun, dk, ij, kt, g, run, k))
  -> RelG(KT, N, Impl.dg_step(Nat.is_lt(0n, left), Spec.GCtx{KT, N}, jd, ktd, gd, left, drun, dk),
    Spec.rg_step(v, Spec.GCtx{KT, N}, ij, kt, g, run, k)):
  match v:
    case False{}:
      +l0 = {(%Equal.sym(Nat, left, Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)), hl) : {_ == 0n : Nat}
          %Equal.sym(Nat, Nat.sub(N, ij), 0n, dsub_le0(N, ij, PP.p6_nlt_le(ij, N, ev)))
            : {Nat.min(Nat.sub(KT, kt), _) == 0n : Nat}
          dmin0(Nat.sub(KT, kt))) : {left == 0n : Nat}}
      %Equal.sym(Nat, left, 0n, l0)
        : RelG(KT, N, Impl.dg_step(Nat.is_lt(0n, _), Spec.GCtx{KT, N}, jd, ktd, gd, _, drun, dk), Spec.RG{ij, kt, g, run, k})
      (kp, (hkt, (Equal.trans(Nat, 0n, left, Nat.min(Nat.sub(KT, kt), Nat.sub(N, ij)), Equal.sym(Nat, left, 0n, l0), hl),
        (%Equal.sym(Bool, Nat.is_lt(ij, N), False{}, ev) : gact(_, jd, ktd, gd, drun, dk, ij, kt, g, run, k)
          Unit{}))))
    case True{}:
      (a1, r1) = ha
      (a2, r2) = r1
      (a3, r3) = r2
      (a4, a5) = r3
      +a = Nat.sub(KT, kt)
      +b = Nat.sub(N, ij)
      +lp = {(%Equal.sym(Nat, left, Nat.min(a, b), hl) : {Nat.is_lt(0n, _) == True{} : Bool}
          PP.ard_tr(Nat.is_lt(0n, Nat.min(a, b)), Bool.and(Nat.is_lt(0n, a), Nat.is_lt(0n, b)), PP.ar_min_lt(0n, a, b),
            PP.ar_and_intro(Nat.is_lt(0n, a), Nat.is_lt(0n, b), dp_sub_pos(kt, KT, hkt), dp_sub_pos(ij, N, ev))))
        : {Nat.is_lt(0n, left) == True{} : Bool}}
      %Equal.sym(Bool, Nat.is_lt(0n, left), True{}, lp)
        : RelG(KT, N, Impl.dg_step(_, Spec.GCtx{KT, N}, jd, ktd, gd, left, drun, dk), Spec.rg_step(True{}, Spec.GCtx{KT, N}, ij, kt, g, run, k))
      %Equal.sym(Nat, gd, g, a3)
        : RelG(KT, N, Impl.dg_step(True{}, Spec.GCtx{KT, N}, jd, ktd, _, left, drun, dk), Spec.rg_step(True{}, Spec.GCtx{KT, N}, ij, kt, g, run, k))
      %Equal.sym(Nat, drun, run, a4)
        : RelG(KT, N, Impl.dg_step(True{}, Spec.GCtx{KT, N}, jd, ktd, g, left, _, dk), Spec.rg_step(True{}, Spec.GCtx{KT, N}, ij, kt, g, run, k))
      %Equal.sym(Nat, dk, k, a5)
        : RelG(KT, N, Impl.dg_step(True{}, Spec.GCtx{KT, N}, jd, ktd, g, left, run, _), Spec.rg_step(True{}, Spec.GCtx{KT, N}, ij, kt, g, run, k))
      gn2(Nat.is_eq(Nat.sub(left, 1n), 0n), Nat.is_eq(1n+kt, KT), KT, N, jd, ktd, left, ij, kt, g, run, k, {==}, {==}, kp, hkt, hl,
        a1, a2, ev, lp)

def im_next(+ctx: Spec.Ctx, +dim: Impl.DIM, +rim: Spec.RIM, hrel: Rel(ctx, dim, rim))
  -> Rel(ctx, Impl.d_next(ctx, dim), Spec.r_next(ctx, rim)):
  match ctx:
    case Spec.TCtx{+phs, +N}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (e0, h1) = hrel
          (eN, h2) = h1
          (eok, h3) = h2
          (fits, live) = h3
          imn_t(phs, N, dim, ij, rem, run, k, e0, eN, eok, fits, live)
        case Spec.RG{ij, kt, g, run, k}:
          (e0, h1) = hrel
          (eN, h2) = h1
          (eok, h3) = h2
          match h3:
    case Spec.GCtx{+KT, +N}:
      match dim:
        case Impl.DG{+jd, +ktd, +gd, +left, +drun, +dk}:
          match rim:
            case Spec.RG{+ij, +kt, +g, +run, +k}:
              (kp, h1) = hrel
              (hkt, h2) = h1
              (hl, ha) = h2
              gn(Nat.is_lt(ij, N), KT, N, jd, ktd, gd, left, drun, dk, ij, kt, g, run, k, {==}, kp, hkt, hl, ha)
            case Spec.RT{ij, rem, run, k}:
              match hrel:
        case Impl.DT{je, rem, run, k}:
          match hrel:

# ==== (D) the loop body over a phase's iterations ====

# (1 + it) - s == 1 + (it - s) for s <= it
def dsub_succ(+it: Nat, +s: Nat, +h: {Nat.is_le(s, it) == True{} : Bool})
  -> {Nat.sub(1n+it, s) == 1n+Nat.sub(it, s) : Nat}:
  +d = Nat.sub(it, s)
  %PP.ar_sub_add(it, s, h) : {Nat.sub(1n+_, s) == 1n+d : Nat}
  %PP.ar_add_succ_r(s, d) : {Nat.sub(_, s) == 1n+d : Nat}
  PP.ar_add_sub(s, 1n+d)

# A segment flush (or none) is the same Seg event on both sides.
def dw_flush(c: Bool, +G: Nat, +T: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +ctx: Spec.Ctx, +co: Nat, +io: Nat, +xo: Nat, +dim: Impl.DIM, +cs: Nat, +qs: Nat, +rim: Spec.RIM,
    h: {Impl.dwalk(T, s, pf, xr, fo, ws, xi, ctx, co, io, xo, dim) == Spec.rwalk(T, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim) : Spec.Res})
  -> {Impl.dwalk(PSpec.trace.flush(c, G, T), s, pf, xr, fo, ws, xi, ctx, co, io, xo, dim) ==
    Spec.rwalk(PSpec.trace.flush(c, G, T), s, pf, xr, fo, ws, xi, ctx, cs, qs, rim) : Spec.Res}:
  match c:
    case True{}:
      Equal.cong(Spec.Res, Spec.Res, x => Spec.cons(Spec.Seg{G}, x), Impl.dwalk(T, s, pf, xr, fo, ws, xi, ctx, co, io, xo, dim),
        Spec.rwalk(T, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim), h)
    case False{}:
      h

# Over the iterations it, it + 1, ... of a phase starting at s (x_off = ((it - s) mod 2 XR) X_ITER, slots
# as byte offsets, cursors related by Rel), DIET = true emits DIET = false's events and exit state.
def dw_trace(left: Nat, +it: Nat, +e: Nat, +KT: Nat, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +ctx: Spec.Ctx, +cs: Nat, +qs: Nat, +dim: Impl.DIM, +rim: Spec.RIM,
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +cad: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}, +sit: {Nat.is_le(s, it) == True{} : Bool},
    +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool}, +hrel: Rel(ctx, dim, rim))
  -> {Impl.dwalk(PSpec.trace(left, it, e, KT), s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs, ws), Nat.mul(qs, ws),
        Nat.mul(Nat.mod(Nat.sub(it, s), Nat.mul(2n, xr)), xi), dim) ==
      Spec.rwalk(PSpec.trace(left, it, e, KT), s, pf, xr, fo, ws, xi, ctx, cs, qs, rim) : Spec.Res}:
  match left:
    case 0n:
      Equal.cong(Spec.Out, Spec.Res, o => Spec.Res{Nil{}, o}, Impl.d_exit(Nat.mul(cs, ws), Nat.mul(qs, ws), ws, dim),
        Spec.r_exit(cs, qs, rim), im_exit(ctx, dim, rim, cs, qs, ws, wspos, hrel))
    case 1n+r0:
      +r = r0
      +j = Nat.sub(it, s)
      +M = Nat.mul(2n, xr)
      +xo = Nat.mul(Nat.mod(j, M), xi)
      +G = Nat.div(it, KT)
      +C = Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n))
      +T = PSpec.trace(r, 1n+it, e, KT)
      +cs1 = Spec.nxt(cs, pf)
      +qs1 = Spec.nxt(qs, pf)
      +dim1 = Impl.d_next(ctx, dim)
      +rim1 = Spec.r_next(ctx, rim)
      +xo1 = Nat.mul(Nat.mod(Nat.sub(1n+it, s), M), xi)
      +DWE = Impl.d_we(Nat.mul(qs, ws), ctx, dim)
      +RWE = Spec.r_we(qs, ws, ctx, rim)
      +ItR = {Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), Nat.mul(Spec.rpiece(j, xr), xi), Spec.rfold(j, fo)} : Spec.Ev}
      +RW = Spec.rwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, cs1, qs1, rim1)
      +hwe = im_we(ctx, dim, rim, qs, ws, hrel)
      rc = da_ring(cs, pf, ws, hcs, wspos)
      -RA = {Impl.dring(Nat.mul(cs, ws), pf, ws) == Nat.mul(cs1, ws) : Nat}
      -RB = {Nat.is_lt(cs1, pf) == True{} : Bool}
      -QA = {Impl.dring(Nat.mul(qs, ws), pf, ws) == Nat.mul(qs1, ws) : Nat}
      -QB = {Nat.is_lt(qs1, pf) == True{} : Bool}
      +sit1 = PP.ar_le_trans(s, it, 1n+it, sit, PP.ar_h_le_succ(it))
      +exo = {Equal.trans(Nat, Impl.dxnext(xo, xr, xi), Nat.mul(Nat.mod(1n+j, M), xi), xo1,
          da_xstep(j, M, xi, da_2pos(xr, xrpos), xipos),
          Equal.cong(Nat, Nat, z => Nat.mul(Nat.mod(z, M), xi), 1n+j, Nat.sub(1n+it, s),
            Equal.sym(Nat, Nat.sub(1n+it, s), 1n+j, dsub_succ(it, s, sit)))) : {Impl.dxnext(xo, xr, xi) == xo1 : Nat}}
      +ih = dw_trace(r, 1n+it, e, KT, s, pf, xr, fo, ws, xi, ctx, cs1, qs1, dim1, rim1, xrpos, fopos, wspos, xipos, cad, sit1,
        PP.ard_snd(RA, RB, da_ring(cs, pf, ws, hcs, wspos)), PP.ard_snd(QA, QB, da_ring(qs, pf, ws, hqs, wspos)),
        im_next(ctx, dim, rim, hrel))
      +efl = dw_flush(C, G, T, s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs1, ws), Nat.mul(qs1, ws), xo1, dim1, cs1, qs1, rim1, ih)
      %Equal.sym(Spec.XE, Impl.dchunk(xo, j, xr, xi), Spec.rchunk(j, xr), Laws.diet_chunk(j, xr, xi, xrpos, xipos))
        : {Spec.cons(Spec.It{_, DWE, Nat.mul(cs, ws), xo, Impl.dfold(xo, xr, fo, xi)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Impl.dring(Nat.mul(cs, ws), pf, ws),
              Impl.dring(Nat.mul(qs, ws), pf, ws), Impl.dxnext(xo, xr, xi), dim1)) == Spec.cons(ItR, RW) : Spec.Res}
      %Equal.sym(Spec.WE, DWE, RWE, hwe)
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), _, Nat.mul(cs, ws), xo, Impl.dfold(xo, xr, fo, xi)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Impl.dring(Nat.mul(cs, ws), pf, ws),
              Impl.dring(Nat.mul(qs, ws), pf, ws), Impl.dxnext(xo, xr, xi), dim1)) == Spec.cons(ItR, RW) : Spec.Res}
      %Equal.sym(Bool, Impl.dfold(xo, xr, fo, xi), Spec.rfold(j, fo), da_fold(j, xr, fo, xi, xrpos, fopos, xipos, cad))
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), xo, _},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Impl.dring(Nat.mul(cs, ws), pf, ws),
              Impl.dring(Nat.mul(qs, ws), pf, ws), Impl.dxnext(xo, xr, xi), dim1)) == Spec.cons(ItR, RW) : Spec.Res}
      %Equal.sym(Nat, Impl.dxnext(xo, xr, xi), xo1, exo)
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), xo, Spec.rfold(j, fo)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Impl.dring(Nat.mul(cs, ws), pf, ws),
              Impl.dring(Nat.mul(qs, ws), pf, ws), _, dim1)) == Spec.cons(ItR, RW) : Spec.Res}
      %Equal.sym(Nat, Impl.dring(Nat.mul(cs, ws), pf, ws), Nat.mul(cs1, ws), PP.ard_fst(RA, RB, rc))
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), xo, Spec.rfold(j, fo)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, _,
              Impl.dring(Nat.mul(qs, ws), pf, ws), xo1, dim1)) == Spec.cons(ItR, RW) : Spec.Res}
      %Equal.sym(Nat, Impl.dring(Nat.mul(qs, ws), pf, ws), Nat.mul(qs1, ws), PP.ard_fst(QA, QB, da_ring(qs, pf, ws, hqs, wspos)))
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), xo, Spec.rfold(j, fo)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs1, ws), _, xo1, dim1)) ==
          Spec.cons(ItR, RW) : Spec.Res}
      %da_piece(j, xr, xrpos)
        : {Spec.cons(Spec.It{Spec.rchunk(j, xr), RWE, Nat.mul(cs, ws), Nat.mul(_, xi), Spec.rfold(j, fo)},
            Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs1, ws), Nat.mul(qs1, ws), xo1, dim1)) ==
          Spec.cons(ItR, RW) : Spec.Res}
      Equal.cong(Spec.Res, Spec.Res, x => Spec.cons(ItR, x),
        Impl.dwalk(PSpec.trace.flush(C, G, T), s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs1, ws), Nat.mul(qs1, ws), xo1, dim1), RW, efl)

# ((s - s) mod M) X_ITER == 0: x_off starts at 0.
def dx0(+s: Nat, +M: Nat, +xi: Nat, +mpos: {Nat.is_lt(0n, M) == True{} : Bool})
  -> {Nat.mul(Nat.mod(Nat.sub(s, s), M), xi) == 0n : Nat}:
  %Equal.sym(Nat, Nat.sub(s, s), 0n, PP.p5_sub_self(s)) : {Nat.mul(Nat.mod(_, M), xi) == 0n : Nat}
  %Equal.sym(Nat, Nat.mod(0n, M), 0n, da_mod_small(0n, M, mpos)) : {Nat.mul(_, xi) == 0n : Nat}
  {==}

def Laws.diet_phase(s, n, kt, phs, pf, xr, fo, ws, xi, cs, qs, ij, rem, run, k, tiles, kts, xrpos, fopos, wspos, xipos,
    cadence, cur, iss, fits, live):
  +e = Nat.add(s, n)
  +ord = PP.ar_le_add_r(s, n)
  +tp = tiles
  +xp = xrpos
  +ctx = Spec.t_ctx(phs)
  +TR = PSpec.trace(Nat.sub(e, s), s, e, kt)
  +D0 = {Impl.DT{Nat.add(ij, rem), rem, run, k} : Impl.DIM}
  +R0 = {Spec.RT{ij, rem, run, k} : Spec.RIM}
  %Equal.sym(List<&2, PSpec.Ev>, Impl.dmainloop(s, e, kt), Part.mainloop(s, e, kt), Laws.diet_skeleton(s, e, kt, ord, tp))
    : {Impl.dwalk(_, s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs, ws), Nat.mul(qs, ws), 0n, D0) ==
      Spec.rwalk(Part.mainloop(s, e, kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, R0) : Spec.Res}
  %Equal.sym(List<&2, PSpec.Ev>, Part.mainloop(s, e, kt), TR, PLaws.mainloop_trace(s, e, kt, ord, tp))
    : {Impl.dwalk(_, s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs, ws), Nat.mul(qs, ws), 0n, D0) ==
      Spec.rwalk(_, s, pf, xr, fo, ws, xi, ctx, cs, qs, R0) : Spec.Res}
  %dx0(s, Nat.mul(2n, xr), xi, da_2pos(xr, xp))
    : {Impl.dwalk(TR, s, pf, xr, fo, ws, xi, ctx, Nat.mul(cs, ws), Nat.mul(qs, ws), _, D0) ==
      Spec.rwalk(TR, s, pf, xr, fo, ws, xi, ctx, cs, qs, R0) : Spec.Res}
  dw_trace(Nat.sub(e, s), s, e, kt, s, pf, xr, fo, ws, xi, ctx, cs, qs, D0, R0, xp, fopos, wspos, xipos, cadence,
    PP.ar_le_refl(s), cur, iss, ({==}, {==}, kts, (fits, live)))

# ==== (E) whole tail / 8201 kernels ====

# The DIET = false cursor invariant holds initially, through the prologue and through a phase.
def init_inv(v: Bool, +phs: List<&2, Spec.Ph>, +ev: {Nat.is_lt(0n, Spec.total(phs)) == v : Bool},
    +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> InvR(Spec.total(phs), Spec.RT{0n, Spec.sel(v, Spec.seek(phs, 0n), 0n), 0n, 0n}):
  match v:
    case True{}:
      -A = {Nat.is_lt(0n, Spec.seek(phs, 0n)) == True{} : Bool}
      -B = {Nat.is_le(Nat.add(0n, Spec.seek(phs, 0n)), Spec.total(phs)) == True{} : Bool}
      (PP.ard_snd(A, B, seek_ok(phs, 0n, ev, ok)),
        (%Equal.sym(Bool, Nat.is_lt(0n, Spec.seek(phs, 0n)), True{}, PP.ard_fst(A, B, seek_ok(phs, 0n, ev, ok)))
            : {Bool.or(Nat.is_le(Spec.total(phs), 0n), _) == True{} : Bool}
          PP.p6_or_true(Nat.is_le(Spec.total(phs), 0n))))
    case False{}:
      (PP.ar_h_le_zero(Spec.total(phs)),
        (%Equal.sym(Bool, Nat.is_le(Spec.total(phs), 0n), True{}, PP.p6_nlt_le(0n, Spec.total(phs), ev))
            : {Bool.or(_, False{}) == True{} : Bool}
          {==}))

def invr_next(+phs: List<&2, Spec.Ph>, +N: Nat, rim: Spec.RIM, +hinv: InvR(N, rim), +eN: {N == Spec.total(phs) : Nat},
    +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> InvR(N, Spec.r_next(Spec.TCtx{phs, N}, rim)):
  match rim:
    case Spec.RT{+ij, +rem, +run, +k}:
      (fits, live) = hinv
      inv_step(Nat.is_lt(ij, N), phs, N, ij, rem, run, k, {==}, eN, ok, fits, live)
    case Spec.RG{ij, kt, g, run, k}:
      match hinv:

def pro_inv(t: Nat, +phs: List<&2, Spec.Ph>, +rim: Spec.RIM, +hinv: InvR(Spec.total(phs), rim),
    +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> InvR(Spec.total(phs), Spec.pro_state(t, Spec.t_ctx(phs), rim)):
  match t:
    case 0n:
      hinv
    case 1n+u:
      pro_inv(u, phs, Spec.r_next(Spec.t_ctx(phs), rim),
        invr_next(phs, Spec.total(phs), rim, hinv, {==}, ok), ok)

# A phase result that carries on: iss_slot < PF and the cursor invariant.
def ResOk(+pf: Nat, +N: Nat, r: Spec.Res) -> Data:
  match r:
    case Spec.Res{e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{cs, +qs, +ij, +rem, +run, +k}:
              P2({Nat.is_lt(qs, pf) == True{} : Bool}, InvR(N, Spec.RT{ij, rem, run, k}))
        case Spec.End{}:
          Empty

def resok_cons(+ev: Spec.Ev, +pf: Nat, +N: Nat, r: Spec.Res, +h: ResOk(pf, N, r)) -> ResOk(pf, N, Spec.cons(ev, r)):
  match r:
    case Spec.Res{e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{cs, qs, ij, rem, run, k}:
              h
        case Spec.End{}:
          match h:

def rwalk_ok(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +phs: List<&2, Spec.Ph>, +N: Nat, +cs: Nat, +qs: Nat, +rim: Spec.RIM,
    +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool}, +hinv: InvR(N, rim),
    +eN: {N == Spec.total(phs) : Nat}, +ok: {Laws.phases_ok(phs) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> ResOk(pf, N, Spec.rwalk(evs, s, pf, xr, fo, ws, xi, Spec.TCtx{phs, N}, cs, qs, rim)):
  match evs:
    case Nil{}:
      match rim:
        case Spec.RT{ij, rem, run, k}:
          (hqs, hinv)
        case Spec.RG{ij, kt, g, run, k}:
          match hinv:
    case ev <> rest0:
      match ev:
        case PSpec.Tile{g, it}:
          +rest = rest0
          -RA = {Impl.dring(Nat.mul(cs, ws), pf, ws) == Nat.mul(Spec.nxt(cs, pf), ws) : Nat}
          -RB = {Nat.is_lt(Spec.nxt(cs, pf), pf) == True{} : Bool}
          -QA = {Impl.dring(Nat.mul(qs, ws), pf, ws) == Nat.mul(Spec.nxt(qs, pf), ws) : Nat}
          -QB = {Nat.is_lt(Spec.nxt(qs, pf), pf) == True{} : Bool}
          +j = Nat.sub(it, s)
          +ctx = {Spec.TCtx{phs, N} : Spec.Ctx}
          resok_cons(Spec.It{Spec.rchunk(j, xr), Spec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(Spec.rpiece(j, xr), xi),
              Spec.rfold(j, fo)}, pf, N,
            Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim)),
            rwalk_ok(rest, s, pf, xr, fo, ws, xi, phs, N, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim),
              PP.ard_snd(RA, RB, da_ring(cs, pf, ws, hcs, wspos)), PP.ard_snd(QA, QB, da_ring(qs, pf, ws, hqs, wspos)),
              invr_next(phs, N, rim, hinv, eN, ok), eN, ok, wspos))
        case PSpec.Flush{g}:
          +rest = rest0
          resok_cons(Spec.Seg{g}, pf, N, Spec.rwalk(rest, s, pf, xr, fo, ws, xi, Spec.TCtx{phs, N}, cs, qs, rim),
            rwalk_ok(rest, s, pf, xr, fo, ws, xi, phs, N, cs, qs, rim, hcs, hqs, hinv, eN, ok, wspos))

# ref_phase from st_of(cs, qs, cursor) carries on.
def phase_ok_st(+p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +phs: List<&2, Spec.Ph>, +cs: Nat, +qs: Nat,
    rim: Spec.RIM, +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool},
    +hinv: InvR(Spec.total(phs), rim), +ok: {Laws.phases_ok(phs) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> ResOk(pf, Spec.total(phs), Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cs, qs, rim))):
  match p:
    case Spec.Ph{+s, +n, +kt}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          rwalk_ok(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, phs, Spec.total(phs), cs, qs,
            Spec.RT{ij, rem, run, k}, hcs, hqs, hinv, {==}, ok, wspos)
        case Spec.RG{ij, kt2, g, run, k}:
          match hinv:

# diet_phase == ref_phase from st_of(cs, qs, cursor).
def phase_eq_st(+p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +phs: List<&2, Spec.Ph>, +cs: Nat, +qs: Nat,
    rim: Spec.RIM, +kp: {Laws.phases_ok([p]) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +cad: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat},
    +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool},
    +hinv: InvR(Spec.total(phs), rim), +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> {Impl.diet_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cs, qs, rim)) ==
    Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cs, qs, rim)) : Spec.Res}:
  match p:
    case Spec.Ph{+s, +n, +kt}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (fits, live) = hinv
          Laws.diet_phase(s, n, kt, phs, pf, xr, fo, ws, xi, cs, qs, ij, rem, run, k,
            PP.ar_and_l(Nat.is_lt(0n, kt), True{}, kp), ok, xrpos, fopos, wspos, xipos, cad, hcs, hqs, fits, live)
        case Spec.RG{ij, kt2, g, run, k}:
          match hinv:

def then_eq(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +phs: List<&2, Spec.Ph>,
    +h: ResOk(pf, Spec.total(phs), r), +kp: {Laws.phases_ok([p]) == True{} : Bool}, +hcr: {Nat.is_lt(cr, pf) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +cad: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}, +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> {Impl.diet_then(r, p, cr, pf, xr, fo, ws, xi, Spec.t_ctx(phs)) == Spec.ref_then(r, p, cr, pf, xr, fo, ws, xi, Spec.t_ctx(phs))
    : List<&2, Spec.Ev>}:
  match r:
    case Spec.Res{+e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{cs, +qs, +ij, +rem, +run, +k}:
              (hqs, hinv) = h
              +rim = {Spec.RT{ij, rem, run, k} : Spec.RIM}
              +S1 = {Spec.St{cr, qs, ij, rem, run, k} : Spec.St}
              %Equal.sym(Spec.Res, Impl.diet_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cr, qs, rim)),
                  Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cr, qs, rim)),
                  phase_eq_st(p, pf, xr, fo, ws, xi, phs, cr, qs, rim, kp, xrpos, fopos, wspos, xipos, cad, hcr, hqs, hinv, ok))
                : {List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, [Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}],
                    Spec.res_all(_))) ==
                  List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, [Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}],
                    Spec.res_all(Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), S1)))) : List<&2, Spec.Ev>}
              {==}
        case Spec.End{}:
          match h:

def then2_eq(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +q: Spec.Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +phs: List<&2, Spec.Ph>, +h: ResOk(pf, Spec.total(phs), r), +kp: {Laws.phases_ok([p]) == True{} : Bool},
    +kq: {Laws.phases_ok([q]) == True{} : Bool}, +hcr: {Nat.is_lt(cr, pf) == True{} : Bool},
    +hcq: {Nat.is_lt(cq, pf) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +fopos: {Nat.is_lt(0n, fo) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +cad: {Nat.mod(Nat.mul(2n, xr), fo) == 0n : Nat}, +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> {Impl.diet_then2(r, p, cr, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)) ==
    Spec.ref_then2(r, p, cr, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)) : List<&2, Spec.Ev>}:
  match r:
    case Spec.Res{+e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{cs, +qs, +ij, +rem, +run, +k}:
              (hqs, hinv) = h
              +rim = {Spec.RT{ij, rem, run, k} : Spec.RIM}
              +S1 = {Spec.St{cr, qs, ij, rem, run, k} : Spec.St}
              +X = {[Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}] : List<&2, Spec.Ev>}
              +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), S1)
              %Equal.sym(Spec.Res, Impl.diet_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.st_of(cr, qs, rim)), RP,
                  phase_eq_st(p, pf, xr, fo, ws, xi, phs, cr, qs, rim, kp, xrpos, fopos, wspos, xipos, cad, hcr, hqs, hinv, ok))
                : {List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, X, Impl.diet_then(_, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)))) ==
                  List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, X, Spec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs))))
                  : List<&2, Spec.Ev>}
              Equal.cong(List<&2, Spec.Ev>, List<&2, Spec.Ev>, z => List.append(&2, Spec.Ev, e, List.append(&2, Spec.Ev, X, z)),
                Impl.diet_then(RP, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)), Spec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)),
                then_eq(RP, q, cq, pf, xr, fo, ws, xi, phs,
                  phase_ok_st(p, pf, xr, fo, ws, xi, phs, cr, qs, rim, hcr, hqs, hinv, ok, wspos), kq, hcq,
                  xrpos, fopos, wspos, xipos, cad, ok))
        case Spec.End{}:
          match h:

# PF - 1 < PF for PF >= 1
def pred_lt(pf: Nat, pos: {Nat.is_lt(0n, pf) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(pf, 1n), pf) == True{} : Bool}:
  match pf:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n), 0n) == True{} : Bool}, PP.ar_false_true(pos))
    case 1n+p0:
      +p = p0
      %Equal.sym(Nat, Nat.sub(p, 0n), p, PP.ar_sub_zero_r(p)) : {Nat.is_lt(_, 1n+p) == True{} : Bool}
      PP.p6_lt_succ(p)

def Laws.diet_mlp(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, kt1, kt2, pfpos, xrpos, fopos, wspos, xipos, cadence, ring2):
  +cdx = cadence
  +xrx = xrpos
  +fox = fopos
  +wsx = wspos
  +xix = xipos
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p1, p2] : List<&2, Spec.Ph>}
  +k1p = kt1
  +k2p = kt2
  +ok = PP.ar_and_intro(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{}), k1p, PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==}))
  +kp1 = PP.ar_and_intro(Nat.is_lt(0n, k1), True{}, k1p, {==})
  +kp2 = PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==})
  +ctx = Spec.t_ctx(phs)
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.t_init(phs))
  +hinv0 = pro_inv(Nat.sub(pf, 1n), phs, Spec.t_init(phs), init_inv(Nat.is_lt(0n, Spec.total(phs)), phs, {==}, ok), ok)
  +pp = pfpos
  +hq = pred_lt(pf, pp)
  +st0 = Spec.st_of(0n, Nat.sub(pf, 1n), R0)
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs))
  +RP = Spec.ref_phase(p1, pf, xr, fo, ws, xi, ctx, st0)
  %Equal.sym(Spec.Res, Impl.diet_phase(p1, pf, xr, fo, ws, xi, ctx, st0), RP,
      phase_eq_st(p1, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, kp1, xrx, fox, wsx, xix, cdx, pp, hq, hinv0, ok))
    : {List.append(&2, Spec.Ev, PRO, Impl.diet_then(_, p2, r2, pf, xr, fo, ws, xi, ctx)) ==
      List.append(&2, Spec.Ev, PRO, Spec.ref_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx)) : List<&2, Spec.Ev>}
  Equal.cong(List<&2, Spec.Ev>, List<&2, Spec.Ev>, z => List.append(&2, Spec.Ev, PRO, z),
    Impl.diet_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx), Spec.ref_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx),
    then_eq(RP, p2, r2, pf, xr, fo, ws, xi, phs, phase_ok_st(p1, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, pp, hq, hinv0, ok, wsx),
      kp2, ring2, xrx, fox, wsx, xix, cdx, ok))

def Laws.diet_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, kt0, kt1, kt2, pfpos, xrpos, fopos, wspos,
    xipos, cadence, ring1, ring2):
  +cdx = cadence
  +xrx = xrpos
  +fox = fopos
  +wsx = wspos
  +xix = xipos
  +p0 = {Spec.Ph{s0, n0, k0} : Spec.Ph}
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p0, p1, p2] : List<&2, Spec.Ph>}
  +k0p = kt0
  +k1p = kt1
  +k2p = kt2
  +ok = PP.ar_and_intro(Nat.is_lt(0n, k0), Bool.and(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{})), k0p,
    PP.ar_and_intro(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{}), k1p, PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==})))
  +kp0 = PP.ar_and_intro(Nat.is_lt(0n, k0), True{}, k0p, {==})
  +kp1 = PP.ar_and_intro(Nat.is_lt(0n, k1), True{}, k1p, {==})
  +kp2 = PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==})
  +ctx = Spec.t_ctx(phs)
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.t_init(phs))
  +hinv0 = pro_inv(Nat.sub(pf, 1n), phs, Spec.t_init(phs), init_inv(Nat.is_lt(0n, Spec.total(phs)), phs, {==}, ok), ok)
  +pp = pfpos
  +hq = pred_lt(pf, pp)
  +st0 = Spec.st_of(0n, Nat.sub(pf, 1n), R0)
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs))
  +RP = Spec.ref_phase(p0, pf, xr, fo, ws, xi, ctx, st0)
  %Equal.sym(Spec.Res, Impl.diet_phase(p0, pf, xr, fo, ws, xi, ctx, st0), RP,
      phase_eq_st(p0, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, kp0, xrx, fox, wsx, xix, cdx, pp, hq, hinv0, ok))
    : {List.append(&2, Spec.Ev, PRO, Impl.diet_then2(_, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx)) ==
      List.append(&2, Spec.Ev, PRO, Spec.ref_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx)) : List<&2, Spec.Ev>}
  Equal.cong(List<&2, Spec.Ev>, List<&2, Spec.Ev>, z => List.append(&2, Spec.Ev, PRO, z),
    Impl.diet_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx), Spec.ref_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx),
    then2_eq(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, phs,
      phase_ok_st(p0, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, pp, hq, hinv0, ok, wsx),
      kp1, kp2, ring1, ring2, xrx, fox, wsx, xix, cdx, ok))

# ==== (F) the m16g kernel ====

# m16g cursor invariant: iss_kt < KT.
def InvG(+KT: Nat, rim: Spec.RIM) -> Data:
  match rim:
    case Spec.RG{ij, +kt, g, run, k}:
      {Nat.is_lt(kt, KT) == True{} : Bool}
    case Spec.RT{ij, rem, run, k}:
      Empty

def g_src_inv(z: Bool, +KT: Nat, +j1: Nat, +g1: Nat, +run: Nat, +k: Nat, +kp: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> InvG(KT, Spec.rg_src(z, j1, g1, run, k)):
  match z:
    case True{}:
      kp
    case False{}:
      kp

def g_wrap_inv(u: Bool, +KT: Nat, +N: Nat, +j1: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +eu: {Nat.is_eq(1n+kt, KT) == u : Bool}, +hkt: {Nat.is_lt(kt, KT) == True{} : Bool})
  -> InvG(KT, Spec.rg_wrap(u, Spec.GCtx{KT, N}, j1, kt, g, run, k)):
  match u:
    case True{}:
      g_src_inv(Nat.is_lt(j1, N), KT, j1, 1n+g, run, k, PP.ar_le_lt_trans(0n, kt, KT, PP.ar_h_le_zero(kt), hkt))
    case False{}:
      da_lt_ne(1n+kt, KT, PP.ard_rt(Nat.is_lt(kt, KT), Nat.is_le(1n+kt, KT), PP.ar_lt_succ_le(kt, KT), hkt), eu)

def g_step_inv(v: Bool, +KT: Nat, +N: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +hkt: {Nat.is_lt(kt, KT) == True{} : Bool})
  -> InvG(KT, Spec.rg_step(v, Spec.GCtx{KT, N}, ij, kt, g, run, k)):
  match v:
    case True{}:
      g_wrap_inv(Nat.is_eq(1n+kt, KT), KT, N, 1n+ij, kt, g, run, k, {==}, hkt)
    case False{}:
      hkt

def g_inv_next(+KT: Nat, +N: Nat, rim: Spec.RIM, +h: InvG(KT, rim)) -> InvG(KT, Spec.r_next(Spec.GCtx{KT, N}, rim)):
  match rim:
    case Spec.RG{+ij, +kt, +g, +run, +k}:
      g_step_inv(Nat.is_lt(ij, N), KT, N, ij, kt, g, run, k, h)
    case Spec.RT{ij, rem, run, k}:
      match h:

def g_pro_inv(t: Nat, +KT: Nat, +N: Nat, +rim: Spec.RIM, +h: InvG(KT, rim))
  -> InvG(KT, Spec.pro_state(t, Spec.GCtx{KT, N}, rim)):
  match t:
    case 0n:
      h
    case 1n+u:
      g_pro_inv(u, KT, N, Spec.r_next(Spec.GCtx{KT, N}, rim), g_inv_next(KT, N, rim, h))

def g_act_refl(v: Bool, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat) -> gact(v, ij, kt, g, run, k, ij, kt, g, run, k):
  match v:
    case True{}:
      ({==}, (PP.ar_le_refl(kt), ({==}, ({==}, {==}))))
    case False{}:
      Unit{}

# iss_left = min(KT - iss_kt, n_iter - iss_j) from the prologue's cursor is related to it.
def g_init_rel(+KT: Nat, +N: Nat, rim: Spec.RIM, +h: InvG(KT, rim)) -> RelG(KT, N, Impl.dg_init(KT, N, rim), rim):
  match rim:
    case Spec.RG{+ij, +kt, +g, +run, +k}:
      (PP.ar_le_lt_trans(0n, kt, KT, PP.ar_h_le_zero(kt), h), (h, ({==}, g_act_refl(Nat.is_lt(ij, N), ij, kt, g, run, k))))
    case Spec.RT{ij, rem, run, k}:
      match h:

def Laws.diet_m16g(s, n, KT, pf, xr, fo, ws, xi, tiles, pfpos, xrpos, fopos, wspos, xipos, cadence):
  +tp = tiles
  +xp = xrpos
  +pp = pfpos
  +e = Nat.add(s, n)
  +ord = PP.ar_le_add_r(s, n)
  +ctx = {Spec.GCtx{KT, n} : Spec.Ctx}
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.g_init(s, KT))
  +D0 = Impl.dg_init(KT, n, R0)
  +TR = PSpec.trace(Nat.sub(e, s), s, e, KT)
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.g_init(s, KT))
  +hinv = g_pro_inv(Nat.sub(pf, 1n), KT, n, Spec.g_init(s, KT), PP.ard_dm_lt(s, KT, tp))
  +eq = {(%Equal.sym(List<&2, PSpec.Ev>, Impl.dmainloop(s, e, KT), Part.mainloop(s, e, KT), Laws.diet_skeleton(s, e, KT, ord, tp))
        : {Impl.dwalk(_, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.mul(Nat.sub(pf, 1n), ws), 0n, D0) ==
          Spec.rwalk(Part.mainloop(s, e, KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0) : Spec.Res}
      %Equal.sym(List<&2, PSpec.Ev>, Part.mainloop(s, e, KT), TR, PLaws.mainloop_trace(s, e, KT, ord, tp))
        : {Impl.dwalk(_, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.mul(Nat.sub(pf, 1n), ws), 0n, D0) ==
          Spec.rwalk(_, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0) : Spec.Res}
      %dx0(s, Nat.mul(2n, xr), xi, da_2pos(xr, xp))
        : {Impl.dwalk(TR, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.mul(Nat.sub(pf, 1n), ws), _, D0) ==
          Spec.rwalk(TR, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0) : Spec.Res}
      dw_trace(Nat.sub(e, s), s, e, KT, s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), D0, R0, xp, fopos, wspos, xipos, cadence,
        PP.ar_le_refl(s), pp, pred_lt(pf, pp), g_init_rel(KT, n, R0, hinv)))
    : {Impl.dwalk(Impl.dmainloop(s, e, KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.mul(Nat.sub(pf, 1n), ws), 0n, D0) ==
      Spec.rwalk(Part.mainloop(s, e, KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0) : Spec.Res}}
  Equal.cong(Spec.Res, List<&2, Spec.Ev>, r => List.append(&2, Spec.Ev, PRO, Spec.res_evs(r)),
    Impl.dwalk(Impl.dmainloop(s, e, KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.mul(Nat.sub(pf, 1n), ws), 0n, D0),
    Spec.rwalk(Part.mainloop(s, e, KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0), eq)

# ==== (G) must never: every offset inside its buffer ====

def ir_app(a: List<&2, Spec.Ev>, +b: List<&2, Spec.Ev>, +rl: Nat, +xl: Nat, +ha: {Laws.in_ring(a, rl, xl) == True{} : Bool},
    +hb: {Laws.in_ring(b, rl, xl) == True{} : Bool})
  -> {Laws.in_ring(List.append(&2, Spec.Ev, a, b), rl, xl) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case ev <> rest0:
      match ev:
        case Spec.It{x, +w, +ring, +xoff, fold}:
          +rest = rest0
          +A = Laws.we_in(w, rl)
          +R = Nat.is_lt(ring, rl)
          +X = Nat.is_lt(xoff, xl)
          +T = Laws.in_ring(rest, rl, xl)
          +h1 = PP.ar_and_r(A, Bool.and(R, Bool.and(X, T)), ha)
          +h2 = PP.ar_and_r(R, Bool.and(X, T), h1)
          PP.ar_and_intro(A, Bool.and(R, Bool.and(X, Laws.in_ring(List.append(&2, Spec.Ev, rest, b), rl, xl))),
            PP.ar_and_l(A, Bool.and(R, Bool.and(X, T)), ha),
            PP.ar_and_intro(R, Bool.and(X, Laws.in_ring(List.append(&2, Spec.Ev, rest, b), rl, xl)), PP.ar_and_l(R, Bool.and(X, T), h1),
              PP.ar_and_intro(X, Laws.in_ring(List.append(&2, Spec.Ev, rest, b), rl, xl), PP.ar_and_l(X, T, h2),
                ir_app(rest, b, rl, xl, PP.ar_and_r(X, T, h2), hb))))
        case Spec.Seg{g}:
          +rest = rest0
          ir_app(rest, b, rl, xl, ha, hb)
        case Spec.Pro{+w}:
          +rest = rest0
          PP.ar_and_intro(Laws.we_in(w, rl), Laws.in_ring(List.append(&2, Spec.Ev, rest, b), rl, xl),
            PP.ar_and_l(Laws.we_in(w, rl), Laws.in_ring(rest, rl, xl), ha),
            ir_app(rest, b, rl, xl, PP.ar_and_r(Laws.we_in(w, rl), Laws.in_ring(rest, rl, xl), ha), hb))
        case Spec.Exit{st}:
          +rest = rest0
          ir_app(rest, b, rl, xl, ha, hb)

def we_ok(b: Bool, +off: Nat, +run: Nat, +k: Nat, +rl: Nat, +h: {Nat.is_lt(off, rl) == True{} : Bool})
  -> {Laws.we_in(Spec.wsel(b, Spec.Iss{off, run, k}), rl) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def rwe_in(+qs: Nat, +ws: Nat, +ctx: Spec.Ctx, rim: Spec.RIM, +pf: Nat, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Laws.we_in(Spec.r_we(qs, ws, ctx, rim), Nat.mul(pf, ws)) == True{} : Bool}:
  match rim:
    case Spec.RT{+ij, rem, +run, +k}:
      we_ok(Nat.is_lt(ij, Spec.ctx_n(ctx)), Nat.mul(qs, ws), run, k, Nat.mul(pf, ws),
        PP.ard_tr(Nat.is_lt(Nat.mul(qs, ws), Nat.mul(pf, ws)), Nat.is_lt(qs, pf), PP.ar_mul_lt_cancel(qs, pf, ws, wspos), hqs))
    case Spec.RG{+ij, kt, g, +run, +k}:
      we_ok(Nat.is_lt(ij, Spec.ctx_n(ctx)), Nat.mul(qs, ws), run, k, Nat.mul(pf, ws),
        PP.ard_tr(Nat.is_lt(Nat.mul(qs, ws), Nat.mul(pf, ws)), Nat.is_lt(qs, pf), PP.ar_mul_lt_cancel(qs, pf, ws, wspos), hqs))

def res_evs_cons(+ev: Spec.Ev, r: Spec.Res) -> {Spec.res_evs(Spec.cons(ev, r)) == ev <> Spec.res_evs(r) : List<&2, Spec.Ev>}:
  match r:
    case Spec.Res{e, o}:
      {==}

def ir_walk(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx,
    +cs: Nat, +qs: Nat, +rim: Spec.RIM, +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Laws.in_ring(Spec.res_evs(Spec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), Nat.mul(pf, ws),
    Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case PSpec.Tile{g, it}:
          +rest = rest0
          +j = Nat.sub(it, s)
          +M = Nat.mul(2n, xr)
          +rl = Nat.mul(pf, ws)
          +xl = Nat.mul(M, xi)
          -RA = {Impl.dring(Nat.mul(cs, ws), pf, ws) == Nat.mul(Spec.nxt(cs, pf), ws) : Nat}
          -RB = {Nat.is_lt(Spec.nxt(cs, pf), pf) == True{} : Bool}
          -QA = {Impl.dring(Nat.mul(qs, ws), pf, ws) == Nat.mul(Spec.nxt(qs, pf), ws) : Nat}
          -QB = {Nat.is_lt(Spec.nxt(qs, pf), pf) == True{} : Bool}
          +IT = {Spec.It{Spec.rchunk(j, xr), Spec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(Spec.rpiece(j, xr), xi),
            Spec.rfold(j, fo)} : Spec.Ev}
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim))
          +pl = {(%Equal.sym(Nat, Spec.rpiece(j, xr), Nat.mod(j, M), da_piece(j, xr, xrpos)) : {Nat.is_lt(_, M) == True{} : Bool}
              PP.ard_dm_lt(j, M, da_2pos(xr, xrpos))) : {Nat.is_lt(Spec.rpiece(j, xr), M) == True{} : Bool}}
          %Equal.sym(List<&2, Spec.Ev>, Spec.res_evs(Spec.cons(IT, X)), IT <> Spec.res_evs(X), res_evs_cons(IT, X)) : {Laws.in_ring(_, rl, xl) == True{} : Bool}
          PP.ar_and_intro(Laws.we_in(Spec.r_we(qs, ws, ctx, rim), rl),
            Bool.and(Nat.is_lt(Nat.mul(cs, ws), rl), Bool.and(Nat.is_lt(Nat.mul(Spec.rpiece(j, xr), xi), xl), Laws.in_ring(Spec.res_evs(X), rl, xl))),
            rwe_in(qs, ws, ctx, rim, pf, hqs, wspos),
            PP.ar_and_intro(Nat.is_lt(Nat.mul(cs, ws), rl), Bool.and(Nat.is_lt(Nat.mul(Spec.rpiece(j, xr), xi), xl), Laws.in_ring(Spec.res_evs(X), rl, xl)),
              PP.ard_tr(Nat.is_lt(Nat.mul(cs, ws), rl), Nat.is_lt(cs, pf), PP.ar_mul_lt_cancel(cs, pf, ws, wspos), hcs),
              PP.ar_and_intro(Nat.is_lt(Nat.mul(Spec.rpiece(j, xr), xi), xl), Laws.in_ring(Spec.res_evs(X), rl, xl),
                PP.ard_tr(Nat.is_lt(Nat.mul(Spec.rpiece(j, xr), xi), xl), Nat.is_lt(Spec.rpiece(j, xr), M), PP.ar_mul_lt_cancel(Spec.rpiece(j, xr), M, xi, xipos), pl),
                ir_walk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim),
                  PP.ard_snd(RA, RB, da_ring(cs, pf, ws, hcs, wspos)), PP.ard_snd(QA, QB, da_ring(qs, pf, ws, hqs, wspos)),
                  xrpos, xipos, wspos))))
        case PSpec.Flush{g}:
          +rest = rest0
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(List<&2, Spec.Ev>, Spec.res_evs(Spec.cons(Spec.Seg{g}, X)), Spec.Seg{g} <> Spec.res_evs(X), res_evs_cons(Spec.Seg{g}, X))
            : {Laws.in_ring(_, Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}
          ir_walk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim, hcs, hqs, xrpos, xipos, wspos)

def ir_out(o: Spec.Out, +rl: Nat, +xl: Nat) -> {Laws.in_ring(Spec.out_evs(o), rl, xl) == True{} : Bool}:
  match o:
    case Spec.Cont{st}:
      {==}
    case Spec.End{}:
      {==}

def ir_res_all(r: Spec.Res, +rl: Nat, +xl: Nat, +h: {Laws.in_ring(Spec.res_evs(r), rl, xl) == True{} : Bool})
  -> {Laws.in_ring(Spec.res_all(r), rl, xl) == True{} : Bool}:
  match r:
    case Spec.Res{+e, +o}:
      ir_app(e, Spec.out_evs(o), rl, xl, h, ir_out(o, rl, xl))

# The prologue copies slots d, d + 1, ... (d + t <= PF).
def ir_pro(t: Nat, +d: Nat, +ws: Nat, +ctx: Spec.Ctx, +rim: Spec.RIM, +pf: Nat, +xl: Nat,
    +hd: {Nat.is_le(Nat.add(d, t), pf) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Laws.in_ring(Spec.pro(t, d, ws, ctx, rim), Nat.mul(pf, ws), xl) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+u0:
      +u = u0
      +hd1 = {(%PP.ar_add_succ_r(d, u) : {Nat.is_le(_, pf) == True{} : Bool}
          hd) : {Nat.is_le(1n+Nat.add(d, u), pf) == True{} : Bool}}
      +dlt = PP.ar_le_lt_trans(d, Nat.add(d, u), pf, PP.ar_le_add_r(d, u), PP.ard_rt(Nat.is_le(1n+Nat.add(d, u), pf), Nat.is_lt(Nat.add(d, u), pf),
        Equal.sym(Bool, Nat.is_lt(Nat.add(d, u), pf), Nat.is_le(1n+Nat.add(d, u), pf), PP.ar_lt_succ_le(Nat.add(d, u), pf)), hd1))
      PP.ar_and_intro(Laws.we_in(Spec.r_we(d, ws, ctx, rim), Nat.mul(pf, ws)),
        Laws.in_ring(Spec.pro(u, 1n+d, ws, ctx, Spec.r_next(ctx, rim)), Nat.mul(pf, ws), xl),
        rwe_in(d, ws, ctx, rim, pf, dlt, wspos),
        ir_pro(u, 1n+d, ws, ctx, Spec.r_next(ctx, rim), pf, xl, hd1, wspos))

# A phase's events from st_of(cs, qs, cursor).
def ir_phase(+p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, +cs: Nat, +qs: Nat, rim: Spec.RIM,
    +hcs: {Nat.is_lt(cs, pf) == True{} : Bool}, +hqs: {Nat.is_lt(qs, pf) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Laws.in_ring(Spec.res_evs(Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, Spec.st_of(cs, qs, rim))), Nat.mul(pf, ws),
    Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}:
  match p:
    case Spec.Ph{+s, +n, +kt}:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          ir_walk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, Spec.RT{ij, rem, run, k}, hcs, hqs,
            xrpos, xipos, wspos)
        case Spec.RG{ij, kt2, g, run, k}:
          ir_walk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, Spec.RT{0n, 0n, 0n, 0n}, hcs, hqs,
            xrpos, xipos, wspos)

def ir_then(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +phs: List<&2, Spec.Ph>,
    +h: ResOk(pf, Spec.total(phs), r), +he: {Laws.in_ring(Spec.res_evs(r), Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool},
    +hcr: {Nat.is_lt(cr, pf) == True{} : Bool}, +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool},
    +xipos: {Nat.is_lt(0n, xi) == True{} : Bool}, +wspos: {Nat.is_lt(0n, ws) == True{} : Bool})
  -> {Laws.in_ring(Spec.ref_then(r, p, cr, pf, xr, fo, ws, xi, Spec.t_ctx(phs)), Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}:
  match r:
    case Spec.Res{+e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{+cs, +qs, +ij, +rem, +run, +k}:
              (hqs, hinv) = h
              +rl = Nat.mul(pf, ws)
              +xl = Nat.mul(Nat.mul(2n, xr), xi)
              +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.St{cr, qs, ij, rem, run, k})
              ir_app(e, List.append(&2, Spec.Ev, [Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}], Spec.res_all(RP)), rl, xl, he,
                ir_app([Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}], Spec.res_all(RP), rl, xl, {==},
                  ir_res_all(RP, rl, xl, ir_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), cr, qs, Spec.RT{ij, rem, run, k}, hcr, hqs,
                    xrpos, xipos, wspos))))
        case Spec.End{}:
          match h:

def ir_then2(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +q: Spec.Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +phs: List<&2, Spec.Ph>, +h: ResOk(pf, Spec.total(phs), r),
    +he: {Laws.in_ring(Spec.res_evs(r), Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool},
    +hcr: {Nat.is_lt(cr, pf) == True{} : Bool}, +hcq: {Nat.is_lt(cq, pf) == True{} : Bool},
    +xrpos: {Nat.is_lt(0n, xr) == True{} : Bool}, +xipos: {Nat.is_lt(0n, xi) == True{} : Bool},
    +wspos: {Nat.is_lt(0n, ws) == True{} : Bool}, +ok: {Laws.phases_ok(phs) == True{} : Bool})
  -> {Laws.in_ring(Spec.ref_then2(r, p, cr, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs)), Nat.mul(pf, ws), Nat.mul(Nat.mul(2n, xr), xi)) == True{} : Bool}:
  match r:
    case Spec.Res{+e, o}:
      match o:
        case Spec.Cont{st}:
          match st:
            case Spec.St{+cs, +qs, +ij, +rem, +run, +k}:
              (hqs, hinv) = h
              +rl = Nat.mul(pf, ws)
              +xl = Nat.mul(Nat.mul(2n, xr), xi)
              +rim = {Spec.RT{ij, rem, run, k} : Spec.RIM}
              +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), Spec.St{cr, qs, ij, rem, run, k})
              +TH = Spec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, Spec.t_ctx(phs))
              ir_app(e, List.append(&2, Spec.Ev, [Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}], TH), rl, xl, he,
                ir_app([Spec.Exit{Spec.St{cs, qs, ij, rem, run, k}}], TH, rl, xl, {==},
                  ir_then(RP, q, cq, pf, xr, fo, ws, xi, phs, phase_ok_st(p, pf, xr, fo, ws, xi, phs, cr, qs, rim, hcr, hqs, hinv, ok, wspos),
                    ir_phase(p, pf, xr, fo, ws, xi, Spec.t_ctx(phs), cr, qs, rim, hcr, hqs, xrpos, xipos, wspos), hcq, xrpos, xipos, wspos)))
        case Spec.End{}:
          match h:

def Laws.diet_mlp_in_ring(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, kt1, kt2, pfpos, xrpos, fopos, wspos, xipos, cadence, ring2):
  +cdx = cadence
  +xrx = xrpos
  +fox = fopos
  +wsx = wspos
  +xix = xipos
  +k1p = kt1
  +k2p = kt2
  +pp = pfpos
  +r2p = ring2
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p1, p2] : List<&2, Spec.Ph>}
  +ok = PP.ar_and_intro(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{}), k1p, PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==}))
  +ctx = Spec.t_ctx(phs)
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.t_init(phs))
  +hinv0 = pro_inv(Nat.sub(pf, 1n), phs, Spec.t_init(phs), init_inv(Nat.is_lt(0n, Spec.total(phs)), phs, {==}, ok), ok)
  +hq = pred_lt(pf, pp)
  +st0 = Spec.st_of(0n, Nat.sub(pf, 1n), R0)
  +rl = Nat.mul(pf, ws)
  +xl = Nat.mul(Nat.mul(2n, xr), xi)
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs))
  +RP = Spec.ref_phase(p1, pf, xr, fo, ws, xi, ctx, st0)
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_mlp(p1, p2, r2, pf, xr, fo, ws, xi), Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi),
      Laws.diet_mlp(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, k1p, k2p, pp, xrx, fox, wsx, xix, cdx, r2p))
    : {Laws.in_ring(_, rl, xl) == True{} : Bool}
  ir_app(PRO, Spec.ref_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx), rl, xl,
    ir_pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs), pf, xl, PP.ar_lt_le(Nat.sub(pf, 1n), pf, hq), wsx),
    ir_then(RP, p2, r2, pf, xr, fo, ws, xi, phs, phase_ok_st(p1, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, pp, hq, hinv0, ok, wsx),
      ir_phase(p1, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, hq, xrx, xix, wsx), r2p, xrx, xix, wsx))

def Laws.diet_tail_in_ring(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, kt0, kt1, kt2, pfpos, xrpos, fopos,
    wspos, xipos, cadence, ring1, ring2):
  +cdx = cadence
  +xrx = xrpos
  +fox = fopos
  +wsx = wspos
  +xix = xipos
  +k0p = kt0
  +k1p = kt1
  +k2p = kt2
  +pp = pfpos
  +r1p = ring1
  +r2p = ring2
  +p0 = {Spec.Ph{s0, n0, k0} : Spec.Ph}
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p0, p1, p2] : List<&2, Spec.Ph>}
  +ok = PP.ar_and_intro(Nat.is_lt(0n, k0), Bool.and(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{})), k0p,
    PP.ar_and_intro(Nat.is_lt(0n, k1), Bool.and(Nat.is_lt(0n, k2), True{}), k1p, PP.ar_and_intro(Nat.is_lt(0n, k2), True{}, k2p, {==})))
  +ctx = Spec.t_ctx(phs)
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.t_init(phs))
  +hinv0 = pro_inv(Nat.sub(pf, 1n), phs, Spec.t_init(phs), init_inv(Nat.is_lt(0n, Spec.total(phs)), phs, {==}, ok), ok)
  +hq = pred_lt(pf, pp)
  +st0 = Spec.st_of(0n, Nat.sub(pf, 1n), R0)
  +rl = Nat.mul(pf, ws)
  +xl = Nat.mul(Nat.mul(2n, xr), xi)
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs))
  +RP = Spec.ref_phase(p0, pf, xr, fo, ws, xi, ctx, st0)
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi), Spec.ref_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi),
      Laws.diet_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, k0p, k1p, k2p, pp, xrx, fox, wsx, xix, cdx, r1p, r2p))
    : {Laws.in_ring(_, rl, xl) == True{} : Bool}
  ir_app(PRO, Spec.ref_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx), rl, xl,
    ir_pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.t_init(phs), pf, xl, PP.ar_lt_le(Nat.sub(pf, 1n), pf, hq), wsx),
    ir_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, phs,
      phase_ok_st(p0, pf, xr, fo, ws, xi, phs, 0n, Nat.sub(pf, 1n), R0, pp, hq, hinv0, ok, wsx),
      ir_phase(p0, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, hq, xrx, xix, wsx), r1p, r2p, xrx, xix, wsx, ok))

def Laws.diet_m16g_in_ring(s, n, KT, pf, xr, fo, ws, xi, tiles, pfpos, xrpos, fopos, wspos, xipos, cadence):
  +cdx = cadence
  +xrx = xrpos
  +fox = fopos
  +wsx = wspos
  +xix = xipos
  +tp = tiles
  +pp = pfpos
  +hq = pred_lt(pf, pp)
  +ctx = {Spec.GCtx{KT, n} : Spec.Ctx}
  +rl = Nat.mul(pf, ws)
  +xl = Nat.mul(Nat.mul(2n, xr), xi)
  +R0 = Spec.pro_state(Nat.sub(pf, 1n), ctx, Spec.g_init(s, KT))
  +PRO = Spec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.g_init(s, KT))
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi), Spec.ref_m16g(s, n, KT, pf, xr, fo, ws, xi),
      Laws.diet_m16g(s, n, KT, pf, xr, fo, ws, xi, tp, pp, xrx, fox, wsx, xix, cdx))
    : {Laws.in_ring(_, rl, xl) == True{} : Bool}
  ir_app(PRO, Spec.res_evs(Spec.rwalk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0)), rl, xl,
    ir_pro(Nat.sub(pf, 1n), 0n, ws, ctx, Spec.g_init(s, KT), pf, xl, PP.ar_lt_le(Nat.sub(pf, 1n), pf, hq), wsx),
    ir_walk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, xr, fo, ws, xi, ctx, 0n, Nat.sub(pf, 1n), R0, pp, hq, xrx, xix, wsx))

# ==== (H) must never: no skipped or duplicated weight copy ====
# The weight copies of a trace, ring offsets dropped ((G) bounds those), are the DIET = false cursor's
# copies over the prologue steps and loop iterations. That cursor copies stream tiles 0 .. n_tot - 1
# (tail / 8201, pointer run + k) or k-tile iterations s .. s + n - 1 (m16g, pointer run * KT + k) once
# each, in order, then nothing; PF - 1 + n_tot steps cover the whole stream.

def wi_nw(w: Spec.WE) -> Spec.WE:
  match w:
    case Spec.NoW{}:
      Spec.NoW{}
    case Spec.Iss{off, run, k}:
      Spec.Iss{0n, run, k}

def wi_wl(evs: List<&2, Spec.Ev>) -> List<&2, Spec.WE>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          wi_nw(w) <> wi_wl(rest)
        case Spec.Seg{g}:
          wi_wl(rest)
        case Spec.Pro{w}:
          wi_nw(w) <> wi_wl(rest)
        case Spec.Exit{st}:
          wi_wl(rest)

# The copies of t cursor steps (a prologue step or a loop iteration: copy if live, then advance).
def wi_cur(t: Nat, +ctx: Spec.Ctx, +rim: Spec.RIM) -> List<&2, Spec.WE>:
  match t:
    case 0n:
      Nil{}
    case 1n+u:
      wi_nw(Spec.r_we(0n, 0n, ctx, rim)) <> wi_cur(u, ctx, Spec.r_next(ctx, rim))

def wi_ft(ws: List<&2, Spec.WE>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      Laws.iss_t(w, wi_ft(rest))

def wi_fg(ws: List<&2, Spec.WE>, +KT: Nat) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      Laws.iss_g(w, KT, wi_fg(rest, KT))

def wi_tiles(evs: List<&2, PSpec.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case PSpec.Tile{g, it}:
          1n+wi_tiles(rest)
        case PSpec.Flush{g}:
          wi_tiles(rest)

def wi_out(r: Spec.Res) -> Spec.Out:
  match r:
    case Spec.Res{e, o}:
      o

def wi_orim(o: Spec.Out) -> Spec.RIM:
  match o:
    case Spec.Cont{st}:
      match st:
        case Spec.St{cs, qs, ij, rem, run, k}:
          Spec.RT{ij, rem, run, k}
    case Spec.End{}:
      Spec.RT{0n, 0n, 0n, 0n}

def wi_norm(rim: Spec.RIM) -> Spec.RIM:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      Spec.RT{ij, rem, run, k}
    case Spec.RG{ij, kt, g, run, k}:
      Spec.RT{0n, 0n, 0n, 0n}

def wi_isrt(rim: Spec.RIM) -> Bool:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      True{}
    case Spec.RG{ij, kt, g, run, k}:
      False{}

def wi_strim(st: Spec.St) -> Spec.RIM:
  match st:
    case Spec.St{cs, qs, ij, rem, run, k}:
      Spec.RT{ij, rem, run, k}

def wi_ph_n(p: Spec.Ph) -> Nat:
  match p:
    case Spec.Ph{+s, n, kt}:
      wi_tiles(Part.mainloop(s, Nat.add(s, n), kt))

# ---- list plumbing ----

def wi_cons2(+x1: Spec.WE, +x2: Spec.WE, +l1: List<&2, Spec.WE>, +l2: List<&2, Spec.WE>, +e1: {x1 == x2 : Spec.WE}, +e2: {l1 == l2 : List<&2, Spec.WE>})
  -> {x1 <> l1 == x2 <> l2 : List<&2, Spec.WE>}:
  Equal.trans(List<&2, Spec.WE>, x1 <> l1, x2 <> l1, x2 <> l2, Equal.cong(Spec.WE, List<&2, Spec.WE>, z => z <> l1, x1, x2, e1),
    Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => x2 <> z, l1, l2, e2))

def wi_ncons2(+x1: Nat, +x2: Nat, +l1: List<&2, Nat>, +l2: List<&2, Nat>, +e1: {x1 == x2 : Nat},
    +e2: {l1 == l2 : List<&2, Nat>})
  -> {x1 <> l1 == x2 <> l2 : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, x1 <> l1, x2 <> l1, x2 <> l2, Equal.cong(Nat, List<&2, Nat>, z => z <> l1, x1, x2, e1),
    Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x2 <> z, l1, l2, e2))

def wi_app2(+x1: List<&2, Spec.WE>, +x2: List<&2, Spec.WE>, +y1: List<&2, Spec.WE>, +y2: List<&2, Spec.WE>, +ex: {x1 == x2 : List<&2, Spec.WE>}, +ey: {y1 == y2 : List<&2, Spec.WE>})
  -> {List.append(&2, Spec.WE, x1, y1) == List.append(&2, Spec.WE, x2, y2) : List<&2, Spec.WE>}:
  Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, x1, y1), List.append(&2, Spec.WE, x2, y1), List.append(&2, Spec.WE, x2, y2),
    Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => List.append(&2, Spec.WE, z, y1), x1, x2, ex),
    Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => List.append(&2, Spec.WE, x2, z), y1, y2, ey))

def wi_nadd2(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat, +ea: {a1 == a2 : Nat}, +eb: {b1 == b2 : Nat})
  -> {Nat.add(a1, b1) == Nat.add(a2, b2) : Nat}:
  Equal.trans(Nat, Nat.add(a1, b1), Nat.add(a2, b1), Nat.add(a2, b2), Equal.cong(Nat, Nat, z => Nat.add(z, b1), a1, a2, ea),
    Equal.cong(Nat, Nat, z => Nat.add(a2, z), b1, b2, eb))

def wi_nilr(xs: List<&2, Spec.WE>) -> {List.append(&2, Spec.WE, xs, Nil{}) == xs : List<&2, Spec.WE>}:
  match xs:
    case Nil{}:
      {==}
    case x0 <> rest0:
      +x = x0
      +rest = rest0
      Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => x <> z, List.append(&2, Spec.WE, rest, Nil{}), rest, wi_nilr(rest))

def wi_app(a: List<&2, Spec.Ev>, +b: List<&2, Spec.Ev>)
  -> {wi_wl(List.append(&2, Spec.Ev, a, b)) == List.append(&2, Spec.WE, wi_wl(a), wi_wl(b)) : List<&2, Spec.WE>}:
  match a:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case Spec.It{x, +w, ring, xoff, fold}:
          +rest = rest0
          Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => wi_nw(w) <> z, wi_wl(List.append(&2, Spec.Ev, rest, b)),
            List.append(&2, Spec.WE, wi_wl(rest), wi_wl(b)), wi_app(rest, b))
        case Spec.Seg{g}:
          wi_app(rest0, b)
        case Spec.Pro{+w}:
          +rest = rest0
          Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => wi_nw(w) <> z, wi_wl(List.append(&2, Spec.Ev, rest, b)),
            List.append(&2, Spec.WE, wi_wl(rest), wi_wl(b)), wi_app(rest, b))
        case Spec.Exit{st}:
          wi_app(rest0, b)

def wi_outnil(o: Spec.Out) -> {wi_wl(Spec.out_evs(o)) == Nil{} : List<&2, Spec.WE>}:
  match o:
    case Spec.Cont{st}:
      {==}
    case Spec.End{}:
      {==}

def wi_all(r: Spec.Res) -> {wi_wl(Spec.res_all(r)) == wi_wl(Spec.res_evs(r)) : List<&2, Spec.WE>}:
  match r:
    case Spec.Res{+e, +o}:
      Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, e, Spec.out_evs(o))), List.append(&2, Spec.WE, wi_wl(e), wi_wl(Spec.out_evs(o))),
        wi_wl(e), wi_app(e, Spec.out_evs(o)),
        Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(e), wi_wl(Spec.out_evs(o))), List.append(&2, Spec.WE, wi_wl(e), Nil{}), wi_wl(e),
          Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => List.append(&2, Spec.WE, wi_wl(e), z), wi_wl(Spec.out_evs(o)), Nil{}, wi_outnil(o)),
          wi_nilr(wi_wl(e))))

# The issued lists are read off the copies.
def wi_itw(w: Spec.WE, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +e: {xs == ys : List<&2, Nat>})
  -> {Laws.iss_t(w, xs) == Laws.iss_t(wi_nw(w), ys) : List<&2, Nat>}:
  match w:
    case Spec.NoW{}:
      e
    case Spec.Iss{off, +run, +k}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.add(run, k) <> z, xs, ys, e)

def wi_it(evs: List<&2, Spec.Ev>) -> {Laws.issued(evs) == wi_ft(wi_wl(evs)) : List<&2, Nat>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          +rest = rest0
          wi_itw(w, Laws.issued(rest), wi_ft(wi_wl(rest)), wi_it(rest))
        case Spec.Seg{g}:
          wi_it(rest0)
        case Spec.Pro{w}:
          +rest = rest0
          wi_itw(w, Laws.issued(rest), wi_ft(wi_wl(rest)), wi_it(rest))
        case Spec.Exit{st}:
          wi_it(rest0)

def wi_igw(w: Spec.WE, +KT: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +e: {xs == ys : List<&2, Nat>})
  -> {Laws.iss_g(w, KT, xs) == Laws.iss_g(wi_nw(w), KT, ys) : List<&2, Nat>}:
  match w:
    case Spec.NoW{}:
      e
    case Spec.Iss{off, +run, +k}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Nat.add(Nat.mul(run, KT), k) <> z, xs, ys, e)

def wi_ig(evs: List<&2, Spec.Ev>, +KT: Nat) -> {Laws.issued_g(evs, KT) == wi_fg(wi_wl(evs), KT) : List<&2, Nat>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case Spec.It{x, w, ring, xoff, fold}:
          +rest = rest0
          wi_igw(w, KT, Laws.issued_g(rest, KT), wi_fg(wi_wl(rest), KT), wi_ig(rest, KT))
        case Spec.Seg{g}:
          wi_ig(rest0, KT)
        case Spec.Pro{w}:
          +rest = rest0
          wi_igw(w, KT, Laws.issued_g(rest, KT), wi_fg(wi_wl(rest), KT), wi_ig(rest, KT))
        case Spec.Exit{st}:
          wi_ig(rest0, KT)

# ---- traces are cursor steps ----

# The copy does not depend on the ring slot it goes to.
def wi_sel(b: Bool, +o: Nat, +run: Nat, +k: Nat)
  -> {wi_nw(Spec.wsel(b, Spec.Iss{o, run, k})) == wi_nw(Spec.wsel(b, Spec.Iss{0n, run, k})) : Spec.WE}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wi_slot(+q: Nat, +ws: Nat, +ctx: Spec.Ctx, rim: Spec.RIM)
  -> {wi_nw(Spec.r_we(q, ws, ctx, rim)) == wi_nw(Spec.r_we(0n, 0n, ctx, rim)) : Spec.WE}:
  match rim:
    case Spec.RT{+ij, rem, +run, +k}:
      wi_sel(Nat.is_lt(ij, Spec.ctx_n(ctx)), Nat.mul(q, ws), run, k)
    case Spec.RG{+ij, kt, g, +run, +k}:
      wi_sel(Nat.is_lt(ij, Spec.ctx_n(ctx)), Nat.mul(q, ws), run, k)

def wi_pro(t: Nat, +d: Nat, +ws: Nat, +ctx: Spec.Ctx, +rim: Spec.RIM)
  -> {wi_wl(Spec.pro(t, d, ws, ctx, rim)) == wi_cur(t, ctx, rim) : List<&2, Spec.WE>}:
  match t:
    case 0n:
      {==}
    case 1n+u0:
      +u = u0
      wi_cons2(wi_nw(Spec.r_we(d, ws, ctx, rim)), wi_nw(Spec.r_we(0n, 0n, ctx, rim)), wi_wl(Spec.pro(u, 1n+d, ws, ctx, Spec.r_next(ctx, rim))),
        wi_cur(u, ctx, Spec.r_next(ctx, rim)), wi_slot(d, ws, ctx, rim), wi_pro(u, 1n+d, ws, ctx, Spec.r_next(ctx, rim)))

def wi_walk(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx,
    +cs: Nat, +qs: Nat, +rim: Spec.RIM)
  -> {wi_wl(Spec.res_evs(Spec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim))) == wi_cur(wi_tiles(evs), ctx, rim) : List<&2, Spec.WE>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest0:
      match ev:
        case PSpec.Tile{g, it}:
          +rest = rest0
          +j = Nat.sub(it, s)
          +IT = {Spec.It{Spec.rchunk(j, xr), Spec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(Spec.rpiece(j, xr), xi),
            Spec.rfold(j, fo)} : Spec.Ev}
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim))
          %Equal.sym(List<&2, Spec.Ev>, Spec.res_evs(Spec.cons(IT, X)), IT <> Spec.res_evs(X), res_evs_cons(IT, X))
            : {wi_wl(_) == wi_cur(1n+wi_tiles(rest), ctx, rim) : List<&2, Spec.WE>}
          wi_cons2(wi_nw(Spec.r_we(qs, ws, ctx, rim)), wi_nw(Spec.r_we(0n, 0n, ctx, rim)), wi_wl(Spec.res_evs(X)),
            wi_cur(wi_tiles(rest), ctx, Spec.r_next(ctx, rim)), wi_slot(qs, ws, ctx, rim),
            wi_walk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim)))
        case PSpec.Flush{g}:
          +rest = rest0
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(List<&2, Spec.Ev>, Spec.res_evs(Spec.cons(Spec.Seg{g}, X)), Spec.Seg{g} <> Spec.res_evs(X), res_evs_cons(Spec.Seg{g}, X))
            : {wi_wl(_) == wi_cur(wi_tiles(rest), ctx, rim) : List<&2, Spec.WE>}
          wi_walk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)

def wi_out_cons(+ev: Spec.Ev, r: Spec.Res) -> {wi_out(Spec.cons(ev, r)) == wi_out(r) : Spec.Out}:
  match r:
    case Spec.Res{e, o}:
      {==}

def wi_exit(+cs: Nat, +qs: Nat, rim: Spec.RIM) -> {wi_orim(Spec.r_exit(cs, qs, rim)) == wi_norm(rim) : Spec.RIM}:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      {==}
    case Spec.RG{ij, kt, g, run, k}:
      {==}

# The cursor a phase hands on is the cursor after its iterations.
def wi_wout(evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx,
    +cs: Nat, +qs: Nat, +rim: Spec.RIM)
  -> {wi_orim(wi_out(Spec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim))) ==
    wi_norm(Spec.pro_state(wi_tiles(evs), ctx, rim)) : Spec.RIM}:
  match evs:
    case Nil{}:
      wi_exit(cs, qs, rim)
    case ev <> rest0:
      match ev:
        case PSpec.Tile{g, it}:
          +rest = rest0
          +j = Nat.sub(it, s)
          +IT = {Spec.It{Spec.rchunk(j, xr), Spec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(Spec.rpiece(j, xr), xi),
            Spec.rfold(j, fo)} : Spec.Ev}
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim))
          %Equal.sym(Spec.Out, wi_out(Spec.cons(IT, X)), wi_out(X), wi_out_cons(IT, X))
            : {wi_orim(_) == wi_norm(Spec.pro_state(1n+wi_tiles(rest), ctx, rim)) : Spec.RIM}
          wi_wout(rest, s, pf, xr, fo, ws, xi, ctx, Spec.nxt(cs, pf), Spec.nxt(qs, pf), Spec.r_next(ctx, rim))
        case PSpec.Flush{g}:
          +rest = rest0
          +X = Spec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(Spec.Out, wi_out(Spec.cons(Spec.Seg{g}, X)), wi_out(X), wi_out_cons(Spec.Seg{g}, X))
            : {wi_orim(_) == wi_norm(Spec.pro_state(wi_tiles(rest), ctx, rim)) : Spec.RIM}
          wi_wout(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)

# a steps then b steps are a + b steps.
def wi_comp(a: Nat, +b: Nat, +ctx: Spec.Ctx, +rim: Spec.RIM)
  -> {List.append(&2, Spec.WE, wi_cur(a, ctx, rim), wi_cur(b, ctx, Spec.pro_state(a, ctx, rim))) == wi_cur(Nat.add(a, b), ctx, rim)
    : List<&2, Spec.WE>}:
  match a:
    case 0n:
      {==}
    case 1n+a0:
      +W = wi_nw(Spec.r_we(0n, 0n, ctx, rim))
      +nx = Spec.r_next(ctx, rim)
      Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, z => W <> z, List.append(&2, Spec.WE, wi_cur(a0, ctx, nx), wi_cur(b, ctx, Spec.pro_state(a0, ctx, nx))),
        wi_cur(Nat.add(a0, b), ctx, nx), wi_comp(a0, b, ctx, nx))

# ---- the tail / 8201 cursor stays a tail cursor ----

def wi_rts(v: Bool, +ctx: Spec.Ctx, +j1: Nat, +r1: Nat, +run: Nat, +k: Nat)
  -> {wi_isrt(Spec.rt_seek(v, ctx, j1, r1, run, k)) == True{} : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def wi_rti(v: Bool, +ctx: Spec.Ctx, +j1: Nat, +r1: Nat, +run: Nat, +k: Nat)
  -> {wi_isrt(Spec.rt_iss(v, ctx, j1, r1, run, k)) == True{} : Bool}:
  match v:
    case True{}:
      wi_rts(Nat.is_lt(j1, Spec.ctx_n(ctx)), ctx, j1, r1, run, k)
    case False{}:
      {==}

def wi_rtst(v: Bool, +ctx: Spec.Ctx, +ij: Nat, +rem: Nat, +run: Nat, +k: Nat)
  -> {wi_isrt(Spec.rt_step(v, ctx, ij, rem, run, k)) == True{} : Bool}:
  match v:
    case True{}:
      wi_rti(Nat.is_eq(Nat.sub(rem, 1n), 0n), ctx, 1n+ij, Nat.sub(rem, 1n), run, k)
    case False{}:
      {==}

def wi_rtn(+ctx: Spec.Ctx, rim: Spec.RIM, h: {wi_isrt(rim) == True{} : Bool}) -> {wi_isrt(Spec.r_next(ctx, rim)) == True{} : Bool}:
  match rim:
    case Spec.RT{+ij, +rem, +run, +k}:
      wi_rtst(Nat.is_lt(ij, Spec.ctx_n(ctx)), ctx, ij, rem, run, k)
    case Spec.RG{ij, kt, g, run, k}:
      Empty.absurd({wi_isrt(Spec.r_next(ctx, Spec.RG{ij, kt, g, run, k})) == True{} : Bool}, PP.ar_false_true(h))

def wi_rtps(t: Nat, +ctx: Spec.Ctx, +rim: Spec.RIM, +h: {wi_isrt(rim) == True{} : Bool})
  -> {wi_isrt(Spec.pro_state(t, ctx, rim)) == True{} : Bool}:
  match t:
    case 0n:
      h
    case 1n+u:
      wi_rtps(u, ctx, Spec.r_next(ctx, rim), wi_rtn(ctx, rim, h))

def wi_nrm(rim: Spec.RIM, h: {wi_isrt(rim) == True{} : Bool}) -> {wi_norm(rim) == rim : Spec.RIM}:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      {==}
    case Spec.RG{ij, kt, g, run, k}:
      Empty.absurd({wi_norm(Spec.RG{ij, kt, g, run, k}) == Spec.RG{ij, kt, g, run, k} : Spec.RIM}, PP.ar_false_true(h))

# ---- a phase has n iterations ----

def wi_tf(c: Bool, +g: Nat, +T: List<&2, PSpec.Ev>) -> {wi_tiles(PSpec.trace.flush(c, g, T)) == wi_tiles(T) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def wi_ttr(left: Nat, +it: Nat, +e: Nat, +KT: Nat) -> {wi_tiles(PSpec.trace(left, it, e, KT)) == left : Nat}:
  match left:
    case 0n:
      {==}
    case 1n+l0:
      +l = l0
      +T = PSpec.trace(l, 1n+it, e, KT)
      +F = PSpec.trace.flush(Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n)), Nat.div(it, KT), T)
      Equal.cong(Nat, Nat, z => 1n+z, wi_tiles(F), l,
        Equal.trans(Nat, wi_tiles(F), wi_tiles(T), l,
          wi_tf(Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n)), Nat.div(it, KT), T), wi_ttr(l, 1n+it, e, KT)))

def wi_phn(+s: Nat, +n: Nat, +kt: Nat, +tiles: {Nat.is_lt(0n, kt) == True{} : Bool}) -> {wi_ph_n(Spec.Ph{s, n, kt}) == n : Nat}:
  +e = Nat.add(s, n)
  +ml = PLaws.mainloop_trace(s, e, kt, PP.ar_le_add_r(s, n), tiles)
  Equal.trans(Nat, wi_tiles(Part.mainloop(s, e, kt)), wi_tiles(PSpec.trace(Nat.sub(e, s), s, e, kt)), n,
    Equal.cong(List<&2, PSpec.Ev>, Nat, z => wi_tiles(z), Part.mainloop(s, e, kt), PSpec.trace(Nat.sub(e, s), s, e, kt), ml),
    Equal.trans(Nat, wi_tiles(PSpec.trace(Nat.sub(e, s), s, e, kt)), Nat.sub(e, s), n, wi_ttr(Nat.sub(e, s), s, e, kt),
      PP.ar_add_sub(s, n)))

# ---- the tail / 8201 cursor copies tiles a, a + 1, ... once each ----

# "b holds while the cursor is live" (d stream tiles still to copy).
def wi_live(d: Nat, b: Bool) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n+x:
      b

def wi_live_t(d: Nat, b: Bool, h: {b == True{} : Bool}) -> {wi_live(d, b) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+x:
      h

# a < 1 + (d + a)
def wi_ltd(+a: Nat, +d: Nat) -> {Nat.is_lt(a, 1n+Nat.add(d, a)) == True{} : Bool}:
  PP.ard_tr(Nat.is_lt(a, 1n+Nat.add(d, a)), Nat.is_le(1n+a, 1n+Nat.add(d, a)), PP.ar_lt_succ_le(a, 1n+Nat.add(d, a)),
    PP.ar_le_add_l(d, a))

# i == a and 1 + (d + a) == N give i < N.
def wi_live_lt(+i: Nat, +a: Nat, +d: Nat, +N: Nat, +e1: {i == a : Nat}, +e2: {1n+Nat.add(d, a) == N : Nat})
  -> {Nat.is_lt(i, N) == True{} : Bool}:
  %e2 : {Nat.is_lt(i, _) == True{} : Bool}
  %Equal.sym(Nat, i, a, e1) : {Nat.is_lt(_, 1n+Nat.add(d, a)) == True{} : Bool}
  wi_ltd(a, d)

# b copied while live and then nothing: 1 + i == 1 + a, and 1 + i >= N forces d == 0.
def wi_dead(d: Nat, b: Bool, +i: Nat, +a: Nat, +N: Nat, +e1: {i == a : Nat}, +e2: {1n+Nat.add(d, a) == N : Nat},
    hz: {Nat.is_lt(1n+i, N) == False{} : Bool})
  -> {wi_live(d, b) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+x0:
      +x = x0
      Empty.absurd({wi_live(1n+x, b) == True{} : Bool},
        PP.ar_false_ne(Nat.is_lt(1n+i, N), hz, wi_live_lt(1n+i, 1n+a, x, N, Equal.cong(Nat, Nat, z => 1n+z, i, a, e1),
          (%Equal.sym(Nat, Nat.add(x, 1n+a), 1n+Nat.add(x, a), PP.ar_add_succ_r(x, a)) : {1n+_ == N : Nat}
            e2))))

def wi_CI(d: Nat, +N: Nat, +a: Nat, rim: Spec.RIM) -> Data:
  match rim:
    case Spec.RT{+ij, rem, +run, +k}:
      P2({ij == a : Nat}, P2({Nat.add(d, a) == N : Nat}, {wi_live(d, Nat.is_eq(Nat.add(run, k), a)) == True{} : Bool}))
    case Spec.RG{ij, kt, g, run, k}:
      {False{} == True{} : Bool}

def wi_ci_seek(z: Bool, +d: Nat, +phs: List<&2, Spec.Ph>, +N: Nat, +a: Nat, +ij: Nat, +r1: Nat, +run: Nat, +k: Nat,
    +ez: {Nat.is_lt(1n+ij, N) == z : Bool}, +e1: {ij == a : Nat}, +e2: {1n+Nat.add(d, a) == N : Nat})
  -> wi_CI(d, N, 1n+a, Spec.rt_seek(z, Spec.TCtx{phs, N}, 1n+ij, r1, run, k)):
  match z:
    case True{}:
      +s1 = Equal.cong(Nat, Nat, y => 1n+y, ij, a, e1)
      +s2 = {(%Equal.sym(Nat, Nat.add(d, 1n+a), 1n+Nat.add(d, a), PP.ar_add_succ_r(d, a)) : {_ == N : Nat}
          e2) : {Nat.add(d, 1n+a) == N : Nat}}
      (s1, (s2, wi_live_t(d, Nat.is_eq(Nat.add(1n+ij, 0n), 1n+a),
        (%Equal.sym(Nat, Nat.add(1n+ij, 0n), 1n+a, Equal.trans(Nat, Nat.add(1n+ij, 0n), 1n+ij, 1n+a, PP.ar_add_zero_r(1n+ij), s1))
            : {Nat.is_eq(_, 1n+a) == True{} : Bool}
          PP.ar_eq_refl(1n+a)))))
    case False{}:
      +s1 = Equal.cong(Nat, Nat, y => 1n+y, ij, a, e1)
      +s2 = {(%Equal.sym(Nat, Nat.add(d, 1n+a), 1n+Nat.add(d, a), PP.ar_add_succ_r(d, a)) : {_ == N : Nat}
          e2) : {Nat.add(d, 1n+a) == N : Nat}}
      (s1, (s2, wi_dead(d, Nat.is_eq(Nat.add(run, k), 1n+a), ij, a, N, e1, e2, ez)))

def wi_ci_iss(w: Bool, +d: Nat, +phs: List<&2, Spec.Ph>, +N: Nat, +a: Nat, +ij: Nat, +r1: Nat, +run: Nat, +k: Nat,
    +e1: {ij == a : Nat}, +e2: {1n+Nat.add(d, a) == N : Nat}, +e3: {Nat.add(run, k) == a : Nat})
  -> wi_CI(d, N, 1n+a, Spec.rt_iss(w, Spec.TCtx{phs, N}, 1n+ij, r1, run, k)):
  match w:
    case True{}:
      wi_ci_seek(Nat.is_lt(1n+ij, N), d, phs, N, a, ij, r1, run, k, {==}, e1, e2)
    case False{}:
      (Equal.cong(Nat, Nat, z => 1n+z, ij, a, e1),
        ((%Equal.sym(Nat, Nat.add(d, 1n+a), 1n+Nat.add(d, a), PP.ar_add_succ_r(d, a)) : {_ == N : Nat}
            e2),
          wi_live_t(d, Nat.is_eq(Nat.add(run, 1n+k), 1n+a),
            (%Equal.sym(Nat, Nat.add(run, 1n+k), 1n+a, Equal.trans(Nat, Nat.add(run, 1n+k), 1n+Nat.add(run, k), 1n+a,
                PP.ar_add_succ_r(run, k), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(run, k), a, e3)))
                : {Nat.is_eq(_, 1n+a) == True{} : Bool}
              PP.ar_eq_refl(1n+a)))))

# A dead cursor copies nothing more.
def wi_done(u: Nat, +phs: List<&2, Spec.Ph>, +N: Nat, +ij: Nat, +rem: Nat, +run: Nat, +k: Nat,
    +hf: {Nat.is_lt(ij, N) == False{} : Bool})
  -> {wi_ft(wi_cur(u, Spec.TCtx{phs, N}, Spec.RT{ij, rem, run, k})) == Nil{} : List<&2, Nat>}:
  match u:
    case 0n:
      {==}
    case 1n+u0:
      +ctx = {Spec.TCtx{phs, N} : Spec.Ctx}
      %Equal.sym(Bool, Nat.is_lt(ij, N), False{}, hf)
        : {Laws.iss_t(wi_nw(Spec.wsel(_, Spec.Iss{0n, run, k})), wi_ft(wi_cur(u0, ctx, Spec.rt_step(_, ctx, ij, rem, run, k))))
          == Nil{} : List<&2, Nat>}
      wi_done(u0, phs, N, ij, rem, run, k, hf)

# From a cursor at tile a with d tiles left, d + u steps copy a .. a + d - 1.
def wi_ct(d: Nat, +u: Nat, +phs: List<&2, Spec.Ph>, +N: Nat, +a: Nat, rim: Spec.RIM, h: wi_CI(d, N, a, rim))
  -> {wi_ft(wi_cur(Nat.add(d, u), Spec.TCtx{phs, N}, rim)) == Laws.rng(d, a) : List<&2, Nat>}:
  match d:
    case 0n:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (e1, h2) = h
          (e2, e3) = h2
          +eqn = Equal.trans(Nat, ij, a, N, e1, e2)
          wi_done(u, phs, N, ij, rem, run, k,
            (%Equal.sym(Nat, ij, N, eqn) : {Nat.is_lt(_, N) == False{} : Bool}
              PP.ar_lt_irrefl(N)))
        case Spec.RG{ij, kt, g, run, k}:
          Empty.absurd({wi_ft(wi_cur(u, Spec.TCtx{phs, N}, Spec.RG{ij, kt, g, run, k})) == Nil{} : List<&2, Nat>}, PP.ar_false_true(h))
    case 1n+dd:
      match rim:
        case Spec.RT{+ij, +rem, +run, +k}:
          (e1, h2) = h
          (e2, e3) = h2
          +d0 = dd
          +e1x = e1
          +e2x = e2
          +ev = PP.ar_eq_true(Nat.add(run, k), a, e3)
          +ctx = {Spec.TCtx{phs, N} : Spec.Ctx}
          +hlt = wi_live_lt(ij, a, d0, N, e1x, e2x)
          +NX = Spec.rt_iss(Nat.is_eq(Nat.sub(rem, 1n), 0n), ctx, 1n+ij, Nat.sub(rem, 1n), run, k)
          %Equal.sym(Bool, Nat.is_lt(ij, N), True{}, hlt)
            : {Laws.iss_t(wi_nw(Spec.wsel(_, Spec.Iss{0n, run, k})), wi_ft(wi_cur(Nat.add(d0, u), ctx, Spec.rt_step(_, ctx, ij, rem, run, k))))
              == Laws.rng(1n+d0, a) : List<&2, Nat>}
          wi_ncons2(Nat.add(run, k), a, wi_ft(wi_cur(Nat.add(d0, u), ctx, NX)), Laws.rng(d0, 1n+a), ev,
            wi_ct(d0, u, phs, N, 1n+a, NX,
              wi_ci_iss(Nat.is_eq(Nat.sub(rem, 1n), 0n), d0, phs, N, a, ij, Nat.sub(rem, 1n), run, k, e1x, e2x, ev)))
        case Spec.RG{ij, kt, g, run, k}:
          +d0 = dd
          Empty.absurd({wi_ft(wi_cur(Nat.add(1n+d0, u), Spec.TCtx{phs, N}, Spec.RG{ij, kt, g, run, k})) == Laws.rng(1n+d0, a)
            : List<&2, Nat>}, PP.ar_false_true(h))

# ---- tail / 8201 kernels: prologue and phases are consecutive cursor steps ----

def wi_so(+cr: Nat, o: Spec.Out) -> {wi_strim(Spec.set_cs(cr, Spec.out_st(o))) == wi_orim(o) : Spec.RIM}:
  match o:
    case Spec.Cont{st}:
      match st:
        case Spec.St{cs, qs, ij, rem, run, k}:
          {==}
    case Spec.End{}:
      {==}

def wi_sto(+cs: Nat, +qs: Nat, rim: Spec.RIM) -> {wi_strim(Spec.st_of(cs, qs, rim)) == wi_norm(rim) : Spec.RIM}:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      {==}
    case Spec.RG{ij, kt, g, run, k}:
      {==}

def wi_rest(o: Spec.Out, +RA: List<&2, Spec.Ev>)
  -> {wi_wl(List.append(&2, Spec.Ev, Spec.out_evs(o), RA)) == wi_wl(RA) : List<&2, Spec.WE>}:
  match o:
    case Spec.Cont{st}:
      {==}
    case Spec.End{}:
      {==}

def wi_phA(p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, st: Spec.St)
  -> {wi_wl(Spec.res_evs(Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st))) == wi_cur(wi_ph_n(p), ctx, wi_strim(st)) : List<&2, Spec.WE>}:
  match p:
    case Spec.Ph{+s, +n, +kt}:
      match st:
        case Spec.St{+cs, +qs, +ij, +rem, +run, +k}:
          wi_walk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, Spec.RT{ij, rem, run, k})

def wi_phB(p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, st: Spec.St)
  -> {wi_orim(wi_out(Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st))) == wi_norm(Spec.pro_state(wi_ph_n(p), ctx, wi_strim(st)))
    : Spec.RIM}:
  match p:
    case Spec.Ph{+s, +n, +kt}:
      match st:
        case Spec.St{+cs, +qs, +ij, +rem, +run, +k}:
          wi_wout(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, Spec.RT{ij, rem, run, k})

# A phase started from a tail cursor R: its copies and the cursor it hands on.
def wi_phR(+p: Spec.Ph, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, +st: Spec.St, +R: Spec.RIM,
    +eR: {wi_strim(st) == R : Spec.RIM}, +hrt: {wi_isrt(R) == True{} : Bool})
  -> {wi_wl(Spec.res_evs(Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st))) == wi_cur(wi_ph_n(p), ctx, R) : List<&2, Spec.WE>} &
    {wi_orim(wi_out(Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st))) == Spec.pro_state(wi_ph_n(p), ctx, R) : Spec.RIM}:
  +n = wi_ph_n(p)
  +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st)
  (Equal.trans(List<&2, Spec.WE>, wi_wl(Spec.res_evs(RP)), wi_cur(n, ctx, wi_strim(st)), wi_cur(n, ctx, R), wi_phA(p, pf, xr, fo, ws, xi, ctx, st),
      Equal.cong(Spec.RIM, List<&2, Spec.WE>, y => wi_cur(n, ctx, y), wi_strim(st), R, eR)),
    Equal.trans(Spec.RIM, wi_orim(wi_out(RP)), wi_norm(Spec.pro_state(n, ctx, wi_strim(st))), Spec.pro_state(n, ctx, R),
      wi_phB(p, pf, xr, fo, ws, xi, ctx, st),
      Equal.trans(Spec.RIM, wi_norm(Spec.pro_state(n, ctx, wi_strim(st))), wi_norm(Spec.pro_state(n, ctx, R)), Spec.pro_state(n, ctx, R),
        Equal.cong(Spec.RIM, Spec.RIM, y => wi_norm(Spec.pro_state(n, ctx, y)), wi_strim(st), R, eR),
        wi_nrm(Spec.pro_state(n, ctx, R), wi_rtps(n, ctx, R, hrt)))))

def wi_then(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: Spec.Ctx, +R: Spec.RIM,
    +hR: {wi_orim(wi_out(r)) == R : Spec.RIM}, +hrt: {wi_isrt(R) == True{} : Bool})
  -> {wi_wl(Spec.ref_then(r, p, cr, pf, xr, fo, ws, xi, ctx)) == List.append(&2, Spec.WE, wi_wl(Spec.res_evs(r)), wi_cur(wi_ph_n(p), ctx, R))
    : List<&2, Spec.WE>}:
  match r:
    case Spec.Res{+e, +o}:
      +st1 = Spec.set_cs(cr, Spec.out_st(o))
      +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st1)
      +RA = Spec.res_all(RP)
      +Y = List.append(&2, Spec.Ev, Spec.out_evs(o), RA)
      +C = wi_cur(wi_ph_n(p), ctx, R)
      -PA = {wi_wl(Spec.res_evs(RP)) == C : List<&2, Spec.WE>}
      -PB = {wi_orim(wi_out(RP)) == Spec.pro_state(wi_ph_n(p), ctx, R) : Spec.RIM}
      +eR = Equal.trans(Spec.RIM, wi_strim(st1), wi_orim(o), R, wi_so(cr, o), hR)
      +eY = Equal.trans(List<&2, Spec.WE>, wi_wl(Y), wi_wl(RA), C, wi_rest(o, RA),
        Equal.trans(List<&2, Spec.WE>, wi_wl(RA), wi_wl(Spec.res_evs(RP)), C, wi_all(RP),
          PP.ard_fst(PA, PB, wi_phR(p, pf, xr, fo, ws, xi, ctx, st1, R, eR, hrt))))
      Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, e, Y)), List.append(&2, Spec.WE, wi_wl(e), wi_wl(Y)), List.append(&2, Spec.WE, wi_wl(e), C),
        wi_app(e, Y), Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, y => List.append(&2, Spec.WE, wi_wl(e), y), wi_wl(Y), C, eY))

def wi_then2(r: Spec.Res, +p: Spec.Ph, +cr: Nat, +q: Spec.Ph, +cq: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat,
    +ctx: Spec.Ctx, +R: Spec.RIM, +hR: {wi_orim(wi_out(r)) == R : Spec.RIM}, +hrt: {wi_isrt(R) == True{} : Bool})
  -> {wi_wl(Spec.ref_then2(r, p, cr, q, cq, pf, xr, fo, ws, xi, ctx)) ==
    List.append(&2, Spec.WE, wi_wl(Spec.res_evs(r)), wi_cur(Nat.add(wi_ph_n(p), wi_ph_n(q)), ctx, R)) : List<&2, Spec.WE>}:
  match r:
    case Spec.Res{+e, +o}:
      +np = wi_ph_n(p)
      +nq = wi_ph_n(q)
      +st1 = Spec.set_cs(cr, Spec.out_st(o))
      +RP = Spec.ref_phase(p, pf, xr, fo, ws, xi, ctx, st1)
      +TH = Spec.ref_then(RP, q, cq, pf, xr, fo, ws, xi, ctx)
      +Y = List.append(&2, Spec.Ev, Spec.out_evs(o), TH)
      +R2 = Spec.pro_state(np, ctx, R)
      +C = wi_cur(Nat.add(np, nq), ctx, R)
      -PA = {wi_wl(Spec.res_evs(RP)) == wi_cur(np, ctx, R) : List<&2, Spec.WE>}
      -PB = {wi_orim(wi_out(RP)) == R2 : Spec.RIM}
      +eR = Equal.trans(Spec.RIM, wi_strim(st1), wi_orim(o), R, wi_so(cr, o), hR)
      +eTH = wi_then(RP, q, cq, pf, xr, fo, ws, xi, ctx, R2, PP.ard_snd(PA, PB, wi_phR(p, pf, xr, fo, ws, xi, ctx, st1, R, eR, hrt)), wi_rtps(np, ctx, R, hrt))
      +eY = Equal.trans(List<&2, Spec.WE>, wi_wl(Y), wi_wl(TH), C, wi_rest(o, TH),
        Equal.trans(List<&2, Spec.WE>, wi_wl(TH), List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(nq, ctx, R2)), C, eTH,
          Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(nq, ctx, R2)),
            List.append(&2, Spec.WE, wi_cur(np, ctx, R), wi_cur(nq, ctx, R2)), C,
            Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, y => List.append(&2, Spec.WE, y, wi_cur(nq, ctx, R2)), wi_wl(Spec.res_evs(RP)), wi_cur(np, ctx, R),
              PP.ard_fst(PA, PB, wi_phR(p, pf, xr, fo, ws, xi, ctx, st1, R, eR, hrt))),
            wi_comp(np, nq, ctx, R))))
      Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, e, Y)), List.append(&2, Spec.WE, wi_wl(e), wi_wl(Y)), List.append(&2, Spec.WE, wi_wl(e), C),
        wi_app(e, Y), Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, y => List.append(&2, Spec.WE, wi_wl(e), y), wi_wl(Y), C, eY))

# The initial tail / 8201 cursor: tile 0, all n_tot tiles to copy.
def wi_ci0(+phs: List<&2, Spec.Ph>) -> wi_CI(Spec.total(phs), Spec.total(phs), 0n, Spec.t_init(phs)):
  ({==}, (PP.ar_add_zero_r(Spec.total(phs)), wi_live_t(Spec.total(phs), Nat.is_eq(0n, 0n), {==})))

# Prologue then a stream of `rest` iterations from the prologue's cursor: pf - 1 + rest steps.
def wi_head(+phs: List<&2, Spec.Ph>, +pf: Nat, +ws: Nat, +REST: List<&2, Spec.Ev>, +rest: Nat,
    +er: {wi_wl(REST) == wi_cur(rest, Spec.t_ctx(phs), Spec.pro_state(Nat.sub(pf, 1n), Spec.t_ctx(phs), Spec.t_init(phs))) : List<&2, Spec.WE>},
    +en: {rest == Spec.total(phs) : Nat})
  -> {wi_ft(wi_wl(List.append(&2, Spec.Ev, Spec.pro(Nat.sub(pf, 1n), 0n, ws, Spec.t_ctx(phs), Spec.t_init(phs)), REST))) ==
    Laws.rng(Spec.total(phs), 0n) : List<&2, Nat>}:
  +ctx = Spec.t_ctx(phs)
  +I = Spec.t_init(phs)
  +P = Nat.sub(pf, 1n)
  +N = Spec.total(phs)
  +PRO = Spec.pro(P, 0n, ws, ctx, I)
  +e1 = Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, PRO, REST)), List.append(&2, Spec.WE, wi_wl(PRO), wi_wl(REST)),
    wi_cur(Nat.add(P, rest), ctx, I), wi_app(PRO, REST),
    Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(PRO), wi_wl(REST)), List.append(&2, Spec.WE, wi_cur(P, ctx, I), wi_cur(rest, ctx, Spec.pro_state(P, ctx, I))),
      wi_cur(Nat.add(P, rest), ctx, I), wi_app2(wi_wl(PRO), wi_cur(P, ctx, I), wi_wl(REST), wi_cur(rest, ctx, Spec.pro_state(P, ctx, I)),
        wi_pro(P, 0n, ws, ctx, I), er),
      wi_comp(P, rest, ctx, I)))
  +e2 = Equal.trans(Nat, Nat.add(P, rest), Nat.add(rest, P), Nat.add(N, P), PP.ar_add_comm(P, rest),
    Equal.cong(Nat, Nat, y => Nat.add(y, P), rest, N, en))
  %Equal.sym(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, PRO, REST)), wi_cur(Nat.add(N, P), ctx, I),
      Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, PRO, REST)), wi_cur(Nat.add(P, rest), ctx, I), wi_cur(Nat.add(N, P), ctx, I), e1,
        Equal.cong(Nat, List<&2, Spec.WE>, y => wi_cur(y, ctx, I), Nat.add(P, rest), Nat.add(N, P), e2)))
    : {wi_ft(_) == Laws.rng(N, 0n) : List<&2, Nat>}
  wi_ct(N, P, phs, N, 0n, I, wi_ci0(phs))

def wi_isrt0(+phs: List<&2, Spec.Ph>, +pf: Nat)
  -> {wi_isrt(Spec.pro_state(Nat.sub(pf, 1n), Spec.t_ctx(phs), Spec.t_init(phs))) == True{} : Bool}:
  wi_rtps(Nat.sub(pf, 1n), Spec.t_ctx(phs), Spec.t_init(phs), {==})

def Laws.diet_mlp_issues(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, kt1, kt2, pfpos, xrpos, fopos, wspos, xipos, cadence, ring2):
  +k1p = kt1
  +k2p = kt2
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p1, p2] : List<&2, Spec.Ph>}
  +ctx = Spec.t_ctx(phs)
  +P = Nat.sub(pf, 1n)
  +R0 = Spec.pro_state(P, ctx, Spec.t_init(phs))
  +h0 = wi_isrt0(phs, pf)
  +st0 = Spec.st_of(0n, P, R0)
  +RP = Spec.ref_phase(p1, pf, xr, fo, ws, xi, ctx, st0)
  +TH = Spec.ref_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx)
  +n1e = wi_phn(s1, n1, k1, k1p)
  +n2e = wi_phn(s2, n2, k2, k2p)
  +R1 = Spec.pro_state(wi_ph_n(p1), ctx, R0)
  -PA = {wi_wl(Spec.res_evs(RP)) == wi_cur(wi_ph_n(p1), ctx, R0) : List<&2, Spec.WE>}
  -PB = {wi_orim(wi_out(RP)) == R1 : Spec.RIM}
  +e0 = Equal.trans(Spec.RIM, wi_strim(st0), wi_norm(R0), R0, wi_sto(0n, P, R0), wi_nrm(R0, h0))
  +eT = wi_then(RP, p2, r2, pf, xr, fo, ws, xi, ctx, R1, PP.ard_snd(PA, PB, wi_phR(p1, pf, xr, fo, ws, xi, ctx, st0, R0, e0, h0)), wi_rtps(wi_ph_n(p1), ctx, R0, h0))
  +er = Equal.trans(List<&2, Spec.WE>, wi_wl(TH), List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(wi_ph_n(p2), ctx, R1)),
    wi_cur(Nat.add(wi_ph_n(p1), wi_ph_n(p2)), ctx, R0), eT,
    Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(wi_ph_n(p2), ctx, R1)),
      List.append(&2, Spec.WE, wi_cur(wi_ph_n(p1), ctx, R0), wi_cur(wi_ph_n(p2), ctx, R1)), wi_cur(Nat.add(wi_ph_n(p1), wi_ph_n(p2)), ctx, R0),
      Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, y => List.append(&2, Spec.WE, y, wi_cur(wi_ph_n(p2), ctx, R1)), wi_wl(Spec.res_evs(RP)), wi_cur(wi_ph_n(p1), ctx, R0),
        PP.ard_fst(PA, PB, wi_phR(p1, pf, xr, fo, ws, xi, ctx, st0, R0, e0, h0))),
      wi_comp(wi_ph_n(p1), wi_ph_n(p2), ctx, R0)))
  +en = Equal.trans(Nat, Nat.add(wi_ph_n(p1), wi_ph_n(p2)), Nat.add(n1, n2), Spec.total(phs),
    wi_nadd2(wi_ph_n(p1), n1, wi_ph_n(p2), n2, n1e, n2e),
    Equal.cong(Nat, Nat, y => Nat.add(n1, y), n2, Nat.add(n2, 0n), Equal.sym(Nat, Nat.add(n2, 0n), n2, PP.ar_add_zero_r(n2))))
  +NN = Nat.add(n1, n2)
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_mlp(p1, p2, r2, pf, xr, fo, ws, xi), Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi),
      Laws.diet_mlp(s1, n1, k1, s2, n2, k2, r2, pf, xr, fo, ws, xi, k1p, k2p, pfpos, xrpos, fopos, wspos, xipos, cadence, ring2))
    : {Laws.issued(_) == Laws.rng(NN, 0n) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Laws.issued(Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi)),
      wi_ft(wi_wl(Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi))), wi_it(Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi)))
    : {_ == Laws.rng(NN, 0n) : List<&2, Nat>}
  %Equal.cong(Nat, Nat, y => Nat.add(n1, y), Nat.add(n2, 0n), n2, PP.ar_add_zero_r(n2)) : {wi_ft(wi_wl(Spec.ref_mlp(p1, p2, r2, pf, xr, fo, ws, xi))) == Laws.rng(_, 0n) : List<&2, Nat>}
  wi_head(phs, pf, ws, TH, Nat.add(wi_ph_n(p1), wi_ph_n(p2)), er, en)

def Laws.diet_tail_issues(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, kt0, kt1, kt2, pfpos, xrpos, fopos,
    wspos, xipos, cadence, ring1, ring2):
  +k0p = kt0
  +k1p = kt1
  +k2p = kt2
  +p0 = {Spec.Ph{s0, n0, k0} : Spec.Ph}
  +p1 = {Spec.Ph{s1, n1, k1} : Spec.Ph}
  +p2 = {Spec.Ph{s2, n2, k2} : Spec.Ph}
  +phs = {[p0, p1, p2] : List<&2, Spec.Ph>}
  +ctx = Spec.t_ctx(phs)
  +P = Nat.sub(pf, 1n)
  +R0 = Spec.pro_state(P, ctx, Spec.t_init(phs))
  +h0 = wi_isrt0(phs, pf)
  +st0 = Spec.st_of(0n, P, R0)
  +RP = Spec.ref_phase(p0, pf, xr, fo, ws, xi, ctx, st0)
  +TH = Spec.ref_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx)
  +m0 = wi_ph_n(p0)
  +m12 = Nat.add(wi_ph_n(p1), wi_ph_n(p2))
  +R1 = Spec.pro_state(m0, ctx, R0)
  -PA = {wi_wl(Spec.res_evs(RP)) == wi_cur(m0, ctx, R0) : List<&2, Spec.WE>}
  -PB = {wi_orim(wi_out(RP)) == R1 : Spec.RIM}
  +e0 = Equal.trans(Spec.RIM, wi_strim(st0), wi_norm(R0), R0, wi_sto(0n, P, R0), wi_nrm(R0, h0))
  +eT = wi_then2(RP, p1, r1, p2, r2, pf, xr, fo, ws, xi, ctx, R1, PP.ard_snd(PA, PB, wi_phR(p0, pf, xr, fo, ws, xi, ctx, st0, R0, e0, h0)),
    wi_rtps(m0, ctx, R0, h0))
  +er = Equal.trans(List<&2, Spec.WE>, wi_wl(TH), List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(m12, ctx, R1)),
    wi_cur(Nat.add(m0, m12), ctx, R0), eT,
    Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(Spec.res_evs(RP)), wi_cur(m12, ctx, R1)),
      List.append(&2, Spec.WE, wi_cur(m0, ctx, R0), wi_cur(m12, ctx, R1)), wi_cur(Nat.add(m0, m12), ctx, R0),
      Equal.cong(List<&2, Spec.WE>, List<&2, Spec.WE>, y => List.append(&2, Spec.WE, y, wi_cur(m12, ctx, R1)), wi_wl(Spec.res_evs(RP)), wi_cur(m0, ctx, R0),
        PP.ard_fst(PA, PB, wi_phR(p0, pf, xr, fo, ws, xi, ctx, st0, R0, e0, h0))),
      wi_comp(m0, m12, ctx, R0)))
  +en = Equal.trans(Nat, Nat.add(m0, m12), Nat.add(n0, Nat.add(n1, n2)), Spec.total(phs),
    wi_nadd2(m0, n0, m12, Nat.add(n1, n2), wi_phn(s0, n0, k0, k0p),
      wi_nadd2(wi_ph_n(p1), n1, wi_ph_n(p2), n2, wi_phn(s1, n1, k1, k1p), wi_phn(s2, n2, k2, k2p))),
    Equal.cong(Nat, Nat, y => Nat.add(n0, Nat.add(n1, y)), n2, Nat.add(n2, 0n), Equal.sym(Nat, Nat.add(n2, 0n), n2, PP.ar_add_zero_r(n2))))
  +NN = Nat.add(n0, Nat.add(n1, n2))
  +REF = Spec.ref_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi)
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_tail(p0, p1, p2, r1, r2, pf, xr, fo, ws, xi), REF,
      Laws.diet_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, xr, fo, ws, xi, k0p, k1p, k2p, pfpos, xrpos, fopos, wspos, xipos,
        cadence, ring1, ring2))
    : {Laws.issued(_) == Laws.rng(NN, 0n) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Laws.issued(REF), wi_ft(wi_wl(REF)), wi_it(REF)) : {_ == Laws.rng(NN, 0n) : List<&2, Nat>}
  %Equal.cong(Nat, Nat, y => Nat.add(n0, Nat.add(n1, y)), Nat.add(n2, 0n), n2, PP.ar_add_zero_r(n2))
    : {wi_ft(wi_wl(REF)) == Laws.rng(_, 0n) : List<&2, Nat>}
  wi_head(phs, pf, ws, TH, Nat.add(m0, m12), er, en)

# ---- the m16g cursor copies k-tile iterations v, v + 1, ... once each ----

# A live m16g cursor points at (g, kt) with g * KT + kt == v.
def wi_gb(+run: Nat, +k: Nat, +g: Nat, +kt: Nat, +KT: Nat, +v: Nat) -> Bool:
  Bool.and(Nat.is_eq(run, g), Bool.and(Nat.is_eq(k, kt), Nat.is_eq(Nat.add(Nat.mul(g, KT), kt), v)))

def wi_CG(d: Nat, +N: Nat, +KT: Nat, +j: Nat, +v: Nat, rim: Spec.RIM) -> Data:
  match rim:
    case Spec.RT{ij, rem, run, k}:
      {False{} == True{} : Bool}
    case Spec.RG{+ij, +kt, +g, +run, +k}:
      P2({ij == j : Nat}, P2({Nat.add(d, j) == N : Nat}, {wi_live(d, wi_gb(run, k, g, kt, KT, v)) == True{} : Bool}))

def wi_eqt(+x: Nat, +y: Nat, +e: {x == y : Nat}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_eq(_, y) == True{} : Bool}
  PP.ar_eq_refl(y)

def wi_cg_src(z: Bool, +d: Nat, +KT: Nat, +N: Nat, +j: Nat, +v: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +ez: {Nat.is_lt(1n+ij, N) == z : Bool}, +ekt: {1n+kt == KT : Nat}, +e1: {ij == j : Nat}, +e2: {1n+Nat.add(d, j) == N : Nat},
    +ex: {Nat.add(Nat.mul(g, KT), kt) == v : Nat})
  -> wi_CG(d, N, KT, 1n+j, 1n+v, Spec.rg_src(z, 1n+ij, 1n+g, run, k)):
  match z:
    case True{}:
      +s1 = Equal.cong(Nat, Nat, y => 1n+y, ij, j, e1)
      +s2 = {(%Equal.sym(Nat, Nat.add(d, 1n+j), 1n+Nat.add(d, j), PP.ar_add_succ_r(d, j)) : {_ == N : Nat}
          e2) : {Nat.add(d, 1n+j) == N : Nat}}
      +MG = Nat.mul(g, KT)
      +X0 = Nat.add(Nat.mul(1n+g, KT), 0n)
      +e01 = PP.ar_add_zero_r(Nat.mul(1n+g, KT))
      +e12 = Equal.cong(Nat, Nat, y => Nat.add(y, MG), KT, 1n+kt, Equal.sym(Nat, 1n+kt, KT, ekt))
      +e23 = Equal.cong(Nat, Nat, y => 1n+y, Nat.add(kt, MG), Nat.add(MG, kt), PP.ar_add_comm(kt, MG))
      +e34 = Equal.cong(Nat, Nat, y => 1n+y, Nat.add(MG, kt), v, ex)
      +ev = Equal.trans(Nat, X0, Nat.add(KT, MG), 1n+v, e01,
        Equal.trans(Nat, Nat.add(KT, MG), Nat.add(1n+kt, MG), 1n+v, e12,
          Equal.trans(Nat, Nat.add(1n+kt, MG), 1n+Nat.add(MG, kt), 1n+v, e23, e34)))
      (s1, (s2, wi_live_t(d, wi_gb(1n+g, 0n, 1n+g, 0n, KT, 1n+v),
        PP.ar_and_intro(Nat.is_eq(1n+g, 1n+g), Bool.and(Nat.is_eq(0n, 0n), Nat.is_eq(X0, 1n+v)), PP.ar_eq_refl(1n+g),
          PP.ar_and_intro(Nat.is_eq(0n, 0n), Nat.is_eq(X0, 1n+v), {==}, wi_eqt(X0, 1n+v, ev))))))
    case False{}:
      +s1 = Equal.cong(Nat, Nat, y => 1n+y, ij, j, e1)
      +s2 = {(%Equal.sym(Nat, Nat.add(d, 1n+j), 1n+Nat.add(d, j), PP.ar_add_succ_r(d, j)) : {_ == N : Nat}
          e2) : {Nat.add(d, 1n+j) == N : Nat}}
      (s1, (s2, wi_dead(d, wi_gb(run, k, 1n+g, 0n, KT, 1n+v), ij, j, N, e1, e2, ez)))

def wi_cg_wrap(w: Bool, +d: Nat, +KT: Nat, +N: Nat, +j: Nat, +v: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +ew: {Nat.is_eq(1n+kt, KT) == w : Bool}, +e1: {ij == j : Nat}, +e2: {1n+Nat.add(d, j) == N : Nat},
    +b1: {Nat.is_eq(run, g) == True{} : Bool}, +b2: {Nat.is_eq(k, kt) == True{} : Bool},
    +b3: {Nat.is_eq(Nat.add(Nat.mul(g, KT), kt), v) == True{} : Bool})
  -> wi_CG(d, N, KT, 1n+j, 1n+v, Spec.rg_wrap(w, Spec.GCtx{KT, N}, 1n+ij, kt, g, run, k)):
  match w:
    case True{}:
      wi_cg_src(Nat.is_lt(1n+ij, N), d, KT, N, j, v, ij, kt, g, run, k, {==}, PP.ar_eq_true(1n+kt, KT, ew), e1, e2,
        PP.ar_eq_true(Nat.add(Nat.mul(g, KT), kt), v, b3))
    case False{}:
      +MG = Nat.mul(g, KT)
      (Equal.cong(Nat, Nat, y => 1n+y, ij, j, e1),
        ((%Equal.sym(Nat, Nat.add(d, 1n+j), 1n+Nat.add(d, j), PP.ar_add_succ_r(d, j)) : {_ == N : Nat}
            e2),
          wi_live_t(d, wi_gb(run, 1n+k, g, 1n+kt, KT, 1n+v),
            PP.ar_and_intro(Nat.is_eq(run, g), Bool.and(Nat.is_eq(1n+k, 1n+kt), Nat.is_eq(Nat.add(MG, 1n+kt), 1n+v)), b1,
              PP.ar_and_intro(Nat.is_eq(1n+k, 1n+kt), Nat.is_eq(Nat.add(MG, 1n+kt), 1n+v), b2,
                (%Equal.sym(Nat, Nat.add(MG, 1n+kt), 1n+Nat.add(MG, kt), PP.ar_add_succ_r(MG, kt)) : {Nat.is_eq(_, 1n+v) == True{} : Bool}
                  b3))))))

def wi_gdone(u: Nat, +KT: Nat, +N: Nat, +ij: Nat, +kt: Nat, +g: Nat, +run: Nat, +k: Nat,
    +hf: {Nat.is_lt(ij, N) == False{} : Bool})
  -> {wi_fg(wi_cur(u, Spec.GCtx{KT, N}, Spec.RG{ij, kt, g, run, k}), KT) == Nil{} : List<&2, Nat>}:
  match u:
    case 0n:
      {==}
    case 1n+u0:
      +ctx = {Spec.GCtx{KT, N} : Spec.Ctx}
      %Equal.sym(Bool, Nat.is_lt(ij, N), False{}, hf)
        : {Laws.iss_g(wi_nw(Spec.wsel(_, Spec.Iss{0n, run, k})), KT, wi_fg(wi_cur(u0, ctx, Spec.rg_step(_, ctx, ij, kt, g, run, k)), KT))
          == Nil{} : List<&2, Nat>}
      wi_gdone(u0, KT, N, ij, kt, g, run, k, hf)

def wi_cg(d: Nat, +u: Nat, +KT: Nat, +N: Nat, +j: Nat, +v: Nat, rim: Spec.RIM, h: wi_CG(d, N, KT, j, v, rim))
  -> {wi_fg(wi_cur(Nat.add(d, u), Spec.GCtx{KT, N}, rim), KT) == Laws.rng(d, v) : List<&2, Nat>}:
  match d:
    case 0n:
      match rim:
        case Spec.RT{ij, rem, run, k}:
          Empty.absurd({wi_fg(wi_cur(u, Spec.GCtx{KT, N}, Spec.RT{ij, rem, run, k}), KT) == Nil{} : List<&2, Nat>}, PP.ar_false_true(h))
        case Spec.RG{+ij, +kt, +g, +run, +k}:
          (e1, h2) = h
          (e2, e3) = h2
          +eqn = Equal.trans(Nat, ij, j, N, e1, e2)
          wi_gdone(u, KT, N, ij, kt, g, run, k,
            (%Equal.sym(Nat, ij, N, eqn) : {Nat.is_lt(_, N) == False{} : Bool}
              PP.ar_lt_irrefl(N)))
    case 1n+dd:
      match rim:
        case Spec.RT{ij, rem, run, k}:
          +d0 = dd
          Empty.absurd({wi_fg(wi_cur(Nat.add(1n+d0, u), Spec.GCtx{KT, N}, Spec.RT{ij, rem, run, k}), KT) == Laws.rng(1n+d0, v)
            : List<&2, Nat>}, PP.ar_false_true(h))
        case Spec.RG{+ij, +kt, +g, +run, +k}:
          (e1, h2) = h
          (e2, e3) = h2
          +d0 = dd
          +e1x = e1
          +e2x = e2
          +MG = Nat.mul(g, KT)
          +A = Nat.is_eq(run, g)
          +B = Nat.is_eq(k, kt)
          +C = Nat.is_eq(Nat.add(MG, kt), v)
          +h3 = {e3 : {Bool.and(A, Bool.and(B, C)) == True{} : Bool}}
          +b1 = PP.ar_and_l(A, Bool.and(B, C), h3)
          +b23 = PP.ar_and_r(A, Bool.and(B, C), h3)
          +b2 = PP.ar_and_l(B, C, b23)
          +b3 = PP.ar_and_r(B, C, b23)
          +ehead = Equal.trans(Nat, Nat.add(Nat.mul(run, KT), k), Nat.add(MG, kt), v,
            wi_nadd2(Nat.mul(run, KT), MG, k, kt, Equal.cong(Nat, Nat, y => Nat.mul(y, KT), run, g, PP.ar_eq_true(run, g, b1)),
              PP.ar_eq_true(k, kt, b2)),
            PP.ar_eq_true(Nat.add(MG, kt), v, b3))
          +ctx = {Spec.GCtx{KT, N} : Spec.Ctx}
          +hlt = wi_live_lt(ij, j, d0, N, e1x, e2x)
          +NX = Spec.rg_wrap(Nat.is_eq(1n+kt, KT), ctx, 1n+ij, kt, g, run, k)
          %Equal.sym(Bool, Nat.is_lt(ij, N), True{}, hlt)
            : {Laws.iss_g(wi_nw(Spec.wsel(_, Spec.Iss{0n, run, k})), KT, wi_fg(wi_cur(Nat.add(d0, u), ctx, Spec.rg_step(_, ctx, ij, kt, g, run, k)), KT))
              == Laws.rng(1n+d0, v) : List<&2, Nat>}
          wi_ncons2(Nat.add(Nat.mul(run, KT), k), v, wi_fg(wi_cur(Nat.add(d0, u), ctx, NX), KT), Laws.rng(d0, 1n+v), ehead,
            wi_cg(d0, u, KT, N, 1n+j, 1n+v, NX,
              wi_cg_wrap(Nat.is_eq(1n+kt, KT), d0, KT, N, j, v, ij, kt, g, run, k, {==}, e1x, e2x, b1, b2, b3)))

def Laws.diet_m16g_issues(s, n, KT, pf, xr, fo, ws, xi, tiles, pfpos, xrpos, fopos, wspos, xipos, cadence):
  +tp = tiles
  +ctx = {Spec.GCtx{KT, n} : Spec.Ctx}
  +I = Spec.g_init(s, KT)
  +P = Nat.sub(pf, 1n)
  +R0 = Spec.pro_state(P, ctx, I)
  +ML = Part.mainloop(s, Nat.add(s, n), KT)
  +m = wi_tiles(ML)
  +PRO = Spec.pro(P, 0n, ws, ctx, I)
  +WK = Spec.res_evs(Spec.rwalk(ML, s, pf, xr, fo, ws, xi, ctx, 0n, P, R0))
  +REF = Spec.ref_m16g(s, n, KT, pf, xr, fo, ws, xi)
  +DQ = Nat.div(s, KT)
  +RQ = Nat.mod(s, KT)
  +ci0 = {({==}, (PP.ar_add_zero_r(n), wi_live_t(n, wi_gb(DQ, RQ, DQ, RQ, KT, s),
      PP.ar_and_intro(Nat.is_eq(DQ, DQ), Bool.and(Nat.is_eq(RQ, RQ), Nat.is_eq(Nat.add(Nat.mul(DQ, KT), RQ), s)), PP.ar_eq_refl(DQ),
        PP.ar_and_intro(Nat.is_eq(RQ, RQ), Nat.is_eq(Nat.add(Nat.mul(DQ, KT), RQ), s), PP.ar_eq_refl(RQ),
          wi_eqt(Nat.add(Nat.mul(DQ, KT), RQ), s, PP.ard_dm_eq(s, KT, tp))))))) : wi_CG(n, n, KT, 0n, s, I)}
  +e1 = Equal.trans(List<&2, Spec.WE>, wi_wl(List.append(&2, Spec.Ev, PRO, WK)), List.append(&2, Spec.WE, wi_wl(PRO), wi_wl(WK)),
    wi_cur(Nat.add(P, m), ctx, I), wi_app(PRO, WK),
    Equal.trans(List<&2, Spec.WE>, List.append(&2, Spec.WE, wi_wl(PRO), wi_wl(WK)), List.append(&2, Spec.WE, wi_cur(P, ctx, I), wi_cur(m, ctx, R0)),
      wi_cur(Nat.add(P, m), ctx, I),
      wi_app2(wi_wl(PRO), wi_cur(P, ctx, I), wi_wl(WK), wi_cur(m, ctx, R0), wi_pro(P, 0n, ws, ctx, I),
        wi_walk(ML, s, pf, xr, fo, ws, xi, ctx, 0n, P, R0)),
      wi_comp(P, m, ctx, I)))
  +e2 = Equal.trans(Nat, Nat.add(P, m), Nat.add(m, P), Nat.add(n, P), PP.ar_add_comm(P, m),
    Equal.cong(Nat, Nat, y => Nat.add(y, P), m, n, wi_phn(s, n, KT, tp)))
  %Equal.sym(List<&2, Spec.Ev>, Impl.diet_m16g(s, n, KT, pf, xr, fo, ws, xi), REF,
      Laws.diet_m16g(s, n, KT, pf, xr, fo, ws, xi, tp, pfpos, xrpos, fopos, wspos, xipos, cadence))
    : {Laws.issued_g(_, KT) == Laws.rng(n, s) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, Laws.issued_g(REF, KT), wi_fg(wi_wl(REF), KT), wi_ig(REF, KT)) : {_ == Laws.rng(n, s) : List<&2, Nat>}
  %Equal.sym(List<&2, Spec.WE>, wi_wl(REF), wi_cur(Nat.add(n, P), ctx, I),
      Equal.trans(List<&2, Spec.WE>, wi_wl(REF), wi_cur(Nat.add(P, m), ctx, I), wi_cur(Nat.add(n, P), ctx, I), e1,
        Equal.cong(Nat, List<&2, Spec.WE>, y => wi_cur(y, ctx, I), Nat.add(P, m), Nat.add(n, P), e2)))
    : {wi_fg(_, KT) == Laws.rng(n, s) : List<&2, Nat>}
  wi_cg(n, P, KT, n, 0n, s, I, ci0)
