# Proofs of the residual add + RMSNorm fusion laws (bend/norm_fuse_laws.bend) about the Bend
# model bend/norm_fuse.bend against bend/norm_fuse_spec.bend. Structural evidence only: no unsafe
# definitions, axioms, holes, foreign proof code or answer tables. Nat arithmetic lemmas are the
# proven ar_* lemmas of bend/gemm_m16_partition_proof.bend.
import Base
import ./norm_fuse.bend as Impl
import ./norm_fuse_spec.bend as Spec
import ./norm_fuse_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

# ==== Served shape: by computation ====

def Laws.served_shape():
  ({==}, ({==}, {==}))

# ==== (d) Aliasing ====

# The third loop only stores y.
def al_ev3(cols: List<&2, Nat>, +w: List<&2, Nat>)
    -> {Spec.raw_ok(Impl.ev3(cols), w) == True{} : Bool}:
  match cols:
    case Nil{}:
      {==}
    case c <> rest:
      al_ev3(rest, w)

# The second loop only stores r (then the barrier and the third loop).
def al_ev2(cols: List<&2, Nat>, +c3: List<&2, Nat>, +w: List<&2, Nat>)
    -> {Spec.raw_ok(Impl.ev2(cols, Impl.ev3(c3)), w) == True{} : Bool}:
  match cols:
    case Nil{}:
      al_ev3(c3, w)
    case c <> rest:
      al_ev2(rest, c3, c <> w)

# The first loop only loads, before any store: nothing is written yet when r is read.
def al_ev1(cols: List<&2, Nat>, +tail: List<&2, Spec.Ev>)
    -> {Spec.raw_ok(Impl.ev1(cols, tail), Nil{}) == Spec.raw_ok(tail, Nil{}) : Bool}:
  match cols:
    case Nil{}:
      {==}
    case c <> rest:
      al_ev1(rest, tail)

def Laws.alias_reads_first(R, B, t, n):
  +cols = Impl.cols_reg(R, B, t, n)
  Equal.trans(Bool, Spec.raw_ok(Impl.ev1(cols, Impl.ev2(cols, Impl.ev3(cols))), Nil{}),
    Spec.raw_ok(Impl.ev2(cols, Impl.ev3(cols)), Nil{}), True{},
    al_ev1(cols, Impl.ev2(cols, Impl.ev3(cols))), al_ev2(cols, cols, Nil{}))

# ==== (e) Layer chain ====

# A deferred add folded into the input norm is the unfused add then norm.
def ch_step(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H,
    ~fnorm: Nat -> S -> S -> Spec.Normed<S, H>,
    ~fused: @i:Nat -> @x:S -> @y:S ->
      {fnorm(i, y, x) == Spec.Normed{plus(x, y), norm(i, plus(x, y))} : Spec.Normed<S, H>},
    pend: Bool, st: Spec.Step<S>, +i: Nat)
    -> {Spec.u_step(~S, ~H, ~plus, ~norm, st, i) ==
      Impl.f_step(~S, ~H, ~plus, ~norm, ~fnorm, pend, st, i) : Spec.Normed<S, H>}:
  match pend:
    case False{}:
      {==}
    case True{}:
      match st:
        case Spec.Stop{x}:
          {==}
        case Spec.Half{+x, +y}:
          Equal.sym(Spec.Normed<S, H>, fnorm(i, y, x),
            Spec.Normed{plus(x, y), norm(i, plus(x, y))}, fused(i, x, y))

def ch_go(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H,
    ~fnorm: Nat -> S -> S -> Spec.Normed<S, H>, ~body: Nat -> S -> H -> Spec.Step<S>,
    ~other: Nat -> S -> S,
    ~fused: @i:Nat -> @x:S -> @y:S ->
      {fnorm(i, y, x) == Spec.Normed{plus(x, y), norm(i, plus(x, y))} : Spec.Normed<S, H>},
    mods: List<&2, Spec.Mod>, +i: Nat, +st: Spec.Step<S>, pend: Bool,
    ok: {Spec.linked_ok(mods, pend) == True{} : Bool})
    -> {Impl.f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, mods, i, st, pend) ==
      Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, mods, i, st) : Spec.Run<S, H>}:
  match mods:
    case Nil{}:
      {==}
    case Spec.Blk{link} <> rest:
      %ch_step(~S, ~H, ~plus, ~norm, ~fnorm, ~fused, pend, st, i) :
        {Spec.run.cons(~S, ~H, _,
          Impl.f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, rest, 1n+i,
            body(i, Spec.normed.x(~S, ~H, _), Spec.normed.h(~S, ~H, _)), link)) ==
          Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, Spec.Blk{link} <> rest, i, st)
          : Spec.Run<S, H>}
      +u = Spec.u_step(~S, ~H, ~plus, ~norm, st, i)
      %Equal.sym(Spec.Run<S, H>,
        Impl.f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, rest, 1n+i,
          body(i, Spec.normed.x(~S, ~H, u), Spec.normed.h(~S, ~H, u)), link),
        Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, rest, 1n+i,
          body(i, Spec.normed.x(~S, ~H, u), Spec.normed.h(~S, ~H, u))),
        ch_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, ~fused, rest, 1n+i,
          body(i, Spec.normed.x(~S, ~H, u), Spec.normed.h(~S, ~H, u)), link, ok)) :
        {Spec.run.cons(~S, ~H, u, _) ==
          Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, Spec.Blk{link} <> rest, i, st)
          : Spec.Run<S, H>}
      {==}
    case Spec.Other{} <> rest:
      match pend:
        case False{}:
          ch_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, ~fused, rest, 1n+i,
            Spec.Stop{other(i, Spec.settle(~S, ~plus, st))}, False{}, ok)
        case True{}:
          Empty.absurd({Impl.f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, rest, 1n+i,
              Spec.Stop{other(i, Impl.f_pass(~S, ~plus, True{}, st))}, False{}) ==
            Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, rest, 1n+i,
              Spec.Stop{other(i, Spec.settle(~S, ~plus, st))}) : Spec.Run<S, H>},
            Ar.ar_false_true(ok))

def Laws.chain(S, H, plus, norm, fnorm, body, other, fused, mods, x0, ok):
  ch_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, ~fused, mods, 0n, Spec.Stop{x0}, False{},
    ok)

# ==== Nat / Bool helpers ====

def nf_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
    -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def nf_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Ar.ar_true_false(h))

# not (c < n) gives n <= c.
def nf_le_of_not_lt(+c: Nat, +n: Nat, h: {Nat.is_lt(c, n) == False{} : Bool})
    -> {Nat.is_le(n, c) == True{} : Bool}:
  nf_not_false(Nat.is_le(n, c),
    Equal.trans(Bool, Bool.not(Nat.is_le(n, c)), Nat.is_lt(c, n), False{},
      Equal.sym(Bool, Nat.is_lt(c, n), Bool.not(Nat.is_le(n, c)), Ar.ar_lt_not_le(c, n)), h))

# n <= c gives not (c < n).
def nf_not_lt.go(+c: Nat, +n: Nat, h: {Nat.is_le(n, c) == True{} : Bool})
    -> {Bool.not(Nat.is_le(n, c)) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(n, c), True{}, h) : {Bool.not(_) == False{} : Bool}
  {==}

def nf_not_lt(+c: Nat, +n: Nat, h: {Nat.is_le(n, c) == True{} : Bool})
    -> {Nat.is_lt(c, n) == False{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(c, n), Bool.not(Nat.is_le(n, c)), False{}, Ar.ar_lt_not_le(c, n),
    nf_not_lt.go(c, n, h))

# n <= c gives n <= c + B.
def nf_le_step(+n: Nat, +c: Nat, +B: Nat, h: {Nat.is_le(n, c) == True{} : Bool})
    -> {Nat.is_le(n, Nat.add(c, B)) == True{} : Bool}:
  Ar.ar_le_trans(n, c, Nat.add(c, B), h, Ar.ar_le_add_r(c, B))

# n <= a and a == b give n <= b.
def nf_le_eq(+n: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}, h: {Nat.is_le(n, a) == True{} : Bool})
    -> {Nat.is_le(n, b) == True{} : Bool}:
  %e : {Nat.is_le(n, _) == True{} : Bool}
  h

# ==== (c) Per-thread column order ====

# Past the end the loop stops.
def co_loop_past(f: Nat, +B: Nat, +c: Nat, +n: Nat, h: {Nat.is_le(n, c) == True{} : Bool})
    -> {Spec.cols_loop(f, B, c, n) == Nil{} : List<&2, Nat>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(Bool, Nat.is_lt(c, n), False{}, nf_not_lt(c, n, h)) :
        {Spec.loop.pick(_, c, Spec.cols_loop(g, B, Nat.add(c, B), n)) == Nil{} : List<&2, Nat>}
      {==}

# Past the end every later guarded iteration is skipped.
def co_reg_past(R: Nat, +B: Nat, +c: Nat, +n: Nat, +h: {Nat.is_le(n, c) == True{} : Bool})
    -> {Impl.cols_reg(R, B, c, n) == Nil{} : List<&2, Nat>}:
  match R:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Bool, Nat.is_lt(c, n), False{}, nf_not_lt(c, n, h)) :
        {Impl.reg.pick(_, c, Impl.cols_reg(r, B, Nat.add(c, B), n)) == Nil{} : List<&2, Nat>}
      co_reg_past(r, B, Nat.add(c, B), n, nf_le_step(n, c, B, h))

# One iteration: both keep column c (c < n) or both stop (the rest is empty past the end).
def co_fin(v: Bool, +g: Nat, +B: Nat, +c: Nat, +n: Nat, +e: {Nat.is_lt(c, n) == v : Bool})
    -> {Impl.reg.pick(Nat.is_lt(c, n), c, Spec.cols_loop(g, B, Nat.add(c, B), n)) ==
      Spec.loop.pick(Nat.is_lt(c, n), c, Spec.cols_loop(g, B, Nat.add(c, B), n))
      : List<&2, Nat>}:
  match v:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(c, n), True{}, e) :
        {Impl.reg.pick(_, c, Spec.cols_loop(g, B, Nat.add(c, B), n)) ==
          Spec.loop.pick(_, c, Spec.cols_loop(g, B, Nat.add(c, B), n)) : List<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(c, n), False{}, e) :
        {Impl.reg.pick(_, c, Spec.cols_loop(g, B, Nat.add(c, B), n)) ==
          Spec.loop.pick(_, c, Spec.cols_loop(g, B, Nat.add(c, B), n)) : List<&2, Nat>}
      co_loop_past(g, B, Nat.add(c, B), n, nf_le_step(n, c, B, nf_le_of_not_lt(c, n, e)))

# c + (B + m) == (c + B) + m moves one stride into the start column.
def co_shift(+n: Nat, +c: Nat, +B: Nat, +m: Nat,
    h: {Nat.is_le(n, Nat.add(c, Nat.add(B, m))) == True{} : Bool})
    -> {Nat.is_le(n, Nat.add(Nat.add(c, B), m)) == True{} : Bool}:
  nf_le_eq(n, Nat.add(c, Nat.add(B, m)), Nat.add(Nat.add(c, B), m),
    Equal.sym(Nat, Nat.add(Nat.add(c, B), m), Nat.add(c, Nat.add(B, m)),
      Ar.ar_add_assoc(c, B, m)), h)

# n <= c + 0 gives n <= c.
def co_zero(+n: Nat, +c: Nat, h: {Nat.is_le(n, Nat.add(c, 0n)) == True{} : Bool})
    -> {Nat.is_le(n, c) == True{} : Bool}:
  nf_le_eq(n, Nat.add(c, 0n), c, Ar.ar_add_zero_r(c), h)

# The register iterations and the strided loop list the same columns whenever both run past
# the end of the row: n <= c + R B and n <= c + f B.
def co_main(R: Nat, f: Nat, +B: Nat, +c: Nat, +n: Nat,
    h1: {Nat.is_le(n, Nat.add(c, Nat.mul(R, B))) == True{} : Bool},
    h2: {Nat.is_le(n, Nat.add(c, Nat.mul(f, B))) == True{} : Bool})
    -> {Impl.cols_reg(R, B, c, n) == Spec.cols_loop(f, B, c, n) : List<&2, Nat>}:
  match R f:
    case 0n 0n:
      {==}
    case 0n 1n+(+g):
      Equal.sym(List<&2, Nat>, Spec.cols_loop(1n+g, B, c, n), Nil{},
        co_loop_past(1n+g, B, c, n, co_zero(n, c, h1)))
    case 1n+(+r) 0n:
      co_reg_past(1n+r, B, c, n, co_zero(n, c, h2))
    case 1n+(+r) 1n+(+g):
      %Equal.sym(List<&2, Nat>, Impl.cols_reg(r, B, Nat.add(c, B), n),
        Spec.cols_loop(g, B, Nat.add(c, B), n),
        co_main(r, g, B, Nat.add(c, B), n, co_shift(n, c, B, Nat.mul(r, B), h1),
          co_shift(n, c, B, Nat.mul(g, B), h2))) :
        {Impl.reg.pick(Nat.is_lt(c, n), c, _) ==
          Spec.loop.pick(Nat.is_lt(c, n), c, Spec.cols_loop(g, B, Nat.add(c, B), n))
          : List<&2, Nat>}
      co_fin(Nat.is_lt(c, n), g, B, c, n, {==})

# 1 <= B from 0 < B.
def nf_one_le(+B: Nat, pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.is_le(1n, B) == True{} : Bool}:
  nf_rt(Nat.is_lt(0n, B), Nat.is_le(1n, B), Ar.ar_lt_succ_le(0n, B), pos)

# n <= n B for B >= 1.
def nf_le_mul(+n: Nat, +B: Nat, pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.is_le(n, Nat.mul(n, B)) == True{} : Bool}:
  %Ar.ar_mul_comm(B, n) : {Nat.is_le(n, _) == True{} : Bool}
  %Ar.ar_add_zero_r(n) : {Nat.is_le(_, Nat.mul(B, n)) == True{} : Bool}
  Ar.ar_le_mul_mono(1n, B, n, nf_one_le(B, pos))

# a <= t + a.
def nf_le_add_l(+a: Nat, +t: Nat) -> {Nat.is_le(a, Nat.add(t, a)) == True{} : Bool}:
  %Ar.ar_add_comm(a, t) : {Nat.is_le(a, _) == True{} : Bool}
  Ar.ar_le_add_r(a, t)

def Laws.cols_order(R, B, t, n, pos, fits):
  co_main(R, n, B, t, n,
    Ar.ar_le_trans(n, Nat.mul(R, B), Nat.add(t, Nat.mul(R, B)), fits,
      nf_le_add_l(Nat.mul(R, B), t)),
    Ar.ar_le_trans(n, Nat.mul(n, B), Nat.add(t, Nat.mul(n, B)), nf_le_mul(n, B, pos),
      nf_le_add_l(Nat.mul(n, B), t)))

# ==== (a), (c) Values: the fused column value is torch's residual sum ====

# y + r == r + y lane by lane (the only algebraic step of the refinement).
def ve_radd(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F}, x: Spec.V4<F>, r: Spec.V4<F>)
    -> {Impl.radd(~F, ~add, ~un, x, r) == Spec.tadd(~F, ~add, ~un, r, x) : Spec.V4<F>}:
  match x r:
    case Spec.V4{+a, +b, +d, +e} Spec.V4{+p, +q, +s, +t}:
      %comm(p, a) : {Spec.V4{un(Spec.Rt{}, _), un(Spec.Rt{}, add(b, q)),
          un(Spec.Rt{}, add(d, s)), un(Spec.Rt{}, add(e, t))} ==
        Spec.tadd(~F, ~add, ~un, Spec.V4{p, q, s, t}, Spec.V4{a, b, d, e}) : Spec.V4<F>}
      %comm(q, b) : {Spec.V4{un(Spec.Rt{}, add(p, a)), un(Spec.Rt{}, _),
          un(Spec.Rt{}, add(d, s)), un(Spec.Rt{}, add(e, t))} ==
        Spec.tadd(~F, ~add, ~un, Spec.V4{p, q, s, t}, Spec.V4{a, b, d, e}) : Spec.V4<F>}
      %comm(s, d) : {Spec.V4{un(Spec.Rt{}, add(p, a)), un(Spec.Rt{}, add(q, b)),
          un(Spec.Rt{}, _), un(Spec.Rt{}, add(e, t))} ==
        Spec.tadd(~F, ~add, ~un, Spec.V4{p, q, s, t}, Spec.V4{a, b, d, e}) : Spec.V4<F>}
      %comm(t, e) : {Spec.V4{un(Spec.Rt{}, add(p, a)), un(Spec.Rt{}, add(q, b)),
          un(Spec.Rt{}, add(s, d)), un(Spec.Rt{}, _)} ==
        Spec.tadd(~F, ~add, ~un, Spec.V4{p, q, s, t}, Spec.V4{a, b, d, e}) : Spec.V4<F>}
      {==}

def ve_vsum(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F}, +row: Nat, +c: Nat)
    -> {Spec.resid(~F, ~add, ~un, ~mem, row, c) == Impl.vsum(~F, ~add, ~un, ~mem, row, c)
      : Spec.V4<F>}:
  Equal.sym(Spec.V4<F>, Impl.vsum(~F, ~add, ~un, ~mem, row, c),
    Spec.resid(~F, ~add, ~un, ~mem, row, c),
    ve_radd(~F, ~add, ~un, ~comm, mem(Spec.BX{}, row, c), mem(Spec.BR{}, row, c)))

# Same columns in the same order give the same fma chain.
def pe_partial(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F},
    cols: List<&2, Nat>, +row: Nat, +acc: F)
    -> {Spec.partial(~F, ~add, ~fma, ~un, ~mem, cols, row, acc) ==
      Impl.partial(~F, ~add, ~fma, ~un, ~mem, cols, row, acc) : F}:
  match cols:
    case Nil{}:
      {==}
    case +c <> rest:
      %ve_vsum(~F, ~add, ~un, ~mem, ~comm, row, c) :
        {Spec.partial(~F, ~add, ~fma, ~un, ~mem, rest, row,
            Spec.sum_sq4(~F, ~fma, acc, Spec.resid(~F, ~add, ~un, ~mem, row, c))) ==
          Impl.partial(~F, ~add, ~fma, ~un, ~mem, rest, row, Spec.sum_sq4(~F, ~fma, acc, _))
          : F}
      pe_partial(~F, ~add, ~fma, ~un, ~mem, ~comm, rest, row,
        Spec.sum_sq4(~F, ~fma, acc, Spec.resid(~F, ~add, ~un, ~mem, row, c)))

# cols_order, turned to rewrite the register columns into the loop columns.
def co_rw(+R: Nat, +B: Nat, +t: Nat, +n: Nat, +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    +fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool})
    -> {Spec.cols_loop(n, B, t, n) == Impl.cols_reg(R, B, t, n) : List<&2, Nat>}:
  Equal.sym(List<&2, Nat>, Impl.cols_reg(R, B, t, n), Spec.cols_loop(n, B, t, n),
    Laws.cols_order(R, B, t, n, pos, fits))

def pe_parts(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Spec.Un -> F -> F,
    ~zero: F, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F},
    k: Nat, +t: Nat, +R: Nat, +B: Nat, +n: Nat, +row: Nat,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    +fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool})
    -> {Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, B, n, row) ==
      Impl.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, R, B, n, row) : List<&2, F>}:
  match k:
    case 0n:
      {==}
    case 1n+m:
      %co_rw(R, B, t, n, pos, fits) :
        {Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, 1n+m, t, B, n, row) ==
          Impl.partial(~F, ~add, ~fma, ~un, ~mem, _, row, zero) <>
          Impl.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, m, 1n+t, R, B, n, row) : List<&2, F>}
      %pe_partial(~F, ~add, ~fma, ~un, ~mem, ~comm, Spec.cols_loop(n, B, t, n), row, zero) :
        {Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, 1n+m, t, B, n, row) ==
          _ <> Impl.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, m, 1n+t, R, B, n, row)
          : List<&2, F>}
      %pe_parts(~F, ~add, ~fma, ~un, ~zero, ~mem, ~comm, m, 1n+t, R, B, n, row, pos, fits) :
        {Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, 1n+m, t, B, n, row) ==
          Spec.partial(~F, ~add, ~fma, ~un, ~mem, Spec.cols_loop(n, B, t, n), row, zero) <> _
          : List<&2, F>}
      {==}

def Laws.partials_equal(F, add, fma, un, zero, mem, comm, k, t, R, B, n, row, pos, fits):
  Equal.sym(List<&2, F>, Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, B, n, row),
    Impl.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, R, B, n, row),
    pe_parts(~F, ~add, ~fma, ~un, ~zero, ~mem, ~comm, k, t, R, B, n, row, pos, fits))

# Same columns, same values, same rmf: the same output stores.
def ro_writes(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~un: Spec.Un -> F -> F, ~cast: F -> O, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F},
    cols: List<&2, Nat>, +row: Nat, +rmf: F)
    -> {Spec.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, cols, row, rmf) ==
      Impl.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, cols, row, rmf)
      : List<&2, Spec.Wr<Spec.V4<O>>>}:
  match cols:
    case Nil{}:
      {==}
    case +c <> rest:
      %ve_vsum(~F, ~add, ~un, ~mem, ~comm, row, c) :
        {Spec.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, c <> rest, row, rmf) ==
          Spec.Wr{c, Spec.apply(~F, ~O, ~mul, ~un, ~cast, _, mem(Spec.BW{}, 0n, c), rmf)} <>
          Impl.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, row, rmf)
          : List<&2, Spec.Wr<Spec.V4<O>>>}
      %ro_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, ~comm, rest, row, rmf) :
        {Spec.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, c <> rest, row, rmf) ==
          Spec.Wr{c, Spec.apply(~F, ~O, ~mul, ~un, ~cast,
            Spec.resid(~F, ~add, ~un, ~mem, row, c), mem(Spec.BW{}, 0n, c), rmf)} <> _
          : List<&2, Spec.Wr<Spec.V4<O>>>}
      {==}

# Thread by thread, the same stores given the same reduced sums.
def ro_block(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~un: Spec.Un -> F -> F, ~cast: F -> O, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F},
    sums: List<&2, F>, +t: Nat, +R: Nat, +B: Nat, +n: Nat, +row: Nat,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    +fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool})
    -> {Spec.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, sums, t, B, n, row) ==
      Impl.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, sums, t, R, B, n, row)
      : List<&2, Spec.Wr<Spec.V4<O>>>}:
  match sums:
    case Nil{}:
      {==}
    case +s <> rest:
      %co_rw(R, B, t, n, pos, fits) :
        {Spec.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, s <> rest, t, B, n, row) ==
          List.append(&2, Spec.Wr<Spec.V4<O>>,
            Impl.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, _, row, un(Spec.Rms{}, s)),
            Impl.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, 1n+t, R, B, n, row))
          : List<&2, Spec.Wr<Spec.V4<O>>>}
      %ro_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, ~comm, Spec.cols_loop(n, B, t, n), row,
          un(Spec.Rms{}, s)) :
        {Spec.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, s <> rest, t, B, n, row) ==
          List.append(&2, Spec.Wr<Spec.V4<O>>, _,
            Impl.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, 1n+t, R, B, n, row))
          : List<&2, Spec.Wr<Spec.V4<O>>>}
      %ro_block(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, ~comm, rest, 1n+t, R, B, n, row, pos,
          fits) :
        {Spec.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, s <> rest, t, B, n, row) ==
          List.append(&2, Spec.Wr<Spec.V4<O>>,
            Spec.out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, Spec.cols_loop(n, B, t, n),
              row, un(Spec.Rms{}, s)), _)
          : List<&2, Spec.Wr<Spec.V4<O>>>}
      {==}

# 0 < 32 W for 0 < W.
def nf_pos32(+W: Nat, pos: {Nat.is_lt(0n, W) == True{} : Bool})
    -> {Nat.is_lt(0n, Nat.mul(32n, W)) == True{} : Bool}:
  Ar.ar_lt_le_trans(0n, W, Nat.mul(32n, W), pos, Ar.ar_le_add_r(W, Nat.mul(31n, W)))

def Laws.refine_out(F, O, add, mul, fma, un, zero, cast, mem, comm, W, R, n, row, pos, fits):
  +B = Nat.mul(32n, W)
  +pb = nf_pos32(W, pos)
  +ft = fits
  %pe_parts(~F, ~add, ~fma, ~un, ~zero, ~mem, ~comm, B, 0n, R, B, n, row, pb, ft) :
    {Impl.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem,
        Spec.reduce_dyn(~F, ~add, ~zero, W, _), 0n, R, B, n, row) ==
      Spec.unfused_out(~F, ~O, ~add, ~mul, ~fma, ~un, ~zero, ~cast, ~mem, W, n, row)
      : List<&2, Spec.Wr<Spec.V4<O>>>}
  Equal.sym(List<&2, Spec.Wr<Spec.V4<O>>>,
    Spec.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem,
      Spec.reduce_dyn(~F, ~add, ~zero, W,
        Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, B, 0n, B, n, row)), 0n, B, n, row),
    Impl.block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem,
      Spec.reduce_dyn(~F, ~add, ~zero, W,
        Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, B, 0n, B, n, row)), 0n, R, B, n, row),
    ro_block(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, ~comm,
      Spec.reduce_dyn(~F, ~add, ~zero, W,
        Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, B, 0n, B, n, row)),
      0n, R, B, n, row, pb, ft))

# ==== (b) Ownership ====

def nf_or_true_r(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# A column of the rest stays a column after the guarded head.
def ow_pick(v: Bool, +c: Nat, +j: Nat, +rest: List<&2, Nat>,
    h: {Spec.member(j, rest) == True{} : Bool})
    -> {Spec.member(j, Impl.reg.pick(v, c, rest)) == True{} : Bool}:
  match v:
    case True{}:
      %Equal.sym(Bool, Spec.member(j, rest), True{}, h) :
        {Bool.or(Nat.is_eq(c, j), _) == True{} : Bool}
      nf_or_true_r(Nat.is_eq(c, j))
    case False{}:
      h

# Iteration i < R of the register loop, if in range, visits column c + i B.
def ow_visit(i: Nat, R: Nat, +B: Nat, +c: Nat, +n: Nat,
    hi: {Nat.is_lt(i, R) == True{} : Bool},
    hc: {Nat.is_lt(Nat.add(c, Nat.mul(i, B)), n) == True{} : Bool})
    -> {Spec.member(Nat.add(c, Nat.mul(i, B)), Impl.cols_reg(R, B, c, n)) == True{} : Bool}:
  match i R:
    case 0n 0n:
      Empty.absurd({Spec.member(Nat.add(c, 0n), Nil{}) == True{} : Bool}, Ar.ar_false_true(hi))
    case 0n 1n+(+r):
      +h0 = Equal.trans(Bool, Nat.is_lt(c, n), Nat.is_lt(Nat.add(c, 0n), n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_lt(x, n), c, Nat.add(c, 0n),
          Equal.sym(Nat, Nat.add(c, 0n), c, Ar.ar_add_zero_r(c))), hc)
      %Equal.sym(Nat, Nat.add(c, 0n), c, Ar.ar_add_zero_r(c)) :
        {Spec.member(_, Impl.reg.pick(Nat.is_lt(c, n), c,
          Impl.cols_reg(r, B, Nat.add(c, B), n))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(c, n), True{}, h0) :
        {Spec.member(c, Impl.reg.pick(_, c, Impl.cols_reg(r, B, Nat.add(c, B), n))) == True{}
          : Bool}
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, Ar.ar_eq_refl(c)) :
        {Bool.or(_, Spec.member(c, Impl.cols_reg(r, B, Nat.add(c, B), n))) == True{} : Bool}
      {==}
    case 1n+p 0n:
      Empty.absurd({Spec.member(Nat.add(c, Nat.mul(1n+p, B)), Nil{}) == True{} : Bool},
        Ar.ar_false_true(hi))
    case 1n+(+p) 1n+(+r):
      %Ar.ar_add_assoc(c, B, Nat.mul(p, B)) :
        {Spec.member(_, Impl.reg.pick(Nat.is_lt(c, n), c,
          Impl.cols_reg(r, B, Nat.add(c, B), n))) == True{} : Bool}
      ow_pick(Nat.is_lt(c, n), c, Nat.add(Nat.add(c, B), Nat.mul(p, B)),
        Impl.cols_reg(r, B, Nat.add(c, B), n),
        ow_visit(p, r, B, Nat.add(c, B), n, hi,
          Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.add(c, B), Nat.mul(p, B)), n),
            Nat.is_lt(Nat.add(c, Nat.add(B, Nat.mul(p, B))), n), True{},
            Equal.cong(Nat, Bool, x => Nat.is_lt(x, n),
              Nat.add(Nat.add(c, B), Nat.mul(p, B)), Nat.add(c, Nat.add(B, Nat.mul(p, B))),
              Ar.ar_add_assoc(c, B, Nat.mul(p, B))), hc)))

# j % B + (j / B) B == j.
def ow_split(+j: Nat, +B: Nat, pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.add(Nat.mod(j, B), Nat.mul(Nat.div(j, B), B)) == j : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mod(j, B), Nat.mul(Nat.div(j, B), B)),
    Nat.add(Nat.mul(Nat.div(j, B), B), Nat.mod(j, B)), j,
    Ar.ar_add_comm(Nat.mod(j, B), Nat.mul(Nat.div(j, B), B)), Ar.ard_dm_eq(j, B, pos))

def ow_cover_mem(+R: Nat, +B: Nat, +n: Nat, +j: Nat, +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool},
    +inside: {Nat.is_lt(j, n) == True{} : Bool})
    -> {Spec.member(j, Impl.cols_reg(R, B, Nat.mod(j, B), n)) == True{} : Bool}:
  +sp = ow_split(j, B, pos)
  %sp : {Spec.member(_, Impl.cols_reg(R, B, Nat.mod(j, B), n)) == True{} : Bool}
  ow_visit(Nat.div(j, B), R, B, Nat.mod(j, B), n,
    Equal.trans(Bool, Nat.is_lt(Nat.div(j, B), R), Nat.is_lt(j, Nat.mul(R, B)), True{},
      Ar.ar_div_lt(R, j, B, pos), Ar.ar_lt_le_trans(j, n, Nat.mul(R, B), inside, fits)),
    Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mod(j, B), Nat.mul(Nat.div(j, B), B)), n),
      Nat.is_lt(j, n), True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, n),
        Nat.add(Nat.mod(j, B), Nat.mul(Nat.div(j, B), B)), j, sp), inside))

def Laws.own_cover(R, B, n, j, pos, fits, inside):
  +p = pos
  (ow_cover_mem(R, B, n, j, p, fits, inside), Ar.ard_dm_lt(j, B, p))

# (c + B) % B == c % B.
def ow_mod_step(+c: Nat, +B: Nat, +pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.mod(Nat.add(c, B), B) == Nat.mod(c, B) : Nat}:
  +d = Nat.div(c, B)
  +m = Nat.mod(c, B)
  Equal.trans(Nat, Nat.mod(Nat.add(c, B), B), Nat.mod(Nat.add(Nat.add(Nat.mul(d, B), m), B), B),
    m,
    Equal.cong(Nat, Nat, x => Nat.mod(Nat.add(x, B), B), c, Nat.add(Nat.mul(d, B), m),
      Equal.sym(Nat, Nat.add(Nat.mul(d, B), m), c, Ar.ard_dm_eq(c, B, pos))),
    Equal.trans(Nat, Nat.mod(Nat.add(Nat.add(Nat.mul(d, B), m), B), B),
      Nat.mod(Nat.add(Nat.mul(1n+d, B), m), B), m,
      Equal.cong(Nat, Nat, x => Nat.mod(x, B), Nat.add(Nat.add(Nat.mul(d, B), m), B),
        Nat.add(Nat.add(B, Nat.mul(d, B)), m),
        Equal.sym(Nat, Nat.add(Nat.add(B, Nat.mul(d, B)), m),
          Nat.add(Nat.add(Nat.mul(d, B), m), B), Ar.ard_swap(Nat.mul(d, B), m, B))),
      Ar.ard_snd({Nat.div(Nat.add(Nat.mul(1n+d, B), m), B) == 1n+d : Nat},
        {Nat.mod(Nat.add(Nat.mul(1n+d, B), m), B) == m : Nat},
        Ar.ar_div_unique(1n+d, m, B, Ar.ard_dm_lt(c, B, pos)))))

# Head of a thread's column list: c itself (c == j) or a later column (IH).
def ow_ex_head(w: Bool, +c: Nat, +j: Nat, +B: Nat, +rest: List<&2, Nat>,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    ew: {Nat.is_eq(c, j) == w : Bool},
    h: {Bool.or(w, Spec.member(j, rest)) == True{} : Bool},
    ih: {Spec.member(j, rest) == True{} : Bool} -> {Nat.mod(j, B) == Nat.mod(Nat.add(c, B), B) : Nat})
    -> {Nat.mod(j, B) == Nat.mod(c, B) : Nat}:
  match w:
    case True{}:
      Equal.cong(Nat, Nat, x => Nat.mod(x, B), j, c,
        Equal.sym(Nat, c, j, Ar.ar_eq_true(c, j, ew)))
    case False{}:
      Equal.trans(Nat, Nat.mod(j, B), Nat.mod(Nat.add(c, B), B), Nat.mod(c, B), ih(h),
        ow_mod_step(c, B, pos))

def ow_ex_pick(v: Bool, +c: Nat, +j: Nat, +B: Nat, +rest: List<&2, Nat>,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    h: {Spec.member(j, Impl.reg.pick(v, c, rest)) == True{} : Bool},
    ih: {Spec.member(j, rest) == True{} : Bool} -> {Nat.mod(j, B) == Nat.mod(Nat.add(c, B), B) : Nat})
    -> {Nat.mod(j, B) == Nat.mod(c, B) : Nat}:
  match v:
    case True{}:
      ow_ex_head(Nat.is_eq(c, j), c, j, B, rest, pos, {==}, h, ih)
    case False{}:
      Equal.trans(Nat, Nat.mod(j, B), Nat.mod(Nat.add(c, B), B), Nat.mod(c, B), ih(h),
        ow_mod_step(c, B, pos))

# Every column a thread visits is congruent to its first column modulo B.
def ow_ex(R: Nat, +B: Nat, +c: Nat, +n: Nat, +j: Nat, +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    h: {Spec.member(j, Impl.cols_reg(R, B, c, n)) == True{} : Bool})
    -> {Nat.mod(j, B) == Nat.mod(c, B) : Nat}:
  match R:
    case 0n:
      Empty.absurd({Nat.mod(j, B) == Nat.mod(c, B) : Nat}, Ar.ar_false_true(h))
    case 1n+(+r):
      ow_ex_pick(Nat.is_lt(c, n), c, j, B, Impl.cols_reg(r, B, Nat.add(c, B), n), pos, h,
        hh => ow_ex(r, B, Nat.add(c, B), n, j, pos, hh))

def Laws.own_exclusive(R, B, t, n, j, small, hit):
  +s = small
  +pos = Ar.ard_pos(t, B, s)
  Equal.sym(Nat, Nat.mod(j, B), t,
    Equal.trans(Nat, Nat.mod(j, B), Nat.mod(t, B), t, ow_ex(R, B, t, n, j, pos, hit),
      Ar.ard_snd({Nat.div(Nat.add(Nat.mul(0n, B), t), B) == 0n : Nat},
        {Nat.mod(Nat.add(Nat.mul(0n, B), t), B) == t : Nat},
        Ar.ar_div_unique(0n, t, B, s))))

# Lower bound: every column a thread visits is at least its first column.
def ow_lb_head(w: Bool, +c: Nat, +j: Nat, +B: Nat, -rest: List<&2, Nat>,
    ew: {Nat.is_eq(c, j) == w : Bool},
    h: {Bool.or(w, Spec.member(j, rest)) == True{} : Bool},
    ih: {Spec.member(j, rest) == True{} : Bool} -> {Nat.is_le(Nat.add(c, B), j) == True{} : Bool})
    -> {Nat.is_le(c, j) == True{} : Bool}:
  match w:
    case True{}:
      %Ar.ar_eq_true(c, j, ew) : {Nat.is_le(c, _) == True{} : Bool}
      Ar.ar_le_refl(c)
    case False{}:
      Ar.ar_le_trans(c, Nat.add(c, B), j, Ar.ar_le_add_r(c, B), ih(h))

def ow_lb_pick(v: Bool, +c: Nat, +j: Nat, +B: Nat, +rest: List<&2, Nat>,
    h: {Spec.member(j, Impl.reg.pick(v, c, rest)) == True{} : Bool},
    ih: {Spec.member(j, rest) == True{} : Bool} -> {Nat.is_le(Nat.add(c, B), j) == True{} : Bool})
    -> {Nat.is_le(c, j) == True{} : Bool}:
  match v:
    case True{}:
      ow_lb_head(Nat.is_eq(c, j), c, j, B, rest, {==}, h, ih)
    case False{}:
      Ar.ar_le_trans(c, Nat.add(c, B), j, Ar.ar_le_add_r(c, B), ih(h))

def ow_lb(R: Nat, +B: Nat, +c: Nat, +n: Nat, +j: Nat,
    h: {Spec.member(j, Impl.cols_reg(R, B, c, n)) == True{} : Bool})
    -> {Nat.is_le(c, j) == True{} : Bool}:
  match R:
    case 0n:
      Empty.absurd({Nat.is_le(c, j) == True{} : Bool}, Ar.ar_false_true(h))
    case 1n+(+r):
      ow_lb_pick(Nat.is_lt(c, n), c, j, B, Impl.cols_reg(r, B, Nat.add(c, B), n), h,
        hh => ow_lb(r, B, Nat.add(c, B), n, j, hh))

# A column absent from a list occurs 0 times in it.
def ow_occ0_head(w: Bool, +c: Nat, +j: Nat, +rest: List<&2, Nat>,
    ew: {Nat.is_eq(c, j) == w : Bool},
    h: {Bool.or(w, Spec.member(j, rest)) == False{} : Bool},
    ih: {Spec.member(j, rest) == False{} : Bool} -> {Spec.occ(j, rest) == 0n : Nat})
    -> {Nat.add(Spec.occ.bit(Nat.is_eq(c, j)), Spec.occ(j, rest)) == 0n : Nat}:
  match w:
    case True{}:
      Empty.absurd({Nat.add(Spec.occ.bit(Nat.is_eq(c, j)), Spec.occ(j, rest)) == 0n : Nat},
        Ar.ar_true_false(h))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(c, j), False{}, ew) :
        {Nat.add(Spec.occ.bit(_), Spec.occ(j, rest)) == 0n : Nat}
      ih(h)

def ow_occ0(xs: List<&2, Nat>, +j: Nat, h: {Spec.member(j, xs) == False{} : Bool})
    -> {Spec.occ(j, xs) == 0n : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +c <> +rest:
      ow_occ0_head(Nat.is_eq(c, j), c, j, rest, {==}, h, hh => ow_occ0(rest, j, hh))

# c < c + B for B >= 1.
def ow_lt_step(+c: Nat, +B: Nat, pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.is_lt(c, Nat.add(c, B)) == True{} : Bool}:
  %Ar.ar_add_zero_r(c) : {Nat.is_lt(_, Nat.add(c, B)) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(Nat.add(c, 0n), Nat.add(c, B)), Nat.is_lt(0n, B), True{},
    Ar.ar_lt_add_cancel(c, 0n, B), pos)

# Head c of a thread's list, c == j: j occurs nowhere later (later columns are >= c + B > c).
def ow_single_head(w: Bool, +c: Nat, +j: Nat, +B: Nat, +r: Nat, +n: Nat,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    ew: {Nat.is_eq(c, j) == w : Bool},
    ih: {Nat.is_le(Spec.occ(j, Impl.cols_reg(r, B, Nat.add(c, B), n)), 1n) == True{} : Bool})
    -> {Nat.is_le(Nat.add(Spec.occ.bit(w), Spec.occ(j, Impl.cols_reg(r, B, Nat.add(c, B), n))),
      1n) == True{} : Bool}:
  match w:
    case False{}:
      ih
    case True{}:
      +cj = Ar.ar_eq_true(c, j, ew)
      +rest = Impl.cols_reg(r, B, Nat.add(c, B), n)
      +zero = ow_occ0(rest, j, Ar.ar_not_true(Spec.member(j, rest),
        yes => Ar.ard_lt_self(Nat.add(c, B),
          Ar.ar_le_lt_trans(Nat.add(c, B), c, Nat.add(c, B),
            nf_le_eq(Nat.add(c, B), j, c, Equal.sym(Nat, c, j, cj),
              ow_lb(r, B, Nat.add(c, B), n, j, yes)),
            ow_lt_step(c, B, pos)))))
      %Equal.sym(Nat, Spec.occ(j, rest), 0n, zero) :
        {Nat.is_le(Nat.add(1n, _), 1n) == True{} : Bool}
      {==}

def ow_single_pick(v: Bool, +c: Nat, +j: Nat, +B: Nat, +r: Nat, +n: Nat,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool},
    ih: {Nat.is_le(Spec.occ(j, Impl.cols_reg(r, B, Nat.add(c, B), n)), 1n) == True{} : Bool})
    -> {Nat.is_le(Spec.occ(j, Impl.reg.pick(v, c, Impl.cols_reg(r, B, Nat.add(c, B), n))), 1n) ==
      True{} : Bool}:
  match v:
    case True{}:
      ow_single_head(Nat.is_eq(c, j), c, j, B, r, n, pos, {==}, ih)
    case False{}:
      ih

def ow_single(R: Nat, +B: Nat, +c: Nat, +n: Nat, +j: Nat,
    +pos: {Nat.is_lt(0n, B) == True{} : Bool})
    -> {Nat.is_le(Spec.occ(j, Impl.cols_reg(R, B, c, n)), 1n) == True{} : Bool}:
  match R:
    case 0n:
      {==}
    case 1n+(+r):
      ow_single_pick(Nat.is_lt(c, n), c, j, B, r, n, pos,
        ow_single(r, B, Nat.add(c, B), n, j, pos))

def Laws.own_single(R, B, t, n, j, pos):
  ow_single(R, B, t, n, j, pos)

# ==== (a) Residual stream: last store wins, every column is stored, every store is y + r ====

# The last store over xs ++ ys: first xs, then ys.
def fr_app(~A: Data, xs: List<&2, Spec.Wr<A>>, +ys: List<&2, Spec.Wr<A>>, +j: Nat, d: A)
    -> {Spec.final(~A, List.append(&2, Spec.Wr<A>, xs, ys), j, d) ==
      Spec.final(~A, ys, j, Spec.final(~A, xs, j, d)) : A}:
  match xs:
    case Nil{}:
      {==}
    case Spec.Wr{c, v} <> rest:
      fr_app(~A, rest, ys, j, Spec.final.pick(~A, Nat.is_eq(c, j), v, d))

def fr_same(~A: Data, m: Bool, +v: A) -> {Spec.final.pick(~A, m, v, v) == v : A}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# One residual store to column c of the value of column c.
def fr_head(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, w: Bool, +c: Nat, +j: Nat, +row: Nat, +m: Bool,
    +ew: {Nat.is_eq(c, j) == w : Bool}, +d: Spec.V4<F>)
    -> {Spec.final.pick(~Spec.V4<F>, m, Impl.vsum(~F, ~add, ~un, ~mem, row, j),
        Spec.final.pick(~Spec.V4<F>, Nat.is_eq(c, j), Impl.vsum(~F, ~add, ~un, ~mem, row, c), d)) ==
      Spec.final.pick(~Spec.V4<F>, Bool.or(Nat.is_eq(c, j), m),
        Impl.vsum(~F, ~add, ~un, ~mem, row, j), d) : Spec.V4<F>}:
  match w:
    case True{}:
      +cj = Ar.ar_eq_true(c, j, ew)
      %Equal.sym(Bool, Nat.is_eq(c, j), True{}, ew) :
        {Spec.final.pick(~Spec.V4<F>, m, Impl.vsum(~F, ~add, ~un, ~mem, row, j),
            Spec.final.pick(~Spec.V4<F>, _, Impl.vsum(~F, ~add, ~un, ~mem, row, c), d)) ==
          Spec.final.pick(~Spec.V4<F>, Bool.or(_, m), Impl.vsum(~F, ~add, ~un, ~mem, row, j), d)
          : Spec.V4<F>}
      %Equal.sym(Nat, c, j, cj) :
        {Spec.final.pick(~Spec.V4<F>, m, Impl.vsum(~F, ~add, ~un, ~mem, row, j),
            Impl.vsum(~F, ~add, ~un, ~mem, row, _)) ==
          Impl.vsum(~F, ~add, ~un, ~mem, row, j) : Spec.V4<F>}
      fr_same(~Spec.V4<F>, m, Impl.vsum(~F, ~add, ~un, ~mem, row, j))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(c, j), False{}, ew) :
        {Spec.final.pick(~Spec.V4<F>, m, Impl.vsum(~F, ~add, ~un, ~mem, row, j),
            Spec.final.pick(~Spec.V4<F>, _, Impl.vsum(~F, ~add, ~un, ~mem, row, c), d)) ==
          Spec.final.pick(~Spec.V4<F>, Bool.or(_, m), Impl.vsum(~F, ~add, ~un, ~mem, row, j), d)
          : Spec.V4<F>}
      {==}

# After a thread's residual stores, column j holds its sum if the thread visits j.
def fr_rw(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, cols: List<&2, Nat>, +row: Nat, +j: Nat,
    +d: Spec.V4<F>)
    -> {Spec.final(~Spec.V4<F>, Impl.resid_writes(~F, ~add, ~un, ~mem, cols, row), j, d) ==
      Spec.final.pick(~Spec.V4<F>, Spec.member(j, cols), Impl.vsum(~F, ~add, ~un, ~mem, row, j),
        d) : Spec.V4<F>}:
  match cols:
    case Nil{}:
      {==}
    case +c <> +rest:
      +d1 = Spec.final.pick(~Spec.V4<F>, Nat.is_eq(c, j), Impl.vsum(~F, ~add, ~un, ~mem, row, c),
        d)
      Equal.trans(Spec.V4<F>,
        Spec.final(~Spec.V4<F>, Impl.resid_writes(~F, ~add, ~un, ~mem, rest, row), j, d1),
        Spec.final.pick(~Spec.V4<F>, Spec.member(j, rest), Impl.vsum(~F, ~add, ~un, ~mem, row, j),
          d1),
        Spec.final.pick(~Spec.V4<F>, Bool.or(Nat.is_eq(c, j), Spec.member(j, rest)),
          Impl.vsum(~F, ~add, ~un, ~mem, row, j), d),
        fr_rw(~F, ~add, ~un, ~mem, rest, row, j, d1),
        fr_head(~F, ~add, ~un, ~mem, Nat.is_eq(c, j), c, j, row, Spec.member(j, rest), {==}, d))

def fr_or_assoc(a: Bool, b: Bool, c: Bool)
    -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def fr_member_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +j: Nat)
    -> {Spec.member(j, List.append(&2, Nat, xs, ys)) ==
      Bool.or(Spec.member(j, xs), Spec.member(j, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Equal.sym(Bool, Spec.member(j, List.append(&2, Nat, rest, ys)),
        Bool.or(Spec.member(j, rest), Spec.member(j, ys)), fr_member_app(rest, ys, j)) :
        {Bool.or(Nat.is_eq(c, j), _) ==
          Bool.or(Bool.or(Nat.is_eq(c, j), Spec.member(j, rest)), Spec.member(j, ys)) : Bool}
      fr_or_assoc(Nat.is_eq(c, j), Spec.member(j, rest), Spec.member(j, ys))

def fr_pick2(~A: Data, ma: Bool, mb: Bool, +v: A, +d: A)
    -> {Spec.final.pick(~A, mb, v, Spec.final.pick(~A, ma, v, d)) ==
      Spec.final.pick(~A, Bool.or(ma, mb), v, d) : A}:
  match ma mb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# After threads t .. t + k - 1, column j holds its sum if one of them visits j.
def fr_block(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, k: Nat, +t: Nat, +R: Nat, +B: Nat, +n: Nat,
    +row: Nat, +j: Nat, +d: Spec.V4<F>)
    -> {Spec.final(~Spec.V4<F>, Impl.block_resid(~F, ~add, ~un, ~mem, k, t, R, B, n, row), j, d)
      == Spec.final.pick(~Spec.V4<F>, Spec.member(j, Impl.block_cols(k, t, R, B, n)),
        Impl.vsum(~F, ~add, ~un, ~mem, row, j), d) : Spec.V4<F>}:
  match k:
    case 0n:
      {==}
    case 1n+(+m):
      +vj = Impl.vsum(~F, ~add, ~un, ~mem, row, j)
      +ct = Impl.cols_reg(R, B, t, n)
      +rwt = Impl.resid_writes(~F, ~add, ~un, ~mem, ct, row)
      +brr = Impl.block_resid(~F, ~add, ~un, ~mem, m, 1n+t, R, B, n, row)
      +bcr = Impl.block_cols(m, 1n+t, R, B, n)
      +ma = Spec.member(j, ct)
      +mb = Spec.member(j, bcr)
      +d1 = Spec.final(~Spec.V4<F>, rwt, j, d)
      Equal.trans(Spec.V4<F>, Spec.final(~Spec.V4<F>, List.append(&2, Spec.Wr<Spec.V4<F>>, rwt, brr), j, d),
        Spec.final(~Spec.V4<F>, brr, j, d1),
        Spec.final.pick(~Spec.V4<F>, Spec.member(j, List.append(&2, Nat, ct, bcr)), vj, d),
        fr_app(~Spec.V4<F>, rwt, brr, j, d),
        Equal.trans(Spec.V4<F>, Spec.final(~Spec.V4<F>, brr, j, d1), Spec.final.pick(~Spec.V4<F>, mb, vj, d1),
          Spec.final.pick(~Spec.V4<F>, Spec.member(j, List.append(&2, Nat, ct, bcr)), vj, d),
          fr_block(~F, ~add, ~un, ~mem, m, 1n+t, R, B, n, row, j, d1),
          Equal.trans(Spec.V4<F>, Spec.final.pick(~Spec.V4<F>, mb, vj, d1),
            Spec.final.pick(~Spec.V4<F>, mb, vj, Spec.final.pick(~Spec.V4<F>, ma, vj, d)),
            Spec.final.pick(~Spec.V4<F>, Spec.member(j, List.append(&2, Nat, ct, bcr)), vj, d),
            Equal.cong(Spec.V4<F>, Spec.V4<F>, x => Spec.final.pick(~Spec.V4<F>, mb, vj, x), d1,
              Spec.final.pick(~Spec.V4<F>, ma, vj, d), fr_rw(~F, ~add, ~un, ~mem, ct, row, j, d)),
            Equal.trans(Spec.V4<F>, Spec.final.pick(~Spec.V4<F>, mb, vj, Spec.final.pick(~Spec.V4<F>, ma, vj, d)),
              Spec.final.pick(~Spec.V4<F>, Bool.or(ma, mb), vj, d),
              Spec.final.pick(~Spec.V4<F>, Spec.member(j, List.append(&2, Nat, ct, bcr)), vj, d),
              fr_pick2(~Spec.V4<F>, ma, mb, vj, d),
              Equal.cong(Bool, Spec.V4<F>, x => Spec.final.pick(~Spec.V4<F>, x, vj, d), Bool.or(ma, mb),
                Spec.member(j, List.append(&2, Nat, ct, bcr)),
                Equal.sym(Bool, Spec.member(j, List.append(&2, Nat, ct, bcr)), Bool.or(ma, mb),
                  fr_member_app(ct, bcr, j)))))))

# Thread t0 + dd (dd < k) visits j, so the threads t0 .. t0 + k - 1 do.
def fr_cover(dd: Nat, k: Nat, +t0: Nat, +R: Nat, +B: Nat, +n: Nat, +j: Nat,
    h: {Spec.member(j, Impl.cols_reg(R, B, Nat.add(t0, dd), n)) == True{} : Bool},
    hd: {Nat.is_lt(dd, k) == True{} : Bool})
    -> {Spec.member(j, Impl.block_cols(k, t0, R, B, n)) == True{} : Bool}:
  match dd k:
    case 0n 0n:
      Empty.absurd({Spec.member(j, Impl.block_cols(0n, t0, R, B, n)) == True{} : Bool},
        Ar.ar_false_true(hd))
    case 0n 1n+(+m):
      +h0 = Equal.trans(Bool, Spec.member(j, Impl.cols_reg(R, B, t0, n)),
        Spec.member(j, Impl.cols_reg(R, B, Nat.add(t0, 0n), n)), True{},
        Equal.cong(Nat, Bool, x => Spec.member(j, Impl.cols_reg(R, B, x, n)), t0,
          Nat.add(t0, 0n), Equal.sym(Nat, Nat.add(t0, 0n), t0, Ar.ar_add_zero_r(t0))), h)
      %Equal.sym(Bool, Spec.member(j, List.append(&2, Nat, Impl.cols_reg(R, B, t0, n),
          Impl.block_cols(m, 1n+t0, R, B, n))),
        Bool.or(Spec.member(j, Impl.cols_reg(R, B, t0, n)),
          Spec.member(j, Impl.block_cols(m, 1n+t0, R, B, n))),
        fr_member_app(Impl.cols_reg(R, B, t0, n), Impl.block_cols(m, 1n+t0, R, B, n), j)) :
        {_ == True{} : Bool}
      %Equal.sym(Bool, Spec.member(j, Impl.cols_reg(R, B, t0, n)), True{}, h0) :
        {Bool.or(_, Spec.member(j, Impl.block_cols(m, 1n+t0, R, B, n))) == True{} : Bool}
      {==}
    case 1n+p 0n:
      Empty.absurd({Spec.member(j, Impl.block_cols(0n, t0, R, B, n)) == True{} : Bool},
        Ar.ar_false_true(hd))
    case 1n+(+p) 1n+(+m):
      +ih = fr_cover(p, m, 1n+t0, R, B, n, j,
        Equal.trans(Bool, Spec.member(j, Impl.cols_reg(R, B, 1n+Nat.add(t0, p), n)),
          Spec.member(j, Impl.cols_reg(R, B, Nat.add(t0, 1n+p), n)), True{},
          Equal.cong(Nat, Bool, x => Spec.member(j, Impl.cols_reg(R, B, x, n)),
            1n+Nat.add(t0, p), Nat.add(t0, 1n+p),
            Equal.sym(Nat, Nat.add(t0, 1n+p), 1n+Nat.add(t0, p), Ar.ar_add_succ_r(t0, p))), h),
        hd)
      %Equal.sym(Bool, Spec.member(j, List.append(&2, Nat, Impl.cols_reg(R, B, t0, n),
          Impl.block_cols(m, 1n+t0, R, B, n))),
        Bool.or(Spec.member(j, Impl.cols_reg(R, B, t0, n)),
          Spec.member(j, Impl.block_cols(m, 1n+t0, R, B, n))),
        fr_member_app(Impl.cols_reg(R, B, t0, n), Impl.block_cols(m, 1n+t0, R, B, n), j)) :
        {_ == True{} : Bool}
      %Equal.sym(Bool, Spec.member(j, Impl.block_cols(m, 1n+t0, R, B, n)), True{}, ih) :
        {Bool.or(Spec.member(j, Impl.cols_reg(R, B, t0, n)), _) == True{} : Bool}
      nf_or_true_r(Spec.member(j, Impl.cols_reg(R, B, t0, n)))

def Laws.refine_resid(F, add, un, mem, comm, W, R, n, row, j, pos, fits, inside):
  +B = Nat.mul(32n, W)
  +pb = nf_pos32(W, pos)
  +d = mem(Spec.BR{}, row, j)
  +vj = Impl.vsum(~F, ~add, ~un, ~mem, row, j)
  +mj = Spec.member(j, Impl.block_cols(B, 0n, R, B, n))
  +cov = fr_cover(Nat.mod(j, B), B, 0n, R, B, n, j, ow_cover_mem(R, B, n, j, pb, fits, inside),
    Ar.ard_dm_lt(j, B, pb))
  Equal.trans(Spec.V4<F>, Spec.final(~Spec.V4<F>, Impl.block_resid(~F, ~add, ~un, ~mem, B, 0n, R, B, n, row), j, d),
    Spec.final.pick(~Spec.V4<F>, mj, vj, d), Spec.resid(~F, ~add, ~un, ~mem, row, j),
    fr_block(~F, ~add, ~un, ~mem, B, 0n, R, B, n, row, j, d),
    Equal.trans(Spec.V4<F>, Spec.final.pick(~Spec.V4<F>, mj, vj, d), vj, Spec.resid(~F, ~add, ~un, ~mem, row, j),
      Equal.cong(Bool, Spec.V4<F>, x => Spec.final.pick(~Spec.V4<F>, x, vj, d), mj, True{}, cov),
      Equal.sym(Spec.V4<F>, Spec.resid(~F, ~add, ~un, ~mem, row, j), vj,
        ve_vsum(~F, ~add, ~un, ~mem, ~comm, row, j))))
