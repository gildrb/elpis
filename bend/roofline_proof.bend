# Proofs of the roofline laws (roofline_laws.bend). Structural evidence only:
# no unsafe definitions, axioms, holes or foreign code. The byte-model laws
# close by evaluation of the binary forms; the ceiling algebra reuses the Nat
# lemmas of gemm_m16_partition_proof.bend (as norm_fuse_proof.bend does).
import Base
import ./roofline_bin.bend as N
import ./roofline.bend as Impl
import ./roofline_spec.bend as Spec
import ./roofline_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

# ==== (a) byte model ====

def Laws.floor_form():
  {==}

def Laws.floor_exact(d, c, w):
  {==}

def Laws.phases_partition(d, c, w):
  {==}

# ==== Nat helpers ====

# a <= b gives a + e <= b + e.
def rl_le_add_r_mono(+a: Nat, +b: Nat, +e: Nat, ab: {Nat.is_le(a, b) == True{} : Bool})
    -> {Nat.is_le(Nat.add(a, e), Nat.add(b, e)) == True{} : Bool}:
  %Ar.ar_add_comm(e, a) : {Nat.is_le(_, Nat.add(b, e)) == True{} : Bool}
  %Ar.ar_add_comm(e, b) : {Nat.is_le(Nat.add(e, a), _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(Nat.add(e, a), Nat.add(e, b)), Nat.is_le(a, b), True{},
    Ar.ar_le_add_cancel(e, a, b), ab)

# a <= b and c <= e give a + c <= b + e.
def rl_le_add_mono(+a: Nat, +b: Nat, +c: Nat, +e: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool}, ce: {Nat.is_le(c, e) == True{} : Bool})
    -> {Nat.is_le(Nat.add(a, c), Nat.add(b, e)) == True{} : Bool}:
  Ar.ar_le_trans(Nat.add(a, c), Nat.add(a, e), Nat.add(b, e),
    Equal.trans(Bool, Nat.is_le(Nat.add(a, c), Nat.add(a, e)), Nat.is_le(c, e), True{},
      Ar.ar_le_add_cancel(a, c, e), ce),
    rl_le_add_r_mono(a, b, e, ab))

# min is monotone in its first argument.
def rl_min_mono(+a: Nat, +b: Nat, +W: Nat, ab: {Nat.is_le(a, b) == True{} : Bool})
    -> {Nat.is_le(Nat.min(a, W), Nat.min(b, W)) == True{} : Bool}:
  match a b W:
    case 0n _ _:
      Ar.ar_h_le_zero(Nat.min(b, W))
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(Nat.min(1n+p, W), Nat.min(0n, W)) == True{} : Bool},
        Ar.ar_false_true(ab))
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      rl_min_mono(p, q, r, ab)

# (a + b) + (c + d) == (a + c) + (b + d).
def rl_swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
    -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))),
    Ar.ar_add_assoc(a, b, Nat.add(c, d)))
    : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), Ar.ar_h_add_swap(b, c, d))
    : {Nat.add(a, _) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))),
    Ar.ar_add_assoc(a, c, Nat.add(b, d)))

# ==== (b) ceiling ====

def rl_sched(ps: List<&2, N.Phase>, +bw: Nat, +u: Nat,
    +fits: {N.Sched.fits(ps, bw, u) == True{} : Bool})
    -> {Nat.is_le(Nat.mul(N.Sched.bytes(ps), u), Nat.mul(N.Sched.time(ps), bw)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{N.Phase{+b, +t}, +rest}:
      +h1 = Ar.ar_and_l(Nat.is_le(Nat.mul(b, u), Nat.mul(t, bw)), N.Sched.fits(rest, bw, u), fits)
      +h2 = Ar.ar_and_r(Nat.is_le(Nat.mul(b, u), Nat.mul(t, bw)), N.Sched.fits(rest, bw, u), fits)
      %Equal.sym(Nat, Nat.mul(Nat.add(b, N.Sched.bytes(rest)), u),
        Nat.add(Nat.mul(b, u), Nat.mul(N.Sched.bytes(rest), u)),
        Ar.ar_mul_add_l(b, N.Sched.bytes(rest), u))
        : {Nat.is_le(_, Nat.mul(Nat.add(t, N.Sched.time(rest)), bw)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.add(t, N.Sched.time(rest)), bw),
        Nat.add(Nat.mul(t, bw), Nat.mul(N.Sched.time(rest), bw)),
        Ar.ar_mul_add_l(t, N.Sched.time(rest), bw))
        : {Nat.is_le(Nat.add(Nat.mul(b, u), Nat.mul(N.Sched.bytes(rest), u)), _) == True{} : Bool}
      rl_le_add_mono(Nat.mul(b, u), Nat.mul(t, bw), Nat.mul(N.Sched.bytes(rest), u),
        Nat.mul(N.Sched.time(rest), bw), h1, rl_sched(rest, bw, u, h2))

def Laws.ceiling(ps, bw, u, total, fits, part):
  %part : {Nat.is_le(Nat.mul(_, u), Nat.mul(N.Sched.time(ps), bw)) == True{} : Bool}
  rl_sched(ps, bw, u, fits)

# ==== (c) tokens ====

# r * (B * u) <= (r * T) * bw from B * u <= T * bw.
def rl_tc_bc(+r: Nat, +B: Nat, +u: Nat, +T: Nat, +bw: Nat,
    fits: {Nat.is_le(Nat.mul(B, u), Nat.mul(T, bw)) == True{} : Bool})
    -> {Nat.is_le(Nat.mul(r, Nat.mul(B, u)), Nat.mul(Nat.mul(r, T), bw)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(r, T), bw), Nat.mul(r, Nat.mul(T, bw)), Ar.ar_mul_assoc(r, T, bw))
    : {Nat.is_le(Nat.mul(r, Nat.mul(B, u)), _) == True{} : Bool}
  %Ar.ar_mul_comm(Nat.mul(B, u), r) : {Nat.is_le(_, Nat.mul(r, Nat.mul(T, bw))) == True{} : Bool}
  %Ar.ar_mul_comm(Nat.mul(T, bw), r) : {Nat.is_le(Nat.mul(Nat.mul(B, u), r), _) == True{} : Bool}
  Ar.ar_le_mul_mono(Nat.mul(B, u), Nat.mul(T, bw), r, fits)

def Laws.toks_ceiling(B, bw, u, T, tm, r, s, fits, rate):
  %Equal.sym(Nat, Nat.mul(Nat.mul(r, B), u), Nat.mul(r, Nat.mul(B, u)), Ar.ar_mul_assoc(r, B, u))
    : {Nat.is_le(_, Nat.mul(Nat.mul(tm, s), bw)) == True{} : Bool}
  Ar.ar_le_trans(Nat.mul(r, Nat.mul(B, u)), Nat.mul(Nat.mul(r, T), bw), Nat.mul(Nat.mul(tm, s), bw),
    rl_tc_bc(r, B, u, T, bw, fits), Ar.ar_le_mul_mono(Nat.mul(r, T), Nat.mul(tm, s), bw, rate))

def rl_refute(x: Bool, h: {True{} == Bool.not(x) : Bool}, le: {x == True{} : Bool}) -> Empty:
  match x:
    case True{}:
      Ar.ar_true_false(h)
    case False{}:
      Ar.ar_false_true(le)

def Laws.toks_refuted(B, bw, u, T, tm, r, s, above, fits, rate):
  rl_refute(Nat.is_le(Nat.mul(Nat.mul(r, B), u), Nat.mul(Nat.mul(tm, s), bw)),
    Equal.trans(Bool, True{}, Nat.is_lt(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(Nat.mul(r, B), u)),
      Bool.not(Nat.is_le(Nat.mul(Nat.mul(r, B), u), Nat.mul(Nat.mul(tm, s), bw))),
      Equal.sym(Bool, Nat.is_lt(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(Nat.mul(r, B), u)), True{}, above),
      Ar.ar_lt_not_le(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(Nat.mul(r, B), u))),
    Laws.toks_ceiling(B, bw, u, T, tm, r, s, fits, rate))

def rl_tc2(+B: Nat, +bw: Nat, +u: Nat, +T: Nat, +tm: Nat, +r: Nat, +s: Nat,
    fits: {Nat.is_le(Nat.mul(B, u), Nat.mul(T, bw)) == True{} : Bool},
    rate: {Nat.is_le(Nat.mul(r, T), Nat.mul(tm, s)) == True{} : Bool})
    -> {Nat.is_le(Nat.mul(r, Nat.mul(B, u)), Nat.mul(Nat.mul(tm, s), bw)) == True{} : Bool}:
  %Ar.ar_mul_assoc(r, B, u) : {Nat.is_le(_, Nat.mul(Nat.mul(tm, s), bw)) == True{} : Bool}
  Laws.toks_ceiling(B, bw, u, T, tm, r, s, fits, rate)

def Laws.ceiling_rate(B, bw, u, T, tm, r, s, pos, fits, rate):
  Equal.trans(Bool, Nat.is_le(r, N.Ceil.rate(tm, s, bw, B, u)),
    Nat.is_le(Nat.mul(r, Nat.mul(B, u)), Nat.mul(Nat.mul(tm, s), bw)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.mul(r, Nat.mul(B, u)), Nat.mul(Nat.mul(tm, s), bw)),
      Nat.is_le(r, Nat.div(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(B, u))),
      Ar.ar_div_le(r, Nat.mul(Nat.mul(tm, s), bw), Nat.mul(B, u), pos)),
    rl_tc2(B, bw, u, T, tm, r, s, fits, rate))

# ==== (d) monotone ====

def rl_win_mono(+d: Nat, +e: Nat)
    -> {Nat.is_le(N.Lin.win(d), N.Lin.win(Nat.add(d, e))) == True{} : Bool}:
  rl_min_mono(Nat.add(d, 8n), Nat.add(Nat.add(d, e), 8n), U32.to_nat(2056),
    rl_le_add_r_mono(d, Nat.add(d, e), 8n, Ar.ar_le_add_r(d, e)))

def Laws.monotone_depth(l, d, e, c):
  match l:
    case N.Lin{+l0, +ld, +lc, +lw}:
      +de = Nat.add(d, e)
      +cc = Nat.mul(c, lc)
      rl_le_add_mono(l0, l0,
        Nat.add(Nat.mul(d, ld), Nat.add(cc, Nat.mul(N.Lin.win(d), lw))),
        Nat.add(Nat.mul(de, ld), Nat.add(cc, Nat.mul(N.Lin.win(de), lw))),
        Ar.ar_le_refl(l0),
        rl_le_add_mono(Nat.mul(d, ld), Nat.mul(de, ld),
          Nat.add(cc, Nat.mul(N.Lin.win(d), lw)), Nat.add(cc, Nat.mul(N.Lin.win(de), lw)),
          Ar.ar_le_mul_mono(d, de, ld, Ar.ar_le_add_r(d, e)),
          rl_le_add_mono(cc, cc, Nat.mul(N.Lin.win(d), lw), Nat.mul(N.Lin.win(de), lw),
            Ar.ar_le_refl(cc),
            Ar.ar_le_mul_mono(N.Lin.win(d), N.Lin.win(de), lw, rl_win_mono(d, e)))))

# ==== (e) ledger ====

def rl_ledger_add(rs: List<&2, N.Row>, +ok: {N.Ledger.valid(rs) == True{} : Bool})
    -> {Nat.add(N.Ledger.floor(rs), N.Ledger.loss(rs)) == N.Ledger.meas(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{N.Row{+m, +f}, +rest}:
      +h1 = Ar.ar_and_l(Nat.is_le(f, m), N.Ledger.valid(rest), ok)
      +h2 = Ar.ar_and_r(Nat.is_le(f, m), N.Ledger.valid(rest), ok)
      %Equal.sym(Nat,
        Nat.add(Nat.add(f, N.Ledger.floor(rest)), Nat.add(Nat.sub(m, f), N.Ledger.loss(rest))),
        Nat.add(Nat.add(f, Nat.sub(m, f)), Nat.add(N.Ledger.floor(rest), N.Ledger.loss(rest))),
        rl_swap4(f, N.Ledger.floor(rest), Nat.sub(m, f), N.Ledger.loss(rest)))
        : {_ == Nat.add(m, N.Ledger.meas(rest)) : Nat}
      %Equal.sym(Nat, Nat.add(f, Nat.sub(m, f)), m, Ar.ar_sub_add(m, f, h1))
        : {Nat.add(_, Nat.add(N.Ledger.floor(rest), N.Ledger.loss(rest))) ==
          Nat.add(m, N.Ledger.meas(rest)) : Nat}
      %Equal.sym(Nat, Nat.add(N.Ledger.floor(rest), N.Ledger.loss(rest)), N.Ledger.meas(rest),
        rl_ledger_add(rest, h2))
        : {Nat.add(m, _) == Nat.add(m, N.Ledger.meas(rest)) : Nat}
      {==}

def Laws.ledger(rs, ok):
  +v = ok
  %rl_ledger_add(rs, v) : {N.Ledger.loss(rs) == Nat.sub(_, N.Ledger.floor(rs)) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(N.Ledger.floor(rs), N.Ledger.loss(rs)), N.Ledger.floor(rs)),
    N.Ledger.loss(rs), Ar.ar_add_sub(N.Ledger.floor(rs), N.Ledger.loss(rs)))
