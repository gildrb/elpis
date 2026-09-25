# Proofs of gemm_m16_wpart_laws.bend, from Base, the ext 2001 v2 partition lemmas
# (gemm_m16_partition_proof.bend) and the 8201 schedule's counting lemmas (mlp_m16_sched_proof.bend).
# No @unsafe definitions, axioms, holes, foreign proof code or answer tables. Every def precedes its uses.
import Base
import ./gemm_m16_wpart.bend as Impl
import ./gemm_m16_wpart_spec.bend as Spec
import ./gemm_m16_wpart_laws.bend as Laws
import ./gemm_m16_partition.bend as V2
import ./gemm_m16_partition_spec.bend as V2Spec
import ./gemm_m16_partition_laws.bend as V2Laws
import ./gemm_m16_partition_proof.bend as PP
import ./mlp_m16_sched_proof.bend as MP

# ==== (A) Nat / Bool helpers ====

def w_sub0l(n: Nat) -> {Nat.sub(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= b gives a - b = 0.
def w_sub_le0(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.sub(1n+p, 0n) == 0n : Nat}, PP.ar_false_true(h))
    case 1n+p 1n+q:
      w_sub_le0(p, q, h)

# b <= a gives min(a, b) = b.
def w_min_r(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.min(0n, 1n+q) == 1n+q : Nat}, PP.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %w_min_r(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# b <= a gives (1 + a) - b = 1 + (a - b).
def w_sub_succ(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool})
  -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, PP.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      w_sub_succ(p, q, h)

# min(b, n) + (b - n) = b.
def w_min_sub(b: Nat, n: Nat) -> {Nat.add(Nat.min(b, n), Nat.sub(b, n)) == b : Nat}:
  match b n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %w_min_sub(p, q) : {1n+Nat.add(Nat.min(p, q), Nat.sub(p, q)) == 1n+_ : Nat}
      {==}

# a * (b + c) = a * b + a * c.
def w_mul_add_r(+a: Nat, +b: Nat, +c: Nat)
  -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  %PP.ar_mul_comm(Nat.add(b, c), a) : {_ == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %PP.ar_mul_comm(b, a) : {Nat.mul(Nat.add(b, c), a) == Nat.add(_, Nat.mul(a, c)) : Nat}
  %PP.ar_mul_comm(c, a) : {Nat.mul(Nat.add(b, c), a) == Nat.add(Nat.mul(b, a), _) : Nat}
  PP.ar_mul_add_l(b, c, a)

# a <= b and c <= d give a + c <= b + d.
def w_add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool},
    cd: {Nat.is_le(c, d) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  PP.ar_le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d),
    PP.ard_tr(Nat.is_le(Nat.add(a, c), Nat.add(a, d)), Nat.is_le(c, d), PP.ar_le_add_cancel(a, c, d), cd),
    (%PP.ar_add_comm(d, a) : {Nat.is_le(_, Nat.add(b, d)) == True{} : Bool}
      %PP.ar_add_comm(d, b) : {Nat.is_le(Nat.add(d, a), _) == True{} : Bool}
      PP.ard_tr(Nat.is_le(Nat.add(d, a), Nat.add(d, b)), Nat.is_le(a, b), PP.ar_le_add_cancel(d, a, b), ab)))

# a <= b gives c * a <= c * b.
def w_le_mul_l(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}:
  %PP.ar_mul_comm(a, c) : {Nat.is_le(_, Nat.mul(c, b)) == True{} : Bool}
  %PP.ar_mul_comm(b, c) : {Nat.is_le(Nat.mul(a, c), _) == True{} : Bool}
  PP.ar_le_mul_mono(a, b, c, ab)

# not (a <= b) gives b < a.
def w_lt_of_nle(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool})
  -> {Nat.is_lt(b, a) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(b, a), Bool.not(Nat.is_le(a, b)), PP.ar_lt_not_le(b, a)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(a, b), False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

# b < a gives not (a <= b).
def w_nle_of_lt(+a: Nat, +b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool})
  -> {Nat.is_le(a, b) == False{} : Bool}:
  PP.p1l_not_true(Nat.is_le(a, b),
    PP.ard_rt(Nat.is_lt(b, a), Bool.not(Nat.is_le(a, b)), PP.ar_lt_not_le(b, a), h))

# not (a < b) gives b <= a.
def w_le_of_nlt(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool})
  -> {Nat.is_le(b, a) == True{} : Bool}:
  PP.p1l_not_false(Nat.is_le(b, a), Equal.trans(Bool, Bool.not(Nat.is_le(b, a)), Nat.is_lt(a, b),
    False{}, Equal.sym(Bool, Nat.is_lt(a, b), Bool.not(Nat.is_le(b, a)), PP.ar_lt_not_le(a, b)), h))

# 0 / n = 0.
def w_div_zero(n: Nat) -> {Nat.div(0n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# 0 < c and 0 < w give 0 < c * w.
def w_mul_pos(+c: Nat, +w: Nat, cpos: {Nat.is_lt(0n, c) == True{} : Bool},
    wpos: {Nat.is_lt(0n, w) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.mul(c, w)) == True{} : Bool}:
  match c:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PP.ar_false_true(cpos))
    case 1n+q:
      PP.ar_lt_le_trans(0n, w, Nat.add(w, Nat.mul(q, w)), wpos, PP.ar_le_add_r(w, Nat.mul(q, w)))

# Two Nats with the same lower sets (every q: q <= m iff q <= n) are equal.
def w_le_ext(+m: Nat, +n: Nat, em: {Nat.is_le(m, m) == Nat.is_le(m, n) : Bool},
    en: {Nat.is_le(n, m) == Nat.is_le(n, n) : Bool}) -> {m == n : Nat}:
  PP.ar_le_antisym(m, n,
    Equal.trans(Bool, Nat.is_le(m, n), Nat.is_le(m, m), True{}, Equal.sym(Bool, Nat.is_le(m, m),
      Nat.is_le(m, n), em), PP.ar_le_refl(m)),
    Equal.trans(Bool, Nat.is_le(n, m), Nat.is_le(n, n), True{}, en, PP.ar_le_refl(n)))

# ==== (B) the weight prefix W ====

def W_zero(+nsm: Nat, +w0: Nat, +w1: Nat) -> {Impl.wpre(0n, nsm, w0, w1) == 0n : Nat}:
  %Equal.sym(Nat, Nat.sub(0n, nsm), 0n, w_sub0l(nsm))
    : {Nat.add(Nat.mul(w0, Nat.min(0n, nsm)), Nat.mul(w1, _)) == 0n : Nat}
  %Equal.sym(Nat, Nat.mul(w1, 0n), 0n, PP.ar_mul_zero_r(w1)) : {Nat.add(Nat.mul(w0, 0n), _) == 0n : Nat}
  %Equal.sym(Nat, Nat.mul(w0, 0n), 0n, PP.ar_mul_zero_r(w0)) : {Nat.add(_, 0n) == 0n : Nat}
  {==}

# b <= nsm: W(b) = w0 * b.
def W_lo(+b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, h: {Nat.is_le(b, nsm) == True{} : Bool})
  -> {Impl.wpre(b, nsm, w0, w1) == Nat.mul(w0, b) : Nat}:
  +hh = h
  %Equal.sym(Nat, Nat.min(b, nsm), b, PP.ar_min_left(b, nsm, hh))
    : {Nat.add(Nat.mul(w0, _), Nat.mul(w1, Nat.sub(b, nsm))) == Nat.mul(w0, b) : Nat}
  %Equal.sym(Nat, Nat.sub(b, nsm), 0n, w_sub_le0(b, nsm, hh))
    : {Nat.add(Nat.mul(w0, b), Nat.mul(w1, _)) == Nat.mul(w0, b) : Nat}
  %Equal.sym(Nat, Nat.mul(w1, 0n), 0n, PP.ar_mul_zero_r(w1))
    : {Nat.add(Nat.mul(w0, b), _) == Nat.mul(w0, b) : Nat}
  PP.ar_add_zero_r(Nat.mul(w0, b))

# nsm <= b: W(b) = w0 * nsm + w1 * (b - nsm).
def W_hi(+b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, h: {Nat.is_le(nsm, b) == True{} : Bool})
  -> {Impl.wpre(b, nsm, w0, w1) == Nat.add(Nat.mul(w0, nsm), Nat.mul(w1, Nat.sub(b, nsm))) : Nat}:
  %Equal.sym(Nat, Nat.min(b, nsm), nsm, w_min_r(b, nsm, h))
    : {Nat.add(Nat.mul(w0, _), Nat.mul(w1, Nat.sub(b, nsm))) ==
      Nat.add(Nat.mul(w0, nsm), Nat.mul(w1, Nat.sub(b, nsm))) : Nat}
  {==}

# One block step: W(b + 1) = W(b) + weight(b < nsm).
def W_step_go(v: Bool, +b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, e: {Nat.is_lt(b, nsm) == v : Bool})
  -> {Impl.wpre(1n+b, nsm, w0, w1) == Nat.add(Impl.wpre(b, nsm, w0, w1), Spec.weight(v, w0, w1)) : Nat}:
  match v:
    case True{}:
      +lt = e
      +le1 = PP.ard_rt(Nat.is_lt(b, nsm), Nat.is_le(1n+b, nsm), PP.ar_lt_succ_le(b, nsm), lt)
      %Equal.sym(Nat, Impl.wpre(1n+b, nsm, w0, w1), Nat.mul(w0, 1n+b), W_lo(1n+b, nsm, w0, w1, le1))
        : {_ == Nat.add(Impl.wpre(b, nsm, w0, w1), w0) : Nat}
      %Equal.sym(Nat, Impl.wpre(b, nsm, w0, w1), Nat.mul(w0, b), W_lo(b, nsm, w0, w1, PP.ar_lt_le(b, nsm, lt)))
        : {Nat.mul(w0, 1n+b) == Nat.add(_, w0) : Nat}
      %Equal.sym(Nat, Nat.mul(w0, 1n+b), Nat.add(w0, Nat.mul(w0, b)), PP.ar_mul_succ_r(w0, b))
        : {_ == Nat.add(Nat.mul(w0, b), w0) : Nat}
      PP.ar_add_comm(w0, Nat.mul(w0, b))
    case False{}:
      +hle = w_le_of_nlt(b, nsm, e)
      +hle1 = PP.ar_le_trans(nsm, b, 1n+b, hle, PP.ar_h_le_succ(b))
      +A = Nat.mul(w0, nsm)
      +s = Nat.sub(b, nsm)
      %Equal.sym(Nat, Impl.wpre(1n+b, nsm, w0, w1), Nat.add(A, Nat.mul(w1, Nat.sub(1n+b, nsm))),
          W_hi(1n+b, nsm, w0, w1, hle1))
        : {_ == Nat.add(Impl.wpre(b, nsm, w0, w1), w1) : Nat}
      %Equal.sym(Nat, Impl.wpre(b, nsm, w0, w1), Nat.add(A, Nat.mul(w1, s)), W_hi(b, nsm, w0, w1, hle))
        : {Nat.add(A, Nat.mul(w1, Nat.sub(1n+b, nsm))) == Nat.add(_, w1) : Nat}
      %Equal.sym(Nat, Nat.sub(1n+b, nsm), 1n+s, w_sub_succ(b, nsm, hle))
        : {Nat.add(A, Nat.mul(w1, _)) == Nat.add(Nat.add(A, Nat.mul(w1, s)), w1) : Nat}
      %Equal.sym(Nat, Nat.mul(w1, 1n+s), Nat.add(w1, Nat.mul(w1, s)), PP.ar_mul_succ_r(w1, s))
        : {Nat.add(A, _) == Nat.add(Nat.add(A, Nat.mul(w1, s)), w1) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(A, Nat.mul(w1, s)), w1), Nat.add(A, Nat.add(Nat.mul(w1, s), w1)),
          PP.ar_add_assoc(A, Nat.mul(w1, s), w1))
        : {Nat.add(A, Nat.add(w1, Nat.mul(w1, s))) == _ : Nat}
      %PP.ar_add_comm(Nat.mul(w1, s), w1)
        : {Nat.add(A, _) == Nat.add(A, Nat.add(Nat.mul(w1, s), w1)) : Nat}
      {==}

def W_step(+b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
  -> {Impl.wpre(1n+b, nsm, w0, w1) ==
    Nat.add(Impl.wpre(b, nsm, w0, w1), Spec.weight(Nat.is_lt(b, nsm), w0, w1)) : Nat}:
  W_step_go(Nat.is_lt(b, nsm), b, nsm, w0, w1, {==})

def Laws.wpre_is_wsum(b, nsm, w0, w1):
  match b:
    case 0n:
      W_zero(nsm, w0, w1)
    case 1n+c:
      %Laws.wpre_is_wsum(c, nsm, w0, w1)
        : {Impl.wpre(1n+c, nsm, w0, w1) == Nat.add(_, Spec.weight(Nat.is_lt(c, nsm), w0, w1)) : Nat}
      W_step(c, nsm, w0, w1)

def weight_pos(v: Bool, -w0: Nat, -w1: Nat, w0pos: {Nat.is_lt(0n, w0) == True{} : Bool},
    w1pos: {Nat.is_lt(0n, w1) == True{} : Bool})
  -> {Nat.is_lt(0n, Spec.weight(v, w0, w1)) == True{} : Bool}:
  match v:
    case True{}:
      w0pos
    case False{}:
      w1pos

def W_mono1(+c: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
  -> {Nat.is_le(Impl.wpre(c, nsm, w0, w1), Impl.wpre(1n+c, nsm, w0, w1)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.wpre(1n+c, nsm, w0, w1),
      Nat.add(Impl.wpre(c, nsm, w0, w1), Spec.weight(Nat.is_lt(c, nsm), w0, w1)), W_step(c, nsm, w0, w1))
    : {Nat.is_le(Impl.wpre(c, nsm, w0, w1), _) == True{} : Bool}
  PP.ar_le_add_r(Impl.wpre(c, nsm, w0, w1), Spec.weight(Nat.is_lt(c, nsm), w0, w1))

def W_mono_d(+d: Nat, +b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
  -> {Nat.is_le(Impl.wpre(b, nsm, w0, w1), Impl.wpre(Nat.add(d, b), nsm, w0, w1)) == True{} : Bool}:
  match d:
    case 0n:
      PP.ar_le_refl(Impl.wpre(b, nsm, w0, w1))
    case 1n+e:
      PP.ar_le_trans(Impl.wpre(b, nsm, w0, w1), Impl.wpre(Nat.add(e, b), nsm, w0, w1),
        Impl.wpre(1n+Nat.add(e, b), nsm, w0, w1), W_mono_d(e, b, nsm, w0, w1),
        W_mono1(Nat.add(e, b), nsm, w0, w1))

# b <= c gives W(b) <= W(c).
def W_mono(+b: Nat, +c: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, h: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(Impl.wpre(b, nsm, w0, w1), Impl.wpre(c, nsm, w0, w1)) == True{} : Bool}:
  %Equal.trans(Nat, Nat.add(Nat.sub(c, b), b), Nat.add(b, Nat.sub(c, b)), c,
      PP.ar_add_comm(Nat.sub(c, b), b), PP.ar_sub_add(c, b, h))
    : {Nat.is_le(Impl.wpre(b, nsm, w0, w1), Impl.wpre(_, nsm, w0, w1)) == True{} : Bool}
  W_mono_d(Nat.sub(c, b), b, nsm, w0, w1)

# W(G) >= 1 for w0, w1, G >= 1.
def WG_pos(+G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, w0pos: {Nat.is_lt(0n, w0) == True{} : Bool},
    w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}, grid: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool}:
  +g1 = PP.ard_rt(Nat.is_lt(0n, G), Nat.is_le(1n, G), PP.ar_lt_succ_le(0n, G), grid)
  PP.ar_lt_le_trans(0n, Impl.wpre(1n, nsm, w0, w1), Impl.wpre(G, nsm, w0, w1),
    (%Equal.sym(Nat, Impl.wpre(1n, nsm, w0, w1),
        Nat.add(Impl.wpre(0n, nsm, w0, w1), Spec.weight(Nat.is_lt(0n, nsm), w0, w1)), W_step(0n, nsm, w0, w1))
      : {Nat.is_lt(0n, _) == True{} : Bool}
      %Equal.sym(Nat, Impl.wpre(0n, nsm, w0, w1), 0n, W_zero(nsm, w0, w1))
        : {Nat.is_lt(0n, Nat.add(_, Spec.weight(Nat.is_lt(0n, nsm), w0, w1))) == True{} : Bool}
      weight_pos(Nat.is_lt(0n, nsm), w0, w1, w0pos, w1pos)),
    W_mono(1n, G, nsm, w0, w1, g1))

# ==== (C) start ====

def Laws.start_zero(total, G, nsm, w0, w1):
  %Equal.sym(Nat, Impl.wpre(0n, nsm, w0, w1), 0n, W_zero(nsm, w0, w1))
    : {Nat.div(Nat.mul(total, _), Impl.wpre(G, nsm, w0, w1)) == 0n : Nat}
  %Equal.sym(Nat, Nat.mul(total, 0n), 0n, PP.ar_mul_zero_r(total))
    : {Nat.div(_, Impl.wpre(G, nsm, w0, w1)) == 0n : Nat}
  w_div_zero(Impl.wpre(G, nsm, w0, w1))

def start_full(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    grid: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.start(G, total, G, nsm, w0, w1) == total : Nat}:
  +WG = Impl.wpre(G, nsm, w0, w1)
  %PP.ar_mul_comm(WG, total) : {Nat.div(_, WG) == total : Nat}
  PP.p1l_start_full(total, WG, WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid))

def Laws.start_full(total, G, nsm, w0, w1, w0pos, w1pos, grid):
  start_full(total, G, nsm, w0, w1, w0pos, w1pos, grid)

def start_mono(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +b: Nat, +c: Nat,
    wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    ordered: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), Impl.start(c, total, G, nsm, w0, w1)) ==
    True{} : Bool}:
  PP.ar_div_mono(Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Nat.mul(total, Impl.wpre(c, nsm, w0, w1)),
    Impl.wpre(G, nsm, w0, w1), wgpos,
    w_le_mul_l(Impl.wpre(b, nsm, w0, w1), Impl.wpre(c, nsm, w0, w1), total, W_mono(b, c, nsm, w0, w1, ordered)))

def Laws.start_mono(total, G, nsm, w0, w1, b, c, w0pos, w1pos, grid, ordered):
  start_mono(total, G, nsm, w0, w1, b, c, WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid), ordered)

# ==== (D) the closed-form owner: b <= owner(x) iff W(b) <= P iff start(b) <= x ====

# c <= P - A iff A + c <= P   (A <= P)
def le_sub_r(+c: Nat, +P: Nat, +A: Nat, h: {Nat.is_le(A, P) == True{} : Bool})
  -> {Nat.is_le(c, Nat.sub(P, A)) == Nat.is_le(Nat.add(A, c), P) : Bool}:
  %PP.ar_sub_add(P, A, h) : {Nat.is_le(c, Nat.sub(P, A)) == Nat.is_le(Nat.add(A, c), _) : Bool}
  Equal.sym(Bool, Nat.is_le(Nat.add(A, c), Nat.add(A, Nat.sub(P, A))), Nat.is_le(c, Nat.sub(P, A)),
    PP.ar_le_add_cancel(A, c, Nat.sub(P, A)))

# P < w0 nsm, b <= nsm.
def inv_tt(+b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, w0pos: {Nat.is_lt(0n, w0) == True{} : Bool},
    ble: {Nat.is_le(b, nsm) == True{} : Bool})
  -> {Nat.is_le(b, Nat.div(P, w0)) == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  %PP.ar_div_le(b, P, w0, w0pos) : {_ == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}
  %Equal.sym(Nat, Impl.wpre(b, nsm, w0, w1), Nat.mul(w0, b), W_lo(b, nsm, w0, w1, ble))
    : {Nat.is_le(Nat.mul(b, w0), P) == Nat.is_le(_, P) : Bool}
  %PP.ar_mul_comm(b, w0) : {Nat.is_le(Nat.mul(b, w0), P) == Nat.is_le(_, P) : Bool}
  {==}

# P < w0 nsm, nsm < b: both sides false.
def inv_tf(+b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, w0pos: {Nat.is_lt(0n, w0) == True{} : Bool},
    below: {Nat.is_lt(P, Nat.mul(w0, nsm)) == True{} : Bool},
    bgt: {Nat.is_le(b, nsm) == False{} : Bool})
  -> {Nat.is_le(b, Nat.div(P, w0)) == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  +bl = below
  +nb = PP.ar_lt_le(nsm, b, w_lt_of_nle(b, nsm, bgt))
  +f1 = w_nle_of_lt(Impl.wpre(b, nsm, w0, w1), P,
    PP.ar_lt_le_trans(P, Nat.mul(w0, nsm), Impl.wpre(b, nsm, w0, w1), bl,
      (%W_lo(nsm, nsm, w0, w1, PP.ar_le_refl(nsm)) : {Nat.is_le(_, Impl.wpre(b, nsm, w0, w1)) == True{} : Bool}
        W_mono(nsm, b, nsm, w0, w1, nb))))
  +f2 = w_nle_of_lt(Nat.mul(b, w0), P,
    PP.ar_lt_le_trans(P, Nat.mul(w0, nsm), Nat.mul(b, w0), bl,
      (%PP.ar_mul_comm(nsm, w0) : {Nat.is_le(_, Nat.mul(b, w0)) == True{} : Bool}
        PP.ar_le_mul_mono(nsm, b, w0, nb))))
  Equal.trans(Bool, Nat.is_le(b, Nat.div(P, w0)), Nat.is_le(Nat.mul(b, w0), P),
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P),
    Equal.sym(Bool, Nat.is_le(Nat.mul(b, w0), P), Nat.is_le(b, Nat.div(P, w0)), PP.ar_div_le(b, P, w0, w0pos)),
    Equal.trans(Bool, Nat.is_le(Nat.mul(b, w0), P), False{}, Nat.is_le(Impl.wpre(b, nsm, w0, w1), P),
      f2, Equal.sym(Bool, Nat.is_le(Impl.wpre(b, nsm, w0, w1), P), False{}, f1)))

# w0 nsm <= P, b <= nsm: both sides true.
def inv_ft(+b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    above: {Nat.is_le(Nat.mul(w0, nsm), P) == True{} : Bool},
    ble: {Nat.is_le(b, nsm) == True{} : Bool})
  -> {Nat.is_le(b, Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))) ==
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  +bl = ble
  Equal.trans(Bool, Nat.is_le(b, Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))), True{},
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P),
    PP.ar_le_trans(b, nsm, Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1)), bl,
      PP.ar_le_add_r(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))),
    Equal.sym(Bool, Nat.is_le(Impl.wpre(b, nsm, w0, w1), P), True{},
      (%Equal.sym(Nat, Impl.wpre(b, nsm, w0, w1), Nat.mul(w0, b), W_lo(b, nsm, w0, w1, bl))
        : {Nat.is_le(_, P) == True{} : Bool}
        PP.ar_le_trans(Nat.mul(w0, b), Nat.mul(w0, nsm), P, w_le_mul_l(b, nsm, w0, bl), above))))

# w0 nsm <= P, nsm < b: b <= nsm + (P - A) / w1 iff A + w1 (b - nsm) <= P.
def inv_ff(+b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    above: {Nat.is_le(Nat.mul(w0, nsm), P) == True{} : Bool},
    bgt: {Nat.is_le(b, nsm) == False{} : Bool})
  -> {Nat.is_le(b, Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))) ==
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  +nb = PP.ar_lt_le(nsm, b, w_lt_of_nle(b, nsm, bgt))
  +A = Nat.mul(w0, nsm)
  +d = Nat.sub(b, nsm)
  +q = Nat.div(Nat.sub(P, A), w1)
  %PP.ar_sub_add(b, nsm, nb) : {Nat.is_le(_, Nat.add(nsm, q)) == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.add(nsm, d), Nat.add(nsm, q)), Nat.is_le(d, q), PP.ar_le_add_cancel(nsm, d, q))
    : {_ == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}
  %PP.ar_div_le(d, Nat.sub(P, A), w1, w1pos) : {_ == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.mul(d, w1), Nat.sub(P, A)), Nat.is_le(Nat.add(A, Nat.mul(d, w1)), P),
      le_sub_r(Nat.mul(d, w1), P, A, above))
    : {_ == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}
  %Equal.sym(Nat, Impl.wpre(b, nsm, w0, w1), Nat.add(A, Nat.mul(w1, d)), W_hi(b, nsm, w0, w1, nb))
    : {Nat.is_le(Nat.add(A, Nat.mul(d, w1)), P) == Nat.is_le(_, P) : Bool}
  %PP.ar_mul_comm(d, w1) : {Nat.is_le(Nat.add(A, Nat.mul(d, w1)), P) == Nat.is_le(Nat.add(A, _), P) : Bool}
  {==}

def inv_lo(u: Bool, +b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, below: {Nat.is_lt(P, Nat.mul(w0, nsm)) == True{} : Bool},
    eu: {Nat.is_le(b, nsm) == u : Bool})
  -> {Nat.is_le(b, Nat.div(P, w0)) == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  match u:
    case True{}:
      inv_tt(b, P, nsm, w0, w1, w0pos, eu)
    case False{}:
      inv_tf(b, P, nsm, w0, w1, w0pos, below, eu)

def inv_hi(u: Bool, +b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}, above: {Nat.is_le(Nat.mul(w0, nsm), P) == True{} : Bool},
    eu: {Nat.is_le(b, nsm) == u : Bool})
  -> {Nat.is_le(b, Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))) ==
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  match u:
    case True{}:
      inv_ft(b, P, nsm, w0, w1, above, eu)
    case False{}:
      inv_ff(b, P, nsm, w0, w1, w1pos, above, eu)

def inv_go(v: Bool, +b: Nat, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    ev: {Nat.is_lt(P, Nat.mul(w0, nsm)) == v : Bool})
  -> {Nat.is_le(b, Impl.owner.pick(v, P, nsm, w0, w1)) == Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) : Bool}:
  match v:
    case True{}:
      inv_lo(Nat.is_le(b, nsm), b, P, nsm, w0, w1, w0pos, ev, {==})
    case False{}:
      inv_hi(Nat.is_le(b, nsm), b, P, nsm, w0, w1, w1pos, w_le_of_nlt(P, Nat.mul(w0, nsm), ev), {==})

# b <= owner(x) iff start(b) <= x   (w0, w1, G, total >= 1)
def galois(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    work: {Nat.is_lt(0n, total) == True{} : Bool})
  -> {Nat.is_le(b, Impl.owner(x, total, G, nsm, w0, w1)) ==
    Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x) : Bool}:
  +WG = Impl.wpre(G, nsm, w0, w1)
  +P = Impl.wprefix(x, total, WG)
  Equal.trans(Bool, Nat.is_le(b, Impl.owner(x, total, G, nsm, w0, w1)),
    Nat.is_le(Impl.wpre(b, nsm, w0, w1), P), Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x),
    inv_go(Nat.is_lt(P, Nat.mul(w0, nsm)), b, P, nsm, w0, w1, w0pos, w1pos, {==}),
    (%PP.ar_mul_comm(Impl.wpre(b, nsm, w0, w1), total)
      : {Nat.is_le(Impl.wpre(b, nsm, w0, w1), P) == Nat.is_le(Nat.div(_, WG), x) : Bool}
      PP.p1_le_owner(Impl.wpre(b, nsm, w0, w1), x, total, WG, work, wgpos)))

def Laws.owner_galois(total, G, nsm, w0, w1, b, x, w0pos, w1pos, grid, work):
  +p0 = w0pos
  +p1 = w1pos
  galois(b, x, total, G, nsm, w0, w1, p0, p1, WG_pos(G, nsm, w0, w1, p0, p1, grid), work)

# owner(x) <= b iff x < start(b + 1)
def owner_le(+x: Nat, +b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    work: {Nat.is_lt(0n, total) == True{} : Bool})
  -> {Nat.is_le(Impl.owner(x, total, G, nsm, w0, w1), b) ==
    Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1)) : Bool}:
  +o = Impl.owner(x, total, G, nsm, w0, w1)
  +s = Impl.start(1n+b, total, G, nsm, w0, w1)
  Equal.trans(Bool, Nat.is_le(o, b), Nat.is_lt(o, 1n+b), Nat.is_lt(x, s),
    PP.p1_le_lt_succ(o, b),
    Equal.trans(Bool, Nat.is_lt(o, 1n+b), Bool.not(Nat.is_le(1n+b, o)), Nat.is_lt(x, s),
      PP.ar_lt_not_le(o, 1n+b),
      Equal.trans(Bool, Bool.not(Nat.is_le(1n+b, o)), Bool.not(Nat.is_le(s, x)), Nat.is_lt(x, s),
        Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(1n+b, o), Nat.is_le(s, x),
          galois(1n+b, x, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work)),
        Equal.sym(Bool, Nat.is_lt(x, s), Bool.not(Nat.is_le(s, x)), PP.ar_lt_not_le(x, s)))))

# x < total gives total >= 1.
def work_of(+x: Nat, +total: Nat, inside: {Nat.is_lt(x, total) == True{} : Bool})
  -> {Nat.is_lt(0n, total) == True{} : Bool}:
  PP.ar_le_lt_trans(0n, x, total, PP.ar_h_le_zero(x), inside)

# owner(x) < G for x < total.
def owner_lt(+x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +grid: {Nat.is_lt(0n, G) == True{} : Bool}, inside: {Nat.is_lt(x, total) == True{} : Bool})
  -> {Nat.is_lt(Impl.owner(x, total, G, nsm, w0, w1), G) == True{} : Bool}:
  +ins = inside
  +g1 = PP.ard_rt(Nat.is_lt(0n, G), Nat.is_le(1n, G), PP.ar_lt_succ_le(0n, G), grid)
  +o = Impl.owner(x, total, G, nsm, w0, w1)
  %PP.p1_le_pred(o, G, g1) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(o, Nat.sub(G, 1n)), Nat.is_lt(x, Impl.start(1n+Nat.sub(G, 1n), total, G, nsm, w0, w1)),
      owner_le(x, Nat.sub(G, 1n), total, G, nsm, w0, w1, w0pos, w1pos,
        WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid), work_of(x, total, ins)))
    : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(1n, Nat.sub(G, 1n)), G, PP.ar_sub_add(G, 1n, g1))
    : {Nat.is_lt(x, Impl.start(_, total, G, nsm, w0, w1)) == True{} : Bool}
  %Equal.sym(Nat, Impl.start(G, total, G, nsm, w0, w1), total, start_full(total, G, nsm, w0, w1, w0pos, w1pos, grid))
    : {Nat.is_lt(x, _) == True{} : Bool}
  ins

def Laws.owner_correct(total, G, nsm, w0, w1, x, w0pos, w1pos, grid, inside):
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  +ins = inside
  +wg = WG_pos(G, nsm, w0, w1, p0, p1, gp)
  +wk = work_of(x, total, ins)
  +o = Impl.owner(x, total, G, nsm, w0, w1)
  (Equal.trans(Bool, Nat.is_le(Impl.start(o, total, G, nsm, w0, w1), x), Nat.is_le(o, o), True{},
      Equal.sym(Bool, Nat.is_le(o, o), Nat.is_le(Impl.start(o, total, G, nsm, w0, w1), x),
        galois(o, x, total, G, nsm, w0, w1, p0, p1, wg, wk)),
      PP.ar_le_refl(o)),
    (Equal.trans(Bool, Nat.is_lt(x, Impl.start(1n+o, total, G, nsm, w0, w1)), Nat.is_le(o, o), True{},
        Equal.sym(Bool, Nat.is_le(o, o), Nat.is_lt(x, Impl.start(1n+o, total, G, nsm, w0, w1)),
          owner_le(x, o, total, G, nsm, w0, w1, p0, p1, wg, wk)),
        PP.ar_le_refl(o)),
      owner_lt(x, total, G, nsm, w0, w1, p0, p1, gp, ins)))

# start(b) <= x < start(b + 1) gives owner(x) = b.
def uniq(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool},
    lo: {Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x) == True{} : Bool},
    hi: {Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1)) == True{} : Bool})
  -> {Impl.owner(x, total, G, nsm, w0, w1) == b : Nat}:
  +o = Impl.owner(x, total, G, nsm, w0, w1)
  PP.ar_le_antisym(o, b,
    Equal.trans(Bool, Nat.is_le(o, b), Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1)), True{},
      owner_le(x, b, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work), hi),
    Equal.trans(Bool, Nat.is_le(b, o), Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x), True{},
      galois(b, x, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work), lo))

def Laws.owner_unique(total, G, nsm, w0, w1, b, x, w0pos, w1pos, grid, work, lo, hi):
  +p0 = w0pos
  +p1 = w1pos
  uniq(b, x, total, G, nsm, w0, w1, p0, p1, WG_pos(G, nsm, w0, w1, p0, p1, grid), work, lo, hi)

# start(b) <= x iff total * wsum(b) < (x + 1) * wsum(G)
def sb(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool})
  -> {Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x) == Spec.starts_by(b, x, total, G, nsm, w0, w1) : Bool}:
  Equal.trans(Bool, Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x),
    Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), 1n+x), Spec.starts_by(b, x, total, G, nsm, w0, w1),
    PP.p1_le_lt_succ(Impl.start(b, total, G, nsm, w0, w1), x),
    Equal.trans(Bool, Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), 1n+x),
      Nat.is_lt(Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Nat.mul(1n+x, Impl.wpre(G, nsm, w0, w1))),
      Spec.starts_by(b, x, total, G, nsm, w0, w1),
      PP.ar_div_lt(1n+x, Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Impl.wpre(G, nsm, w0, w1), wgpos),
      (%Laws.wpre_is_wsum(b, nsm, w0, w1)
        : {Nat.is_lt(Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Nat.mul(1n+x, Impl.wpre(G, nsm, w0, w1))) ==
          Nat.is_lt(Nat.mul(total, _), Nat.mul(1n+x, Spec.wsum(G, nsm, w0, w1))) : Bool}
        %Laws.wpre_is_wsum(G, nsm, w0, w1)
          : {Nat.is_lt(Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Nat.mul(1n+x, Impl.wpre(G, nsm, w0, w1))) ==
            Nat.is_lt(Nat.mul(total, Impl.wpre(b, nsm, w0, w1)), Nat.mul(1n+x, _)) : Bool}
        {==})))

def range_owned(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool})
  -> {Bool.and(Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x),
      Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1))) ==
    Spec.owns(b, x, total, G, nsm, w0, w1) : Bool}:
  +s0 = Impl.start(b, total, G, nsm, w0, w1)
  +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
  %sb(b, x, total, G, nsm, w0, w1, wgpos)
    : {Bool.and(Nat.is_le(s0, x), Nat.is_lt(x, s1)) ==
      Bool.and(_, Bool.not(Spec.starts_by(1n+b, x, total, G, nsm, w0, w1))) : Bool}
  %Equal.trans(Bool, Nat.is_lt(x, s1), Bool.not(Nat.is_le(s1, x)),
      Bool.not(Spec.starts_by(1n+b, x, total, G, nsm, w0, w1)),
      PP.ar_lt_not_le(x, s1),
      Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(s1, x), Spec.starts_by(1n+b, x, total, G, nsm, w0, w1),
        sb(1n+b, x, total, G, nsm, w0, w1, wgpos)))
    : {Bool.and(Nat.is_le(s0, x), Nat.is_lt(x, s1)) == Bool.and(Nat.is_le(s0, x), _) : Bool}
  {==}

def Laws.range_is_owned(total, G, nsm, w0, w1, b, x, w0pos, w1pos, grid):
  range_owned(b, x, total, G, nsm, w0, w1, WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid))

# owners(c, x) == [x < start(c)]
def owners_start(+c: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool})
  -> {Spec.owners(c, x, total, G, nsm, w0, w1) ==
    V2Spec.bit(Nat.is_lt(x, Impl.start(c, total, G, nsm, w0, w1))) : Nat}:
  match c:
    case 0n:
      %Equal.sym(Nat, Impl.start(0n, total, G, nsm, w0, w1), 0n, Laws.start_zero(total, G, nsm, w0, w1))
        : {0n == V2Spec.bit(Nat.is_lt(x, _)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, PP.p1l_lt_zero(x)) : {0n == V2Spec.bit(_) : Nat}
      {==}
    case 1n+b:
      +s0 = Impl.start(b, total, G, nsm, w0, w1)
      +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
      %Equal.sym(Nat, Spec.owners(b, x, total, G, nsm, w0, w1), V2Spec.bit(Nat.is_lt(x, s0)),
          owners_start(b, x, total, G, nsm, w0, w1, wgpos))
        : {Nat.add(_, V2Spec.bit(Spec.owns(b, x, total, G, nsm, w0, w1))) == V2Spec.bit(Nat.is_lt(x, s1)) : Nat}
      %range_owned(b, x, total, G, nsm, w0, w1, wgpos)
        : {Nat.add(V2Spec.bit(Nat.is_lt(x, s0)), V2Spec.bit(_)) == V2Spec.bit(Nat.is_lt(x, s1)) : Nat}
      PP.p1l_bit_step_go(Nat.is_lt(x, s0), x, s0, s1,
        start_mono(total, G, nsm, w0, w1, b, 1n+b, wgpos, PP.ar_h_le_succ(b)), {==})

def Laws.owners_exactly_one(total, G, nsm, w0, w1, x, w0pos, w1pos, grid, inside):
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  %Equal.sym(Nat, Spec.owners(G, x, total, G, nsm, w0, w1),
      V2Spec.bit(Nat.is_lt(x, Impl.start(G, total, G, nsm, w0, w1))),
      owners_start(G, x, total, G, nsm, w0, w1, WG_pos(G, nsm, w0, w1, p0, p1, gp)))
    : {_ == 1n : Nat}
  %Equal.sym(Nat, Impl.start(G, total, G, nsm, w0, w1), total, start_full(total, G, nsm, w0, w1, p0, p1, gp))
    : {V2Spec.bit(Nat.is_lt(x, _)) == 1n : Nat}
  %Equal.sym(Bool, Nat.is_lt(x, total), True{}, inside) : {V2Spec.bit(_) == 1n : Nat}
  {==}

def pick_same(v: Bool, -a: Nat) -> {Spec.search.pick(v, a, a) == a : Nat}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def srch_step(v: Bool, +c: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool},
    ev: {Spec.starts_by(1n+c, x, total, G, nsm, w0, w1) == v : Bool},
    h: {Nat.is_lt(x, Impl.start(2n+c, total, G, nsm, w0, w1)) == True{} : Bool},
    ih: {Nat.is_lt(x, Impl.start(1n+c, total, G, nsm, w0, w1)) == True{} : Bool} ->
      {Spec.search(1n+c, x, total, G, nsm, w0, w1) == Impl.owner(x, total, G, nsm, w0, w1) : Nat})
  -> {Spec.search.pick(v, 1n+c, Spec.search(1n+c, x, total, G, nsm, w0, w1)) ==
    Impl.owner(x, total, G, nsm, w0, w1) : Nat}:
  match v:
    case True{}:
      Equal.sym(Nat, Impl.owner(x, total, G, nsm, w0, w1), 1n+c,
        uniq(1n+c, x, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work,
          Equal.trans(Bool, Nat.is_le(Impl.start(1n+c, total, G, nsm, w0, w1), x),
            Spec.starts_by(1n+c, x, total, G, nsm, w0, w1), True{},
            sb(1n+c, x, total, G, nsm, w0, w1, wgpos), ev),
          h))
    case False{}:
      ih(w_lt_of_nle(Impl.start(1n+c, total, G, nsm, w0, w1), x,
        Equal.trans(Bool, Nat.is_le(Impl.start(1n+c, total, G, nsm, w0, w1), x),
          Spec.starts_by(1n+c, x, total, G, nsm, w0, w1), False{}, sb(1n+c, x, total, G, nsm, w0, w1, wgpos), ev)))

# x < start(c + 1) gives search(c + 1, x) = owner(x).
def srch(+c: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool},
    h: {Nat.is_lt(x, Impl.start(1n+c, total, G, nsm, w0, w1)) == True{} : Bool})
  -> {Spec.search(1n+c, x, total, G, nsm, w0, w1) == Impl.owner(x, total, G, nsm, w0, w1) : Nat}:
  match c:
    case 0n:
      %Equal.sym(Nat, Spec.search.pick(Spec.starts_by(0n, x, total, G, nsm, w0, w1), 0n, 0n), 0n,
          pick_same(Spec.starts_by(0n, x, total, G, nsm, w0, w1), 0n))
        : {_ == Impl.owner(x, total, G, nsm, w0, w1) : Nat}
      Equal.sym(Nat, Impl.owner(x, total, G, nsm, w0, w1), 0n,
        uniq(0n, x, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work,
          (%Equal.sym(Nat, Impl.start(0n, total, G, nsm, w0, w1), 0n, Laws.start_zero(total, G, nsm, w0, w1))
              : {Nat.is_le(_, x) == True{} : Bool}
            PP.ar_h_le_zero(x)),
          h))
    case 1n+d:
      srch_step(Spec.starts_by(1n+d, x, total, G, nsm, w0, w1), d, x, total, G, nsm, w0, w1,
        w0pos, w1pos, wgpos, work, {==}, h,
        hh => srch(d, x, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work, hh))

def Laws.owner_is_search(total, G, nsm, w0, w1, x, w0pos, w1pos, grid, inside):
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  +ins = inside
  +g1 = PP.ard_rt(Nat.is_lt(0n, G), Nat.is_le(1n, G), PP.ar_lt_succ_le(0n, G), gp)
  %PP.ar_sub_add(G, 1n, g1) : {Impl.owner(x, total, G, nsm, w0, w1) == Spec.search(_, x, total, G, nsm, w0, w1) : Nat}
  Equal.sym(Nat, Spec.search(1n+Nat.sub(G, 1n), x, total, G, nsm, w0, w1), Impl.owner(x, total, G, nsm, w0, w1),
    srch(Nat.sub(G, 1n), x, total, G, nsm, w0, w1, p0, p1, WG_pos(G, nsm, w0, w1, p0, p1, gp), work_of(x, total, ins),
      (%Equal.sym(Nat, Nat.add(1n, Nat.sub(G, 1n)), G, PP.ar_sub_add(G, 1n, g1))
          : {Nat.is_lt(x, Impl.start(_, total, G, nsm, w0, w1)) == True{} : Bool}
        %Equal.sym(Nat, Impl.start(G, total, G, nsm, w0, w1), total, start_full(total, G, nsm, w0, w1, p0, p1, gp))
          : {Nat.is_lt(x, _) == True{} : Bool}
        ins)))

# ==== (E) equal weights are v2 ====

def W_eq(+b: Nat, +nsm: Nat, +w: Nat) -> {Impl.wpre(b, nsm, w, w) == Nat.mul(w, b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(w, Nat.min(b, nsm)), Nat.mul(w, Nat.sub(b, nsm))),
    Nat.mul(w, Nat.add(Nat.min(b, nsm), Nat.sub(b, nsm))), Nat.mul(w, b),
    Equal.sym(Nat, Nat.mul(w, Nat.add(Nat.min(b, nsm), Nat.sub(b, nsm))),
      Nat.add(Nat.mul(w, Nat.min(b, nsm)), Nat.mul(w, Nat.sub(b, nsm))),
      w_mul_add_r(w, Nat.min(b, nsm), Nat.sub(b, nsm))),
    Equal.cong(Nat, Nat, t => Nat.mul(w, t), Nat.add(Nat.min(b, nsm), Nat.sub(b, nsm)), b, w_min_sub(b, nsm)))

# (a w) / (c w) = a / c   (c, w >= 1)
def div_cancel(+a: Nat, +c: Nat, +w: Nat, +cpos: {Nat.is_lt(0n, c) == True{} : Bool},
    +wpos: {Nat.is_lt(0n, w) == True{} : Bool})
  -> {Nat.div(Nat.mul(a, w), Nat.mul(c, w)) == Nat.div(a, c) : Nat}:
  +cw = w_mul_pos(c, w, cpos, wpos)
  +d1 = Nat.div(Nat.mul(a, w), Nat.mul(c, w))
  +d2 = Nat.div(a, c)
  PP.ar_le_antisym(d1, d2,
    PP.ard_rt(Nat.is_le(Nat.mul(d1, c), a), Nat.is_le(d1, d2), PP.ar_div_le(d1, a, c, cpos),
      PP.ard_tr(Nat.is_le(Nat.mul(d1, c), a), Nat.is_le(Nat.mul(Nat.mul(d1, c), w), Nat.mul(a, w)),
        Equal.sym(Bool, Nat.is_le(Nat.mul(Nat.mul(d1, c), w), Nat.mul(a, w)), Nat.is_le(Nat.mul(d1, c), a),
          PP.ar_mul_le_cancel(Nat.mul(d1, c), a, w, wpos)),
        (%Equal.sym(Nat, Nat.mul(Nat.mul(d1, c), w), Nat.mul(d1, Nat.mul(c, w)), PP.ar_mul_assoc(d1, c, w))
          : {Nat.is_le(_, Nat.mul(a, w)) == True{} : Bool}
          PP.ard_le_mul_div(Nat.mul(a, w), Nat.mul(c, w), cw)))),
    PP.ard_rt(Nat.is_le(Nat.mul(d2, Nat.mul(c, w)), Nat.mul(a, w)), Nat.is_le(d2, d1),
      PP.ar_div_le(d2, Nat.mul(a, w), Nat.mul(c, w), cw),
      (%PP.ar_mul_assoc(d2, c, w) : {Nat.is_le(_, Nat.mul(a, w)) == True{} : Bool}
        PP.ar_le_mul_mono(Nat.mul(d2, c), a, w, PP.ard_le_mul_div(a, c, cpos)))))

def start_v2(+b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w: Nat, +wpos: {Nat.is_lt(0n, w) == True{} : Bool},
    +grid: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.start(b, total, G, nsm, w, w) == V2.start(b, total, G) : Nat}:
  %Equal.sym(Nat, Impl.wpre(b, nsm, w, w), Nat.mul(w, b), W_eq(b, nsm, w))
    : {Nat.div(Nat.mul(total, _), Impl.wpre(G, nsm, w, w)) == V2.start(b, total, G) : Nat}
  %Equal.sym(Nat, Impl.wpre(G, nsm, w, w), Nat.mul(w, G), W_eq(G, nsm, w))
    : {Nat.div(Nat.mul(total, Nat.mul(w, b)), _) == V2.start(b, total, G) : Nat}
  %PP.ar_mul_comm(b, w) : {Nat.div(Nat.mul(total, _), Nat.mul(w, G)) == V2.start(b, total, G) : Nat}
  %PP.ar_mul_assoc(total, b, w) : {Nat.div(_, Nat.mul(w, G)) == V2.start(b, total, G) : Nat}
  %PP.ar_mul_comm(b, total) : {Nat.div(Nat.mul(_, w), Nat.mul(w, G)) == V2.start(b, total, G) : Nat}
  %PP.ar_mul_comm(G, w) : {Nat.div(Nat.mul(Nat.mul(b, total), w), _) == V2.start(b, total, G) : Nat}
  div_cancel(Nat.mul(b, total), G, w, grid, wpos)

def owner_v2_le(+q: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w: Nat,
    +wpos: {Nat.is_lt(0n, w) == True{} : Bool}, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool})
  -> {Nat.is_le(q, Impl.owner(x, total, G, nsm, w, w)) == Nat.is_le(q, V2.owner(x, total, G)) : Bool}:
  Equal.trans(Bool, Nat.is_le(q, Impl.owner(x, total, G, nsm, w, w)), Nat.is_le(Impl.start(q, total, G, nsm, w, w), x),
    Nat.is_le(q, V2.owner(x, total, G)),
    galois(q, x, total, G, nsm, w, w, wpos, wpos, WG_pos(G, nsm, w, w, wpos, wpos, grid), work),
    (%Equal.sym(Nat, Impl.start(q, total, G, nsm, w, w), V2.start(q, total, G), start_v2(q, total, G, nsm, w, wpos, grid))
        : {Nat.is_le(_, x) == Nat.is_le(q, V2.owner(x, total, G)) : Bool}
      Equal.sym(Bool, Nat.is_le(q, V2.owner(x, total, G)), Nat.is_le(V2.start(q, total, G), x),
        PP.p1_le_owner(q, x, total, G, work, grid))))

def Laws.equal_weights_is_v2(total, G, nsm, w, b, x, wpos, grid, work):
  +wp = wpos
  +gp = grid
  +wk = work
  +o1 = Impl.owner(x, total, G, nsm, w, w)
  +o2 = V2.owner(x, total, G)
  (start_v2(b, total, G, nsm, w, wp, gp),
    w_le_ext(o1, o2, owner_v2_le(o1, x, total, G, nsm, w, wp, gp, wk),
      owner_v2_le(o2, x, total, G, nsm, w, wp, gp, wk)))

# ==== (F) the host guard ====

# The go loop of weights_valid yields every checked slice: start(d + b0) < start(d + b0 + 1), d < left.
def go_at(+left: Nat, +b0: Nat, +d: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    small: {Nat.is_lt(d, left) == True{} : Bool},
    h: {Impl.weights_valid.go(left, b0, total, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(Impl.start(Nat.add(d, b0), total, G, nsm, w0, w1),
    Impl.start(1n+Nat.add(d, b0), total, G, nsm, w0, w1)) == True{} : Bool}:
  match left d:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(Impl.start(b0, total, G, nsm, w0, w1), Impl.start(1n+b0, total, G, nsm, w0, w1)) ==
        True{} : Bool}, PP.ar_false_true(small))
    case 0n 1n+dp:
      Empty.absurd({Nat.is_lt(Impl.start(1n+Nat.add(dp, b0), total, G, nsm, w0, w1),
        Impl.start(2n+Nat.add(dp, b0), total, G, nsm, w0, w1)) == True{} : Bool}, PP.ar_false_true(small))
    case 1n+rest 0n:
      PP.ar_and_l(Nat.is_lt(Impl.start(b0, total, G, nsm, w0, w1), Impl.start(1n+b0, total, G, nsm, w0, w1)),
        Impl.weights_valid.go(rest, 1n+b0, total, G, nsm, w0, w1), h)
    case 1n+rest 1n+dp:
      %PP.ar_add_succ_r(dp, b0)
        : {Nat.is_lt(Impl.start(_, total, G, nsm, w0, w1), Impl.start(1n+_, total, G, nsm, w0, w1)) ==
          True{} : Bool}
      go_at(rest, 1n+b0, dp, total, G, nsm, w0, w1, small,
        PP.ar_and_r(Nat.is_lt(Impl.start(b0, total, G, nsm, w0, w1), Impl.start(1n+b0, total, G, nsm, w0, w1)),
          Impl.weights_valid.go(rest, 1n+b0, total, G, nsm, w0, w1), h))

def valid_go(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    v: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool})
  -> {Impl.weights_valid.go(G, 0n, total, G, nsm, w0, w1) == True{} : Bool}:
  +c1 = Nat.is_le(1n, w0)
  +c2 = Nat.is_le(1n, w1)
  +c3 = Nat.is_le(1n, nsm)
  +c4 = Nat.is_le(nsm, G)
  +c5 = Nat.is_le(G, Nat.mul(2n, nsm))
  +go = Impl.weights_valid.go(G, 0n, total, G, nsm, w0, w1)
  PP.ar_and_r(c5, go, PP.ar_and_r(c4, Bool.and(c5, go), PP.ar_and_r(c3, Bool.and(c4, Bool.and(c5, go)),
    PP.ar_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go))),
      PP.ar_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go)))), v)))))

def valid_nonempty(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +b: Nat,
    valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool},
    block: {Nat.is_lt(b, G) == True{} : Bool})
  -> {Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Impl.start(1n+b, total, G, nsm, w0, w1)) == True{} : Bool}:
  %PP.ar_add_zero_r(b)
    : {Nat.is_lt(Impl.start(_, total, G, nsm, w0, w1), Impl.start(1n+_, total, G, nsm, w0, w1)) == True{} : Bool}
  go_at(G, 0n, b, total, G, nsm, w0, w1, block, valid_go(total, G, nsm, w0, w1, valid))

def Laws.valid_nonempty(total, G, nsm, w0, w1, b, valid, block):
  valid_nonempty(total, G, nsm, w0, w1, b, valid, block)

# A non-empty first slice forces total >= 1.
def tot_pos(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    ne: {Nat.is_lt(Impl.start(0n, total, G, nsm, w0, w1), Impl.start(1n, total, G, nsm, w0, w1)) == True{} : Bool})
  -> {Nat.is_lt(0n, total) == True{} : Bool}:
  match total:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        PP.ar_false_true(Equal.trans(Bool, False{},
          Nat.is_lt(Impl.start(0n, 0n, G, nsm, w0, w1), Impl.start(1n, 0n, G, nsm, w0, w1)), True{},
          Equal.sym(Bool, Nat.is_lt(Nat.div(0n, Impl.wpre(G, nsm, w0, w1)), Nat.div(0n, Impl.wpre(G, nsm, w0, w1))),
            False{}, PP.ar_lt_irrefl(Nat.div(0n, Impl.wpre(G, nsm, w0, w1)))),
          ne)))
    case 1n+t:
      {==}

def valid_dom(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_lt(0n, w0) == True{} : Bool} & {Nat.is_lt(0n, w1) == True{} : Bool} &
    {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, total) == True{} : Bool}:
  +c1 = Nat.is_le(1n, w0)
  +c2 = Nat.is_le(1n, w1)
  +c3 = Nat.is_le(1n, nsm)
  +c4 = Nat.is_le(nsm, G)
  +c5 = Nat.is_le(G, Nat.mul(2n, nsm))
  +go = Impl.weights_valid.go(G, 0n, total, G, nsm, w0, w1)
  +r1 = PP.ar_and_r(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go)))), valid)
  +r2 = PP.ar_and_r(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go))), r1)
  +r3 = PP.ar_and_r(c3, Bool.and(c4, Bool.and(c5, go)), r2)
  +h1 = PP.ar_and_l(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go)))), valid)
  +h2 = PP.ar_and_l(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go))), r1)
  +h3 = PP.ar_and_l(c3, Bool.and(c4, Bool.and(c5, go)), r2)
  +h4 = PP.ar_and_l(c4, Bool.and(c5, go), r3)
  +gpos = PP.ard_tr(Nat.is_lt(0n, G), Nat.is_le(1n, G), PP.ar_lt_succ_le(0n, G), PP.ar_le_trans(1n, nsm, G, h3, h4))
  (PP.ard_tr(Nat.is_lt(0n, w0), Nat.is_le(1n, w0), PP.ar_lt_succ_le(0n, w0), h1),
    (PP.ard_tr(Nat.is_lt(0n, w1), Nat.is_le(1n, w1), PP.ar_lt_succ_le(0n, w1), h2),
      (gpos, tot_pos(total, G, nsm, w0, w1, valid_nonempty(total, G, nsm, w0, w1, 0n, valid, gpos)))))

def Laws.valid_domain(total, G, nsm, w0, w1, valid):
  valid_dom(total, G, nsm, w0, w1, valid)

# ==== (G) groups, contributors and slots ====

def os_eq(+left: Nat, +x: Nat, +b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool})
  -> {Spec.owns_some(left, x, b, total, G, nsm, w0, w1) ==
    PP.p1t_os(left, x, Impl.start(b, total, G, nsm, w0, w1), Impl.start(1n+b, total, G, nsm, w0, w1)) : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      +s0 = Impl.start(b, total, G, nsm, w0, w1)
      +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
      %os_eq(r, 1n+x, b, total, G, nsm, w0, w1, wgpos)
        : {Bool.or(Spec.owns(b, x, total, G, nsm, w0, w1), Spec.owns_some(r, 1n+x, b, total, G, nsm, w0, w1)) ==
          Bool.or(Bool.and(Nat.is_le(s0, x), Nat.is_lt(x, s1)), _) : Bool}
      %Equal.sym(Bool, Bool.and(Nat.is_le(s0, x), Nat.is_lt(x, s1)), Spec.owns(b, x, total, G, nsm, w0, w1),
          range_owned(b, x, total, G, nsm, w0, w1, wgpos))
        : {Bool.or(Spec.owns(b, x, total, G, nsm, w0, w1), Spec.owns_some(r, 1n+x, b, total, G, nsm, w0, w1)) ==
          Bool.or(_, Spec.owns_some(r, 1n+x, b, total, G, nsm, w0, w1)) : Bool}
      {==}

# Block b touches group g iff its range is non-empty and meets [g KT, (g + 1) KT).
def touches_range(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool})
  -> {Spec.touches(b, g, KT, total, G, nsm, w0, w1) ==
    Bool.and(Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Impl.start(1n+b, total, G, nsm, w0, w1)),
      Bool.and(Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, total, G, nsm, w0, w1)))) : Bool}:
  match KT:
    case 0n:
      +s0 = Impl.start(b, total, G, nsm, w0, w1)
      +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
      %Equal.sym(Nat, Nat.mul(g, 0n), 0n, PP.ar_mul_zero_r(g))
        : {False{} == Bool.and(Nat.is_lt(s0, s1), Bool.and(Nat.is_lt(s0, _), Nat.is_lt(_, s1))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(s0, 0n), False{}, PP.p1t_lt0(s0))
        : {False{} == Bool.and(Nat.is_lt(s0, s1), Bool.and(_, Nat.is_lt(0n, s1))) : Bool}
      PP.p1t_and_false_r(Nat.is_lt(s0, s1))
    case 1n+k:
      +s0 = Impl.start(b, total, G, nsm, w0, w1)
      +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
      %PP.ar_add_comm(Nat.mul(g, 1n+k), 1n+k)
        : {Spec.touches(b, g, 1n+k, total, G, nsm, w0, w1) ==
          Bool.and(Nat.is_lt(s0, s1), Bool.and(Nat.is_lt(s0, _), Nat.is_lt(Nat.mul(g, 1n+k), s1))) : Bool}
      Equal.trans(Bool, Spec.owns_some(1n+k, Nat.mul(g, 1n+k), b, total, G, nsm, w0, w1),
        PP.p1t_os(1n+k, Nat.mul(g, 1n+k), s0, s1), PP.p1t_rng(k, Nat.mul(g, 1n+k), s0, s1),
        os_eq(1n+k, Nat.mul(g, 1n+k), b, total, G, nsm, w0, w1, wgpos),
        PP.p1t_main(s0, s1, Nat.mul(g, 1n+k), k))

# b <= last_contrib(g) iff start(b) < (g + 1) KT   (KT >= 1)
def le_hi_iff(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) ==
    Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Nat.mul(1n+g, KT)) : Bool}:
  Equal.trans(Bool, Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1)),
    Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), Nat.sub(Nat.mul(1n+g, KT), 1n)),
    Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Nat.mul(1n+g, KT)),
    galois(b, Nat.sub(Nat.mul(1n+g, KT), 1n), total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work),
    PP.p2_le_pred(Impl.start(b, total, G, nsm, w0, w1), Nat.mul(1n+g, KT), PP.p2_m_pos(g, KT, kpos)))

# first_contrib(g) <= b iff g KT < start(b + 1)
def lo_le_iff(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool})
  -> {Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b) ==
    Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, total, G, nsm, w0, w1)) : Bool}:
  owner_le(Nat.mul(g, KT), b, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work)

# A touching block lies in [first_contrib(g), last_contrib(g)] (no non-empty-slice assumption).
def touch_in(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    touch: {Spec.touches(b, g, KT, total, G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b) == True{} : Bool} &
    {Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) == True{} : Bool}:
  +s0 = Impl.start(b, total, G, nsm, w0, w1)
  +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
  +A = Nat.is_lt(s0, Nat.mul(1n+g, KT))
  +B = Nat.is_lt(Nat.mul(g, KT), s1)
  +t = PP.ard_rt(Spec.touches(b, g, KT, total, G, nsm, w0, w1), Bool.and(Nat.is_lt(s0, s1), Bool.and(A, B)),
    touches_range(b, g, KT, total, G, nsm, w0, w1, wgpos), touch)
  +ab = PP.ar_and_r(Nat.is_lt(s0, s1), Bool.and(A, B), t)
  (Equal.trans(Bool, Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b), B, True{},
      lo_le_iff(b, g, KT, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work), PP.ar_and_r(A, B, ab)),
    Equal.trans(Bool, Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1)), A, True{},
      le_hi_iff(b, g, KT, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work, kpos), PP.ar_and_l(A, B, ab)))

# first_contrib(g) <= last_contrib(g)
def lo_le_hi(+g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) ==
    True{} : Bool}:
  +y = Nat.sub(Nat.mul(1n+g, KT), 1n)
  +hi = Impl.last_contrib(g, KT, total, G, nsm, w0, w1)
  Equal.trans(Bool, Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), hi),
    Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+hi, total, G, nsm, w0, w1)), True{},
    lo_le_iff(hi, g, KT, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work),
    PP.ar_le_lt_trans(Nat.mul(g, KT), y, Impl.start(1n+hi, total, G, nsm, w0, w1), PP.p2_gk_le_xhi(g, KT, kpos),
      Equal.trans(Bool, Nat.is_lt(y, Impl.start(1n+hi, total, G, nsm, w0, w1)), Nat.is_le(hi, hi), True{},
        Equal.sym(Bool, Nat.is_le(hi, hi), Nat.is_lt(y, Impl.start(1n+hi, total, G, nsm, w0, w1)),
          owner_le(y, hi, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work)),
        PP.ar_le_refl(hi))))

# ---- max_contrib: the running maximum bounds every nc and never drops ----

def mc_go_mc(+left: Nat, +g0: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +mc: Nat)
  -> {Nat.is_le(mc, Impl.max_contrib.go(left, g0, KT, total, G, nsm, w0, w1, mc)) == True{} : Bool}:
  match left:
    case 0n:
      PP.ar_le_refl(mc)
    case 1n+rest:
      +n = Impl.nc(g0, KT, total, G, nsm, w0, w1)
      +m2 = V2.max_contrib.pick(Nat.is_gt(n, mc), n, mc)
      PP.ar_le_trans(mc, m2, Impl.max_contrib.go(rest, 1n+g0, KT, total, G, nsm, w0, w1, m2),
        PP.p2_pick_mc_go(Nat.is_gt(n, mc), n, mc, {==}),
        mc_go_mc(rest, 1n+g0, KT, total, G, nsm, w0, w1, m2))

def mc_go_nc(+d: Nat, +left: Nat, +g0: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +mc: Nat, small: {Nat.is_lt(d, left) == True{} : Bool})
  -> {Nat.is_le(Impl.nc(Nat.add(d, g0), KT, total, G, nsm, w0, w1),
    Impl.max_contrib.go(left, g0, KT, total, G, nsm, w0, w1, mc)) == True{} : Bool}:
  match d left:
    case 0n 0n:
      Empty.absurd({Nat.is_le(Impl.nc(g0, KT, total, G, nsm, w0, w1), mc) == True{} : Bool}, PP.ar_false_true(small))
    case 1n+dp 0n:
      Empty.absurd({Nat.is_le(Impl.nc(1n+Nat.add(dp, g0), KT, total, G, nsm, w0, w1), mc) == True{} : Bool},
        PP.ar_false_true(small))
    case 0n 1n+rest:
      +n = Impl.nc(g0, KT, total, G, nsm, w0, w1)
      +m2 = V2.max_contrib.pick(Nat.is_gt(n, mc), n, mc)
      PP.ar_le_trans(n, m2, Impl.max_contrib.go(rest, 1n+g0, KT, total, G, nsm, w0, w1, m2),
        PP.p2_pick_n_go(Nat.is_gt(n, mc), n, mc, {==}),
        mc_go_mc(rest, 1n+g0, KT, total, G, nsm, w0, w1, m2))
    case 1n+dp 1n+rest:
      +n = Impl.nc(g0, KT, total, G, nsm, w0, w1)
      +m2 = V2.max_contrib.pick(Nat.is_gt(n, mc), n, mc)
      %PP.ar_add_succ_r(dp, g0)
        : {Nat.is_le(Impl.nc(_, KT, total, G, nsm, w0, w1),
          Impl.max_contrib.go(rest, 1n+g0, KT, total, G, nsm, w0, w1, m2)) == True{} : Bool}
      mc_go_nc(dp, rest, 1n+g0, KT, total, G, nsm, w0, w1, m2, small)

def nc_le_mc(+g: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    group: {Nat.is_lt(g, groups) == True{} : Bool})
  -> {Nat.is_le(Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Impl.max_contrib(groups, KT, G, nsm, w0, w1)) ==
    True{} : Bool}:
  %PP.ar_add_zero_r(g)
    : {Nat.is_le(Impl.nc(_, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Impl.max_contrib(groups, KT, G, nsm, w0, w1)) ==
      True{} : Bool}
  mc_go_nc(g, groups, 0n, KT, Nat.mul(groups, KT), G, nsm, w0, w1, 1n, group)

# g < groups and KT >= 1 give groups * KT >= 1 and (g + 1) KT <= groups * KT.
def grp_work(+g: Nat, +groups: Nat, +KT: Nat, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    +group: {Nat.is_lt(g, groups) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}:
  PP.ard_tr(Nat.is_lt(0n, Nat.mul(groups, KT)), Nat.is_le(1n, Nat.mul(groups, KT)),
    PP.ar_lt_succ_le(0n, Nat.mul(groups, KT)),
    PP.ar_le_trans(1n, Nat.mul(1n+g, KT), Nat.mul(groups, KT), PP.p2_m_pos(g, KT, kpos), PP.p2_m_le(g, groups, KT, group)))

def Laws.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0pos, w1pos, grid, tiles, group):
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  +kp = tiles
  +gr = group
  +total = Nat.mul(groups, KT)
  +wg = WG_pos(G, nsm, w0, w1, p0, p1, gp)
  +wk = grp_work(g, groups, KT, kp, gr)
  (lo_le_hi(g, KT, total, G, nsm, w0, w1, p0, p1, wg, wk, kp),
    (owner_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G, nsm, w0, w1, p0, p1, gp,
        PP.p2_xhi_lt(g, KT, total, kp, PP.p2_m_le(g, groups, KT, gr))),
      (PP.ar_le_add_l(Nat.sub(Impl.last_contrib(g, KT, total, G, nsm, w0, w1),
          Impl.first_contrib(g, KT, total, G, nsm, w0, w1)), 1n),
        nc_le_mc(g, groups, KT, G, nsm, w0, w1, gr))))

# A contributor's slot b - first_contrib(g) is below nc(g) and max_contrib.
def slot_lt(+b: Nat, +g: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +grid: {Nat.is_lt(0n, G) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    +group: {Nat.is_lt(g, groups) == True{} : Bool},
    +touch: {Spec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool})
  -> {Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b) == True{} : Bool} &
    {Nat.is_lt(Nat.sub(b, Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
      Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
    {Nat.is_lt(Nat.sub(b, Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
      Impl.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  +total = Nat.mul(groups, KT)
  +lo = Impl.first_contrib(g, KT, total, G, nsm, w0, w1)
  +hi = Impl.last_contrib(g, KT, total, G, nsm, w0, w1)
  +wg = WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid)
  +wk = grp_work(g, groups, KT, kpos, group)
  +lob = PP.ard_fst({Nat.is_le(lo, b) == True{} : Bool}, {Nat.is_le(b, hi) == True{} : Bool}, touch_in(b, g, KT, total, G, nsm, w0, w1, w0pos, w1pos, wg, wk, kpos, touch))
  +bhi = PP.ard_snd({Nat.is_le(lo, b) == True{} : Bool}, {Nat.is_le(b, hi) == True{} : Bool}, touch_in(b, g, KT, total, G, nsm, w0, w1, w0pos, w1pos, wg, wk, kpos, touch))
  +off = PP.p2_lt_add1(Nat.sub(b, lo), Nat.sub(hi, lo), PP.p2_off_le(b, lo, hi, lob, bhi))
  (lob, (off, PP.ar_lt_le_trans(Nat.sub(b, lo), Impl.nc(g, KT, total, G, nsm, w0, w1),
    Impl.max_contrib(groups, KT, G, nsm, w0, w1), off, nc_le_mc(g, groups, KT, G, nsm, w0, w1, group))))

def Laws.slot_in_range(groups, KT, G, nsm, w0, w1, g, b, w0pos, w1pos, grid, tiles, group, contributor):
  +gr = group
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  +kp = tiles
  +ct = contributor
  +lo = Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)
  +mc = Impl.max_contrib(groups, KT, G, nsm, w0, w1)
  -A = {Nat.is_le(lo, b) == True{} : Bool}
  -B = {Nat.is_lt(Nat.sub(b, lo), Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}
  -C = {Nat.is_lt(Nat.sub(b, lo), mc) == True{} : Bool}
  (PP.ard_fst(A, B & C, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gr, ct)), (PP.ard_fst(B, C, PP.ard_snd(A, B & C, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gr, ct))),
    (PP.ard_snd(B, C, PP.ard_snd(A, B & C, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gr, ct))), PP.p2_addr_lt(g, groups, mc, Nat.sub(b, lo), PP.ard_snd(B, C, PP.ard_snd(A, B & C, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gr, ct))), gr))))

def same_block(+b: Nat, +c: Nat, +g: Nat, +h: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    gh: {g == h : Nat},
    rr: {Nat.sub(b, Impl.first_contrib(g, KT, total, G, nsm, w0, w1)) ==
      Nat.sub(c, Impl.first_contrib(h, KT, total, G, nsm, w0, w1)) : Nat},
    lob: {Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b) == True{} : Bool},
    loc: {Nat.is_le(Impl.first_contrib(h, KT, total, G, nsm, w0, w1), c) == True{} : Bool})
  -> {b == c : Nat}:
  %PP.ar_sub_add(b, Impl.first_contrib(g, KT, total, G, nsm, w0, w1), lob) : {_ == c : Nat}
  %Equal.sym(Nat, Nat.sub(b, Impl.first_contrib(g, KT, total, G, nsm, w0, w1)),
      Nat.sub(c, Impl.first_contrib(h, KT, total, G, nsm, w0, w1)), rr)
    : {Nat.add(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), _) == c : Nat}
  %Equal.sym(Nat, g, h, gh)
    : {Nat.add(Impl.first_contrib(_, KT, total, G, nsm, w0, w1), Nat.sub(c, Impl.first_contrib(h, KT, total, G, nsm, w0, w1))) ==
      c : Nat}
  PP.ar_sub_add(c, Impl.first_contrib(h, KT, total, G, nsm, w0, w1), loc)

def Laws.slot_injective(groups, KT, G, nsm, w0, w1, g, b, h, c, w0pos, w1pos, grid, tiles, group_g, group_h,
    touch_b, touch_c, same):
  +sm = same
  +tb = touch_b
  +tc = touch_c
  +gg = group_g
  +gh2 = group_h
  +p0 = w0pos
  +p1 = w1pos
  +gp = grid
  +kp = tiles
  +total = Nat.mul(groups, KT)
  +mc = Impl.max_contrib(groups, KT, G, nsm, w0, w1)
  +lg = Impl.first_contrib(g, KT, total, G, nsm, w0, w1)
  +lh = Impl.first_contrib(h, KT, total, G, nsm, w0, w1)
  -Ab = {Nat.is_le(lg, b) == True{} : Bool}
  -Bb = {Nat.is_lt(Nat.sub(b, lg), Impl.nc(g, KT, total, G, nsm, w0, w1)) == True{} : Bool}
  -Cb = {Nat.is_lt(Nat.sub(b, lg), mc) == True{} : Bool}
  -Ac = {Nat.is_le(lh, c) == True{} : Bool}
  -Bc = {Nat.is_lt(Nat.sub(c, lh), Impl.nc(h, KT, total, G, nsm, w0, w1)) == True{} : Bool}
  -Cc = {Nat.is_lt(Nat.sub(c, lh), mc) == True{} : Bool}
  +gh = PP.ard_fst({g == h : Nat}, {Nat.sub(b, lg) == Nat.sub(c, lh) : Nat}, PP.ar_divmod_inj(g, Nat.sub(b, lg), h, Nat.sub(c, lh), mc,
    PP.ard_snd(Bb, Cb, PP.ard_snd(Ab, Bb & Cb, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gg, tb))), PP.ard_snd(Bc, Cc, PP.ard_snd(Ac, Bc & Cc, slot_lt(c, h, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gh2, tc))), sm))
  (gh, same_block(b, c, g, h, KT, total, G, nsm, w0, w1, gh,
    PP.ard_snd({g == h : Nat}, {Nat.sub(b, lg) == Nat.sub(c, lh) : Nat}, PP.ar_divmod_inj(g, Nat.sub(b, lg), h, Nat.sub(c, lh), mc,
    PP.ard_snd(Bb, Cb, PP.ard_snd(Ab, Bb & Cb, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gg, tb))), PP.ard_snd(Bc, Cc, PP.ard_snd(Ac, Bc & Cc, slot_lt(c, h, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gh2, tc))), sm)),
    PP.ard_fst(Ab, Bb & Cb, slot_lt(b, g, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gg, tb)), PP.ard_fst(Ac, Bc & Cc, slot_lt(c, h, groups, KT, G, nsm, w0, w1, p0, p1, gp, kp, gh2, tc))))

# Under the host guard: touches(b, g) iff first_contrib(g) <= b <= last_contrib(g), for b < G.
def contig(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool},
    +kpos: {Nat.is_lt(0n, KT) == True{} : Bool}, block: {Nat.is_lt(b, G) == True{} : Bool})
  -> {Spec.touches(b, g, KT, total, G, nsm, w0, w1) ==
    Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
      Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))) : Bool}:
  -P0 = {Nat.is_lt(0n, w0) == True{} : Bool}
  -P1 = {Nat.is_lt(0n, w1) == True{} : Bool}
  -PG = {Nat.is_lt(0n, G) == True{} : Bool}
  -PT = {Nat.is_lt(0n, total) == True{} : Bool}
  +w0p = PP.ard_fst(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, valid))
  +w1p = PP.ard_fst(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, valid)))
  +gpp = PP.ard_fst(PG, PT, PP.ard_snd(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, valid))))
  +wkp = PP.ard_snd(PG, PT, PP.ard_snd(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, valid))))
  +wg = WG_pos(G, nsm, w0, w1, w0p, w1p, gpp)
  +s0 = Impl.start(b, total, G, nsm, w0, w1)
  +s1 = Impl.start(1n+b, total, G, nsm, w0, w1)
  +A = Nat.is_lt(s0, Nat.mul(1n+g, KT))
  +B = Nat.is_lt(Nat.mul(g, KT), s1)
  Equal.trans(Bool, Spec.touches(b, g, KT, total, G, nsm, w0, w1), Bool.and(Nat.is_lt(s0, s1), Bool.and(A, B)),
    Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
      Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))),
    touches_range(b, g, KT, total, G, nsm, w0, w1, wg),
    Equal.trans(Bool, Bool.and(Nat.is_lt(s0, s1), Bool.and(A, B)), Bool.and(A, B),
      Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
        Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))),
      PP.p2_and_true_l(Nat.is_lt(s0, s1), Bool.and(A, B), valid_nonempty(total, G, nsm, w0, w1, b, valid, block)),
      Equal.trans(Bool, Bool.and(A, B), Bool.and(B, A),
        Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
          Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))),
        PP.p2_and_comm(A, B),
        (%lo_le_iff(b, g, KT, total, G, nsm, w0, w1, w0p, w1p, wg, wkp)
            : {Bool.and(_, A) == Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
              Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))) : Bool}
          %le_hi_iff(b, g, KT, total, G, nsm, w0, w1, w0p, w1p, wg, wkp, kpos)
            : {Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b), _) ==
              Bool.and(Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), b),
                Nat.is_le(b, Impl.last_contrib(g, KT, total, G, nsm, w0, w1))) : Bool}
          {==}))))

def Laws.contributors_contiguous(groups, KT, G, nsm, w0, w1, g, b, valid, tiles, group, block):
  contig(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1, valid, tiles, block)

# touch_count(n) + [blocks below lo] == [blocks below hi + 1], n <= G
def tele(+n: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool},
    +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    +lohi: {Nat.is_le(Impl.first_contrib(g, KT, total, G, nsm, w0, w1), Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) ==
      True{} : Bool},
    nle: {Nat.is_le(n, G) == True{} : Bool})
  -> {Nat.add(Spec.touch_count(n, g, KT, total, G, nsm, w0, w1), MP.ltc(n, Impl.first_contrib(g, KT, total, G, nsm, w0, w1))) ==
    MP.ltc(n, 1n+Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +nl = nle
      +lo = Impl.first_contrib(g, KT, total, G, nsm, w0, w1)
      +hi = Impl.last_contrib(g, KT, total, G, nsm, w0, w1)
      +C = Spec.touch_count(m, g, KT, total, G, nsm, w0, w1)
      +T = V2Spec.bit(Spec.touches(m, g, KT, total, G, nsm, w0, w1))
      +L = MP.ltc(m, lo)
      +Lm = V2Spec.bit(Nat.is_lt(m, lo))
      +mG = PP.ard_tr(Nat.is_lt(m, G), Nat.is_le(1n+m, G), PP.ar_lt_succ_le(m, G), nl)
      Equal.trans(Nat, Nat.add(Nat.add(C, T), Nat.add(L, Lm)), Nat.add(Nat.add(C, L), Nat.add(T, Lm)),
        Nat.add(MP.ltc(m, 1n+hi), V2Spec.bit(Nat.is_lt(m, 1n+hi))),
        MP.swap4(C, T, L, Lm),
        (%Equal.sym(Nat, Nat.add(C, L), MP.ltc(m, 1n+hi),
              tele(m, g, KT, total, G, nsm, w0, w1, valid, kpos, lohi, PP.ar_le_trans(m, 1n+m, G, PP.ar_h_le_succ(m), nl)))
            : {Nat.add(_, Nat.add(T, Lm)) == Nat.add(MP.ltc(m, 1n+hi), V2Spec.bit(Nat.is_lt(m, 1n+hi))) : Nat}
          %Equal.sym(Bool, Spec.touches(m, g, KT, total, G, nsm, w0, w1), Bool.and(Nat.is_le(lo, m), Nat.is_le(m, hi)),
              contig(m, g, KT, total, G, nsm, w0, w1, valid, kpos, mG))
            : {Nat.add(MP.ltc(m, 1n+hi), Nat.add(V2Spec.bit(_), Lm)) ==
              Nat.add(MP.ltc(m, 1n+hi), V2Spec.bit(Nat.is_lt(m, 1n+hi))) : Nat}
          Equal.cong(Nat, Nat, t => Nat.add(MP.ltc(m, 1n+hi), t),
            Nat.add(V2Spec.bit(Bool.and(Nat.is_le(lo, m), Nat.is_le(m, hi))), Lm),
            V2Spec.bit(Nat.is_lt(m, 1n+hi)),
            MP.pw_step(Nat.is_lt(m, lo), m, lo, hi, {==}, lohi))))

def Laws.touch_count_is_nc(groups, KT, G, nsm, w0, w1, g, valid, tiles, group):
  +v = valid
  +kp = tiles
  +gr = group
  +total = Nat.mul(groups, KT)
  -P0 = {Nat.is_lt(0n, w0) == True{} : Bool}
  -P1 = {Nat.is_lt(0n, w1) == True{} : Bool}
  -PG = {Nat.is_lt(0n, G) == True{} : Bool}
  -PT = {Nat.is_lt(0n, total) == True{} : Bool}
  +w0p = PP.ard_fst(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, v))
  +w1p = PP.ard_fst(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, v)))
  +gpp = PP.ard_fst(PG, PT, PP.ard_snd(P1, PG & PT, PP.ard_snd(P0, P1 & PG & PT, valid_dom(total, G, nsm, w0, w1, v))))
  +wg = WG_pos(G, nsm, w0, w1, w0p, w1p, gpp)
  +wkp = grp_work(g, groups, KT, kp, gr)
  +lo = Impl.first_contrib(g, KT, total, G, nsm, w0, w1)
  +hi = Impl.last_contrib(g, KT, total, G, nsm, w0, w1)
  +C = Spec.touch_count(G, g, KT, total, G, nsm, w0, w1)
  +lohi = lo_le_hi(g, KT, total, G, nsm, w0, w1, w0p, w1p, wg, wkp, kp)
  +hig = owner_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G, nsm, w0, w1, w0p, w1p, gpp,
    PP.p2_xhi_lt(g, KT, total, kp, PP.p2_m_le(g, groups, KT, gr)))
  +hi1g = Equal.trans(Bool, Nat.is_le(1n+hi, G), Nat.is_lt(hi, G), True{},
    Equal.sym(Bool, Nat.is_lt(hi, G), Nat.is_le(1n+hi, G), PP.ar_lt_succ_le(hi, G)), hig)
  +E2 = Equal.trans(Nat, Nat.add(C, lo), Nat.add(C, MP.ltc(G, lo)), 1n+hi,
    Equal.cong(Nat, Nat, t => Nat.add(C, t), lo, MP.ltc(G, lo),
      Equal.sym(Nat, MP.ltc(G, lo), lo, MP.ltc_full(G, lo, PP.ar_le_trans(lo, hi, G, lohi, PP.ar_lt_le(hi, G, hig))))),
    Equal.trans(Nat, Nat.add(C, MP.ltc(G, lo)), MP.ltc(G, 1n+hi), 1n+hi,
      tele(G, g, KT, total, G, nsm, w0, w1, v, kp, lohi, PP.ar_le_refl(G)), MP.ltc_full(G, 1n+hi, hi1g)))
  +E1 = Equal.trans(Nat, Nat.add(lo, C), Nat.add(C, lo), 1n+hi, PP.ar_add_comm(lo, C), E2)
  Equal.trans(Nat, C, Nat.sub(Nat.add(lo, C), lo), Impl.nc(g, KT, total, G, nsm, w0, w1),
    Equal.sym(Nat, Nat.sub(Nat.add(lo, C), lo), C, PP.ar_add_sub(lo, C)),
    Equal.trans(Nat, Nat.sub(Nat.add(lo, C), lo), Nat.sub(1n+hi, lo), Impl.nc(g, KT, total, G, nsm, w0, w1),
      Equal.cong(Nat, Nat, t => Nat.sub(t, lo), Nat.add(lo, C), 1n+hi, E1),
      Equal.trans(Nat, Nat.sub(1n+hi, lo), 1n+Nat.sub(hi, lo), Nat.add(Nat.sub(hi, lo), 1n),
        MP.sub_succ(hi, lo, lohi), MP.add_one(Nat.sub(hi, lo)))))

# ==== (H) slice length and the contributor bound ====

def lw_go(v: Bool, -L: Nat, -WG: Nat, -total: Nat, -w0: Nat, -w1: Nat,
    l0: {Nat.is_le(Nat.mul(L, WG), Nat.mul(total, w0)) == True{} : Bool},
    l1: {Nat.is_le(Nat.mul(L, WG), Nat.mul(total, w1)) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(L, WG), Nat.mul(total, Spec.weight(v, w0, w1))) == True{} : Bool}:
  match v:
    case True{}:
      l0
    case False{}:
      l1

# start(b) + L <= start(b + 1)
def slice(+b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat,
    wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Impl.start(b, total, G, nsm, w0, w1), L), Impl.start(1n+b, total, G, nsm, w0, w1)) ==
    True{} : Bool}:
  +WG = Impl.wpre(G, nsm, w0, w1)
  +wg = wgpos
  +s = Impl.start(b, total, G, nsm, w0, w1)
  +Wb = Impl.wpre(b, nsm, w0, w1)
  +wt = Spec.weight(Nat.is_lt(b, nsm), w0, w1)
  PP.ard_rt(Nat.is_le(Nat.mul(Nat.add(s, L), WG), Nat.mul(total, Impl.wpre(1n+b, nsm, w0, w1))),
    Nat.is_le(Nat.add(s, L), Impl.start(1n+b, total, G, nsm, w0, w1)),
    PP.ar_div_le(Nat.add(s, L), Nat.mul(total, Impl.wpre(1n+b, nsm, w0, w1)), WG, wg),
    (%Equal.sym(Nat, Nat.mul(Nat.add(s, L), WG), Nat.add(Nat.mul(s, WG), Nat.mul(L, WG)), PP.ar_mul_add_l(s, L, WG))
        : {Nat.is_le(_, Nat.mul(total, Impl.wpre(1n+b, nsm, w0, w1))) == True{} : Bool}
      %Equal.sym(Nat, Impl.wpre(1n+b, nsm, w0, w1), Nat.add(Wb, wt), W_step(b, nsm, w0, w1))
        : {Nat.is_le(Nat.add(Nat.mul(s, WG), Nat.mul(L, WG)), Nat.mul(total, _)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(total, Nat.add(Wb, wt)), Nat.add(Nat.mul(total, Wb), Nat.mul(total, wt)),
          w_mul_add_r(total, Wb, wt))
        : {Nat.is_le(Nat.add(Nat.mul(s, WG), Nat.mul(L, WG)), _) == True{} : Bool}
      w_add_mono(Nat.mul(s, WG), Nat.mul(total, Wb), Nat.mul(L, WG), Nat.mul(total, wt),
        PP.ard_le_mul_div(Nat.mul(total, Wb), WG, wg),
        lw_go(Nat.is_lt(b, nsm), L, WG, total, w0, w1, l0, l1))))

def Laws.slice_len(total, G, nsm, w0, w1, L, b, w0pos, w1pos, grid, l0, l1):
  slice(b, total, G, nsm, w0, w1, L, WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid), l0, l1)

# start(b) + d L <= start(d + b)
def chain(+d: Nat, +b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Impl.start(b, total, G, nsm, w0, w1), Nat.mul(d, L)),
    Impl.start(Nat.add(d, b), total, G, nsm, w0, w1)) == True{} : Bool}:
  match d:
    case 0n:
      +s = Impl.start(b, total, G, nsm, w0, w1)
      %Equal.sym(Nat, Nat.add(s, 0n), s, PP.ar_add_zero_r(s)) : {Nat.is_le(_, s) == True{} : Bool}
      PP.ar_le_refl(s)
    case 1n+e:
      +s = Impl.start(b, total, G, nsm, w0, w1)
      +eL = Nat.mul(e, L)
      +se = Impl.start(Nat.add(e, b), total, G, nsm, w0, w1)
      %Equal.sym(Nat, Nat.add(s, Nat.add(L, eL)), Nat.add(L, Nat.add(s, eL)), PP.ar_h_add_swap(s, L, eL))
        : {Nat.is_le(_, Impl.start(1n+Nat.add(e, b), total, G, nsm, w0, w1)) == True{} : Bool}
      %PP.ar_add_comm(Nat.add(s, eL), L) : {Nat.is_le(_, Impl.start(1n+Nat.add(e, b), total, G, nsm, w0, w1)) == True{} : Bool}
      PP.ar_le_trans(Nat.add(Nat.add(s, eL), L), Nat.add(se, L), Impl.start(1n+Nat.add(e, b), total, G, nsm, w0, w1),
        w_add_mono(Nat.add(s, eL), se, L, L, chain(e, b, total, G, nsm, w0, w1, L, wgpos, l0, l1), PP.ar_le_refl(L)),
        slice(Nat.add(e, b), total, G, nsm, w0, w1, L, wgpos, l0, l1))

# (KT + gk) - 1 < (1 + gk) + M when KT < 2 + M.
def span_ineq(+KT: Nat, +gk: Nat, +M: Nat, h: {Nat.is_lt(KT, Nat.add(2n, M)) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(Nat.add(KT, gk), 1n), Nat.add(1n+gk, M)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(Nat.sub(Nat.add(KT, gk), 1n), Nat.add(1n+gk, M)),
      Nat.is_lt(Nat.add(KT, gk), Nat.add(1n, Nat.add(1n+gk, M))),
      PP.ar_sub_lt_iff(Nat.add(KT, gk), 1n, Nat.add(1n+gk, M), {==}))
    : {_ == True{} : Bool}
  %Equal.trans(Nat, Nat.add(gk, Nat.add(2n, M)), Nat.add(Nat.add(2n, M), gk), 2n+Nat.add(gk, M),
      PP.ar_add_comm(gk, Nat.add(2n, M)),
      Equal.cong(Nat, Nat, t => 2n+t, Nat.add(M, gk), Nat.add(gk, M), PP.ar_add_comm(M, gk)))
    : {Nat.is_lt(Nat.add(KT, gk), _) == True{} : Bool}
  %PP.ar_add_comm(gk, KT) : {Nat.is_lt(_, Nat.add(gk, Nat.add(2n, M))) == True{} : Bool}
  PP.ard_tr(Nat.is_lt(Nat.add(gk, KT), Nat.add(gk, Nat.add(2n, M))), Nat.is_lt(KT, Nat.add(2n, M)),
    PP.ar_lt_add_cancel(gk, KT, Nat.add(2n, M)), h)

# add(D, 1 + lo) = add(lo, 1 + D)
def add_swap1(+D: Nat, +lo: Nat) -> {Nat.add(D, 1n+lo) == Nat.add(lo, 1n+D) : Nat}:
  Equal.trans(Nat, Nat.add(D, 1n+lo), 1n+Nat.add(D, lo), Nat.add(lo, 1n+D), PP.ar_add_succ_r(D, lo),
    Equal.trans(Nat, 1n+Nat.add(D, lo), 1n+Nat.add(lo, D), Nat.add(lo, 1n+D),
      Equal.cong(Nat, Nat, t => 1n+t, Nat.add(D, lo), Nat.add(lo, D), PP.ar_add_comm(D, lo)),
      Equal.sym(Nat, Nat.add(lo, 1n+D), 1n+Nat.add(lo, D), PP.ar_add_succ_r(lo, D))))

def nc_bound(+g: Nat, +total: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat, +D: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool},
    +span: {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+D, L)) == True{} : Bool})
  -> {Nat.is_le(Impl.nc(g, KT, total, G, nsm, w0, w1), 2n+D) == True{} : Bool}:
  +gk = Nat.mul(g, KT)
  +y = Nat.sub(Nat.mul(1n+g, KT), 1n)
  +M = Nat.mul(1n+D, L)
  +lo = Impl.first_contrib(g, KT, total, G, nsm, w0, w1)
  +hi = Impl.last_contrib(g, KT, total, G, nsm, w0, w1)
  +bb = Nat.add(D, 1n+lo)
  +mpos = PP.ar_le_lt_trans(0n, Nat.sub(KT, 2n), M, PP.ar_h_le_zero(Nat.sub(KT, 2n)), span)
  +k2 = PP.ard_rt(Nat.is_lt(Nat.sub(KT, 2n), M), Nat.is_lt(KT, Nat.add(2n, M)), PP.ar_sub_lt_iff(KT, 2n, M, mpos), span)
  +glt = PP.ard_rt(Nat.is_lt(gk, Impl.start(1n+lo, total, G, nsm, w0, w1)), Nat.is_le(1n+gk, Impl.start(1n+lo, total, G, nsm, w0, w1)),
    PP.ar_lt_succ_le(gk, Impl.start(1n+lo, total, G, nsm, w0, w1)),
    Equal.trans(Bool, Nat.is_lt(gk, Impl.start(1n+lo, total, G, nsm, w0, w1)), Nat.is_le(lo, lo), True{},
      Equal.sym(Bool, Nat.is_le(lo, lo), Nat.is_lt(gk, Impl.start(1n+lo, total, G, nsm, w0, w1)),
        owner_le(gk, lo, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work)),
      PP.ar_le_refl(lo)))
  +big = PP.ar_le_trans(Nat.add(1n+gk, M), Nat.add(Impl.start(1n+lo, total, G, nsm, w0, w1), M),
    Impl.start(Nat.add(1n+D, 1n+lo), total, G, nsm, w0, w1),
    w_add_mono(1n+gk, Impl.start(1n+lo, total, G, nsm, w0, w1), M, M, glt, PP.ar_le_refl(M)),
    chain(1n+D, 1n+lo, total, G, nsm, w0, w1, L, wgpos, l0, l1))
  +hle = Equal.trans(Bool, Nat.is_le(hi, bb), Nat.is_lt(y, Impl.start(1n+bb, total, G, nsm, w0, w1)), True{},
    owner_le(y, bb, total, G, nsm, w0, w1, w0pos, w1pos, wgpos, work),
    PP.ar_lt_le_trans(y, Nat.add(1n+gk, M), Impl.start(1n+bb, total, G, nsm, w0, w1), span_ineq(KT, gk, M, k2), big))
  +sub_le = PP.ard_tr(Nat.is_le(Nat.sub(hi, lo), 1n+D), Nat.is_le(hi, Nat.add(lo, 1n+D)),
    PP.ar_le_sub_iff(hi, lo, 1n+D),
    (%add_swap1(D, lo) : {Nat.is_le(hi, _) == True{} : Bool}
      hle))
  %MP.add_one(Nat.sub(hi, lo)) : {Nat.is_le(_, 2n+D) == True{} : Bool}
  sub_le

def Laws.nc_bound(total, KT, G, nsm, w0, w1, L, D, g, w0pos, w1pos, grid, work, tiles, l0, l1, span):
  +p0 = w0pos
  +p1 = w1pos
  nc_bound(g, total, KT, G, nsm, w0, w1, L, D, p0, p1, WG_pos(G, nsm, w0, w1, p0, p1, grid), work, l0, l1, span)

# ---- the running maximum stays below 2 + D when every nc does ----

def pick_le(v: Bool, -n: Nat, -mc: Nat, -B: Nat, nb: {Nat.is_le(n, B) == True{} : Bool},
    mb: {Nat.is_le(mc, B) == True{} : Bool}) -> {Nat.is_le(V2.max_contrib.pick(v, n, mc), B) == True{} : Bool}:
  match v:
    case True{}:
      nb
    case False{}:
      mb

def mc_go_le(+left: Nat, +g0: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat, +D: Nat,
    +mc: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, total) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool},
    +span: {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+D, L)) == True{} : Bool},
    mb: {Nat.is_le(mc, 2n+D) == True{} : Bool})
  -> {Nat.is_le(Impl.max_contrib.go(left, g0, KT, total, G, nsm, w0, w1, mc), 2n+D) == True{} : Bool}:
  match left:
    case 0n:
      mb
    case 1n+rest:
      +n = Impl.nc(g0, KT, total, G, nsm, w0, w1)
      mc_go_le(rest, 1n+g0, KT, total, G, nsm, w0, w1, L, D, V2.max_contrib.pick(Nat.is_gt(n, mc), n, mc),
        w0pos, w1pos, wgpos, work, l0, l1, span,
        pick_le(Nat.is_gt(n, mc), n, mc, 2n+D,
          nc_bound(g0, total, KT, G, nsm, w0, w1, L, D, w0pos, w1pos, wgpos, work, l0, l1, span), mb))

# ---- a witness group with nc >= D' + 1 ----

# (a k) w = (a w) k
def swap_mul(+a: Nat, +k: Nat, +w: Nat) -> {Nat.mul(Nat.mul(a, k), w) == Nat.mul(Nat.mul(a, w), k) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(a, k), w), Nat.mul(a, Nat.mul(k, w)), Nat.mul(Nat.mul(a, w), k),
    PP.ar_mul_assoc(a, k, w),
    Equal.trans(Nat, Nat.mul(a, Nat.mul(k, w)), Nat.mul(a, Nat.mul(w, k)), Nat.mul(Nat.mul(a, w), k),
      Equal.cong(Nat, Nat, t => Nat.mul(a, t), Nat.mul(k, w), Nat.mul(w, k), PP.ar_mul_comm(k, w)),
      Equal.sym(Nat, Nat.mul(Nat.mul(a, w), k), Nat.mul(a, Nat.mul(w, k)), PP.ar_mul_assoc(a, w, k))))

# c <= last_contrib(g) when groups W(c) < (g + 1) W(G)   (total = groups KT)
def c_le_hi(+c: Nat, +g: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    h: {Nat.is_lt(Nat.mul(groups, Impl.wpre(c, nsm, w0, w1)), Nat.mul(1n+g, Impl.wpre(G, nsm, w0, w1))) == True{} : Bool})
  -> {Nat.is_le(c, Impl.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool}:
  +WG = Impl.wpre(G, nsm, w0, w1)
  +Wc = Impl.wpre(c, nsm, w0, w1)
  Equal.trans(Bool, Nat.is_le(c, Impl.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
    Nat.is_lt(Impl.start(c, Nat.mul(groups, KT), G, nsm, w0, w1), Nat.mul(1n+g, KT)), True{},
    le_hi_iff(c, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1, w0pos, w1pos, wgpos, work, kpos),
    (%Equal.sym(Bool, Nat.is_lt(Nat.div(Nat.mul(Nat.mul(groups, KT), Wc), WG), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(Nat.mul(groups, KT), Wc), Nat.mul(Nat.mul(1n+g, KT), WG)),
        PP.ar_div_lt(Nat.mul(1n+g, KT), Nat.mul(Nat.mul(groups, KT), Wc), WG, wgpos)) : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(groups, KT), Wc), Nat.mul(Nat.mul(groups, Wc), KT), swap_mul(groups, KT, Wc))
        : {Nat.is_lt(_, Nat.mul(Nat.mul(1n+g, KT), WG)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(1n+g, KT), WG), Nat.mul(Nat.mul(1n+g, WG), KT), swap_mul(1n+g, KT, WG))
        : {Nat.is_lt(Nat.mul(Nat.mul(groups, Wc), KT), _) == True{} : Bool}
      PP.ard_tr(Nat.is_lt(Nat.mul(Nat.mul(groups, Wc), KT), Nat.mul(Nat.mul(1n+g, WG), KT)),
        Nat.is_lt(Nat.mul(groups, Wc), Nat.mul(1n+g, WG)),
        PP.ar_mul_lt_cancel(Nat.mul(groups, Wc), Nat.mul(1n+g, WG), KT, kpos), h)))

# first_contrib(g) <= c when g W(G) + m <= groups W(c + 1) and W(G) <= m KT   (total = groups KT)
def lo_le_c(+c: Nat, +g: Nat, +m: Nat, +groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +work: {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool},
    h: {Nat.is_le(Nat.add(Nat.mul(g, Impl.wpre(G, nsm, w0, w1)), m),
      Nat.mul(groups, Impl.wpre(1n+c, nsm, w0, w1))) == True{} : Bool},
    hm: {Nat.is_le(Impl.wpre(G, nsm, w0, w1), Nat.mul(m, KT)) == True{} : Bool})
  -> {Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), c) == True{} : Bool}:
  +WG = Impl.wpre(G, nsm, w0, w1)
  +W1 = Impl.wpre(1n+c, nsm, w0, w1)
  +gk = Nat.mul(g, KT)
  +s1 = Impl.start(1n+c, Nat.mul(groups, KT), G, nsm, w0, w1)
  Equal.trans(Bool, Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), c),
    Nat.is_lt(gk, s1), True{},
    lo_le_iff(c, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1, w0pos, w1pos, wgpos, work),
    (%Equal.sym(Bool, Nat.is_lt(gk, s1), Nat.is_le(1n+gk, s1), PP.ar_lt_succ_le(gk, s1)) : {_ == True{} : Bool}
      %PP.ar_div_le(1n+gk, Nat.mul(Nat.mul(groups, KT), W1), WG, wgpos) : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(groups, KT), W1), Nat.mul(Nat.mul(groups, W1), KT), swap_mul(groups, KT, W1))
        : {Nat.is_le(Nat.mul(1n+gk, WG), _) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(Nat.mul(g, KT), WG), Nat.mul(Nat.mul(g, WG), KT), swap_mul(g, KT, WG))
        : {Nat.is_le(Nat.add(WG, _), Nat.mul(Nat.mul(groups, W1), KT)) == True{} : Bool}
      PP.ar_le_trans(Nat.add(WG, Nat.mul(Nat.mul(g, WG), KT)),
        Nat.add(Nat.mul(m, KT), Nat.mul(Nat.mul(g, WG), KT)), Nat.mul(Nat.mul(groups, W1), KT),
        w_add_mono(WG, Nat.mul(m, KT), Nat.mul(Nat.mul(g, WG), KT), Nat.mul(Nat.mul(g, WG), KT), hm,
          PP.ar_le_refl(Nat.mul(Nat.mul(g, WG), KT))),
        (%PP.ar_mul_add_l(m, Nat.mul(g, WG), KT)
            : {Nat.is_le(_, Nat.mul(Nat.mul(groups, W1), KT)) == True{} : Bool}
          PP.ar_le_mul_mono(Nat.add(m, Nat.mul(g, WG)), Nat.mul(groups, W1), KT,
            (%PP.ar_add_comm(Nat.mul(g, WG), m) : {Nat.is_le(_, Nat.mul(groups, W1)) == True{} : Bool}
              h))))))

# lo <= c and c + D' <= hi give D' + 1 <= nc.
def nc_ge(+c: Nat, +Dp: Nat, +lo: Nat, +hi: Nat, loc: {Nat.is_le(lo, c) == True{} : Bool},
    chi: {Nat.is_le(Nat.add(Dp, c), hi) == True{} : Bool})
  -> {Nat.is_le(1n+Dp, Nat.add(Nat.sub(hi, lo), 1n)) == True{} : Bool}:
  +lc = loc
  +lh = PP.ar_le_trans(Nat.add(lo, Dp), Nat.add(c, Dp), hi, w_add_mono(lo, c, Dp, Dp, lc, PP.ar_le_refl(Dp)),
    (%PP.ar_add_comm(Dp, c) : {Nat.is_le(_, hi) == True{} : Bool}
      chi))
  +lohi = PP.ar_le_trans(lo, Nat.add(lo, Dp), hi, PP.ar_le_add_r(lo, Dp), lh)
  %MP.add_one(Nat.sub(hi, lo)) : {Nat.is_le(1n+Dp, _) == True{} : Bool}
  PP.ard_tr(Nat.is_le(Dp, Nat.sub(hi, lo)), Nat.is_le(Nat.add(lo, Dp), hi), le_sub_r(Dp, hi, lo, lohi), lh)

# ---- generic served-instance lemmas ----

def lt_add_pos(+s: Nat, +L: Nat, lpos: {Nat.is_lt(0n, L) == True{} : Bool})
  -> {Nat.is_lt(s, Nat.add(s, L)) == True{} : Bool}:
  %PP.ar_add_zero_r(s) : {Nat.is_lt(_, Nat.add(s, L)) == True{} : Bool}
  PP.ard_tr(Nat.is_lt(Nat.add(s, 0n), Nat.add(s, L)), Nat.is_lt(0n, L), PP.ar_lt_add_cancel(s, 0n, L), lpos)

def go_true(+left: Nat, +b0: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat,
    +wgpos: {Nat.is_lt(0n, Impl.wpre(G, nsm, w0, w1)) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool},
    +lpos: {Nat.is_lt(0n, L) == True{} : Bool})
  -> {Impl.weights_valid.go(left, b0, total, G, nsm, w0, w1) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      +s0 = Impl.start(b0, total, G, nsm, w0, w1)
      +s1 = Impl.start(1n+b0, total, G, nsm, w0, w1)
      PP.ar_and_intro(Nat.is_lt(s0, s1), Impl.weights_valid.go(r, 1n+b0, total, G, nsm, w0, w1),
        PP.ar_lt_le_trans(s0, Nat.add(s0, L), s1, lt_add_pos(s0, L, lpos),
          slice(b0, total, G, nsm, w0, w1, L, wgpos, l0, l1)),
        go_true(r, 1n+b0, total, G, nsm, w0, w1, L, wgpos, l0, l1, lpos))

# The host guard holds when w0, w1, nsm >= 1, nsm <= G <= 2 nsm and a slice length L >= 1 is certified.
def valid_suff(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat,
    +h1: {Nat.is_le(1n, w0) == True{} : Bool}, +h2: {Nat.is_le(1n, w1) == True{} : Bool},
    +h3: {Nat.is_le(1n, nsm) == True{} : Bool}, +h4: {Nat.is_le(nsm, G) == True{} : Bool},
    +h5: {Nat.is_le(G, Nat.mul(2n, nsm)) == True{} : Bool}, +lpos: {Nat.is_lt(0n, L) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool})
  -> {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool}:
  +c1 = Nat.is_le(1n, w0)
  +c2 = Nat.is_le(1n, w1)
  +c3 = Nat.is_le(1n, nsm)
  +c4 = Nat.is_le(nsm, G)
  +c5 = Nat.is_le(G, Nat.mul(2n, nsm))
  +go = Impl.weights_valid.go(G, 0n, total, G, nsm, w0, w1)
  +w0p = PP.ard_tr(Nat.is_lt(0n, w0), Nat.is_le(1n, w0), PP.ar_lt_succ_le(0n, w0), h1)
  +w1p = PP.ard_tr(Nat.is_lt(0n, w1), Nat.is_le(1n, w1), PP.ar_lt_succ_le(0n, w1), h2)
  +gp = PP.ard_tr(Nat.is_lt(0n, G), Nat.is_le(1n, G), PP.ar_lt_succ_le(0n, G), PP.ar_le_trans(1n, nsm, G, h3, h4))
  PP.ar_and_intro(c1, Bool.and(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go)))), h1,
    PP.ar_and_intro(c2, Bool.and(c3, Bool.and(c4, Bool.and(c5, go))), h2,
      PP.ar_and_intro(c3, Bool.and(c4, Bool.and(c5, go)), h3,
        PP.ar_and_intro(c4, Bool.and(c5, go), h4,
          PP.ar_and_intro(c5, go, h5,
            go_true(G, 0n, total, G, nsm, w0, w1, L, WG_pos(G, nsm, w0, w1, w0p, w1p, gp), l0, l1, lpos))))))

# max_contrib <= B when every group has at most 2 + D contributors and 2 + D == B.
def mc_le(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +L: Nat, +D: Nat, +B: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +grid: {Nat.is_lt(0n, G) == True{} : Bool}, +work: {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool},
    +l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w0)) == True{} : Bool},
    +l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w1)) == True{} : Bool},
    +span: {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+D, L)) == True{} : Bool},
    eb: {2n+D == B : Nat})
  -> {Nat.is_le(Impl.max_contrib(groups, KT, G, nsm, w0, w1), B) == True{} : Bool}:
  %eb : {Nat.is_le(Impl.max_contrib(groups, KT, G, nsm, w0, w1), _) == True{} : Bool}
  mc_go_le(groups, 0n, KT, Nat.mul(groups, KT), G, nsm, w0, w1, L, D, 1n, w0pos, w1pos,
    WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid), work, l0, l1, span, {==})

# B <= max_contrib when group g has c in [first_contrib(g), c + D' <= last_contrib(g)] and 1 + D' == B.
def mc_ge(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +c: Nat, +m: Nat, +Dp: Nat, +B: Nat,
    +w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, +w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    +grid: {Nat.is_lt(0n, G) == True{} : Bool}, +work: {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool},
    +kpos: {Nat.is_lt(0n, KT) == True{} : Bool}, group: {Nat.is_lt(g, groups) == True{} : Bool},
    hlo: {Nat.is_le(Nat.add(Nat.mul(g, Impl.wpre(G, nsm, w0, w1)), m),
      Nat.mul(groups, Impl.wpre(1n+c, nsm, w0, w1))) == True{} : Bool},
    hm: {Nat.is_le(Impl.wpre(G, nsm, w0, w1), Nat.mul(m, KT)) == True{} : Bool},
    hhi: {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(Dp, c), nsm, w0, w1)), Nat.mul(1n+g, Impl.wpre(G, nsm, w0, w1))) ==
      True{} : Bool},
    eb: {1n+Dp == B : Nat})
  -> {Nat.is_le(B, Impl.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}:
  +wg = WG_pos(G, nsm, w0, w1, w0pos, w1pos, grid)
  +total = Nat.mul(groups, KT)
  %eb : {Nat.is_le(_, Impl.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}
  PP.ar_le_trans(1n+Dp, Impl.nc(g, KT, total, G, nsm, w0, w1), Impl.max_contrib(groups, KT, G, nsm, w0, w1),
    nc_ge(c, Dp, Impl.first_contrib(g, KT, total, G, nsm, w0, w1), Impl.last_contrib(g, KT, total, G, nsm, w0, w1),
      lo_le_c(c, g, m, groups, KT, G, nsm, w0, w1, w0pos, w1pos, wg, work, hlo, hm),
      c_le_hi(Nat.add(Dp, c), g, groups, KT, G, nsm, w0, w1, w0pos, w1pos, wg, work, kpos, hhi)),
    nc_le_mc(g, groups, KT, G, nsm, w0, w1, group))

# (256 slots of SLOT_FLOATS floats) fit 8 k k bytes when 4 * groups * mc <= k and 8 k = SLOT_FLOATS.
def ws_fit_k(+groups: Nat, +B: Nat, +k: Nat, hq: {Nat.is_le(Nat.mul(Nat.mul(groups, B), 4n), k) == True{} : Bool},
    hsf: {Nat.mul(8n, k) == Impl.slot_floats() : Nat})
  -> {Nat.is_le(Impl.ws_bytes(groups, B), Impl.slot_bytes_of(k)) == True{} : Bool}:
  +gm = Nat.mul(groups, B)
  +X = Nat.mul(8n, k)
  %hsf : {Nat.is_le(Nat.mul(Nat.mul(gm, _), 4n), Impl.slot_bytes_of(k)) == True{} : Bool}
  %Equal.trans(Nat, Nat.mul(X, Nat.mul(gm, 4n)), Nat.mul(Nat.mul(X, gm), 4n), Nat.mul(Nat.mul(gm, X), 4n),
      Equal.sym(Nat, Nat.mul(Nat.mul(X, gm), 4n), Nat.mul(X, Nat.mul(gm, 4n)), PP.ar_mul_assoc(X, gm, 4n)),
      Equal.cong(Nat, Nat, t => Nat.mul(t, 4n), Nat.mul(X, gm), Nat.mul(gm, X), PP.ar_mul_comm(X, gm)))
    : {Nat.is_le(_, Nat.mul(X, k)) == True{} : Bool}
  w_le_mul_l(Nat.mul(gm, 4n), k, X, hq)

def fits_of_cap(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +B: Nat, +k: Nat, +cap: Nat,
    hge: {Nat.is_ge(Nat.mul(groups, KT), G) == True{} : Bool},
    hmc: {Impl.max_contrib(groups, KT, G, nsm, w0, w1) == B : Nat},
    hq: {Nat.is_le(Nat.mul(Nat.mul(groups, B), 4n), k) == True{} : Bool},
    hsf: {Nat.mul(8n, k) == Impl.slot_floats() : Nat},
    scap: {cap == Impl.slot_bytes_of(k) : Nat})
  -> {Impl.launch_fits_cap(groups, KT, G, nsm, w0, w1, cap) == True{} : Bool}:
  PP.ar_and_intro(Nat.is_ge(Nat.mul(groups, KT), G),
    Nat.is_le(Impl.ws_bytes(groups, Impl.max_contrib(groups, KT, G, nsm, w0, w1)), cap), hge,
    (%Equal.sym(Nat, Impl.max_contrib(groups, KT, G, nsm, w0, w1), B, hmc)
        : {Nat.is_le(Impl.ws_bytes(groups, _), cap) == True{} : Bool}
      %Equal.sym(Nat, cap, Impl.slot_bytes_of(k), scap) : {Nat.is_le(Impl.ws_bytes(groups, B), _) == True{} : Bool}
      ws_fit_k(groups, B, k, hq, hsf)))

# ==== (I) served instance: G = 164, nsm = 82, KT = 320, (w0, w1) = (100, 91) ====
# Certificates, each a small closed evaluation after the served constants are substituted into it: slice
# length L = 54 (GDN, total 10240) / 46 (attention, total 8960) with L W(G) <= total w1 <= total w0;
# KT - 2 = 318 < 6 * 54 / 7 * 46 (so nc <= 7 / 8); witnesses: GDN group 18 has blocks 88 .. 94 (margin
# m = 49: W(G) = 15662 <= 49 * 320), attention group 21 has blocks 120 .. 127; 4 * groups * max_contrib
# <= 1024 = k and 8 k = SLOT_FLOATS (so groups * max_contrib slots fit 8 k k bytes).

def h1_gdn(+w0: Nat, +s0: {w0 == Impl.w0_served() : Nat})
  -> {Nat.is_le(1n, w0) == True{} : Bool}:
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h2_gdn(+w1: Nat, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(1n, w1) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h3_gdn(+nsm: Nat, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(1n, nsm) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h4_gdn(+G: Nat, +nsm: Nat, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(nsm, G) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(_, G) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Impl.nsm_served(), _) == True{} : Bool}
  {==}

def h5_gdn(+G: Nat, +nsm: Nat, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(G, Nat.mul(2n, nsm)) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(G, Nat.mul(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(_, Nat.mul(2n, Impl.nsm_served())) == True{} : Bool}
  {==}

def p0_gdn(+w0: Nat, +s0: {w0 == Impl.w0_served() : Nat})
  -> {Nat.is_lt(0n, w0) == True{} : Bool}:
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def p1_gdn(+w1: Nat, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_lt(0n, w1) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pg_gdn(+G: Nat, +sgr: {G == Impl.grid_served() : Nat})
  -> {Nat.is_lt(0n, G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pk_gdn(+KT: Nat, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(0n, KT) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pt_gdn(+groups: Nat, +KT: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(0n, Nat.mul(groups, _)) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_lt(0n, Nat.mul(_, Impl.kt_served())) == True{} : Bool}
  {==}

def w10_gdn(+w0: Nat, +w1: Nat, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(w1, w0) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(_, w0) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Impl.w1_served(), _) == True{} : Bool}
  {==}

def l1_gdn(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Nat.mul(54n, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w1)) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Nat.mul(54n, Impl.wpre(G, nsm, w0, _)), Nat.mul(Nat.mul(groups, KT), _)) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Nat.mul(54n, Impl.wpre(G, nsm, _, Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Nat.mul(54n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Nat.mul(54n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_le(Nat.mul(54n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, _), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_le(Nat.mul(54n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(_, Impl.kt_served()), Impl.w1_served())) == True{} : Bool}
  {==}

def span_gdn(+KT: Nat, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+5n, 54n)) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(Nat.sub(_, 2n), Nat.mul(1n+5n, 54n)) == True{} : Bool}
  {==}

def grp_gdn(+groups: Nat, +sg: {groups == Impl.groups_gdn() : Nat})
  -> {Nat.is_lt(18n, groups) == True{} : Bool}:
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_lt(18n, _) == True{} : Bool}
  {==}

def hlo_gdn(+groups: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(G, nsm, w0, w1)), 49n), Nat.mul(groups, Impl.wpre(1n+88n, nsm, w0, w1))) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(G, nsm, w0, _)), 49n), Nat.mul(groups, Impl.wpre(1n+88n, nsm, w0, _))) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(G, nsm, _, Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+88n, nsm, _, Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+88n, _, Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+88n, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_le(Nat.add(Nat.mul(18n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(_, Impl.wpre(1n+88n, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  {==}

def hm_gdn(+KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Impl.wpre(G, nsm, w0, w1), Nat.mul(49n, KT)) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Impl.wpre(G, nsm, w0, _), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Impl.wpre(G, nsm, _, Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_le(Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, _)) == True{} : Bool}
  {==}

def hhi_gdn(+groups: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(6n, 88n), nsm, w0, w1)), Nat.mul(1n+18n, Impl.wpre(G, nsm, w0, w1))) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(6n, 88n), nsm, w0, _)), Nat.mul(1n+18n, Impl.wpre(G, nsm, w0, _))) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(6n, 88n), nsm, _, Impl.w1_served())), Nat.mul(1n+18n, Impl.wpre(G, nsm, _, Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(6n, 88n), _, Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+18n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(6n, 88n), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+18n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_lt(Nat.mul(_, Impl.wpre(Nat.add(6n, 88n), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+18n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  {==}

def hge_gdn(+groups: Nat, +KT: Nat, +G: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat})
  -> {Nat.is_ge(Nat.mul(groups, KT), G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_ge(Nat.mul(groups, KT), _) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_ge(Nat.mul(groups, _), Impl.grid_served()) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_ge(Nat.mul(_, Impl.kt_served()), Impl.grid_served()) == True{} : Bool}
  {==}

def hq_gdn(+groups: Nat, +k: Nat, +sg: {groups == Impl.groups_gdn() : Nat}, +sk: {k == 1024n : Nat})
  -> {Nat.is_le(Nat.mul(Nat.mul(groups, 7n), 4n), k) == True{} : Bool}:
  %Equal.sym(Nat, k, 1024n, sk) : {Nat.is_le(Nat.mul(Nat.mul(groups, 7n), 4n), _) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_gdn(), sg) : {Nat.is_le(Nat.mul(Nat.mul(_, 7n), 4n), 1024n) == True{} : Bool}
  {==}

def hsf_gdn(+k: Nat, +sk: {k == 1024n : Nat})
  -> {Nat.mul(8n, k) == Impl.slot_floats() : Nat}:
  %Equal.sym(Nat, k, 1024n, sk) : {Nat.mul(8n, _) == Impl.slot_floats() : Nat}
  {==}

def h1_attn(+w0: Nat, +s0: {w0 == Impl.w0_served() : Nat})
  -> {Nat.is_le(1n, w0) == True{} : Bool}:
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h2_attn(+w1: Nat, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(1n, w1) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h3_attn(+nsm: Nat, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(1n, nsm) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(1n, _) == True{} : Bool}
  {==}

def h4_attn(+G: Nat, +nsm: Nat, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(nsm, G) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(_, G) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Impl.nsm_served(), _) == True{} : Bool}
  {==}

def h5_attn(+G: Nat, +nsm: Nat, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat})
  -> {Nat.is_le(G, Nat.mul(2n, nsm)) == True{} : Bool}:
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(G, Nat.mul(2n, _)) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(_, Nat.mul(2n, Impl.nsm_served())) == True{} : Bool}
  {==}

def p0_attn(+w0: Nat, +s0: {w0 == Impl.w0_served() : Nat})
  -> {Nat.is_lt(0n, w0) == True{} : Bool}:
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def p1_attn(+w1: Nat, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_lt(0n, w1) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pg_attn(+G: Nat, +sgr: {G == Impl.grid_served() : Nat})
  -> {Nat.is_lt(0n, G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pk_attn(+KT: Nat, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(0n, KT) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pt_attn(+groups: Nat, +KT: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(0n, Nat.mul(groups, KT)) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(0n, Nat.mul(groups, _)) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_lt(0n, Nat.mul(_, Impl.kt_served())) == True{} : Bool}
  {==}

def w10_attn(+w0: Nat, +w1: Nat, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(w1, w0) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(_, w0) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Impl.w1_served(), _) == True{} : Bool}
  {==}

def l1_attn(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Nat.mul(46n, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w1)) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Nat.mul(46n, Impl.wpre(G, nsm, w0, _)), Nat.mul(Nat.mul(groups, KT), _)) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Nat.mul(46n, Impl.wpre(G, nsm, _, Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Nat.mul(46n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Nat.mul(46n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, KT), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_le(Nat.mul(46n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(groups, _), Impl.w1_served())) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_le(Nat.mul(46n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(Nat.mul(_, Impl.kt_served()), Impl.w1_served())) == True{} : Bool}
  {==}

def span_attn(+KT: Nat, +skt: {KT == Impl.kt_served() : Nat})
  -> {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+6n, 46n)) == True{} : Bool}:
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_lt(Nat.sub(_, 2n), Nat.mul(1n+6n, 46n)) == True{} : Bool}
  {==}

def grp_attn(+groups: Nat, +sg: {groups == Impl.groups_attn() : Nat})
  -> {Nat.is_lt(21n, groups) == True{} : Bool}:
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_lt(21n, _) == True{} : Bool}
  {==}

def hlo_attn(+groups: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(G, nsm, w0, w1)), 49n), Nat.mul(groups, Impl.wpre(1n+120n, nsm, w0, w1))) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(G, nsm, w0, _)), 49n), Nat.mul(groups, Impl.wpre(1n+120n, nsm, w0, _))) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(G, nsm, _, Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+120n, nsm, _, Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+120n, _, Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(groups, Impl.wpre(1n+120n, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_le(Nat.add(Nat.mul(21n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), 49n), Nat.mul(_, Impl.wpre(1n+120n, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  {==}

def hm_attn(+KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_le(Impl.wpre(G, nsm, w0, w1), Nat.mul(49n, KT)) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_le(Impl.wpre(G, nsm, w0, _), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_le(Impl.wpre(G, nsm, _, Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_le(Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_le(Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, KT)) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_le(Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()), Nat.mul(49n, _)) == True{} : Bool}
  {==}

def hhi_attn(+groups: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +sgr: {G == Impl.grid_served() : Nat}, +sn: {nsm == Impl.nsm_served() : Nat}, +s0: {w0 == Impl.w0_served() : Nat}, +s1: {w1 == Impl.w1_served() : Nat})
  -> {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(7n, 120n), nsm, w0, w1)), Nat.mul(1n+21n, Impl.wpre(G, nsm, w0, w1))) == True{} : Bool}:
  %Equal.sym(Nat, w1, Impl.w1_served(), s1) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(7n, 120n), nsm, w0, _)), Nat.mul(1n+21n, Impl.wpre(G, nsm, w0, _))) == True{} : Bool}
  %Equal.sym(Nat, w0, Impl.w0_served(), s0) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(7n, 120n), nsm, _, Impl.w1_served())), Nat.mul(1n+21n, Impl.wpre(G, nsm, _, Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, nsm, Impl.nsm_served(), sn) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(7n, 120n), _, Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+21n, Impl.wpre(G, _, Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_lt(Nat.mul(groups, Impl.wpre(Nat.add(7n, 120n), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+21n, Impl.wpre(_, Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_lt(Nat.mul(_, Impl.wpre(Nat.add(7n, 120n), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served())), Nat.mul(1n+21n, Impl.wpre(Impl.grid_served(), Impl.nsm_served(), Impl.w0_served(), Impl.w1_served()))) == True{} : Bool}
  {==}

def hge_attn(+groups: Nat, +KT: Nat, +G: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +skt: {KT == Impl.kt_served() : Nat}, +sgr: {G == Impl.grid_served() : Nat})
  -> {Nat.is_ge(Nat.mul(groups, KT), G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid_served(), sgr) : {Nat.is_ge(Nat.mul(groups, KT), _) == True{} : Bool}
  %Equal.sym(Nat, KT, Impl.kt_served(), skt) : {Nat.is_ge(Nat.mul(groups, _), Impl.grid_served()) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_ge(Nat.mul(_, Impl.kt_served()), Impl.grid_served()) == True{} : Bool}
  {==}

def hq_attn(+groups: Nat, +k: Nat, +sg: {groups == Impl.groups_attn() : Nat}, +sk: {k == 1024n : Nat})
  -> {Nat.is_le(Nat.mul(Nat.mul(groups, 8n), 4n), k) == True{} : Bool}:
  %Equal.sym(Nat, k, 1024n, sk) : {Nat.is_le(Nat.mul(Nat.mul(groups, 8n), 4n), _) == True{} : Bool}
  %Equal.sym(Nat, groups, Impl.groups_attn(), sg) : {Nat.is_le(Nat.mul(Nat.mul(_, 8n), 4n), 1024n) == True{} : Bool}
  {==}

def hsf_attn(+k: Nat, +sk: {k == 1024n : Nat})
  -> {Nat.mul(8n, k) == Impl.slot_floats() : Nat}:
  %Equal.sym(Nat, k, 1024n, sk) : {Nat.mul(8n, _) == Impl.slot_floats() : Nat}
  {==}

def Laws.served_gdn(groups, KT, G, nsm, w0, w1, k, cap, s_groups, s_kt, s_grid, s_nsm, s_w0, s_w1, s_k, s_cap):
  +sg = s_groups
  +skt = s_kt
  +sgr = s_grid
  +sn = s_nsm
  +s0 = s_w0
  +s1 = s_w1
  +sk = s_k
  +l1 = l1_gdn(groups, KT, G, nsm, w0, w1, sg, skt, sgr, sn, s0, s1)
  +l0 = PP.ar_le_trans(Nat.mul(54n, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w1),
    Nat.mul(Nat.mul(groups, KT), w0), l1, w_le_mul_l(w1, w0, Nat.mul(groups, KT), w10_gdn(w0, w1, s0, s1)))
  +mc = PP.ar_le_antisym(Impl.max_contrib(groups, KT, G, nsm, w0, w1), 7n,
    mc_le(groups, KT, G, nsm, w0, w1, 54n, 5n, 7n, p0_gdn(w0, s0), p1_gdn(w1, s1), pg_gdn(G, sgr), pt_gdn(groups, KT, sg, skt), l0, l1,
      span_gdn(KT, skt), {==}),
    mc_ge(groups, KT, G, nsm, w0, w1, 18n, 88n, 49n, 6n, 7n, p0_gdn(w0, s0), p1_gdn(w1, s1), pg_gdn(G, sgr), pt_gdn(groups, KT, sg, skt),
      pk_gdn(KT, skt), grp_gdn(groups, sg), hlo_gdn(groups, G, nsm, w0, w1, sg, sgr, sn, s0, s1), hm_gdn(KT, G, nsm, w0, w1, skt, sgr, sn, s0, s1), hhi_gdn(groups, G, nsm, w0, w1, sg, sgr, sn, s0, s1), {==}))
  (valid_suff(Nat.mul(groups, KT), G, nsm, w0, w1, 54n, h1_gdn(w0, s0), h2_gdn(w1, s1), h3_gdn(nsm, sn), h4_gdn(G, nsm, sgr, sn), h5_gdn(G, nsm, sgr, sn), {==}, l0, l1),
    (mc, fits_of_cap(groups, KT, G, nsm, w0, w1, 7n, k, cap, hge_gdn(groups, KT, G, sg, skt, sgr), mc, hq_gdn(groups, k, sg, sk), hsf_gdn(k, sk), s_cap)))

def Laws.served_attn(groups, KT, G, nsm, w0, w1, k, cap, s_groups, s_kt, s_grid, s_nsm, s_w0, s_w1, s_k, s_cap):
  +sg = s_groups
  +skt = s_kt
  +sgr = s_grid
  +sn = s_nsm
  +s0 = s_w0
  +s1 = s_w1
  +sk = s_k
  +l1 = l1_attn(groups, KT, G, nsm, w0, w1, sg, skt, sgr, sn, s0, s1)
  +l0 = PP.ar_le_trans(Nat.mul(46n, Impl.wpre(G, nsm, w0, w1)), Nat.mul(Nat.mul(groups, KT), w1),
    Nat.mul(Nat.mul(groups, KT), w0), l1, w_le_mul_l(w1, w0, Nat.mul(groups, KT), w10_attn(w0, w1, s0, s1)))
  +mc = PP.ar_le_antisym(Impl.max_contrib(groups, KT, G, nsm, w0, w1), 8n,
    mc_le(groups, KT, G, nsm, w0, w1, 46n, 6n, 8n, p0_attn(w0, s0), p1_attn(w1, s1), pg_attn(G, sgr), pt_attn(groups, KT, sg, skt), l0, l1,
      span_attn(KT, skt), {==}),
    mc_ge(groups, KT, G, nsm, w0, w1, 21n, 120n, 49n, 7n, 8n, p0_attn(w0, s0), p1_attn(w1, s1), pg_attn(G, sgr), pt_attn(groups, KT, sg, skt),
      pk_attn(KT, skt), grp_attn(groups, sg), hlo_attn(groups, G, nsm, w0, w1, sg, sgr, sn, s0, s1), hm_attn(KT, G, nsm, w0, w1, skt, sgr, sn, s0, s1), hhi_attn(groups, G, nsm, w0, w1, sg, sgr, sn, s0, s1), {==}))
  (valid_suff(Nat.mul(groups, KT), G, nsm, w0, w1, 46n, h1_attn(w0, s0), h2_attn(w1, s1), h3_attn(nsm, sn), h4_attn(G, nsm, sgr, sn), h5_attn(G, nsm, sgr, sn), {==}, l0, l1),
    (mc, fits_of_cap(groups, KT, G, nsm, w0, w1, 8n, k, cap, hge_attn(groups, KT, G, sg, skt, sgr), mc, hq_attn(groups, k, sg, sk), hsf_attn(k, sk), s_cap)))

