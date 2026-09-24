# Proofs of the dense partial-buffer bounds laws (attn_bounds_laws.bend) about the Nat model
# attn_bounds.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign proof
# code or answer tables. Nat arithmetic lemmas come from the proven m16 partition library.
import Base
import ./attn_bounds.bend as Impl
import ./attn_bounds_spec.bend as Spec
import ./attn_bounds_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

# n < n + 1
def ab_lt_succ(+n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ab_lt_succ(p)

# (n >= n + 1) is False
def ab_ge_succ(+n: Nat) -> {Nat.is_ge(n, 1n+n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ab_ge_succ(p)

# (1 + x) - 1 == x
def ab_sub1(+x: Nat) -> {Nat.sub(1n+x, 1n) == x : Nat}:
  Ar.ar_sub_zero_r(x)

# not(split >= S) gives split < S
def ab_runs_lt(+split: Nat, +S: Nat, h: {Bool.not(Nat.is_ge(split, S)) == True{} : Bool})
  -> {Nat.is_lt(split, S) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(split, S), Bool.not(Nat.is_le(S, split)), Ar.ar_lt_not_le(split, S)) : {_ == True{} : Bool}
  %Ar.ar_ge_flip(split, S) : {Bool.not(_) == True{} : Bool}
  h

# x < k and u < n give x * n + u < k * n (row-major block bound)
def ab_blk(+x: Nat, +k: Nat, +u: Nat, +n: Nat,
    xk: {Nat.is_lt(x, k) == True{} : Bool}, un: {Nat.is_lt(u, n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(x, n), u), Nat.mul(k, n)) == True{} : Bool}:
  +xn = Nat.mul(x, n)
  +h1 = Ar.ard_tr(Nat.is_lt(Nat.add(xn, u), Nat.add(xn, n)), Nat.is_lt(u, n),
    Ar.ar_lt_add_cancel(xn, u, n), un)
  +h2 = Ar.ard_rt(Nat.is_lt(Nat.add(xn, u), Nat.add(xn, n)), Nat.is_lt(Nat.add(xn, u), Nat.add(n, xn)),
    Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(xn, u), t), Nat.add(xn, n), Nat.add(n, xn),
      Ar.ar_add_comm(xn, n)), h1)
  +h3 = Ar.ar_le_mul_mono(1n+x, k, n, Ar.ard_rt(Nat.is_lt(x, k), Nat.is_le(1n+x, k), Ar.ar_lt_succ_le(x, k), xk))
  Ar.ar_lt_le_trans(Nat.add(xn, u), Nat.mul(1n+x, n), Nat.mul(k, n), h2, h3)

# pid < B * N gives pid / N < B
def ab_bh_lt(+pid: Nat, +B: Nat, +N: Nat, +pos: {Nat.is_lt(0n, N) == True{} : Bool},
    h: {Nat.is_lt(pid, Nat.mul(B, N)) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(pid, N), B) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.div(pid, N), B), Nat.is_lt(pid, Nat.mul(B, N)), Ar.ar_div_lt(B, pid, N, pos), h)

def Laws.split_store_in_bounds(bsz, kvh, nsub, grid_y, splits, pid, y, sub, nsub_pos, pid_in, sub_in, runs):
  +B = Nat.mul(bsz, kvh)
  +bh = Nat.div(pid, nsub)
  +split = Impl.split_index(pid, y, nsub, grid_y)
  +x = Nat.add(Nat.mul(bh, splits), split)
  +hx = ab_blk(bh, B, split, splits, ab_bh_lt(pid, B, nsub, nsub_pos, pid_in), ab_runs_lt(split, splits, runs))
  ab_blk(x, Nat.mul(B, splits), sub, nsub, hx, sub_in)

def Laws.combine_read_in_bounds(bsz, kvh, nsub, grid_y, splits, pid, s, nsub_pos, pid_in, s_in):
  +np = nsub_pos
  +B = Nat.mul(bsz, kvh)
  +bh = Nat.div(pid, nsub)
  +x = Nat.add(Nat.mul(bh, splits), s)
  +hx = ab_blk(bh, B, s, splits, ab_bh_lt(pid, B, nsub, np, pid_in), s_in)
  ab_blk(x, Nat.mul(B, splits), Nat.mod(pid, nsub), nsub, hx, Ar.ard_dm_lt(pid, nsub, np))

# (a * c) * b == (a * b) * c
def ab_mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, c), b) == Nat.mul(Nat.mul(a, b), c) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), b), Nat.mul(a, Nat.mul(c, b)), Ar.ar_mul_assoc(a, c, b)) : {_ == Nat.mul(Nat.mul(a, b), c) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), Ar.ar_mul_assoc(a, b, c)) : {Nat.mul(a, Nat.mul(c, b)) == _ : Nat}
  %Ar.ar_mul_comm(b, c) : {Nat.mul(a, _) == Nat.mul(a, Nat.mul(b, c)) : Nat}
  {==}

def Laws.plain_store_in_bounds(bsz, kvh, nsub, grid_y, num_splits, pid, split, pid_in, split_in, splits_cap):
  +P = Impl.programs(bsz, kvh, nsub)
  +h1 = ab_blk(pid, P, split, num_splits, pid_in, split_in)
  # P * num_splits <= P * grid_y
  +h2 = Ar.ar_le_mul_mono(num_splits, grid_y, P, splits_cap)
  +h3 = Ar.ard_rt(Nat.is_le(Nat.mul(num_splits, P), Nat.mul(grid_y, P)),
    Nat.is_le(Nat.mul(P, num_splits), Nat.mul(grid_y, P)),
    Equal.cong(Nat, Bool, t => Nat.is_le(t, Nat.mul(grid_y, P)), Nat.mul(num_splits, P),
      Nat.mul(P, num_splits), Ar.ar_mul_comm(num_splits, P)), h2)
  +h4 = Ar.ard_rt(Nat.is_le(Nat.mul(P, num_splits), Nat.mul(grid_y, P)),
    Nat.is_le(Nat.mul(P, num_splits), Nat.mul(P, grid_y)),
    Equal.cong(Nat, Bool, t => Nat.is_le(Nat.mul(P, num_splits), t), Nat.mul(grid_y, P),
      Nat.mul(P, grid_y), Ar.ar_mul_comm(grid_y, P)), h3)
  +h5 = Ar.ar_lt_le_trans(Impl.plain_store_index(pid, split, num_splits), Nat.mul(P, num_splits),
    Nat.mul(P, grid_y), h1, h4)
  # P * grid_y = ((bsz * kvh) * nsub) * grid_y == ((bsz * kvh) * grid_y) * nsub
  %ab_mul_swap(Nat.mul(bsz, kvh), grid_y, nsub) : {Nat.is_lt(Impl.plain_store_index(pid, split, num_splits), _) == True{} : Bool}
  h5

# min(a, b) <= a
def ab_min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      ab_min_le_l(ap, bp)

# a <= c and b <= c give max(a, b) <= c
def ab_max_le(+a: Nat, +b: Nat, +c: Nat, ac: {Nat.is_le(a, c) == True{} : Bool},
    bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      bc
    case 1n+ap 0n _:
      ac
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(Nat.max(1n+ap, 1n+bp), 0n) == True{} : Bool}, Ar.ar_false_true(ac))
    case 1n+ap 1n+bp 1n+cp:
      ab_max_le(ap, bp, cp, ac, bc)

# 1 <= max(1, z)
def ab_max1(+z: Nat) -> {Nat.is_le(1n, Nat.max(1n, z)) == True{} : Bool}:
  match z:
    case 0n:
      {==}
    case 1n+zp:
      Ar.ar_h_le_zero(zp)

def Laws.gqa_splits_in_grid(bsz, kvh, nsub, grid_y, ctas, grid_pos):
  +X = Nat.mul(nsub, grid_y)
  +m = Nat.min(X, Nat.div(ctas, Nat.mul(bsz, kvh)))
  (ab_max1(m),
    ab_max_le(1n, m, X, Ar.ard_rt(Nat.is_lt(0n, X), Nat.is_le(1n, X), Ar.ar_lt_succ_le(0n, X), grid_pos),
      ab_min_le_l(X, Nat.div(ctas, Nat.mul(bsz, kvh)))))

def Laws.pristine_store_out_of_bounds():
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

# a >= 1 and c >= 1 give a * c >= 1
def ab_mul_pos(+a: Nat, +c: Nat, ap: {Nat.is_lt(0n, a) == True{} : Bool}, cp: {Nat.is_lt(0n, c) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(a, c)) == True{} : Bool}:
  match a c:
    case 0n _:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(0n, c)) == True{} : Bool}, Ar.ar_false_true(ap))
    case 1n+a1 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(1n+a1, 0n)) == True{} : Bool}, Ar.ar_false_true(cp))
    case 1n+a1 1n+c1:
      {==}

# S = 1 + s and S <= N * G force G >= 1
def ab_gpos(+n: Nat, +s: Nat, +G: Nat, cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Nat.is_lt(0n, G) == True{} : Bool}:
  match G:
    case 0n:
      +z = Equal.cong(Nat, Bool, t => Nat.is_le(1n+s, t), 0n, Nat.mul(1n+n, 0n),
        Equal.sym(Nat, Nat.mul(1n+n, 0n), 0n, Ar.ar_mul_zero_r(1n+n)))
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_le(1n+s, Nat.mul(1n+n, 0n)), True{}, z, cap)))
    case 1n+gp:
      {==}

# (S - 1) / G < N for S = 1 + s <= N * G
def ab_fq(+n: Nat, +s: Nat, +G: Nat, +cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(s, G), 1n+n) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.div(s, G), 1n+n), Nat.is_lt(s, Nat.mul(1n+n, G)), Ar.ar_div_lt(1n+n, s, G, ab_gpos(n, s, G, cap)),
    Ar.ar_lt_le_trans(s, 1n+s, Nat.mul(1n+n, G), ab_lt_succ(s), cap))

# ((1 + b) * (1 + n) - 1) / (1 + n) == b: the last bh
def ab_bh_max(+b: Nat, +n: Nat)
  -> {Nat.div(Nat.sub(Nat.mul(1n+b, 1n+n), 1n), 1n+n) == b : Nat}:
  +Y = Nat.add(n, Nat.mul(b, 1n+n))
  %Equal.sym(Nat, Nat.sub(Y, 0n), Y, Ar.ar_sub_zero_r(Y)) : {Nat.div(_, 1n+n) == b : Nat}
  %Ar.ar_add_comm(Nat.mul(b, 1n+n), n) : {Nat.div(_, 1n+n) == b : Nat}
  Ar.ard_fst({Nat.div(Nat.add(Nat.mul(b, 1n+n), n), 1n+n) == b : Nat},
    {Nat.mod(Nat.add(Nat.mul(b, 1n+n), n), 1n+n) == n : Nat},
    Ar.ar_div_unique(b, n, 1n+n, ab_lt_succ(n)))

# 1 + (((b * S + s) * N) + n) == ((1 + b) * S) * N with S = 1 + s, N = 1 + n
def ab_core(+b: Nat, +s: Nat, +n: Nat)
  -> {1n+Nat.add(Nat.mul(Nat.add(Nat.mul(b, 1n+s), s), 1n+n), n) == Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n) : Nat}:
  +X = Nat.add(Nat.mul(b, 1n+s), s)
  +XN = Nat.mul(X, 1n+n)
  %Ar.ar_add_succ_r(XN, n) : {_ == Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n) : Nat}
  %Equal.sym(Nat, Nat.add(XN, 1n+n), Nat.add(1n+n, XN), Ar.ar_add_comm(XN, 1n+n)) : {_ == Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n) : Nat}
  Equal.cong(Nat, Nat, t => Nat.mul(1n+t, 1n+n), X, Nat.add(s, Nat.mul(b, 1n+s)), Ar.ar_add_comm(Nat.mul(b, 1n+s), s))

# A3 over B = bsz * kvh, N = NSUB, S = SPLITS, G = GRID_Y.
def ab_A3(+B: Nat, +N: Nat, +S: Nat, +G: Nat) -> Type:
  {Impl.dense_partial_extent(Nat.mul(B, N), G, S, N) == Nat.mul(Nat.mul(B, S), N) : Nat} &
  {Nat.mul(Nat.mul(B, S), N) == Nat.mul(B, Nat.mul(S, N)) : Nat} &
  {Nat.is_lt(Nat.add(Nat.mul(Nat.sub(B, 1n), N), Nat.div(Nat.sub(S, 1n), G)), Nat.mul(B, N)) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(Nat.sub(S, 1n), G), G) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(N, 1n), N) == True{} : Bool} &
  {Impl.split_runs(Nat.add(Nat.mul(Nat.sub(B, 1n), N), Nat.div(Nat.sub(S, 1n), G)), Nat.mod(Nat.sub(S, 1n), G), N, G, S) == True{} : Bool} &
  {1n+Impl.store_index(Nat.add(Nat.mul(Nat.sub(B, 1n), N), Nat.div(Nat.sub(S, 1n), G)), Nat.mod(Nat.sub(S, 1n), G),
    Nat.sub(N, 1n), N, G, S) == Nat.mul(Nat.mul(B, S), N) : Nat}

def ab_c1(+b: Nat, +n: Nat, +s: Nat, +G: Nat, cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Impl.dense_partial_extent(Nat.mul(1n+b, 1n+n), G, 1n+s, 1n+n) == Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n) : Nat}:
  +R = Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n)
  +Z = Nat.mul(Nat.add(Nat.mul(b, 1n+s), s), 1n+n)
  %Equal.sym(Nat, Nat.div(Nat.sub(Nat.mul(1n+b, 1n+n), 1n), 1n+n), b, ab_bh_max(b, n)) :
    {Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(_, 1n+s), Nat.sub(Nat.min(1n+s, Nat.mul(1n+n, G)), 1n)), 1n+n), Nat.sub(1n+n, 1n)), 1n) == R : Nat}
  %Equal.sym(Nat, Nat.min(1n+s, Nat.mul(1n+n, G)), 1n+s, Ar.ar_min_left(1n+s, Nat.mul(1n+n, G), cap)) :
    {Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(b, 1n+s), Nat.sub(_, 1n)), 1n+n), Nat.sub(1n+n, 1n)), 1n) == R : Nat}
  %Equal.sym(Nat, Nat.sub(1n+s, 1n), s, ab_sub1(s)) :
    {Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(b, 1n+s), _), 1n+n), Nat.sub(1n+n, 1n)), 1n) == R : Nat}
  %Equal.sym(Nat, Nat.sub(1n+n, 1n), n, ab_sub1(n)) :
    {Nat.add(Nat.add(Z, _), 1n) == R : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Z, n), 1n), Nat.add(1n, Nat.add(Z, n)), Ar.ar_add_comm(Nat.add(Z, n), 1n)) :
    {_ == R : Nat}
  ab_core(b, s, n)

def ab_c3(+b: Nat, +n: Nat, +s: Nat, +G: Nat, +cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(Nat.sub(1n+b, 1n), 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mul(1n+b, 1n+n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+b, 1n), b, ab_sub1(b)) :
    {Nat.is_lt(Nat.add(Nat.mul(_, 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mul(1n+b, 1n+n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(1n+s, 1n), s, ab_sub1(s)) :
    {Nat.is_lt(Nat.add(Nat.mul(b, 1n+n), Nat.div(_, G)), Nat.mul(1n+b, 1n+n)) == True{} : Bool}
  ab_blk(b, 1n+b, Nat.div(s, G), 1n+n, ab_lt_succ(b), ab_fq(n, s, G, cap))

def ab_c4(+n: Nat, +s: Nat, +G: Nat, cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Nat.is_lt(Nat.mod(Nat.sub(1n+s, 1n), G), G) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+s, 1n), s, ab_sub1(s)) : {Nat.is_lt(Nat.mod(_, G), G) == True{} : Bool}
  Ar.ard_dm_lt(s, G, ab_gpos(n, s, G, cap))

def ab_c5(+n: Nat) -> {Nat.is_lt(Nat.sub(1n+n, 1n), 1n+n) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+n, 1n), n, ab_sub1(n)) : {Nat.is_lt(_, 1n+n) == True{} : Bool}
  ab_lt_succ(n)

def ab_c6(+b: Nat, +n: Nat, +s: Nat, +G: Nat, +cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {Impl.split_runs(Nat.add(Nat.mul(Nat.sub(1n+b, 1n), 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mod(Nat.sub(1n+s, 1n), G), 1n+n, G, 1n+s) == True{} : Bool}:
  +gpos = ab_gpos(n, s, G, cap)
  +q = Nat.div(s, G)
  +yy = Nat.mod(s, G)
  +pid = Nat.add(Nat.mul(b, 1n+n), q)
  du = Ar.ar_div_unique(b, q, 1n+n, ab_fq(n, s, G, cap))
  %Equal.sym(Nat, Nat.sub(1n+b, 1n), b, ab_sub1(b)) :
    {Impl.split_runs(Nat.add(Nat.mul(_, 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mod(Nat.sub(1n+s, 1n), G), 1n+n, G, 1n+s) == True{} : Bool}
  %Equal.sym(Nat, Nat.sub(1n+s, 1n), s, ab_sub1(s)) :
    {Impl.split_runs(Nat.add(Nat.mul(b, 1n+n), Nat.div(_, G)), Nat.mod(_, G), 1n+n, G, 1n+s) == True{} : Bool}
  %Equal.sym(Nat, Nat.mod(pid, 1n+n), q, Ar.ard_snd({Nat.div(pid, 1n+n) == b : Nat}, {Nat.mod(pid, 1n+n) == q : Nat}, du)) :
    {Bool.not(Nat.is_ge(Nat.add(Nat.mul(_, G), yy), 1n+s)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.mul(q, G), yy), s, Ar.ard_dm_eq(s, G, gpos)) :
    {Bool.not(Nat.is_ge(_, 1n+s)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_ge(s, 1n+s), False{}, ab_ge_succ(s)) : {Bool.not(_) == True{} : Bool}
  {==}

def ab_c7(+b: Nat, +n: Nat, +s: Nat, +G: Nat, +cap: {Nat.is_le(1n+s, Nat.mul(1n+n, G)) == True{} : Bool})
  -> {1n+Impl.store_index(Nat.add(Nat.mul(Nat.sub(1n+b, 1n), 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mod(Nat.sub(1n+s, 1n), G),
       Nat.sub(1n+n, 1n), 1n+n, G, 1n+s) == Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n) : Nat}:
  +gpos = ab_gpos(n, s, G, cap)
  +R = Nat.mul(Nat.mul(1n+b, 1n+s), 1n+n)
  +q = Nat.div(s, G)
  +yy = Nat.mod(s, G)
  +pid = Nat.add(Nat.mul(b, 1n+n), q)
  du = Ar.ar_div_unique(b, q, 1n+n, ab_fq(n, s, G, cap))
  du2 = Ar.ar_div_unique(b, q, 1n+n, ab_fq(n, s, G, cap))
  %Equal.sym(Nat, Nat.sub(1n+b, 1n), b, ab_sub1(b)) :
    {1n+Impl.store_index(Nat.add(Nat.mul(_, 1n+n), Nat.div(Nat.sub(1n+s, 1n), G)), Nat.mod(Nat.sub(1n+s, 1n), G),
      Nat.sub(1n+n, 1n), 1n+n, G, 1n+s) == R : Nat}
  %Equal.sym(Nat, Nat.sub(1n+s, 1n), s, ab_sub1(s)) :
    {1n+Impl.store_index(Nat.add(Nat.mul(b, 1n+n), Nat.div(_, G)), Nat.mod(_, G), Nat.sub(1n+n, 1n), 1n+n, G, 1n+s) == R : Nat}
  %Equal.sym(Nat, Nat.sub(1n+n, 1n), n, ab_sub1(n)) :
    {1n+Impl.store_index(pid, yy, _, 1n+n, G, 1n+s) == R : Nat}
  %Equal.sym(Nat, Nat.div(pid, 1n+n), b, Ar.ard_fst({Nat.div(pid, 1n+n) == b : Nat}, {Nat.mod(pid, 1n+n) == q : Nat}, du)) :
    {1n+Nat.add(Nat.mul(Nat.add(Nat.mul(_, 1n+s), Nat.add(Nat.mul(Nat.mod(pid, 1n+n), G), yy)), 1n+n), n) == R : Nat}
  %Equal.sym(Nat, Nat.mod(pid, 1n+n), q, Ar.ard_snd({Nat.div(pid, 1n+n) == b : Nat}, {Nat.mod(pid, 1n+n) == q : Nat}, du2)) :
    {1n+Nat.add(Nat.mul(Nat.add(Nat.mul(b, 1n+s), Nat.add(Nat.mul(_, G), yy)), 1n+n), n) == R : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(q, G), yy), s, Ar.ard_dm_eq(s, G, gpos)) :
    {1n+Nat.add(Nat.mul(Nat.add(Nat.mul(b, 1n+s), _), 1n+n), n) == R : Nat}
  ab_core(b, s, n)

def ab_exact(+B: Nat, +N: Nat, +S: Nat, +G: Nat,
    Bpos: {Nat.is_lt(0n, B) == True{} : Bool}, Npos: {Nat.is_lt(0n, N) == True{} : Bool},
    Spos: {Nat.is_lt(0n, S) == True{} : Bool}, cap: {Nat.is_le(S, Nat.mul(N, G)) == True{} : Bool})
  -> ab_A3(B, N, S, G):
  match B N S:
    case 0n _ _:
      Empty.absurd(ab_A3(0n, N, S, G), Ar.ar_false_true(Bpos))
    case 1n+b 0n _:
      Empty.absurd(ab_A3(1n+b, 0n, S, G), Ar.ar_false_true(Npos))
    case 1n+b 1n+n 0n:
      Empty.absurd(ab_A3(1n+b, 1n+n, 0n, G), Ar.ar_false_true(Spos))
    case 1n+b 1n+n 1n+s:
      +cp = cap
      (ab_c1(b, n, s, G, cp), Ar.ar_mul_assoc(1n+b, 1n+s, 1n+n), ab_c3(b, n, s, G, cp), ab_c4(n, s, G, cp),
        ab_c5(n), ab_c6(b, n, s, G, cp), ab_c7(b, n, s, G, cp))

def Laws.extent_exact(bsz, kvh, nsub, grid_y, splits, bsz_pos, kvh_pos, nsub_pos, splits_pos, splits_cap):
  ab_exact(Nat.mul(bsz, kvh), nsub, splits, grid_y, ab_mul_pos(bsz, kvh, bsz_pos, kvh_pos), nsub_pos, splits_pos, splits_cap)
