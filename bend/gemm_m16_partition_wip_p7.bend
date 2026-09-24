# WIP proofs: laws warp_columns, warp_columns_injective, warp_columns_cover, lane_rows,
# lane_rows_cover.
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p7_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- generic mixed-radix helpers ----

def p7_fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def p7_snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

# (q * b + r) / b == q for r < b.
def p7_div_q(+q: Nat, +r: Nat, +b: Nat, small: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}:
  p7_fst({Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat},
    {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}, Arith.ar_div_unique(q, r, b, small))

# (q * b + r) % b == r for r < b.
def p7_mod_r(+q: Nat, +r: Nat, +b: Nat, small: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}:
  p7_snd({Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat},
    {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}, Arith.ar_div_unique(q, r, b, small))

# a / b * b + a % b == a (b > 0).
def p7_dm_eq(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat}:
  p7_fst({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, Arith.ar_divmod(a, b, pos))

# a % b < b (b > 0).
def p7_dm_lt(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}:
  p7_snd({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, Arith.ar_divmod(a, b, pos))

# x < m gives x * n + n <= m * n.
def p7_mr_le(+x: Nat, +m: Nat, +n: Nat, xm: {Nat.is_lt(x, m) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(x, n), n), Nat.mul(m, n)) == True{} : Bool}:
  %Arith.ar_add_comm(n, Nat.mul(x, n)) : {Nat.is_le(_, Nat.mul(m, n)) == True{} : Bool}
  Arith.ar_le_mul_mono(1n+x, m, n, Equal.trans(Bool, Nat.is_le(1n+x, m), Nat.is_lt(x, m), True{},
    Equal.sym(Bool, Nat.is_lt(x, m), Nat.is_le(1n+x, m), Arith.ar_lt_succ_le(x, m)), xm))

# x < m and y < n give x * n + y < m * n.
def p7_mr_lt(+x: Nat, +y: Nat, +m: Nat, +n: Nat, xm: {Nat.is_lt(x, m) == True{} : Bool},
    yn: {Nat.is_lt(y, n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(x, n), y), Nat.mul(m, n)) == True{} : Bool}:
  Arith.ar_lt_le_trans(Nat.add(Nat.mul(x, n), y), Nat.add(Nat.mul(x, n), n), Nat.mul(m, n),
    Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(x, n), y), Nat.add(Nat.mul(x, n), n)),
      Nat.is_lt(y, n), True{}, Arith.ar_lt_add_cancel(Nat.mul(x, n), y, n), yn),
    p7_mr_le(x, m, n, xm))

# With Q = x / (k n), R = x % (k n): (Q k + R / n) n + R % n == x.
def p7_mod_nest_eq(+x: Nat, +k: Nat, +n: Nat, npos: {Nat.is_lt(0n, n) == True{} : Bool},
    kpos: {Nat.is_lt(0n, Nat.mul(k, n)) == True{} : Bool})
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), Nat.div(Nat.mod(x, Nat.mul(k, n)), n)), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n)) == x : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), Nat.div(Nat.mod(x, Nat.mul(k, n)), n)), n), Nat.add(Nat.mul(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), n), Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n)), Arith.ar_mul_add_l(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n)) : {Nat.add(_, Nat.mod(Nat.mod(x, Nat.mul(k, n)), n)) == x : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), n), Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n)), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n)), Nat.add(Nat.mul(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), n), Nat.add(Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n))), Arith.ar_add_assoc(Nat.mul(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), n), Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n))) : {_ == x : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), n), Nat.mul(Nat.div(x, Nat.mul(k, n)), Nat.mul(k, n)), Arith.ar_mul_assoc(Nat.div(x, Nat.mul(k, n)), k, n)) : {Nat.add(_, Nat.add(Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n))) == x : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n)), Nat.mod(x, Nat.mul(k, n)), p7_dm_eq(Nat.mod(x, Nat.mul(k, n)), n, npos)) : {Nat.add(Nat.mul(Nat.div(x, Nat.mul(k, n)), Nat.mul(k, n)), _) == x : Nat}
  p7_dm_eq(x, Nat.mul(k, n), kpos)

# (x % (k n)) % n == x % n (n > 0, k n > 0).
def p7_mod_nest(+x: Nat, +k: Nat, +n: Nat, npos: {Nat.is_lt(0n, n) == True{} : Bool},
    kpos: {Nat.is_lt(0n, Nat.mul(k, n)) == True{} : Bool})
  -> {Nat.mod(Nat.mod(x, Nat.mul(k, n)), n) == Nat.mod(x, n) : Nat}:
  +np = npos
  %p7_mod_nest_eq(x, k, n, np, kpos) : {Nat.mod(Nat.mod(x, Nat.mul(k, n)), n) == Nat.mod(_, n) : Nat}
  Equal.sym(Nat,
    Nat.mod(Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), Nat.div(Nat.mod(x, Nat.mul(k, n)), n)), n), Nat.mod(Nat.mod(x, Nat.mul(k, n)), n)), n),
    Nat.mod(Nat.mod(x, Nat.mul(k, n)), n),
    p7_mod_r(Nat.add(Nat.mul(Nat.div(x, Nat.mul(k, n)), k), Nat.div(Nat.mod(x, Nat.mul(k, n)), n)),
      Nat.mod(Nat.mod(x, Nat.mul(k, n)), n), n, p7_dm_lt(Nat.mod(x, Nat.mul(k, n)), n, np)))

# Next digit: (x % (k n)) / n * n + x % n == x % (k n).
def p7_digit(+x: Nat, +k: Nat, +n: Nat, npos: {Nat.is_lt(0n, n) == True{} : Bool},
    kpos: {Nat.is_lt(0n, Nat.mul(k, n)) == True{} : Bool})
  -> {Nat.add(Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), Nat.mod(x, n)) == Nat.mod(x, Nat.mul(k, n)) : Nat}:
  +np = npos
  %p7_mod_nest(x, k, n, np, kpos) : {Nat.add(Nat.mul(Nat.div(Nat.mod(x, Nat.mul(k, n)), n), n), _) == Nat.mod(x, Nat.mul(k, n)) : Nat}
  p7_dm_eq(Nat.mod(x, Nat.mul(k, n)), n, np)

# ---- warp columns ----

# col = (w 64 + t 16) + (h 8 + q).
def p7_col_a(+w: Nat, +t: Nat, +h: Nat, +q: Nat)
  -> {Nat.add(Nat.add(Nat.mul(w, 64n), Nat.mul(t, 16n)), Nat.add(Nat.mul(h, 8n), q)) == Impl.col(w, t, h, q) : Nat}:
  Equal.sym(Nat, Impl.col(w, t, h, q), Nat.add(Nat.add(Nat.mul(w, 64n), Nat.mul(t, 16n)), Nat.add(Nat.mul(h, 8n), q)),
    Arith.ar_add_assoc(Nat.add(Nat.mul(w, 64n), Nat.mul(t, 16n)), Nat.mul(h, 8n), q))

# col = w 64 + (t 16 + (h 8 + q)).
def p7_col64(+w: Nat, +t: Nat, +h: Nat, +q: Nat)
  -> {Nat.add(Nat.mul(w, 64n), Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q))) == Impl.col(w, t, h, q) : Nat}:
  %Arith.ar_add_assoc(Nat.mul(w, 64n), Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)) : {_ == Impl.col(w, t, h, q) : Nat}
  p7_col_a(w, t, h, q)

# w 64 + t 16 = wtile(w, t) 16.
def p7_wt16(+w: Nat, +t: Nat)
  -> {Nat.add(Nat.mul(w, 64n), Nat.mul(t, 16n)) == Nat.mul(Impl.wtile(w, t), 16n) : Nat}:
  %Arith.ar_mul_assoc(w, 4n, 16n) : {Nat.add(_, Nat.mul(t, 16n)) == Nat.mul(Impl.wtile(w, t), 16n) : Nat}
  Equal.sym(Nat, Nat.mul(Impl.wtile(w, t), 16n), Nat.add(Nat.mul(Nat.mul(w, 4n), 16n), Nat.mul(t, 16n)),
    Arith.ar_mul_add_l(Nat.mul(w, 4n), t, 16n))

# col = wtile(w, t) 16 + (h 8 + q).
def p7_col16(+w: Nat, +t: Nat, +h: Nat, +q: Nat)
  -> {Nat.add(Nat.mul(Impl.wtile(w, t), 16n), Nat.add(Nat.mul(h, 8n), q)) == Impl.col(w, t, h, q) : Nat}:
  %p7_wt16(w, t) : {Nat.add(_, Nat.add(Nat.mul(h, 8n), q)) == Impl.col(w, t, h, q) : Nat}
  p7_col_a(w, t, h, q)

def p7_hq16(+h: Nat, +q: Nat, h2: {Nat.is_lt(h, 2n) == True{} : Bool},
    q8: {Nat.is_lt(q, 8n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(h, 8n), q), 16n) == True{} : Bool}:
  p7_mr_lt(h, q, 2n, 8n, h2, q8)

def p7_tail64(+t: Nat, +h: Nat, +q: Nat, t4: {Nat.is_lt(t, 4n) == True{} : Bool},
    h2: {Nat.is_lt(h, 2n) == True{} : Bool}, q8: {Nat.is_lt(q, 8n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)), 64n) == True{} : Bool}:
  p7_mr_lt(t, Nat.add(Nat.mul(h, 8n), q), 4n, 16n, t4, p7_hq16(h, q, h2, q8))

def p7_col_lt(+w: Nat, +t: Nat, +h: Nat, +q: Nat, w8: {Nat.is_lt(w, 8n) == True{} : Bool},
    tl: {Nat.is_lt(Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)), 64n) == True{} : Bool})
  -> {Nat.is_lt(Impl.col(w, t, h, q), 512n) == True{} : Bool}:
  %p7_col64(w, t, h, q) : {Nat.is_lt(_, 512n) == True{} : Bool}
  p7_mr_lt(w, Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)), 8n, 64n, w8, tl)

def p7_col_div64(+w: Nat, +t: Nat, +h: Nat, +q: Nat,
    tl: {Nat.is_lt(Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)), 64n) == True{} : Bool})
  -> {Nat.div(Impl.col(w, t, h, q), 64n) == w : Nat}:
  %p7_col64(w, t, h, q) : {Nat.div(_, 64n) == w : Nat}
  p7_div_q(w, Nat.add(Nat.mul(t, 16n), Nat.add(Nat.mul(h, 8n), q)), 64n, tl)

def p7_col_div16(+w: Nat, +t: Nat, +h: Nat, +q: Nat,
    hq: {Nat.is_lt(Nat.add(Nat.mul(h, 8n), q), 16n) == True{} : Bool})
  -> {Nat.div(Impl.col(w, t, h, q), 16n) == Impl.wtile(w, t) : Nat}:
  %p7_col16(w, t, h, q) : {Nat.div(_, 16n) == Impl.wtile(w, t) : Nat}
  p7_div_q(Impl.wtile(w, t), Nat.add(Nat.mul(h, 8n), q), 16n, hq)

def Laws.warp_columns(w, t, h, q, w8, t4, h2, q8):
  +tf = t4
  +hf = h2
  +qf = q8
  (p7_col_lt(w, t, h, q, w8, p7_tail64(t, h, q, tf, hf, qf)),
    p7_col_div64(w, t, h, q, p7_tail64(t, h, q, tf, hf, qf)),
    p7_col_div16(w, t, h, q, p7_hq16(h, q, hf, qf)))

def p7_join4(-A: Type, -B: Type, -C: Type, -D: Type, p: A & B, r: C & D) -> A & B & C & D:
  match p r:
    case (a, b) (c, d):
      (a, b, c, d)

def p7_col_same(+w: Nat, +t: Nat, +h: Nat, +q: Nat, +w2: Nat, +t2: Nat, +h2: Nat, +q2: Nat,
    same: {Impl.col(w, t, h, q) == Impl.col(w2, t2, h2, q2) : Nat})
  -> {Nat.add(Nat.mul(Impl.wtile(w, t), 16n), Nat.add(Nat.mul(h, 8n), q)) == Nat.add(Nat.mul(Impl.wtile(w2, t2), 16n), Nat.add(Nat.mul(h2, 8n), q2)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mul(Impl.wtile(w, t), 16n), Nat.add(Nat.mul(h, 8n), q)), Impl.col(w, t, h, q), p7_col16(w, t, h, q)) : {_ == Nat.add(Nat.mul(Impl.wtile(w2, t2), 16n), Nat.add(Nat.mul(h2, 8n), q2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Impl.wtile(w2, t2), 16n), Nat.add(Nat.mul(h2, 8n), q2)), Impl.col(w2, t2, h2, q2), p7_col16(w2, t2, h2, q2)) : {Impl.col(w, t, h, q) == _ : Nat}
  same

def p7_col_inj_fin(+w: Nat, +t: Nat, +h: Nat, +q: Nat, +w2: Nat, +t2: Nat, +h2: Nat, +q2: Nat,
    tw: {Nat.is_lt(t, 4n) == True{} : Bool}, qw: {Nat.is_lt(q, 8n) == True{} : Bool},
    tw2: {Nat.is_lt(t2, 4n) == True{} : Bool}, qw2: {Nat.is_lt(q2, 8n) == True{} : Bool},
    both: {Impl.wtile(w, t) == Impl.wtile(w2, t2) : Nat} & {Nat.add(Nat.mul(h, 8n), q) == Nat.add(Nat.mul(h2, 8n), q2) : Nat})
  -> {w == w2 : Nat} & {t == t2 : Nat} & {h == h2 : Nat} & {q == q2 : Nat}:
  match both:
    case (e1, e2):
      p7_join4({w == w2 : Nat}, {t == t2 : Nat}, {h == h2 : Nat}, {q == q2 : Nat},
        Arith.ar_divmod_inj(w, t, w2, t2, 4n, tw, tw2, e1),
        Arith.ar_divmod_inj(h, q, h2, q2, 8n, qw, qw2, e2))

def Laws.warp_columns_injective(w, t, h, q, w2, t2, h2, q2, tw, hw, qw, tw2, hw2, qw2, same):
  +qa = qw
  +qb = qw2
  p7_col_inj_fin(w, t, h, q, w2, t2, h2, q2, tw, qa, tw2, qb,
    Arith.ar_divmod_inj(Impl.wtile(w, t), Nat.add(Nat.mul(h, 8n), q), Impl.wtile(w2, t2), Nat.add(Nat.mul(h2, 8n), q2), 16n,
      p7_hq16(h, q, hw, qa), p7_hq16(h2, q2, hw2, qb),
      p7_col_same(w, t, h, q, w2, t2, h2, q2, same)))
