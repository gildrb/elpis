# WIP division lemmas for the m16 partition proofs (merged into
# gemm_m16_partition_proof.bend; imports and `Arith.` prefixes stripped). Statements are a
# FIXED CONTRACT (stubbed in wip_arith's STUB block): never change a statement. Every
# statement below is proven. Prefix new helper defs with ard_.
import Base
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- helpers ----

# Transport truth forwards / backwards along a Bool equation.
def ard_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def ard_tr(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {b == True{} : Bool})
  -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)

# Projections of a proof pair.
def ard_fst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def ard_snd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

# m < m is absurd.
def ard_lt_self(+m: Nat, h: {Nat.is_lt(m, m) == True{} : Bool}) -> Empty:
  Arith.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(m, m), True{},
    Equal.sym(Bool, Nat.is_lt(m, m), False{}, Arith.ar_lt_irrefl(m)), h))

# r < b forces 0 < b.
def ard_pos(r: Nat, +b: Nat, small: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.is_lt(0n, b) == True{} : Bool}:
  match r:
    case 0n:
      small
    case 1n+p:
      Arith.ar_lt_trans(0n, 1n+p, b, {==}, small)

# r + m == bp gives r <= bp.
def ard_le_of_add(+r: Nat, +m: Nat, -bp: Nat, inv: {Nat.add(r, m) == bp : Nat})
  -> {Nat.is_le(r, bp) == True{} : Bool}:
  %inv : {Nat.is_le(r, _) == True{} : Bool}
  Arith.ar_le_add_r(r, m)

# 1 + ((y + x) + n) == x + (z + (1 + n)) when z == y.
def ard_shuffle(+x: Nat, -y: Nat, +z: Nat, +n: Nat, e: {z == y : Nat})
  -> {1n+Nat.add(Nat.add(y, x), n) == Nat.add(x, Nat.add(z, 1n+n)) : Nat}:
  %e : {1n+Nat.add(Nat.add(_, x), n) == Nat.add(x, Nat.add(z, 1n+n)) : Nat}
  %Equal.sym(Nat, Nat.add(z, 1n+n), 1n+Nat.add(z, n), Arith.ar_add_succ_r(z, n)) : {1n+Nat.add(Nat.add(z, x), n) == Nat.add(x, _) : Nat}
  %Equal.sym(Nat, Nat.add(x, 1n+Nat.add(z, n)), 1n+Nat.add(x, Nat.add(z, n)), Arith.ar_add_succ_r(x, Nat.add(z, n))) : {1n+Nat.add(Nat.add(z, x), n) == _ : Nat}
  %Arith.ar_add_comm(x, z) : {1n+Nat.add(_, n) == 1n+Nat.add(x, Nat.add(z, n)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x, z), n), Nat.add(x, Nat.add(z, n)), Arith.ar_add_assoc(x, z, n)) : {1n+_ == 1n+Nat.add(x, Nat.add(z, n)) : Nat}
  {==}

# Invariant of Nat.divmod.go with divisor b = 1 + bp: when r + m == bp,
# q * b + r2 == d * b + (r + n).
def ard_go_eq(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, inv: {Nat.add(r, m) == bp : Nat})
  -> {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+bp), Nat.mod.fin(Nat.divmod.go(n, m, d, r))) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(r, n)) : Nat}:
  match n:
    case 0n:
      %Arith.ar_add_zero_r(r) : {Nat.add(Nat.mul(d, 1n+bp), _) == Nat.add(Nat.mul(d, 1n+bp), Nat.add(r, 0n)) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          +inv2 = Equal.trans(Nat, r, Nat.add(r, 0n), bp,
            Equal.sym(Nat, Nat.add(r, 0n), r, Arith.ar_add_zero_r(r)), inv)
          %ard_shuffle(Nat.mul(d, 1n+bp), bp, r, np, inv2) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Nat.mod.fin(Nat.divmod.go(np, r, 1n+d, 0n))) == _ : Nat}
          ard_go_eq(np, r, 1n+d, 0n, bp, inv2)
        case 1n+mp:
          %Equal.sym(Nat, Nat.add(r, 1n+np), 1n+Nat.add(r, np), Arith.ar_add_succ_r(r, np)) : {Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Nat.mod.fin(Nat.divmod.go(np, mp, d, 1n+r))) == Nat.add(Nat.mul(d, 1n+bp), _) : Nat}
          ard_go_eq(np, mp, d, 1n+r, bp,
            Equal.trans(Nat, 1n+Nat.add(r, mp), Nat.add(r, 1n+mp), bp,
              Equal.sym(Nat, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), Arith.ar_add_succ_r(r, mp)), inv))

# The remainder of Nat.divmod.go stays below b = 1 + bp.
def ard_go_lt(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, inv: {Nat.add(r, m) == bp : Nat})
  -> {Nat.is_lt(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), 1n+bp) == True{} : Bool}:
  match n:
    case 0n:
      Equal.trans(Bool, Nat.is_lt(r, 1n+bp), Nat.is_le(r, bp), True{},
        Arith.ar_lt_succ_le(r, 1n+bp), ard_le_of_add(r, m, bp, inv))
    case 1n+np:
      match m:
        case 0n:
          ard_go_lt(np, r, 1n+d, 0n, bp, Equal.trans(Nat, r, Nat.add(r, 0n), bp,
            Equal.sym(Nat, Nat.add(r, 0n), r, Arith.ar_add_zero_r(r)), inv))
        case 1n+mp:
          ard_go_lt(np, mp, d, 1n+r, bp,
            Equal.trans(Nat, 1n+Nat.add(r, mp), Nat.add(r, 1n+mp), bp,
              Equal.sym(Nat, Nat.add(r, 1n+mp), 1n+Nat.add(r, mp), Arith.ar_add_succ_r(r, mp)), inv))

def ard_le_big(+r: Nat, +m: Nat, +x: Nat, +y: Nat, eq: {r == Nat.add(Nat.add(m, x), y) : Nat})
  -> {Nat.is_le(m, r) == True{} : Bool}:
  %Equal.sym(Nat, r, Nat.add(Nat.add(m, x), y), eq) : {Nat.is_le(m, _) == True{} : Bool}
  Arith.ar_le_trans(m, Nat.add(m, x), Nat.add(Nat.add(m, x), y),
    Arith.ar_le_add_r(m, x), Arith.ar_le_add_r(Nat.add(m, x), y))

# r == (m + x) + y with r < m is absurd.
def ard_big(+r: Nat, +m: Nat, +x: Nat, +y: Nat, small: {Nat.is_lt(r, m) == True{} : Bool},
    eq: {r == Nat.add(Nat.add(m, x), y) : Nat}) -> Empty:
  ard_lt_self(m, Arith.ar_le_lt_trans(m, r, m, ard_le_big(r, m, x, y, eq), small))

# (m + x) + r1 == (m + y) + r2 gives x + r1 == y + r2.
def ard_cancel(+m: Nat, +x: Nat, +r1: Nat, +y: Nat, +r2: Nat,
    same: {Nat.add(Nat.add(m, x), r1) == Nat.add(Nat.add(m, y), r2) : Nat})
  -> {Nat.add(x, r1) == Nat.add(y, r2) : Nat}:
  %Arith.ar_add_sub(m, Nat.add(x, r1)) : {_ == Nat.add(y, r2) : Nat}
  %Arith.ar_add_sub(m, Nat.add(y, r2)) : {Nat.sub(Nat.add(m, Nat.add(x, r1)), m) == _ : Nat}
  %Arith.ar_add_assoc(m, x, r1) : {Nat.sub(_, m) == Nat.sub(Nat.add(m, Nat.add(y, r2)), m) : Nat}
  %Arith.ar_add_assoc(m, y, r2) : {Nat.sub(Nat.add(Nat.add(m, x), r1), m) == Nat.sub(_, m) : Nat}
  Equal.cong(Nat, Nat, t => Nat.sub(t, m), Nat.add(Nat.add(m, x), r1), Nat.add(Nat.add(m, y), r2), same)

# (b + x) + r == (x + r) + b.
def ard_swap(+x: Nat, +r: Nat, +b: Nat)
  -> {Nat.add(Nat.add(b, x), r) == Nat.add(Nat.add(x, r), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(b, x), r), Nat.add(b, Nat.add(x, r)), Nat.add(Nat.add(x, r), b),
    Arith.ar_add_assoc(b, x, r), Arith.ar_add_comm(b, Nat.add(x, r)))

law ar_divmod:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat} &
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

def ar_divmod(a, b, pos):
  match b:
    case 0n:
      Empty.absurd({Nat.add(Nat.mul(Nat.div(a, 0n), 0n), Nat.mod(a, 0n)) == a : Nat} &
        {Nat.is_lt(Nat.mod(a, 0n), 0n) == True{} : Bool}, Arith.ar_false_true(pos))
    case 1n+bp:
      (ard_go_eq(a, bp, 0n, 0n, bp, {==}), ard_go_lt(a, bp, 0n, 0n, bp, {==}))

# Lift a (q, r) equality pair through a successor on q.
def ard_succ_pair(-p1: Nat, -p2: Nat, -r1: Nat, -r2: Nat, h: {p1 == p2 : Nat} & {r1 == r2 : Nat})
  -> {1n+p1 == 1n+p2 : Nat} & {r1 == r2 : Nat}:
  (x, y) = h
  (Equal.cong(Nat, Nat, t => 1n+t, p1, p2, x), y)

# q1 * m + r1 == q2 * m + r2 with r1, r2 < m forces q1 == q2 and r1 == r2.
law ar_divmod_inj:
  for +q1: Nat
  for +r1: Nat
  for +q2: Nat
  for +r2: Nat
  for +m: Nat
  for small1: {Nat.is_lt(r1, m) == True{} : Bool}
  for small2: {Nat.is_lt(r2, m) == True{} : Bool}
  for same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat}
  {q1 == q2 : Nat} & {r1 == r2 : Nat}

def ar_divmod_inj(q1, r1, q2, r2, m, small1, small2, same):
  match q1 q2:
    case 0n 0n:
      ({==}, same)
    case 0n 1n+p2:
      Empty.absurd({0n == 1n+p2 : Nat} & {r1 == r2 : Nat},
        ard_big(r1, m, Nat.mul(p2, m), r2, small1, same))
    case 1n+p1 0n:
      Empty.absurd({1n+p1 == 0n : Nat} & {r1 == r2 : Nat},
        ard_big(r2, m, Nat.mul(p1, m), r1, small2,
          Equal.sym(Nat, Nat.add(Nat.add(m, Nat.mul(p1, m)), r1), r2, same)))
    case 1n+p1 1n+p2:
      ard_succ_pair(p1, p2, r1, r2, ar_divmod_inj(p1, r1, p2, r2, m, small1, small2,
        ard_cancel(m, Nat.mul(p1, m), r1, Nat.mul(p2, m), r2, same)))

# Components of ar_divmod.
def ard_dm_eq(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat}:
  ard_fst({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, ar_divmod(a, b, pos))

def ard_dm_lt(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}:
  ard_snd({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, ar_divmod(a, b, pos))

# (a / b) * b <= a.
def ard_le_mul_div(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.div(a, b), b), a) == True{} : Bool}:
  %ard_dm_eq(a, b, pos) : {Nat.is_le(Nat.mul(Nat.div(a, b), b), _) == True{} : Bool}
  Arith.ar_le_add_r(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b))

# a < (a / b + 1) * b.
def ard_lt_next(+a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(a, Nat.mul(1n+Nat.div(a, b), b)) == True{} : Bool}:
  %Arith.ar_add_comm(Nat.mul(Nat.div(a, b), b), b) : {Nat.is_lt(a, _) == True{} : Bool}
  %ard_dm_eq(a, b, pos) : {Nat.is_lt(_, Nat.add(Nat.mul(Nat.div(a, b), b), b)) == True{} : Bool}
  ard_tr(Nat.is_lt(Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)), Nat.add(Nat.mul(Nat.div(a, b), b), b)),
    Nat.is_lt(Nat.mod(a, b), b),
    Arith.ar_lt_add_cancel(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b), b), ard_dm_lt(a, b, pos))

def ard_div_le_fwd(+q: Nat, +a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_le(Nat.mul(q, b), a) == True{} : Bool})
  -> {Nat.is_le(q, Nat.div(a, b)) == True{} : Bool}:
  ard_rt(Nat.is_lt(q, 1n+Nat.div(a, b)), Nat.is_le(q, Nat.div(a, b)),
    Arith.ar_lt_succ_le(q, 1n+Nat.div(a, b)),
    ard_rt(Nat.is_lt(Nat.mul(q, b), Nat.mul(1n+Nat.div(a, b), b)), Nat.is_lt(q, 1n+Nat.div(a, b)),
      Arith.ar_mul_lt_cancel(q, 1n+Nat.div(a, b), b, pos),
      Arith.ar_le_lt_trans(Nat.mul(q, b), a, Nat.mul(1n+Nat.div(a, b), b), h,
        ard_lt_next(a, b, pos))))

def ard_div_le_bwd(+q: Nat, +a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_le(q, Nat.div(a, b)) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(q, b), a) == True{} : Bool}:
  Arith.ar_le_trans(Nat.mul(q, b), Nat.mul(Nat.div(a, b), b), a,
    Arith.ar_le_mul_mono(q, Nat.div(a, b), b, h), ard_le_mul_div(a, b, pos))

# Galois connection of floor division: q * b <= a iff q <= a / b (b >= 1).
law ar_div_le:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(q, b), a) == Nat.is_le(q, Nat.div(a, b)) : Bool}

def ar_div_le(q, a, b, pos):
  +p = pos
  Arith.ar_bool_ext(Nat.is_le(Nat.mul(q, b), a), Nat.is_le(q, Nat.div(a, b)),
    h => ard_div_le_fwd(q, a, b, p, h), h => ard_div_le_bwd(q, a, b, p, h))

law ar_div_unique:
  for +q: Nat
  for +r: Nat
  for +b: Nat
  for small: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat} &
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}

def ar_div_unique(q, r, b, small):
  +s = small
  +ps = ard_pos(r, b, s)
  ar_divmod_inj(Nat.div(Nat.add(Nat.mul(q, b), r), b), Nat.mod(Nat.add(Nat.mul(q, b), r), b),
    q, r, b, ard_dm_lt(Nat.add(Nat.mul(q, b), r), b, ps), s,
    ard_dm_eq(Nat.add(Nat.mul(q, b), r), b, ps))

# Dual Galois connection of floor division: a / b < q iff a < q * b (b >= 1).
law ar_div_lt:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.div(a, b), q) == Nat.is_lt(a, Nat.mul(q, b)) : Bool}

def ar_div_lt(q, a, b, pos):
  %Equal.sym(Bool, Nat.is_lt(Nat.div(a, b), q), Bool.not(Nat.is_le(q, Nat.div(a, b))), Arith.ar_lt_not_le(Nat.div(a, b), q)) : {_ == Nat.is_lt(a, Nat.mul(q, b)) : Bool}
  %ar_div_le(q, a, b, pos) : {Bool.not(_) == Nat.is_lt(a, Nat.mul(q, b)) : Bool}
  Equal.sym(Bool, Nat.is_lt(a, Nat.mul(q, b)), Bool.not(Nat.is_le(Nat.mul(q, b), a)),
    Arith.ar_lt_not_le(a, Nat.mul(q, b)))

law ar_div_add_self:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.div(Nat.add(a, b), b) == 1n+Nat.div(a, b) : Nat}

def ar_div_add_self(a, b, pos):
  +p = pos
  %ard_dm_eq(a, b, p) : {Nat.div(Nat.add(_, b), b) == 1n+Nat.div(a, b) : Nat}
  %ard_swap(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b), b) : {Nat.div(_, b) == 1n+Nat.div(a, b) : Nat}
  ard_fst({Nat.div(Nat.add(Nat.mul(1n+Nat.div(a, b), b), Nat.mod(a, b)), b) == 1n+Nat.div(a, b) : Nat},
    {Nat.mod(Nat.add(Nat.mul(1n+Nat.div(a, b), b), Nat.mod(a, b)), b) == Nat.mod(a, b) : Nat},
    ar_div_unique(1n+Nat.div(a, b), Nat.mod(a, b), b, ard_dm_lt(a, b, p)))

law ar_div_mono:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  for ac: {Nat.is_le(a, c) == True{} : Bool}
  {Nat.is_le(Nat.div(a, b), Nat.div(c, b)) == True{} : Bool}

def ar_div_mono(a, c, b, pos, ac):
  +p = pos
  ard_rt(Nat.is_le(Nat.mul(Nat.div(a, b), b), c), Nat.is_le(Nat.div(a, b), Nat.div(c, b)),
    ar_div_le(Nat.div(a, b), c, b, p),
    Arith.ar_le_trans(Nat.mul(Nat.div(a, b), b), a, c, ard_le_mul_div(a, b, p), ac))
