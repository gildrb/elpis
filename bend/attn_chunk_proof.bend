# Proofs of the fixed-absolute-chunk verify-attention partition laws (attn_chunk_laws.bend) about the
# Bend model attn_chunk.bend against the reference attn_chunk_spec.bend. Structural evidence only: no
# unsafe definitions, axioms, holes, foreign proof code or answer tables. Nat arithmetic lemmas come
# from the proven m16 partition library; the small ceil-division / counting lemmas follow the
# attn_split_proof.bend ones, restated over this model's definitions.
import Base
import ./attn_chunk.bend as Impl
import ./attn_chunk_spec.bend as Spec
import ./attn_chunk_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def Laws.lanes_once():
  ({==}, {==})

# ---------------------------------------------------------------------------------------------
# Generic helpers

def ac_sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (y + (1 + bp)) - 1 == y + bp
def ac_pred(+y: Nat, +bp: Nat) -> {Nat.sub(Nat.add(y, 1n+bp), 1n) == Nat.add(y, bp) : Nat}:
  %Equal.sym(Nat, Nat.add(y, 1n+bp), 1n+Nat.add(y, bp), Ar.ar_add_succ_r(y, bp)) : {Nat.sub(_, 1n) == Nat.add(y, bp) : Nat}
  ac_sub_zero(Nat.add(y, bp))

# i < ceil(L / b) iff i * b < L (b >= 1)
def ac_live(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(i, Impl.cdiv(L, b)) == Bool.not(Nat.is_le(L, Nat.mul(i, b))) : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(i, Impl.cdiv(L, 0n)) == Bool.not(Nat.is_le(L, Nat.mul(i, 0n))) : Bool}, Ar.ar_false_true(pos))
    case 1n+bp:
      %Equal.sym(Nat, Nat.sub(Nat.add(L, 1n+bp), 1n), Nat.add(L, bp), ac_pred(L, bp)) : {Nat.is_lt(i, Nat.div(_, 1n+bp)) == Bool.not(Nat.is_le(L, Nat.mul(i, 1n+bp))) : Bool}
      +a = Nat.add(L, bp)
      +dv = Nat.div(a, 1n+bp)
      +m = Nat.mul(i, 1n+bp)
      Equal.trans(Bool, Nat.is_lt(i, dv), Nat.is_le(1n+i, dv), Bool.not(Nat.is_le(L, m)),
        Ar.ar_lt_succ_le(i, dv),
      Equal.trans(Bool, Nat.is_le(1n+i, dv), Nat.is_le(1n+Nat.add(bp, m), a), Bool.not(Nat.is_le(L, m)),
        Equal.sym(Bool, Nat.is_le(Nat.mul(1n+i, 1n+bp), a), Nat.is_le(1n+i, dv), Ar.ar_div_le(1n+i, a, 1n+bp, pos)),
      Equal.trans(Bool, Nat.is_le(1n+Nat.add(bp, m), a), Nat.is_lt(Nat.add(bp, m), a), Bool.not(Nat.is_le(L, m)),
        Equal.sym(Bool, Nat.is_lt(Nat.add(bp, m), a), Nat.is_le(1n+Nat.add(bp, m), a), Ar.ar_lt_succ_le(Nat.add(bp, m), a)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(bp, m), a), Nat.is_lt(Nat.add(bp, m), Nat.add(bp, L)), Bool.not(Nat.is_le(L, m)),
        Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(bp, m), t), a, Nat.add(bp, L), Ar.ar_add_comm(L, bp)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(bp, m), Nat.add(bp, L)), Nat.is_lt(m, L), Bool.not(Nat.is_le(L, m)),
        Ar.ar_lt_add_cancel(bp, m, L),
        Ar.ar_lt_not_le(m, L))))))

# i * b < L gives i < ceil(L / b)
def ac_lt_cdiv(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_lt(Nat.mul(i, b), L) == True{} : Bool})
  -> {Nat.is_lt(i, Impl.cdiv(L, b)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(i, Impl.cdiv(L, b)), Bool.not(Nat.is_le(L, Nat.mul(i, b))), ac_live(i, L, b, pos),
    Ar.ard_rt(Nat.is_lt(Nat.mul(i, b), L), Bool.not(Nat.is_le(L, Nat.mul(i, b))), Ar.ar_lt_not_le(Nat.mul(i, b), L), h))

# i <= k && k < i + 1 iff i == k
def ac_le_lt_eq(+i: Nat, +k: Nat)
  -> {Bool.and(Nat.is_le(i, k), Nat.is_lt(k, 1n+i)) == Nat.is_eq(i, k) : Bool}:
  match i k:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      match kp:
        case 0n:
          {==}
        case 1n+kq:
          {==}
    case 1n+ip 0n:
      {==}
    case 1n+ip 1n+kp:
      ac_le_lt_eq(ip, kp)

def ac_and3_false(+x: Bool, +y: Bool) -> {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}:
  match x y:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def ac_and_true_r(+x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# (s && x) == s when s implies x
def ac_keep(+s: Bool, +x: Bool, h: {s == True{} : Bool} -> {x == True{} : Bool})
  -> {Bool.and(s, x) == s : Bool}:
  match s:
    case False{}:
      {==}
    case True{}:
      h({==})

# (x && s) == s when s implies x
def ac_keep_l(+x: Bool, +s: Bool, h: {s == True{} : Bool} -> {x == True{} : Bool})
  -> {Bool.and(x, s) == s : Bool}:
  match x s:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({Bool.and(False{}, True{}) == True{} : Bool}, Ar.ar_false_true(h({==})))
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# ((x && y) && z) == (x && z) when z implies y
def ac_and_drop(+x: Bool, +y: Bool, +z: Bool, h: {z == True{} : Bool} -> {y == True{} : Bool})
  -> {Bool.and(Bool.and(x, y), z) == Bool.and(x, z) : Bool}:
  match x y z:
    case False{} _ _:
      {==}
    case True{} True{} _:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      Empty.absurd({Bool.and(Bool.and(True{}, False{}), True{}) == Bool.and(True{}, True{}) : Bool}, Ar.ar_false_true(h({==})))

# (depth + q_len) - q_len == depth: the kernel's q_abs = L - q_len + gid is depth + gid
def ac_qabs(+depth: Nat, +q_len: Nat) -> {Nat.sub(Nat.add(depth, q_len), q_len) == depth : Nat}:
  %Equal.sym(Nat, Nat.add(depth, q_len), Nat.add(q_len, depth), Ar.ar_add_comm(depth, q_len)) : {Nat.sub(_, q_len) == depth : Nat}
  Ar.ar_add_sub(q_len, depth)

# add(bit(k < j), bit(j == k)) == bit(k < j + 1)
def ac_step(+j: Nat, +k: Nat)
  -> {Nat.add(Impl.bit(Nat.is_lt(k, j)), Impl.bit(Nat.is_eq(j, k))) == Impl.bit(Nat.is_lt(k, 1n+j)) : Nat}:
  match j k:
    case 0n 0n:
      {==}
    case 0n 1n+kp:
      match kp:
        case 0n:
          {==}
        case 1n+kq:
          {==}
    case 1n+jp 0n:
      {==}
    case 1n+jp 1n+kp:
      ac_step(jp, kp)

def ac_step_s(+s: Bool, +j: Nat, +k: Nat)
  -> {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(k, j))), Impl.bit(Bool.and(s, Nat.is_eq(j, k)))) ==
     Impl.bit(Bool.and(s, Nat.is_lt(k, 1n+j))) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      ac_step(j, k)

def ac_zero(+s: Bool, +k: Nat) -> {0n == Impl.bit(Bool.and(s, Nat.is_lt(k, 0n))) : Nat}:
  match s k:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+kp:
      {==}

def ac_bit_once(+s: Bool) -> {Impl.bit(s) == Spec.once(s) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      {==}

# a == b gives (a == b) == True
def ac_eq_of(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Ar.ar_eq_refl(a)

# p < min(e, L) && p <= a is p < e && p <= a when a < L
def ac_min_mask(+p: Nat, +e: Nat, +L: Nat, +a: Nat, +hal: {Nat.is_lt(a, L) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(p, Nat.min(e, L)), Nat.is_le(p, a)) == Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)) : Bool}:
  %Equal.sym(Bool, Nat.is_lt(p, Nat.min(e, L)), Bool.and(Nat.is_lt(p, e), Nat.is_lt(p, L)), Ar.ar_min_lt(p, e, L)) : {Bool.and(_, Nat.is_le(p, a)) == Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)) : Bool}
  ac_and_drop(Nat.is_lt(p, e), Nat.is_lt(p, L), Nat.is_le(p, a), h => Ar.ar_le_lt_trans(p, a, L, h, hal))

# ---------------------------------------------------------------------------------------------
# Tile level

# A position of the tile [m + 64 it, + 64) below e and the row bound a < L lies before the chunk's
# n_end = min(e, L), so the tile index is below ntiles.
def ac_tile_nt(+m: Nat, +e: Nat, +it: Nat, +p: Nat, +L: Nat, +a: Nat,
    +hal: {Nat.is_lt(a, L) == True{} : Bool},
    +h: {Bool.and(Nat.is_le(Nat.add(m, Nat.mul(it, 64n)), p),
      Bool.and(Nat.is_lt(p, Nat.add(Nat.add(m, Nat.mul(it, 64n)), 64n)),
        Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)))) == True{} : Bool})
  -> {Nat.is_lt(it, Impl.cdiv(Nat.sub(Nat.min(e, L), m), 64n)) == True{} : Bool}:
  +n0 = Nat.add(m, Nat.mul(it, 64n))
  +ne = Nat.min(e, L)
  +S = Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a))
  +hn0 = Ar.ar_and_l(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), S), h)
  +h2 = Ar.ar_and_r(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), S), h)
  +h3 = Ar.ar_and_r(Nat.is_lt(p, Nat.add(n0, 64n)), S, h2)
  +hpe = Ar.ar_and_l(Nat.is_lt(p, e), Nat.is_le(p, a), h3)
  +hpa = Ar.ar_and_r(Nat.is_lt(p, e), Nat.is_le(p, a), h3)
  +hpL = Ar.ar_le_lt_trans(p, a, L, hpa, hal)
  +hpne = Ar.ard_tr(Nat.is_lt(p, ne), Bool.and(Nat.is_lt(p, e), Nat.is_lt(p, L)), Ar.ar_min_lt(p, e, L),
    Ar.ar_and_intro(Nat.is_lt(p, e), Nat.is_lt(p, L), hpe, hpL))
  +hn0ne = Ar.ar_le_lt_trans(n0, p, ne, hn0, hpne)
  +hx = Ar.ard_tr(Nat.is_lt(Nat.mul(it, 64n), Nat.sub(ne, m)), Nat.is_lt(n0, ne),
    Ar.ar_lt_sub_iff(ne, m, Nat.mul(it, 64n)), hn0ne)
  ac_lt_cdiv(it, Nat.sub(ne, m), 64n, {==}, hx)

# tile_visits is the absolute tile membership (row_invariant (a))
def ac_tile_visit(+c: Nat, +it: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tile_visits(c, it, p, Nat.add(d, q), k, q, j) == Spec.abs_visit(k, c, it, p, Nat.add(d, j)) : Bool}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +m = Nat.mul(c, k)
  +e = Nat.add(m, k)
  +n0 = Nat.add(m, Nat.mul(it, 64n))
  +ne = Nat.min(e, L)
  +nt = Impl.cdiv(Nat.sub(ne, m), 64n)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  +R = Bool.and(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a))))
  %Equal.sym(Nat, Nat.sub(L, q), d, ac_qabs(d, q)) : {Bool.and(Nat.is_lt(it, nt), Bool.and(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Bool.and(Nat.is_lt(p, ne), Nat.is_le(p, Nat.add(_, j)))))) == R : Bool}
  %Equal.sym(Bool, Bool.and(Nat.is_lt(p, ne), Nat.is_le(p, a)), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)), ac_min_mask(p, e, L, a, hal)) : {Bool.and(Nat.is_lt(it, nt), Bool.and(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), _))) == R : Bool}
  ac_keep_l(Nat.is_lt(it, nt), R, h => ac_tile_nt(m, e, it, p, L, a, hal, h))

def ac_tile(+c: Nat, +it: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tile_hits(c, it, p, Nat.add(d, q), k, q, j) == Spec.once(Spec.abs_visit(k, c, it, p, Nat.add(d, j))) : Nat}:
  +av = Spec.abs_visit(k, c, it, p, Nat.add(d, j))
  %Equal.sym(Bool, Impl.tile_visits(c, it, p, Nat.add(d, q), k, q, j), av, ac_tile_visit(c, it, p, d, q, k, j, row)) : {Impl.bit(_) == Spec.once(av) : Nat}
  ac_bit_once(av)

# ---------------------------------------------------------------------------------------------
# Chunk level

# For m <= p: m + 64 it <= p iff it <= (p - m) / 64
def ac_e1(+m: Nat, +it: Nat, +p: Nat, +hm: {Nat.is_le(m, p) == True{} : Bool})
  -> {Nat.is_le(Nat.add(m, Nat.mul(it, 64n)), p) == Nat.is_le(it, Nat.div(Nat.sub(p, m), 64n)) : Bool}:
  +x = Nat.sub(p, m)
  +M = Nat.mul(it, 64n)
  %Ar.ar_sub_add(p, m, hm) : {Nat.is_le(Nat.add(m, M), _) == Nat.is_le(it, Nat.div(x, 64n)) : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.add(m, M), Nat.add(m, x)), Nat.is_le(M, x), Ar.ar_le_add_cancel(m, M, x)) : {_ == Nat.is_le(it, Nat.div(x, 64n)) : Bool}
  Ar.ar_div_le(it, x, 64n, {==})

# For m <= p: p < m + 64 it + 64 iff (p - m) / 64 < it + 1
def ac_e2(+m: Nat, +it: Nat, +p: Nat, +hm: {Nat.is_le(m, p) == True{} : Bool})
  -> {Nat.is_lt(p, Nat.add(Nat.add(m, Nat.mul(it, 64n)), 64n)) == Nat.is_lt(Nat.div(Nat.sub(p, m), 64n), 1n+it) : Bool}:
  +x = Nat.sub(p, m)
  +M = Nat.mul(it, 64n)
  %Equal.sym(Nat, Nat.add(Nat.add(m, M), 64n), Nat.add(m, Nat.add(M, 64n)), Ar.ar_add_assoc(m, M, 64n)) : {Nat.is_lt(p, _) == Nat.is_lt(Nat.div(x, 64n), 1n+it) : Bool}
  %Equal.sym(Nat, Nat.add(M, 64n), Nat.add(64n, M), Ar.ar_add_comm(M, 64n)) : {Nat.is_lt(p, Nat.add(m, _)) == Nat.is_lt(Nat.div(x, 64n), 1n+it) : Bool}
  Equal.trans(Bool, Nat.is_lt(p, Nat.add(m, Nat.add(64n, M))), Nat.is_lt(x, Nat.add(64n, M)), Nat.is_lt(Nat.div(x, 64n), 1n+it),
    Equal.sym(Bool, Nat.is_lt(x, Nat.add(64n, M)), Nat.is_lt(p, Nat.add(m, Nat.add(64n, M))), Ar.ar_sub_lt_iff(p, m, Nat.add(64n, M), {==})),
    Equal.sym(Bool, Nat.is_lt(Nat.div(x, 64n), 1n+it), Nat.is_lt(x, Nat.mul(1n+it, 64n)), Ar.ar_div_lt(1n+it, x, 64n, {==})))

def ac_visit_fwd(+m: Nat, +it: Nat, +p: Nat, +S: Bool,
    +h: {Bool.and(Nat.is_le(Nat.add(m, Nat.mul(it, 64n)), p),
      Bool.and(Nat.is_lt(p, Nat.add(Nat.add(m, Nat.mul(it, 64n)), 64n)), S)) == True{} : Bool})
  -> {Bool.and(Bool.and(Nat.is_le(m, p), S), Nat.is_eq(it, Nat.div(Nat.sub(p, m), 64n))) == True{} : Bool}:
  +n0 = Nat.add(m, Nat.mul(it, 64n))
  +t = Nat.div(Nat.sub(p, m), 64n)
  +hn0 = Ar.ar_and_l(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), S), h)
  +h2 = Ar.ar_and_r(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), S), h)
  +hlt = Ar.ar_and_l(Nat.is_lt(p, Nat.add(n0, 64n)), S, h2)
  +hS = Ar.ar_and_r(Nat.is_lt(p, Nat.add(n0, 64n)), S, h2)
  +hm = Ar.ar_le_trans(m, n0, p, Ar.ar_le_add_r(m, Nat.mul(it, 64n)), hn0)
  +hle = Ar.ard_rt(Nat.is_le(n0, p), Nat.is_le(it, t), ac_e1(m, it, p, hm), hn0)
  +hlt2 = Ar.ard_rt(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_lt(t, 1n+it), ac_e2(m, it, p, hm), hlt)
  +heq = Ar.ard_rt(Bool.and(Nat.is_le(it, t), Nat.is_lt(t, 1n+it)), Nat.is_eq(it, t), ac_le_lt_eq(it, t),
    Ar.ar_and_intro(Nat.is_le(it, t), Nat.is_lt(t, 1n+it), hle, hlt2))
  Ar.ar_and_intro(Bool.and(Nat.is_le(m, p), S), Nat.is_eq(it, t), Ar.ar_and_intro(Nat.is_le(m, p), S, hm, hS), heq)

def ac_visit_bwd(+m: Nat, +it: Nat, +p: Nat, +S: Bool,
    +h: {Bool.and(Bool.and(Nat.is_le(m, p), S), Nat.is_eq(it, Nat.div(Nat.sub(p, m), 64n))) == True{} : Bool})
  -> {Bool.and(Nat.is_le(Nat.add(m, Nat.mul(it, 64n)), p),
      Bool.and(Nat.is_lt(p, Nat.add(Nat.add(m, Nat.mul(it, 64n)), 64n)), S)) == True{} : Bool}:
  +n0 = Nat.add(m, Nat.mul(it, 64n))
  +t = Nat.div(Nat.sub(p, m), 64n)
  +h1 = Ar.ar_and_l(Bool.and(Nat.is_le(m, p), S), Nat.is_eq(it, t), h)
  +heq = Ar.ar_and_r(Bool.and(Nat.is_le(m, p), S), Nat.is_eq(it, t), h)
  +hm = Ar.ar_and_l(Nat.is_le(m, p), S, h1)
  +hS = Ar.ar_and_r(Nat.is_le(m, p), S, h1)
  +hb = Ar.ard_tr(Bool.and(Nat.is_le(it, t), Nat.is_lt(t, 1n+it)), Nat.is_eq(it, t), ac_le_lt_eq(it, t), heq)
  +hle = Ar.ar_and_l(Nat.is_le(it, t), Nat.is_lt(t, 1n+it), hb)
  +hlt = Ar.ar_and_r(Nat.is_le(it, t), Nat.is_lt(t, 1n+it), hb)
  +hn0 = Ar.ard_tr(Nat.is_le(n0, p), Nat.is_le(it, t), ac_e1(m, it, p, hm), hle)
  +hl = Ar.ard_tr(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_lt(t, 1n+it), ac_e2(m, it, p, hm), hlt)
  Ar.ar_and_intro(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), S), hn0,
    Ar.ar_and_intro(Nat.is_lt(p, Nat.add(n0, 64n)), S, hl, hS))

# Absolute tile it of chunk c holds p iff p is in the chunk (and seen) and it == (p - c chunk) / 64
def ac_visit(+k: Nat, +c: Nat, +it: Nat, +p: Nat, +a: Nat)
  -> {Spec.abs_visit(k, c, it, p, a) ==
     Bool.and(Spec.abs_in_chunk(k, c, p, a), Nat.is_eq(it, Nat.div(Nat.sub(p, Nat.mul(c, k)), 64n))) : Bool}:
  +m = Nat.mul(c, k)
  +S = Bool.and(Nat.is_lt(p, Nat.add(m, k)), Nat.is_le(p, a))
  Ar.ar_bool_ext(Spec.abs_visit(k, c, it, p, a),
    Bool.and(Spec.abs_in_chunk(k, c, p, a), Nat.is_eq(it, Nat.div(Nat.sub(p, m), 64n))),
    h => ac_visit_fwd(m, it, p, S, h), h => ac_visit_bwd(m, it, p, S, h))

# tiles(n) == bit(in_chunk && (p - c chunk) / 64 < n)
def ac_tiles(+n: Nat, +c: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tiles(n, c, p, Nat.add(d, q), k, q, j) ==
     Impl.bit(Bool.and(Spec.abs_in_chunk(k, c, p, Nat.add(d, j)), Nat.is_lt(Nat.div(Nat.sub(p, Nat.mul(c, k)), 64n), n))) : Nat}:
  match n:
    case 0n:
      ac_zero(Spec.abs_in_chunk(k, c, p, Nat.add(d, j)), Nat.div(Nat.sub(p, Nat.mul(c, k)), 64n))
    case 1n+it:
      +L = Nat.add(d, q)
      +a = Nat.add(d, j)
      +s = Spec.abs_in_chunk(k, c, p, a)
      +t = Nat.div(Nat.sub(p, Nat.mul(c, k)), 64n)
      %Equal.sym(Nat, Impl.tiles(it, c, p, L, k, q, j), Impl.bit(Bool.and(s, Nat.is_lt(t, it))), ac_tiles(it, c, p, d, q, k, j, row)) : {Nat.add(_, Impl.tile_hits(c, it, p, L, k, q, j)) == Impl.bit(Bool.and(s, Nat.is_lt(t, 1n+it))) : Nat}
      %Equal.sym(Bool, Impl.tile_visits(c, it, p, L, k, q, j), Spec.abs_visit(k, c, it, p, a), ac_tile_visit(c, it, p, d, q, k, j, row)) : {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(t, it))), Impl.bit(_)) == Impl.bit(Bool.and(s, Nat.is_lt(t, 1n+it))) : Nat}
      %Equal.sym(Bool, Spec.abs_visit(k, c, it, p, a), Bool.and(s, Nat.is_eq(it, t)), ac_visit(k, c, it, p, a)) : {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(t, it))), Impl.bit(_)) == Impl.bit(Bool.and(s, Nat.is_lt(t, 1n+it))) : Nat}
      ac_step_s(s, it, t)

# A seen position of chunk c lies in one of its ntiles tiles
def ac_chunk_nt(+m: Nat, +e: Nat, +L: Nat, +a: Nat, +p: Nat,
    +hal: {Nat.is_lt(a, L) == True{} : Bool},
    +h: {Bool.and(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a))) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(Nat.sub(p, m), 64n), Impl.cdiv(Nat.sub(Nat.min(e, L), m), 64n)) == True{} : Bool}:
  +ne = Nat.min(e, L)
  +x = Nat.sub(p, m)
  +t = Nat.div(x, 64n)
  +hm = Ar.ar_and_l(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)), h)
  +h2 = Ar.ar_and_r(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)), h)
  +hpe = Ar.ar_and_l(Nat.is_lt(p, e), Nat.is_le(p, a), h2)
  +hpa = Ar.ar_and_r(Nat.is_lt(p, e), Nat.is_le(p, a), h2)
  +hpL = Ar.ar_le_lt_trans(p, a, L, hpa, hal)
  +hpne = Ar.ard_tr(Nat.is_lt(p, ne), Bool.and(Nat.is_lt(p, e), Nat.is_lt(p, L)), Ar.ar_min_lt(p, e, L),
    Ar.ar_and_intro(Nat.is_lt(p, e), Nat.is_lt(p, L), hpe, hpL))
  +hmx = Ar.ard_tr(Nat.is_lt(Nat.add(m, x), ne), Nat.is_lt(p, ne),
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, ne), Nat.add(m, x), p, Ar.ar_sub_add(p, m, hm)), hpne)
  +hx = Ar.ard_tr(Nat.is_lt(x, Nat.sub(ne, m)), Nat.is_lt(Nat.add(m, x), ne), Ar.ar_lt_sub_iff(ne, m, x), hmx)
  +htx = Ar.ar_le_lt_trans(Nat.mul(t, 64n), x, Nat.sub(ne, m), Ar.ard_le_mul_div(x, 64n, {==}), hx)
  ac_lt_cdiv(t, Nat.sub(ne, m), 64n, {==}, htx)

# chunk_hits(c) == bit(abs_in_chunk(c)) (row_invariant (b))
def ac_chunk(+c: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.chunk_hits(c, p, Nat.add(d, q), k, q, j) == Impl.bit(Spec.abs_in_chunk(k, c, p, Nat.add(d, j))) : Nat}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +m = Nat.mul(c, k)
  +s = Spec.abs_in_chunk(k, c, p, a)
  +t = Nat.div(Nat.sub(p, m), 64n)
  +nt = Impl.ntiles(c, L, k)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  %Equal.sym(Nat, Impl.tiles(nt, c, p, L, k, q, j), Impl.bit(Bool.and(s, Nat.is_lt(t, nt))), ac_tiles(nt, c, p, d, q, k, j, row)) : {_ == Impl.bit(s) : Nat}
  %Equal.sym(Bool, Bool.and(s, Nat.is_lt(t, nt)), s, ac_keep(s, Nat.is_lt(t, nt), h => ac_chunk_nt(m, Nat.add(m, k), L, a, p, hal, h))) : {Impl.bit(_) == Impl.bit(s) : Nat}
  {==}

def ac_chunk_once(+c: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.chunk_hits(c, p, Nat.add(d, q), k, q, j) == Spec.once(Spec.abs_in_chunk(k, c, p, Nat.add(d, j))) : Nat}:
  +s = Spec.abs_in_chunk(k, c, p, Nat.add(d, j))
  Equal.trans(Nat, Impl.chunk_hits(c, p, Nat.add(d, q), k, q, j), Impl.bit(s), Spec.once(s),
    ac_chunk(c, p, d, q, k, j, row), ac_bit_once(s))

# ---------------------------------------------------------------------------------------------
# attend_once

# Absolute chunk membership, for the conjunct value s, is s && c == p / chunk
def ac_core(+c: Nat, +p: Nat, +k: Nat, +s: Bool, +pos: {Nat.is_lt(0n, k) == True{} : Bool})
  -> {Bool.and(Nat.is_le(Nat.mul(c, k), p), Bool.and(Nat.is_lt(p, Nat.add(Nat.mul(c, k), k)), s)) ==
     Bool.and(s, Nat.is_eq(c, Nat.div(p, k))) : Bool}:
  match s:
    case False{}:
      ac_and3_false(Nat.is_le(Nat.mul(c, k), p), Nat.is_lt(p, Nat.add(Nat.mul(c, k), k)))
    case True{}:
      +m = Nat.mul(c, k)
      +q = Nat.div(p, k)
      +z = Nat.is_lt(p, Nat.add(m, k))
      %Equal.sym(Bool, Bool.and(z, True{}), z, ac_and_true_r(z)) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, q) : Bool}
      %Equal.sym(Nat, Nat.add(m, k), Nat.add(k, m), Ar.ar_add_comm(m, k)) : {Bool.and(Nat.is_le(m, p), Nat.is_lt(p, _)) == Nat.is_eq(c, q) : Bool}
      %Ar.ar_div_lt(1n+c, p, k, pos) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, q) : Bool}
      %Equal.sym(Bool, Nat.is_le(m, p), Nat.is_le(c, q), Ar.ar_div_le(c, p, k, pos)) : {Bool.and(_, Nat.is_lt(q, 1n+c)) == Nat.is_eq(c, q) : Bool}
      ac_le_lt_eq(c, q)

# chunks_hits(n) == bit(sees && p / chunk < n)
def ac_chunks(+n: Nat, +p: Nat, +d: Nat, +q: Nat, +k: Nat, +j: Nat,
    +pos: {Nat.is_lt(0n, k) == True{} : Bool}, +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.chunks_hits(n, p, Nat.add(d, q), k, q, j) ==
     Impl.bit(Bool.and(Spec.sees(p, d, j), Nat.is_lt(Nat.div(p, k), n))) : Nat}:
  match n:
    case 0n:
      ac_zero(Spec.sees(p, d, j), Nat.div(p, k))
    case 1n+c:
      +L = Nat.add(d, q)
      +a = Nat.add(d, j)
      +sv = Spec.sees(p, d, j)
      +D = Nat.div(p, k)
      %Equal.sym(Nat, Impl.chunks_hits(c, p, L, k, q, j), Impl.bit(Bool.and(sv, Nat.is_lt(D, c))), ac_chunks(c, p, d, q, k, j, pos, row)) : {Nat.add(_, Impl.chunk_hits(c, p, L, k, q, j)) == Impl.bit(Bool.and(sv, Nat.is_lt(D, 1n+c))) : Nat}
      %Equal.sym(Nat, Impl.chunk_hits(c, p, L, k, q, j), Impl.bit(Spec.abs_in_chunk(k, c, p, a)), ac_chunk(c, p, d, q, k, j, row)) : {Nat.add(Impl.bit(Bool.and(sv, Nat.is_lt(D, c))), _) == Impl.bit(Bool.and(sv, Nat.is_lt(D, 1n+c))) : Nat}
      %Equal.sym(Bool, Spec.abs_in_chunk(k, c, p, a), Bool.and(sv, Nat.is_eq(c, D)), ac_core(c, p, k, sv, pos)) : {Nat.add(Impl.bit(Bool.and(sv, Nat.is_lt(D, c))), Impl.bit(_)) == Impl.bit(Bool.and(sv, Nat.is_lt(D, 1n+c))) : Nat}
      ac_step_s(sv, c, D)

def Laws.attend_once(depth, q_len, chunk, qpos, p, cpos, row):
  +cp = cpos
  +rw = row
  +L = Nat.add(depth, q_len)
  +a = Nat.add(depth, qpos)
  +D = Nat.div(p, chunk)
  +sv = Spec.sees(p, depth, qpos)
  +lv = Impl.live(L, chunk)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(qpos, q_len), Ar.ar_lt_add_cancel(depth, qpos, q_len), rw)
  +ks = ac_keep(sv, Nat.is_lt(D, lv), e => ac_lt_cdiv(D, L, chunk, cp,
    Ar.ar_le_lt_trans(Nat.mul(D, chunk), p, L, Ar.ard_le_mul_div(p, chunk, cp), Ar.ar_le_lt_trans(p, a, L, e, hal))))
  %Equal.sym(Nat, Impl.chunks_hits(lv, p, L, chunk, q_len, qpos), Impl.bit(Bool.and(sv, Nat.is_lt(D, lv))), ac_chunks(lv, p, depth, q_len, chunk, qpos, cp, rw)) : {_ == Spec.once(sv) : Nat}
  %Equal.sym(Bool, Bool.and(sv, Nat.is_lt(D, lv)), sv, ks) : {Impl.bit(_) == Spec.once(sv) : Nat}
  ac_bit_once(sv)

# ---------------------------------------------------------------------------------------------
# Combine plan

# a <= b gives a - b == 0
def ac_sub_le0(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, Ar.ar_false_true(h))
    case 1n+ap 1n+bp:
      ac_sub_le0(ap, bp, h)

# b <= a gives (1 + a) - b == 1 + (a - b)
def ac_sub_succ(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.sub(1n, 1n+bp) == 1n+Nat.sub(0n, 1n+bp) : Nat}, Ar.ar_false_true(h))
    case 1n+ap 1n+bp:
      ac_sub_succ(ap, bp, h)

def ac_keep_case(b: Bool, -s0: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>,
    t: {b == True{} : Bool} -> {(s0 <> xs) == ys : List<&2, Nat>},
    f: {b == False{} : Bool} -> {xs == ys : List<&2, Nat>})
  -> {Impl.keep(b, s0, xs) == ys : List<&2, Nat>}:
  match b:
    case False{}:
      f({==})
    case True{}:
      t({==})

def ac_merge_in(+D: Nat, +s0: Nat, h: {Nat.is_le(s0, D) == True{} : Bool})
  -> {(s0 <> Spec.range.go(Nat.sub(D, s0), 1n+s0)) == Spec.range.go(Nat.sub(1n+D, s0), s0) : List<&2, Nat>}:
  %Equal.sym(Nat, Nat.sub(1n+D, s0), 1n+Nat.sub(D, s0), ac_sub_succ(D, s0, h)) : {(s0 <> Spec.range.go(Nat.sub(D, s0), 1n+s0)) == Spec.range.go(_, s0) : List<&2, Nat>}
  {==}

def ac_merge_out(+D: Nat, +s0: Nat, h: {Nat.is_le(s0, D) == False{} : Bool})
  -> {Spec.range.go(Nat.sub(D, s0), 1n+s0) == Spec.range.go(Nat.sub(1n+D, s0), s0) : List<&2, Nat>}:
  +hlt = Equal.trans(Bool, Nat.is_lt(D, s0), Bool.not(Nat.is_le(s0, D)), True{}, Ar.ar_lt_not_le(D, s0),
    Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_le(s0, D), False{}, h))
  +h1 = Ar.ar_lt_le(D, s0, hlt)
  +h2 = Ar.ard_rt(Nat.is_lt(D, s0), Nat.is_le(1n+D, s0), Ar.ar_lt_succ_le(D, s0), hlt)
  %Equal.sym(Nat, Nat.sub(D, s0), 0n, ac_sub_le0(D, s0, h1)) : {Spec.range.go(_, 1n+s0) == Spec.range.go(Nat.sub(1n+D, s0), s0) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.sub(1n+D, s0), 0n, ac_sub_le0(1n+D, s0, h2)) : {Spec.range.go(0n, 1n+s0) == Spec.range.go(_, s0) : List<&2, Nat>}
  {==}

# Filtering [s0, s0 + n) by s * chunk <= a leaves [s0, a / chunk] when a / chunk < s0 + n
def ac_merge(+n: Nat, +s0: Nat, +k: Nat, +a: Nat, +pos: {Nat.is_lt(0n, k) == True{} : Bool},
    hlt: {Nat.is_lt(Nat.div(a, k), Nat.add(s0, n)) == True{} : Bool})
  -> {Impl.row_filter(Impl.combine.go(n, s0), k, a) == Spec.range.go(Nat.sub(1n+Nat.div(a, k), s0), s0) : List<&2, Nat>}:
  match n:
    case 0n:
      +D = Nat.div(a, k)
      +h1 = Ar.ard_rt(Nat.is_lt(D, Nat.add(s0, 0n)), Nat.is_lt(D, s0),
        Equal.cong(Nat, Bool, z => Nat.is_lt(D, z), Nat.add(s0, 0n), s0, Ar.ar_add_zero_r(s0)), hlt)
      +h2 = Ar.ard_rt(Nat.is_lt(D, s0), Nat.is_le(1n+D, s0), Ar.ar_lt_succ_le(D, s0), h1)
      %Equal.sym(Nat, Nat.sub(1n+D, s0), 0n, ac_sub_le0(1n+D, s0, h2)) : {Impl.row_filter(Impl.combine.go(0n, s0), k, a) == Spec.range.go(_, s0) : List<&2, Nat>}
      {==}
    case 1n+r:
      +D = Nat.div(a, k)
      +hlt2 = Ar.ard_rt(Nat.is_lt(D, Nat.add(s0, 1n+r)), Nat.is_lt(D, 1n+Nat.add(s0, r)),
        Equal.cong(Nat, Bool, z => Nat.is_lt(D, z), Nat.add(s0, 1n+r), 1n+Nat.add(s0, r), Ar.ar_add_succ_r(s0, r)), hlt)
      %Equal.sym(List<&2, Nat>, Impl.row_filter(Impl.combine.go(r, 1n+s0), k, a), Spec.range.go(Nat.sub(D, s0), 1n+s0), ac_merge(r, 1n+s0, k, a, pos, hlt2)) : {Impl.keep(Nat.is_le(Nat.mul(s0, k), a), s0, _) == Spec.range.go(Nat.sub(1n+D, s0), s0) : List<&2, Nat>}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(s0, k), a), Nat.is_le(s0, D), Ar.ar_div_le(s0, a, k, pos)) : {Impl.keep(_, s0, Spec.range.go(Nat.sub(D, s0), 1n+s0)) == Spec.range.go(Nat.sub(1n+D, s0), s0) : List<&2, Nat>}
      ac_keep_case(Nat.is_le(s0, D), s0, Spec.range.go(Nat.sub(D, s0), 1n+s0), Spec.range.go(Nat.sub(1n+D, s0), s0),
        h => ac_merge_in(D, s0, h), h => ac_merge_out(D, s0, h))

# merged == abs_chunks (row_invariant (c))
def ac_merged(+d: Nat, +q: Nat, +k: Nat, +j: Nat, +pos: {Nat.is_lt(0n, k) == True{} : Bool},
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.merged(Nat.add(d, q), k, q, j) == Spec.abs_chunks(k, Nat.add(d, j)) : List<&2, Nat>}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +D = Nat.div(a, k)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  +hD = ac_lt_cdiv(D, L, k, pos, Ar.ar_le_lt_trans(Nat.mul(D, k), a, L, Ar.ard_le_mul_div(a, k, pos), hal))
  %Equal.sym(Nat, Nat.sub(L, q), d, ac_qabs(d, q)) : {Impl.row_filter(Impl.combine.go(Impl.live(L, k), 0n), k, Nat.add(_, j)) == Spec.abs_chunks(k, a) : List<&2, Nat>}
  ac_merge(Impl.live(L, k), 0n, k, a, pos, hD)

def Laws.row_invariant(depth, q_len, chunk, qpos, c, it, p, cpos, row):
  +cp = cpos
  +rw = row
  (ac_tile(c, it, p, depth, q_len, chunk, qpos, rw), ac_chunk_once(c, p, depth, q_len, chunk, qpos, rw),
    ac_merged(depth, q_len, chunk, qpos, cp, rw))

def Laws.row_invariant_rounds(d1, q1, j1, d2, q2, j2, chunk, c, it, p, cpos, row1, row2, same):
  +cp = cpos
  +r1 = row1
  +r2 = row2
  +sm = same
  +a1 = Nat.add(d1, j1)
  +a2 = Nat.add(d2, j2)
  +T1 = Impl.tile_hits(c, it, p, Nat.add(d1, q1), chunk, q1, j1)
  +T2 = Impl.tile_hits(c, it, p, Nat.add(d2, q2), chunk, q2, j2)
  +C1 = Impl.chunk_hits(c, p, Nat.add(d1, q1), chunk, q1, j1)
  +C2 = Impl.chunk_hits(c, p, Nat.add(d2, q2), chunk, q2, j2)
  +M1 = Impl.merged(Nat.add(d1, q1), chunk, q1, j1)
  +M2 = Impl.merged(Nat.add(d2, q2), chunk, q2, j2)
  (Equal.trans(Nat, T1, Spec.once(Spec.abs_visit(chunk, c, it, p, a1)), T2, ac_tile(c, it, p, d1, q1, chunk, j1, r1),
     Equal.trans(Nat, Spec.once(Spec.abs_visit(chunk, c, it, p, a1)), Spec.once(Spec.abs_visit(chunk, c, it, p, a2)), T2,
       Equal.cong(Nat, Nat, z => Spec.once(Spec.abs_visit(chunk, c, it, p, z)), a1, a2, sm),
       Equal.sym(Nat, T2, Spec.once(Spec.abs_visit(chunk, c, it, p, a2)), ac_tile(c, it, p, d2, q2, chunk, j2, r2)))),
   Equal.trans(Nat, C1, Spec.once(Spec.abs_in_chunk(chunk, c, p, a1)), C2, ac_chunk_once(c, p, d1, q1, chunk, j1, r1),
     Equal.trans(Nat, Spec.once(Spec.abs_in_chunk(chunk, c, p, a1)), Spec.once(Spec.abs_in_chunk(chunk, c, p, a2)), C2,
       Equal.cong(Nat, Nat, z => Spec.once(Spec.abs_in_chunk(chunk, c, p, z)), a1, a2, sm),
       Equal.sym(Nat, C2, Spec.once(Spec.abs_in_chunk(chunk, c, p, a2)), ac_chunk_once(c, p, d2, q2, chunk, j2, r2)))),
   Equal.trans(List<&2, Nat>, M1, Spec.abs_chunks(chunk, a1), M2, ac_merged(d1, q1, chunk, j1, cp, r1),
     Equal.trans(List<&2, Nat>, Spec.abs_chunks(chunk, a1), Spec.abs_chunks(chunk, a2), M2,
       Equal.cong(Nat, List<&2, Nat>, z => Spec.abs_chunks(chunk, z), a1, a2, sm),
       Equal.sym(List<&2, Nat>, M2, Spec.abs_chunks(chunk, a2), ac_merged(d2, q2, chunk, j2, cp, r2)))))

# ---------------------------------------------------------------------------------------------
# Combine skip test

def Laws.skip_witness(depth, q_len, chunk, qpos, s, cpos, row, kept):
  +cp = cpos
  +rw = row
  +L = Nat.add(depth, q_len)
  +a = Nat.add(depth, qpos)
  +m = Nat.mul(s, chunk)
  +hk = Ar.ard_rt(Nat.is_le(m, Nat.add(Nat.sub(L, q_len), qpos)), Nat.is_le(m, a),
    Equal.cong(Nat, Bool, z => Nat.is_le(m, Nat.add(z, qpos)), Nat.sub(L, q_len), depth, ac_qabs(depth, q_len)), kept)
  +hmk = Ar.ard_tr(Nat.is_lt(m, Nat.add(m, chunk)), Nat.is_lt(0n, chunk),
    Equal.trans(Bool, Nat.is_lt(m, Nat.add(m, chunk)), Nat.is_lt(Nat.add(m, 0n), Nat.add(m, chunk)), Nat.is_lt(0n, chunk),
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, Nat.add(m, chunk)), m, Nat.add(m, 0n), Equal.sym(Nat, Nat.add(m, 0n), m, Ar.ar_add_zero_r(m))),
      Ar.ar_lt_add_cancel(m, 0n, chunk)), cp)
  +hin = Ar.ar_and_intro(Nat.is_le(m, m), Bool.and(Nat.is_lt(m, Nat.add(m, chunk)), Nat.is_le(m, a)), Ar.ar_le_refl(m),
    Ar.ar_and_intro(Nat.is_lt(m, Nat.add(m, chunk)), Nat.is_le(m, a), hmk, hk))
  %Equal.sym(Nat, Impl.chunk_hits(s, m, L, chunk, q_len, qpos), Impl.bit(Spec.abs_in_chunk(chunk, s, m, a)), ac_chunk(s, m, depth, q_len, chunk, qpos, rw)) : {_ == 1n : Nat}
  %Equal.sym(Bool, Spec.abs_in_chunk(chunk, s, m, a), True{}, hin) : {Impl.bit(_) == 1n : Nat}
  {==}

# m <= p && (p < e && p <= a) gives m <= a
def ac_in_le(+m: Nat, +p: Nat, +e: Nat, +a: Nat,
    +h: {Bool.and(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a))) == True{} : Bool})
  -> {Nat.is_le(m, a) == True{} : Bool}:
  Ar.ar_le_trans(m, p, a, Ar.ar_and_l(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)), h),
    Ar.ar_and_r(Nat.is_lt(p, e), Nat.is_le(p, a), Ar.ar_and_r(Nat.is_le(m, p), Bool.and(Nat.is_lt(p, e), Nat.is_le(p, a)), h)))

def Laws.skip_sound(depth, q_len, chunk, qpos, s, p, cpos, row, skipped):
  +rw = row
  +L = Nat.add(depth, q_len)
  +a = Nat.add(depth, qpos)
  +m = Nat.mul(s, chunk)
  +hk = Equal.trans(Bool, Nat.is_le(m, a), Nat.is_le(m, Nat.add(Nat.sub(L, q_len), qpos)), False{},
    Equal.cong(Nat, Bool, z => Nat.is_le(m, Nat.add(z, qpos)), depth, Nat.sub(L, q_len), Equal.sym(Nat, Nat.sub(L, q_len), depth, ac_qabs(depth, q_len))),
    skipped)
  +no = Ar.ar_not_true(Spec.abs_in_chunk(chunk, s, p, a), h => Ar.ar_false_ne(Nat.is_le(m, a), hk, ac_in_le(m, p, Nat.add(m, chunk), a, h)))
  %Equal.sym(Nat, Impl.chunk_hits(s, p, L, chunk, q_len, qpos), Impl.bit(Spec.abs_in_chunk(chunk, s, p, a)), ac_chunk(s, p, depth, q_len, chunk, qpos, rw)) : {_ == 0n : Nat}
  %Equal.sym(Bool, Spec.abs_in_chunk(chunk, s, p, a), False{}, no) : {Impl.bit(_) == 0n : Nat}
  {==}

# ---------------------------------------------------------------------------------------------
# CTA chunk loops

# q <= q * S for S >= 1
def ac_le_mul_pos(+q: Nat, +S: Nat, +pos: {Nat.is_lt(0n, S) == True{} : Bool})
  -> {Nat.is_le(q, Nat.mul(q, S)) == True{} : Bool}:
  match S:
    case 0n:
      Empty.absurd({Nat.is_le(q, Nat.mul(q, 0n)) == True{} : Bool}, Ar.ar_false_true(pos))
    case 1n+sp:
      %Equal.sym(Nat, Nat.mul(q, 1n+sp), Nat.add(q, Nat.mul(q, sp)), Ar.ar_mul_succ_r(q, sp)) : {Nat.is_le(q, _) == True{} : Bool}
      Ar.ar_le_add_r(q, Nat.mul(q, sp))

# bit(i == q) + bit(i + 1 <= q) == bit(i <= q)
def ac_step_le1(+i: Nat, +q: Nat)
  -> {Nat.add(Impl.bit(Nat.is_eq(i, q)), Impl.bit(Nat.is_le(1n+i, q))) == Impl.bit(Nat.is_le(i, q)) : Nat}:
  match i q:
    case 0n 0n:
      {==}
    case 0n 1n+qp:
      match qp:
        case 0n:
          {==}
        case 1n+qq:
          {==}
    case 1n+ip 0n:
      {==}
    case 1n+ip 1n+qp:
      ac_step_le1(ip, qp)

def ac_step_le(+y: Bool, +i: Nat, +q: Nat)
  -> {Nat.add(Impl.bit(Bool.and(y, Nat.is_eq(i, q))), Impl.bit(Bool.and(y, Nat.is_le(1n+i, q)))) ==
     Impl.bit(Bool.and(y, Nat.is_le(i, q))) : Nat}:
  match y:
    case False{}:
      {==}
    case True{}:
      ac_step_le1(i, q)

def ac_gate_case(b: Bool, -n: Nat, -r: Nat, t: {b == True{} : Bool} -> {n == r : Nat},
    f: {b == False{} : Bool} -> {0n == r : Nat}) -> {Impl.gate(b, n) == r : Nat}:
  match b:
    case False{}:
      f({==})
    case True{}:
      t({==})

def ac_cta_hit_fwd(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat}, +ht: {Nat.is_lt(c, lv) == True{} : Bool},
    +h: {Nat.is_eq(c, s) == True{} : Bool})
  -> {Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_eq(i, Nat.div(s, S))) == True{} : Bool}:
  +r = Nat.mod(s, S)
  +q = Nat.div(s, S)
  +hcs = Ar.ar_eq_true(c, s, h)
  +hB = Ar.ard_rt(Nat.is_lt(c, lv), Nat.is_lt(s, lv), Equal.cong(Nat, Bool, z => Nat.is_lt(z, lv), c, s, hcs), ht)
  +same = Equal.trans(Nat, Nat.add(Nat.mul(i, S), x), Nat.add(x, Nat.mul(i, S)), Nat.add(Nat.mul(q, S), r),
    Ar.ar_add_comm(Nat.mul(i, S), x),
    Equal.trans(Nat, Nat.add(x, Nat.mul(i, S)), c, Nat.add(Nat.mul(q, S), r),
      Equal.sym(Nat, c, Nat.add(x, Nat.mul(i, S)), hc),
      Equal.trans(Nat, c, s, Nat.add(Nat.mul(q, S), r), hcs,
        Equal.sym(Nat, Nat.add(Nat.mul(q, S), r), s, Ar.ard_dm_eq(s, S, spos)))))
  +hiq = ac_eq_of(i, q, Ar.ard_fst({i == q : Nat}, {x == r : Nat}, Ar.ar_divmod_inj(i, x, q, r, S, xs, Ar.ard_dm_lt(s, S, spos), same)))
  +hxr = ac_eq_of(x, r, Ar.ard_snd({i == q : Nat}, {x == r : Nat}, Ar.ar_divmod_inj(i, x, q, r, S, xs, Ar.ard_dm_lt(s, S, spos), same)))
  Ar.ar_and_intro(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, r)), Nat.is_eq(i, q),
    Ar.ar_and_intro(Nat.is_lt(s, lv), Nat.is_eq(x, r), hB, hxr), hiq)

def ac_cta_hit_bwd(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat},
    +h: {Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_eq(i, Nat.div(s, S))) == True{} : Bool})
  -> {Nat.is_eq(c, s) == True{} : Bool}:
  +r = Nat.mod(s, S)
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, r))
  +hY = Ar.ar_and_l(Y, Nat.is_eq(i, q), h)
  +hiq = Ar.ar_eq_true(i, q, Ar.ar_and_r(Y, Nat.is_eq(i, q), h))
  +hxr = Ar.ar_eq_true(x, r, Ar.ar_and_r(Nat.is_lt(s, lv), Nat.is_eq(x, r), hY))
  +hcs = Equal.trans(Nat, c, Nat.add(x, Nat.mul(i, S)), s, hc,
    Equal.trans(Nat, Nat.add(x, Nat.mul(i, S)), Nat.add(r, Nat.mul(i, S)), s,
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(i, S)), x, r, hxr),
      Equal.trans(Nat, Nat.add(r, Nat.mul(i, S)), Nat.add(r, Nat.mul(q, S)), s,
        Equal.cong(Nat, Nat, z => Nat.add(r, Nat.mul(z, S)), i, q, hiq),
        Equal.trans(Nat, Nat.add(r, Nat.mul(q, S)), Nat.add(Nat.mul(q, S), r), s,
          Ar.ar_add_comm(r, Nat.mul(q, S)), Ar.ard_dm_eq(s, S, spos)))))
  ac_eq_of(c, s, hcs)

# A live iteration c = x + i S (x < S) processes s iff s is live, s mod S == x and s / S == i
def ac_cta_hit(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat}, +ht: {Nat.is_lt(c, lv) == True{} : Bool})
  -> {Nat.is_eq(c, s) == Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_eq(i, Nat.div(s, S))) : Bool}:
  +r = Nat.mod(s, S)
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, r))
  Ar.ar_bool_ext(Nat.is_eq(c, s), Bool.and(Y, Nat.is_eq(i, q)),
    h => ac_cta_hit_fwd(c, i, x, S, s, lv, spos, xs, hc, ht, h),
    h => ac_cta_hit_bwd(c, i, x, S, s, lv, spos, hc, h))

def ac_cta_live(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat}, +ht: {Nat.is_lt(c, lv) == True{} : Bool})
  -> {Nat.add(Impl.bit(Nat.is_eq(c, s)), Impl.bit(Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(1n+i, Nat.div(s, S))))) ==
     Impl.bit(Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S)))) : Nat}:
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S)))
  %Equal.sym(Bool, Nat.is_eq(c, s), Bool.and(Y, Nat.is_eq(i, q)), ac_cta_hit(c, i, x, S, s, lv, spos, xs, hc, ht)) : {Nat.add(Impl.bit(_), Impl.bit(Bool.and(Y, Nat.is_le(1n+i, q)))) == Impl.bit(Bool.and(Y, Nat.is_le(i, q))) : Nat}
  ac_step_le(Y, i, q)

# A dead iteration (c >= live) means no live s = x + q S with q >= i remains
def ac_cta_dead_e(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat}, +hf: {Nat.is_lt(c, lv) == False{} : Bool},
    +h: {Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S))) == True{} : Bool})
  -> Empty:
  +r = Nat.mod(s, S)
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, r))
  +hY = Ar.ar_and_l(Y, Nat.is_le(i, q), h)
  +hi = Ar.ar_and_r(Y, Nat.is_le(i, q), h)
  +hB = Ar.ar_and_l(Nat.is_lt(s, lv), Nat.is_eq(x, r), hY)
  +hxr = Ar.ar_eq_true(x, r, Ar.ar_and_r(Nat.is_lt(s, lv), Nat.is_eq(x, r), hY))
  +mi = Nat.mul(i, S)
  +mq = Nat.mul(q, S)
  +h0 = Ar.ard_tr(Nat.is_le(Nat.add(x, mi), Nat.add(x, mq)), Nat.is_le(mi, mq), Ar.ar_le_add_cancel(x, mi, mq),
    Ar.ar_le_mul_mono(i, q, S, hi))
  +e2 = Equal.trans(Nat, Nat.add(x, mq), Nat.add(r, mq), s,
    Equal.cong(Nat, Nat, z => Nat.add(z, mq), x, r, hxr),
    Equal.trans(Nat, Nat.add(r, mq), Nat.add(mq, r), s, Ar.ar_add_comm(r, mq), Ar.ard_dm_eq(s, S, spos)))
  +hcs = Ar.ard_rt(Nat.is_le(Nat.add(x, mi), Nat.add(x, mq)), Nat.is_le(c, s),
    Equal.trans(Bool, Nat.is_le(Nat.add(x, mi), Nat.add(x, mq)), Nat.is_le(c, Nat.add(x, mq)), Nat.is_le(c, s),
      Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(x, mq)), Nat.add(x, mi), c, Equal.sym(Nat, c, Nat.add(x, mi), hc)),
      Equal.cong(Nat, Bool, z => Nat.is_le(c, z), Nat.add(x, mq), s, e2)), h0)
  Ar.ar_false_ne(Nat.is_lt(c, lv), hf, Ar.ar_le_lt_trans(c, s, lv, hcs, hB))

def ac_cta_dead(+c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat}, +hf: {Nat.is_lt(c, lv) == False{} : Bool})
  -> {0n == Impl.bit(Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S)))) : Nat}:
  +W = Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S)))
  +no = Ar.ar_not_true(W, h => ac_cta_dead_e(c, i, x, S, s, lv, spos, hc, hf, h))
  %Equal.sym(Bool, W, False{}, no) : {0n == Impl.bit(_) : Nat}
  {==}

# Out of fuel (live <= i): no live s has s / S >= i
def ac_cta_zero(+i: Nat, +x: Nat, +S: Nat, +s: Nat, +lv: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +fuel: {Nat.is_le(lv, i) == True{} : Bool},
    +h: {Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S))) == True{} : Bool})
  -> Empty:
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S)))
  +hY = Ar.ar_and_l(Y, Nat.is_le(i, q), h)
  +hi = Ar.ar_and_r(Y, Nat.is_le(i, q), h)
  +hB = Ar.ar_and_l(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S)), hY)
  +hqs = Ar.ar_le_trans(q, Nat.mul(q, S), s, ac_le_mul_pos(q, S, spos), Ar.ard_le_mul_div(s, S, spos))
  +hil = Ar.ar_le_lt_trans(i, s, lv, Ar.ar_le_trans(i, q, s, hi, hqs), hB)
  Ar.ard_lt_self(i, Ar.ar_lt_le_trans(i, lv, i, hil, fuel))

# The chunk loop from c = x + i S (x < S) with fuel f, live <= f + i, processes chunk s once iff
# s is live, s mod S == x and s / S >= i.
def ac_cta(+f: Nat, +c: Nat, +i: Nat, +x: Nat, +S: Nat, +s: Nat, +L: Nat, +k: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +hc: {c == Nat.add(x, Nat.mul(i, S)) : Nat},
    +fuel: {Nat.is_le(Impl.live(L, k), Nat.add(f, i)) == True{} : Bool})
  -> {Impl.cta(f, c, S, s, L, k) ==
     Impl.bit(Bool.and(Bool.and(Nat.is_lt(s, Impl.live(L, k)), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S)))) : Nat}:
  match f:
    case 0n:
      +lv = Impl.live(L, k)
      +W = Bool.and(Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S))), Nat.is_le(i, Nat.div(s, S)))
      +no = Ar.ar_not_true(W, h => ac_cta_zero(i, x, S, s, lv, spos, fuel, h))
      %Equal.sym(Bool, W, False{}, no) : {0n == Impl.bit(_) : Nat}
      {==}
    case 1n+g:
      +lv = Impl.live(L, k)
      +q = Nat.div(s, S)
      +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S)))
      +mi = Nat.mul(i, S)
      +hc2 = Equal.trans(Nat, Nat.add(c, S), Nat.add(Nat.add(x, mi), S), Nat.add(x, Nat.add(S, mi)),
        Equal.cong(Nat, Nat, z => Nat.add(z, S), c, Nat.add(x, mi), hc),
        Equal.trans(Nat, Nat.add(Nat.add(x, mi), S), Nat.add(x, Nat.add(mi, S)), Nat.add(x, Nat.add(S, mi)),
          Ar.ar_add_assoc(x, mi, S),
          Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(mi, S), Nat.add(S, mi), Ar.ar_add_comm(mi, S))))
      +fuel2 = Ar.ard_rt(Nat.is_le(lv, 1n+Nat.add(g, i)), Nat.is_le(lv, Nat.add(g, 1n+i)),
        Equal.cong(Nat, Bool, z => Nat.is_le(lv, z), 1n+Nat.add(g, i), Nat.add(g, 1n+i),
          Equal.sym(Nat, Nat.add(g, 1n+i), 1n+Nat.add(g, i), Ar.ar_add_succ_r(g, i))), fuel)
      %Equal.sym(Nat, Impl.cta(g, Nat.add(c, S), S, s, L, k), Impl.bit(Bool.and(Y, Nat.is_le(1n+i, q))), ac_cta(g, Nat.add(c, S), 1n+i, x, S, s, L, k, spos, xs, hc2, fuel2)) : {Impl.gate(Nat.is_lt(c, lv), Nat.add(Impl.bit(Nat.is_eq(c, s)), _)) == Impl.bit(Bool.and(Y, Nat.is_le(i, q))) : Nat}
      ac_gate_case(Nat.is_lt(c, lv), Nat.add(Impl.bit(Nat.is_eq(c, s)), Impl.bit(Bool.and(Y, Nat.is_le(1n+i, q)))), Impl.bit(Bool.and(Y, Nat.is_le(i, q))),
        h => ac_cta_live(c, i, x, S, s, lv, spos, xs, hc, h), h => ac_cta_dead(c, i, x, S, s, lv, spos, hc, h))

# CTA x < S processes chunk s once iff s is live and s mod S == x
def ac_cta_top(+x: Nat, +S: Nat, +s: Nat, +L: Nat, +k: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool})
  -> {Impl.cta(Impl.live(L, k), x, S, s, L, k) == Impl.bit(Bool.and(Nat.is_lt(s, Impl.live(L, k)), Nat.is_eq(x, Nat.mod(s, S)))) : Nat}:
  +lv = Impl.live(L, k)
  +q = Nat.div(s, S)
  +Y = Bool.and(Nat.is_lt(s, lv), Nat.is_eq(x, Nat.mod(s, S)))
  +fuel0 = Ar.ard_rt(Nat.is_le(lv, lv), Nat.is_le(lv, Nat.add(lv, 0n)),
    Equal.cong(Nat, Bool, z => Nat.is_le(lv, z), lv, Nat.add(lv, 0n), Equal.sym(Nat, Nat.add(lv, 0n), lv, Ar.ar_add_zero_r(lv))),
    Ar.ar_le_refl(lv))
  +G = ac_cta(lv, x, 0n, x, S, s, L, k, spos, xs, Equal.sym(Nat, Nat.add(x, 0n), x, Ar.ar_add_zero_r(x)), fuel0)
  %Equal.sym(Nat, Impl.cta(lv, x, S, s, L, k), Impl.bit(Bool.and(Y, Nat.is_le(0n, q))), G) : {_ == Impl.bit(Y) : Nat}
  %Equal.sym(Bool, Nat.is_le(0n, q), True{}, Ar.ar_h_le_zero(q)) : {Impl.bit(Bool.and(Y, _)) == Impl.bit(Y) : Nat}
  %Equal.sym(Bool, Bool.and(Y, True{}), Y, ac_and_true_r(Y)) : {Impl.bit(_) == Impl.bit(Y) : Nat}
  {==}

# writes(n) == bit(s live && s mod S < n) for n <= S
def ac_writes(+n: Nat, +S: Nat, +s: Nat, +L: Nat, +k: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, hn: {Nat.is_le(n, S) == True{} : Bool})
  -> {Impl.writes(n, S, s, L, k) == Impl.bit(Bool.and(Nat.is_lt(s, Impl.live(L, k)), Nat.is_lt(Nat.mod(s, S), n))) : Nat}:
  match n:
    case 0n:
      ac_zero(Nat.is_lt(s, Impl.live(L, k)), Nat.mod(s, S))
    case 1n+x:
      +lv = Impl.live(L, k)
      +B = Nat.is_lt(s, lv)
      +r = Nat.mod(s, S)
      +hx = Ar.ard_tr(Nat.is_lt(x, S), Nat.is_le(1n+x, S), Ar.ar_lt_succ_le(x, S), hn)
      %Equal.sym(Nat, Impl.writes(x, S, s, L, k), Impl.bit(Bool.and(B, Nat.is_lt(r, x))), ac_writes(x, S, s, L, k, spos, Ar.ar_lt_le(x, S, hx))) : {Nat.add(_, Impl.cta(lv, x, S, s, L, k)) == Impl.bit(Bool.and(B, Nat.is_lt(r, 1n+x))) : Nat}
      %Equal.sym(Nat, Impl.cta(lv, x, S, s, L, k), Impl.bit(Bool.and(B, Nat.is_eq(x, r))), ac_cta_top(x, S, s, L, k, spos, hx)) : {Nat.add(Impl.bit(Bool.and(B, Nat.is_lt(r, x))), _) == Impl.bit(Bool.and(B, Nat.is_lt(r, 1n+x))) : Nat}
      ac_step_s(B, x, r)

def Laws.cta_once(L, S, chunk, s, spos, cpos):
  +sp = spos
  +lv = Impl.live(L, chunk)
  +B = Nat.is_lt(s, lv)
  +r = Nat.mod(s, S)
  %Equal.sym(Nat, Impl.writes(S, S, s, L, chunk), Impl.bit(Bool.and(B, Nat.is_lt(r, S))), ac_writes(S, S, s, L, chunk, sp, Ar.ar_le_refl(S))) : {_ == Spec.once(B) : Nat}
  %Equal.sym(Bool, Nat.is_lt(r, S), True{}, Ar.ard_dm_lt(s, S, sp)) : {Impl.bit(Bool.and(B, _)) == Spec.once(B) : Nat}
  %Equal.sym(Bool, Bool.and(B, True{}), B, ac_and_true_r(B)) : {Impl.bit(_) == Spec.once(B) : Nat}
  ac_bit_once(B)
