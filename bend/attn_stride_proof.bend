# Proofs of the strided absolute-tile verify-attention partition laws (attn_stride_laws.bend) about
# the Bend model attn_stride.bend against the reference attn_stride_spec.bend. Structural evidence
# only: no unsafe definitions, axioms, holes, foreign proof code or answer tables. Nat arithmetic
# lemmas come from the proven m16 partition library; the small ceil-division / counting lemmas
# follow the attn_chunk_proof.bend ones, restated over this model's definitions.
import Base
import ./attn_stride.bend as Impl
import ./attn_stride_spec.bend as Spec
import ./attn_stride_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def Laws.lanes_once():
  ({==}, {==})

# ---------------------------------------------------------------------------------------------
# Generic helpers

def sp_sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (y + (1 + bp)) - 1 == y + bp
def sp_pred(+y: Nat, +bp: Nat) -> {Nat.sub(Nat.add(y, 1n+bp), 1n) == Nat.add(y, bp) : Nat}:
  %Equal.sym(Nat, Nat.add(y, 1n+bp), 1n+Nat.add(y, bp), Ar.ar_add_succ_r(y, bp)) : {Nat.sub(_, 1n) == Nat.add(y, bp) : Nat}
  sp_sub_zero(Nat.add(y, bp))

# i < ceil(L / b) iff i * b < L (b >= 1)
def sp_live(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(i, Impl.cdiv(L, b)) == Bool.not(Nat.is_le(L, Nat.mul(i, b))) : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(i, Impl.cdiv(L, 0n)) == Bool.not(Nat.is_le(L, Nat.mul(i, 0n))) : Bool}, Ar.ar_false_true(pos))
    case 1n+bp:
      %Equal.sym(Nat, Nat.sub(Nat.add(L, 1n+bp), 1n), Nat.add(L, bp), sp_pred(L, bp)) : {Nat.is_lt(i, Nat.div(_, 1n+bp)) == Bool.not(Nat.is_le(L, Nat.mul(i, 1n+bp))) : Bool}
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
def sp_lt_cdiv(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_lt(Nat.mul(i, b), L) == True{} : Bool})
  -> {Nat.is_lt(i, Impl.cdiv(L, b)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(i, Impl.cdiv(L, b)), Bool.not(Nat.is_le(L, Nat.mul(i, b))), sp_live(i, L, b, pos),
    Ar.ard_rt(Nat.is_lt(Nat.mul(i, b), L), Bool.not(Nat.is_le(L, Nat.mul(i, b))), Ar.ar_lt_not_le(Nat.mul(i, b), L), h))

# i <= k && k < i + 1 iff i == k
def sp_le_lt_eq(+i: Nat, +k: Nat)
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
      sp_le_lt_eq(ip, kp)

# (a == b) == (b == a)
def sp_eq_sym(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      sp_eq_sym(ap, bp)

def sp_and3_false(+x: Bool, +y: Bool) -> {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}:
  match x y:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def sp_and_true_r(+x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# s && (e && i) == (e && s) && i
def sp_shuffle(+s: Bool, +e: Bool, +i: Bool)
  -> {Bool.and(s, Bool.and(e, i)) == Bool.and(Bool.and(e, s), i) : Bool}:
  match s e:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# (s && x) == s when s implies x
def sp_keep(+s: Bool, +x: Bool, h: {s == True{} : Bool} -> {x == True{} : Bool})
  -> {Bool.and(s, x) == s : Bool}:
  match s:
    case False{}:
      {==}
    case True{}:
      h({==})

# (x && (y && s)) == s when s implies x && y
def sp_keep2(+x: Bool, +y: Bool, +s: Bool, h: {s == True{} : Bool} -> {Bool.and(x, y) == True{} : Bool})
  -> {Bool.and(x, Bool.and(y, s)) == s : Bool}:
  match s:
    case False{}:
      sp_and3_false(x, y)
    case True{}:
      %Equal.sym(Bool, Bool.and(y, True{}), y, sp_and_true_r(y)) : {Bool.and(x, _) == True{} : Bool}
      h({==})

# (depth + q_len) - q_len == depth: the kernel's q_abs = L - q_len + gid is depth + gid
def sp_qabs(+depth: Nat, +q_len: Nat) -> {Nat.sub(Nat.add(depth, q_len), q_len) == depth : Nat}:
  %Equal.sym(Nat, Nat.add(depth, q_len), Nat.add(q_len, depth), Ar.ar_add_comm(depth, q_len)) : {Nat.sub(_, q_len) == depth : Nat}
  Ar.ar_add_sub(q_len, depth)

# add(bit(k < j), bit(j == k)) == bit(k < j + 1)
def sp_step(+j: Nat, +k: Nat)
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
      sp_step(jp, kp)

def sp_step_s(+s: Bool, +j: Nat, +k: Nat)
  -> {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(k, j))), Impl.bit(Bool.and(s, Nat.is_eq(j, k)))) ==
     Impl.bit(Bool.and(s, Nat.is_lt(k, 1n+j))) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      sp_step(j, k)

def sp_zero(+s: Bool, +k: Nat) -> {0n == Impl.bit(Bool.and(s, Nat.is_lt(k, 0n))) : Nat}:
  match s k:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+kp:
      {==}

def sp_bit_once(+s: Bool) -> {Impl.bit(s) == Spec.once(s) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      {==}

# a == b gives (a == b) == True
def sp_eq_of(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  Ar.ar_eq_refl(a)

# a <= b gives a - b == 0
def sp_sub_le0(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.sub(1n+ap, 0n) == 0n : Nat}, Ar.ar_false_true(h))
    case 1n+ap 1n+bp:
      sp_sub_le0(ap, bp, h)

# b <= a gives (1 + a) - b == 1 + (a - b)
def sp_sub_succ(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.sub(1n, 1n+bp) == 1n+Nat.sub(0n, 1n+bp) : Nat}, Ar.ar_false_true(h))
    case 1n+ap 1n+bp:
      sp_sub_succ(ap, bp, h)

def sp_min_zero_r(+n: Nat) -> {Nat.min(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      {==}

# min(min(n, S), m) == min(S, m) when m <= n
def sp_min_absorb(+m: Nat, +n: Nat, +S: Nat, h: {Nat.is_le(m, n) == True{} : Bool})
  -> {Nat.min(Nat.min(n, S), m) == Nat.min(S, m) : Nat}:
  match m n S:
    case 0n _ _:
      Equal.trans(Nat, Nat.min(Nat.min(n, S), 0n), 0n, Nat.min(S, 0n),
        sp_min_zero_r(Nat.min(n, S)), Equal.sym(Nat, Nat.min(S, 0n), 0n, sp_min_zero_r(S)))
    case 1n+mp 0n _:
      Empty.absurd({Nat.min(Nat.min(0n, S), 1n+mp) == Nat.min(S, 1n+mp) : Nat}, Ar.ar_false_true(h))
    case 1n+mp 1n+np 0n:
      {==}
    case 1n+mp 1n+np 1n+sp:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(Nat.min(np, sp), mp), Nat.min(sp, mp), sp_min_absorb(mp, np, sp, h))

# ---------------------------------------------------------------------------------------------
# Tile level

# A position of tile x + it S seen by the row (a < L) lies in a live tile of a live CTA's loop
def sp_tile_nt(+x: Nat, +it: Nat, +p: Nat, +S: Nat, +L: Nat, +a: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +hal: {Nat.is_lt(a, L) == True{} : Bool},
    +h: {Spec.abs_visit(S, x, it, p, a) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(x, Impl.live_tiles(L)), Nat.is_lt(it, Impl.cta_tiles(Impl.live_tiles(L), x, S))) == True{} : Bool}:
  +c = Nat.add(x, Nat.mul(it, S))
  +n0 = Nat.mul(c, 64n)
  +nt = Impl.live_tiles(L)
  +R2 = Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, a))
  +hn0 = Ar.ar_and_l(Nat.is_le(n0, p), R2, h)
  +hpa = Ar.ar_and_r(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, a), Ar.ar_and_r(Nat.is_le(n0, p), R2, h))
  +hcL = Ar.ar_le_lt_trans(n0, p, L, hn0, Ar.ar_le_lt_trans(p, a, L, hpa, hal))
  +hc = sp_lt_cdiv(c, L, 64n, {==}, hcL)
  +hx = Ar.ar_le_lt_trans(x, c, nt, Ar.ar_le_add_r(x, Nat.mul(it, S)), hc)
  +hit = sp_lt_cdiv(it, Nat.sub(nt, x), S, spos,
    Ar.ard_tr(Nat.is_lt(Nat.mul(it, S), Nat.sub(nt, x)), Nat.is_lt(c, nt), Ar.ar_lt_sub_iff(nt, x, Nat.mul(it, S)), hc))
  Ar.ar_and_intro(Nat.is_lt(x, nt), Nat.is_lt(it, Impl.cta_tiles(nt, x, S)), hx, hit)

# tile_visits is the absolute tile membership (row_invariant (a))
def sp_tile_visit(+x: Nat, +it: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tile_visits(x, it, p, Nat.add(d, q), S, q, j) == Spec.abs_visit(S, x, it, p, Nat.add(d, j)) : Bool}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +nt = Impl.live_tiles(L)
  +n0 = Impl.tile_n0(x, it, S)
  +R = Spec.abs_visit(S, x, it, p, a)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  %Equal.sym(Nat, Nat.sub(L, q), d, sp_qabs(d, q)) : {Bool.and(Nat.is_lt(x, nt), Bool.and(Nat.is_lt(it, Impl.cta_tiles(nt, x, S)), Bool.and(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, Nat.add(_, j)))))) == R : Bool}
  sp_keep2(Nat.is_lt(x, nt), Nat.is_lt(it, Impl.cta_tiles(nt, x, S)), R, h => sp_tile_nt(x, it, p, S, L, a, spos, hal, h))

def sp_tile(+x: Nat, +it: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tile_hits(x, it, p, Nat.add(d, q), S, q, j) == Spec.once(Spec.abs_visit(S, x, it, p, Nat.add(d, j))) : Nat}:
  +av = Spec.abs_visit(S, x, it, p, Nat.add(d, j))
  %Equal.sym(Bool, Impl.tile_visits(x, it, p, Nat.add(d, q), S, q, j), av, sp_tile_visit(x, it, p, d, q, S, j, spos, row)) : {Impl.bit(_) == Spec.once(av) : Nat}
  sp_bit_once(av)

# ---------------------------------------------------------------------------------------------
# Slot (CTA) level

# Absolute tile membership, for the conjunct value s, is s && c == p / 64
def sp_core(+c: Nat, +p: Nat, +s: Bool)
  -> {Bool.and(Nat.is_le(Nat.mul(c, 64n), p), Bool.and(Nat.is_lt(p, Nat.add(Nat.mul(c, 64n), 64n)), s)) ==
     Bool.and(s, Nat.is_eq(c, Nat.div(p, 64n))) : Bool}:
  match s:
    case False{}:
      sp_and3_false(Nat.is_le(Nat.mul(c, 64n), p), Nat.is_lt(p, Nat.add(Nat.mul(c, 64n), 64n)))
    case True{}:
      +m = Nat.mul(c, 64n)
      +t = Nat.div(p, 64n)
      +z = Nat.is_lt(p, Nat.add(m, 64n))
      %Equal.sym(Bool, Bool.and(z, True{}), z, sp_and_true_r(z)) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, t) : Bool}
      %Equal.sym(Nat, Nat.add(m, 64n), Nat.add(64n, m), Ar.ar_add_comm(m, 64n)) : {Bool.and(Nat.is_le(m, p), Nat.is_lt(p, _)) == Nat.is_eq(c, t) : Bool}
      %Ar.ar_div_lt(1n+c, p, 64n, {==}) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, t) : Bool}
      %Equal.sym(Bool, Nat.is_le(m, p), Nat.is_le(c, t), Ar.ar_div_le(c, p, 64n, {==})) : {Bool.and(_, Nat.is_lt(t, 1n+c)) == Nat.is_eq(c, t) : Bool}
      sp_le_lt_eq(c, t)

def sp_split_fwd(+x: Nat, +it: Nat, +t: Nat, +S: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +h: {Nat.is_eq(Nat.add(x, Nat.mul(it, S)), t) == True{} : Bool})
  -> {Bool.and(Nat.is_eq(Nat.mod(t, S), x), Nat.is_eq(it, Nat.div(t, S))) == True{} : Bool}:
  +r = Nat.mod(t, S)
  +q = Nat.div(t, S)
  +c = Nat.add(x, Nat.mul(it, S))
  +hct = Ar.ar_eq_true(c, t, h)
  +same = Equal.trans(Nat, Nat.add(Nat.mul(it, S), x), c, Nat.add(Nat.mul(q, S), r),
    Ar.ar_add_comm(Nat.mul(it, S), x),
    Equal.trans(Nat, c, t, Nat.add(Nat.mul(q, S), r), hct,
      Equal.sym(Nat, Nat.add(Nat.mul(q, S), r), t, Ar.ard_dm_eq(t, S, spos))))
  +hiq = sp_eq_of(it, q, Ar.ard_fst({it == q : Nat}, {x == r : Nat}, Ar.ar_divmod_inj(it, x, q, r, S, xs, Ar.ard_dm_lt(t, S, spos), same)))
  +hrx = sp_eq_of(r, x, Equal.sym(Nat, x, r, Ar.ard_snd({it == q : Nat}, {x == r : Nat}, Ar.ar_divmod_inj(it, x, q, r, S, xs, Ar.ard_dm_lt(t, S, spos), same))))
  Ar.ar_and_intro(Nat.is_eq(r, x), Nat.is_eq(it, q), hrx, hiq)

def sp_split_bwd(+x: Nat, +it: Nat, +t: Nat, +S: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +h: {Bool.and(Nat.is_eq(Nat.mod(t, S), x), Nat.is_eq(it, Nat.div(t, S))) == True{} : Bool})
  -> {Nat.is_eq(Nat.add(x, Nat.mul(it, S)), t) == True{} : Bool}:
  +r = Nat.mod(t, S)
  +q = Nat.div(t, S)
  +hrx = Ar.ar_eq_true(r, x, Ar.ar_and_l(Nat.is_eq(r, x), Nat.is_eq(it, q), h))
  +hiq = Ar.ar_eq_true(it, q, Ar.ar_and_r(Nat.is_eq(r, x), Nat.is_eq(it, q), h))
  +hct = Equal.trans(Nat, Nat.add(x, Nat.mul(it, S)), Nat.add(r, Nat.mul(it, S)), t,
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(it, S)), x, r, Equal.sym(Nat, r, x, hrx)),
    Equal.trans(Nat, Nat.add(r, Nat.mul(it, S)), Nat.add(r, Nat.mul(q, S)), t,
      Equal.cong(Nat, Nat, z => Nat.add(r, Nat.mul(z, S)), it, q, hiq),
      Equal.trans(Nat, Nat.add(r, Nat.mul(q, S)), Nat.add(Nat.mul(q, S), r), t,
        Ar.ar_add_comm(r, Nat.mul(q, S)), Ar.ard_dm_eq(t, S, spos))))
  sp_eq_of(Nat.add(x, Nat.mul(it, S)), t, hct)

# For x < S: tile x + it S is tile t iff t mod S == x and t / S == it
def sp_split(+x: Nat, +it: Nat, +t: Nat, +S: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool})
  -> {Nat.is_eq(Nat.add(x, Nat.mul(it, S)), t) == Bool.and(Nat.is_eq(Nat.mod(t, S), x), Nat.is_eq(it, Nat.div(t, S))) : Bool}:
  Ar.ar_bool_ext(Nat.is_eq(Nat.add(x, Nat.mul(it, S)), t), Bool.and(Nat.is_eq(Nat.mod(t, S), x), Nat.is_eq(it, Nat.div(t, S))),
    h => sp_split_fwd(x, it, t, S, spos, xs, h), h => sp_split_bwd(x, it, t, S, spos, h))

# Tile it of CTA x < S holds a seen p iff p is in slot x and it == (p / 64) / S
def sp_visit(+S: Nat, +x: Nat, +it: Nat, +p: Nat, +a: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool})
  -> {Spec.abs_visit(S, x, it, p, a) ==
     Bool.and(Spec.abs_in_slot(S, x, p, a), Nat.is_eq(it, Nat.div(Nat.div(p, 64n), S))) : Bool}:
  +c = Nat.add(x, Nat.mul(it, S))
  +t = Nat.div(p, 64n)
  +sv = Nat.is_le(p, a)
  +E = Nat.is_eq(Nat.mod(t, S), x)
  +I = Nat.is_eq(it, Nat.div(t, S))
  Equal.trans(Bool, Spec.abs_visit(S, x, it, p, a), Bool.and(sv, Nat.is_eq(c, t)), Bool.and(Bool.and(E, sv), I),
    sp_core(c, p, sv),
    Equal.trans(Bool, Bool.and(sv, Nat.is_eq(c, t)), Bool.and(sv, Bool.and(E, I)), Bool.and(Bool.and(E, sv), I),
      Equal.cong(Bool, Bool, z => Bool.and(sv, z), Nat.is_eq(c, t), Bool.and(E, I), sp_split(x, it, t, S, spos, xs)),
      sp_shuffle(sv, E, I)))

# tiles(n) == bit(in_slot && (p / 64) / S < n)
def sp_tiles(+n: Nat, +x: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.tiles(n, x, p, Nat.add(d, q), S, q, j) ==
     Impl.bit(Bool.and(Spec.abs_in_slot(S, x, p, Nat.add(d, j)), Nat.is_lt(Nat.div(Nat.div(p, 64n), S), n))) : Nat}:
  match n:
    case 0n:
      sp_zero(Spec.abs_in_slot(S, x, p, Nat.add(d, j)), Nat.div(Nat.div(p, 64n), S))
    case 1n+it:
      +L = Nat.add(d, q)
      +a = Nat.add(d, j)
      +Y = Spec.abs_in_slot(S, x, p, a)
      +qq = Nat.div(Nat.div(p, 64n), S)
      %Equal.sym(Nat, Impl.tiles(it, x, p, L, S, q, j), Impl.bit(Bool.and(Y, Nat.is_lt(qq, it))), sp_tiles(it, x, p, d, q, S, j, spos, xs, row)) : {Nat.add(_, Impl.tile_hits(x, it, p, L, S, q, j)) == Impl.bit(Bool.and(Y, Nat.is_lt(qq, 1n+it))) : Nat}
      %Equal.sym(Bool, Impl.tile_visits(x, it, p, L, S, q, j), Spec.abs_visit(S, x, it, p, a), sp_tile_visit(x, it, p, d, q, S, j, spos, row)) : {Nat.add(Impl.bit(Bool.and(Y, Nat.is_lt(qq, it))), Impl.bit(_)) == Impl.bit(Bool.and(Y, Nat.is_lt(qq, 1n+it))) : Nat}
      %Equal.sym(Bool, Spec.abs_visit(S, x, it, p, a), Bool.and(Y, Nat.is_eq(it, qq)), sp_visit(S, x, it, p, a, spos, xs)) : {Nat.add(Impl.bit(Bool.and(Y, Nat.is_lt(qq, it))), Impl.bit(_)) == Impl.bit(Bool.and(Y, Nat.is_lt(qq, 1n+it))) : Nat}
      sp_step_s(Y, it, qq)

# A seen position of slot x lies in one of CTA x's ntiles tiles
def sp_slot_nt(+x: Nat, +p: Nat, +S: Nat, +L: Nat, +a: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +hal: {Nat.is_lt(a, L) == True{} : Bool},
    +h: {Spec.abs_in_slot(S, x, p, a) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(Nat.div(p, 64n), S), Impl.cta_tiles(Impl.live_tiles(L), x, S)) == True{} : Bool}:
  +t = Nat.div(p, 64n)
  +r = Nat.mod(t, S)
  +qq = Nat.div(t, S)
  +nt = Impl.live_tiles(L)
  +mq = Nat.mul(qq, S)
  +hrx = Ar.ar_eq_true(r, x, Ar.ar_and_l(Nat.is_eq(r, x), Nat.is_le(p, a), h))
  +hpa = Ar.ar_and_r(Nat.is_eq(r, x), Nat.is_le(p, a), h)
  +htL = Ar.ar_le_lt_trans(Nat.mul(t, 64n), p, L, Ar.ard_le_mul_div(p, 64n, {==}), Ar.ar_le_lt_trans(p, a, L, hpa, hal))
  +ht = sp_lt_cdiv(t, L, 64n, {==}, htL)
  +e = Equal.trans(Nat, Nat.add(x, mq), Nat.add(r, mq), t,
    Equal.cong(Nat, Nat, z => Nat.add(z, mq), x, r, Equal.sym(Nat, r, x, hrx)),
    Equal.trans(Nat, Nat.add(r, mq), Nat.add(mq, r), t, Ar.ar_add_comm(r, mq), Ar.ard_dm_eq(t, S, spos)))
  +hxq = Ar.ard_tr(Nat.is_lt(Nat.add(x, mq), nt), Nat.is_lt(t, nt),
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, nt), Nat.add(x, mq), t, e), ht)
  sp_lt_cdiv(qq, Nat.sub(nt, x), S, spos,
    Ar.ard_tr(Nat.is_lt(mq, Nat.sub(nt, x)), Nat.is_lt(Nat.add(x, mq), nt), Ar.ar_lt_sub_iff(nt, x, mq), hxq))

# cta_hits(x) == bit(abs_in_slot(x)) for x < S (row_invariant (b))
def sp_slot(+x: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.cta_hits(x, p, Nat.add(d, q), S, q, j) == Impl.bit(Spec.abs_in_slot(S, x, p, Nat.add(d, j))) : Nat}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +Y = Spec.abs_in_slot(S, x, p, a)
  +qq = Nat.div(Nat.div(p, 64n), S)
  +ct = Impl.cta_tiles(Impl.live_tiles(L), x, S)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  %Equal.sym(Nat, Impl.tiles(ct, x, p, L, S, q, j), Impl.bit(Bool.and(Y, Nat.is_lt(qq, ct))), sp_tiles(ct, x, p, d, q, S, j, spos, xs, row)) : {_ == Impl.bit(Y) : Nat}
  %Equal.sym(Bool, Bool.and(Y, Nat.is_lt(qq, ct)), Y, sp_keep(Y, Nat.is_lt(qq, ct), h => sp_slot_nt(x, p, S, L, a, spos, hal, h))) : {Impl.bit(_) == Impl.bit(Y) : Nat}
  {==}

def sp_slot_once(+x: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, +xs: {Nat.is_lt(x, S) == True{} : Bool},
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.cta_hits(x, p, Nat.add(d, q), S, q, j) == Spec.once(Spec.abs_in_slot(S, x, p, Nat.add(d, j))) : Nat}:
  +Y = Spec.abs_in_slot(S, x, p, Nat.add(d, j))
  Equal.trans(Nat, Impl.cta_hits(x, p, Nat.add(d, q), S, q, j), Impl.bit(Y), Spec.once(Y),
    sp_slot(x, p, d, q, S, j, spos, xs, row), sp_bit_once(Y))

# ---------------------------------------------------------------------------------------------
# attend_once

# ctas_hits(k) == bit(sees && (p / 64) mod S < k) for k <= S
def sp_ctas(+k: Nat, +p: Nat, +d: Nat, +q: Nat, +S: Nat, +j: Nat,
    +spos: {Nat.is_lt(0n, S) == True{} : Bool}, hk: {Nat.is_le(k, S) == True{} : Bool},
    +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.ctas_hits(k, p, Nat.add(d, q), S, q, j) ==
     Impl.bit(Bool.and(Spec.sees(p, d, j), Nat.is_lt(Nat.mod(Nat.div(p, 64n), S), k))) : Nat}:
  match k:
    case 0n:
      sp_zero(Spec.sees(p, d, j), Nat.mod(Nat.div(p, 64n), S))
    case 1n+x:
      +L = Nat.add(d, q)
      +a = Nat.add(d, j)
      +sv = Spec.sees(p, d, j)
      +r = Nat.mod(Nat.div(p, 64n), S)
      +hx = Ar.ard_tr(Nat.is_lt(x, S), Nat.is_le(1n+x, S), Ar.ar_lt_succ_le(x, S), hk)
      %Equal.sym(Nat, Impl.ctas_hits(x, p, L, S, q, j), Impl.bit(Bool.and(sv, Nat.is_lt(r, x))), sp_ctas(x, p, d, q, S, j, spos, Ar.ar_lt_le(x, S, hx), row)) : {Nat.add(_, Impl.cta_hits(x, p, L, S, q, j)) == Impl.bit(Bool.and(sv, Nat.is_lt(r, 1n+x))) : Nat}
      %Equal.sym(Nat, Impl.cta_hits(x, p, L, S, q, j), Impl.bit(Spec.abs_in_slot(S, x, p, a)), sp_slot(x, p, d, q, S, j, spos, hx, row)) : {Nat.add(Impl.bit(Bool.and(sv, Nat.is_lt(r, x))), _) == Impl.bit(Bool.and(sv, Nat.is_lt(r, 1n+x))) : Nat}
      %Ar.p2_and_comm(sv, Nat.is_eq(r, x)) : {Nat.add(Impl.bit(Bool.and(sv, Nat.is_lt(r, x))), Impl.bit(_)) == Impl.bit(Bool.and(sv, Nat.is_lt(r, 1n+x))) : Nat}
      %sp_eq_sym(x, r) : {Nat.add(Impl.bit(Bool.and(sv, Nat.is_lt(r, x))), Impl.bit(Bool.and(sv, _))) == Impl.bit(Bool.and(sv, Nat.is_lt(r, 1n+x))) : Nat}
      sp_step_s(sv, x, r)

def Laws.attend_once(depth, q_len, S, qpos, p, spos, row):
  +sp = spos
  +rw = row
  +sv = Spec.sees(p, depth, qpos)
  +r = Nat.mod(Nat.div(p, 64n), S)
  %Equal.sym(Nat, Impl.ctas_hits(S, p, Nat.add(depth, q_len), S, q_len, qpos), Impl.bit(Bool.and(sv, Nat.is_lt(r, S))), sp_ctas(S, p, depth, q_len, S, qpos, sp, Ar.ar_le_refl(S), rw)) : {_ == Spec.once(sv) : Nat}
  %Equal.sym(Bool, Nat.is_lt(r, S), True{}, Ar.ard_dm_lt(Nat.div(p, 64n), S, sp)) : {Impl.bit(Bool.and(sv, _)) == Spec.once(sv) : Nat}
  %Equal.sym(Bool, Bool.and(sv, True{}), sv, sp_and_true_r(sv)) : {Impl.bit(_) == Spec.once(sv) : Nat}
  sp_bit_once(sv)

# ---------------------------------------------------------------------------------------------
# slot_once

def sp_gate_bit(+b: Bool, +e: Bool) -> {Impl.gate(b, Impl.bit(e)) == Impl.bit(Bool.and(b, e)) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def sp_store_fwd(+x: Nat, +s: Nat, +n: Nat,
    +h: {Bool.and(Nat.is_lt(x, n), Nat.is_eq(x, s)) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(s, n), Nat.is_eq(x, s)) == True{} : Bool}:
  +hl = Ar.ar_and_l(Nat.is_lt(x, n), Nat.is_eq(x, s), h)
  +he = Ar.ar_and_r(Nat.is_lt(x, n), Nat.is_eq(x, s), h)
  +hs = Ar.ard_rt(Nat.is_lt(x, n), Nat.is_lt(s, n),
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, n), x, s, Ar.ar_eq_true(x, s, he)), hl)
  Ar.ar_and_intro(Nat.is_lt(s, n), Nat.is_eq(x, s), hs, he)

def sp_store_bwd(+x: Nat, +s: Nat, +n: Nat,
    +h: {Bool.and(Nat.is_lt(s, n), Nat.is_eq(x, s)) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(x, n), Nat.is_eq(x, s)) == True{} : Bool}:
  +hl = Ar.ar_and_l(Nat.is_lt(s, n), Nat.is_eq(x, s), h)
  +he = Ar.ar_and_r(Nat.is_lt(s, n), Nat.is_eq(x, s), h)
  +hx = Ar.ard_tr(Nat.is_lt(x, n), Nat.is_lt(s, n),
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, n), x, s, Ar.ar_eq_true(x, s, he)), hl)
  Ar.ar_and_intro(Nat.is_lt(x, n), Nat.is_eq(x, s), hx, he)

# CTA x stores slot s only when x == s, so its early-return guard x < n is s < n
def sp_store(+x: Nat, +s: Nat, +n: Nat)
  -> {Bool.and(Nat.is_lt(x, n), Nat.is_eq(x, s)) == Bool.and(Nat.is_lt(s, n), Nat.is_eq(x, s)) : Bool}:
  Ar.ar_bool_ext(Bool.and(Nat.is_lt(x, n), Nat.is_eq(x, s)), Bool.and(Nat.is_lt(s, n), Nat.is_eq(x, s)),
    h => sp_store_fwd(x, s, n, h), h => sp_store_bwd(x, s, n, h))

# writes(k) == bit(s < n_tiles && s < k)
def sp_writes(+k: Nat, +s: Nat, +L: Nat)
  -> {Impl.writes(k, s, L) == Impl.bit(Bool.and(Nat.is_lt(s, Impl.live_tiles(L)), Nat.is_lt(s, k))) : Nat}:
  match k:
    case 0n:
      sp_zero(Nat.is_lt(s, Impl.live_tiles(L)), s)
    case 1n+x:
      +nt = Impl.live_tiles(L)
      +B = Nat.is_lt(s, nt)
      %Equal.sym(Nat, Impl.writes(x, s, L), Impl.bit(Bool.and(B, Nat.is_lt(s, x))), sp_writes(x, s, L)) : {Nat.add(_, Impl.cta_store(x, s, L)) == Impl.bit(Bool.and(B, Nat.is_lt(s, 1n+x))) : Nat}
      %Equal.sym(Nat, Impl.gate(Nat.is_lt(x, nt), Impl.bit(Nat.is_eq(x, s))), Impl.bit(Bool.and(Nat.is_lt(x, nt), Nat.is_eq(x, s))), sp_gate_bit(Nat.is_lt(x, nt), Nat.is_eq(x, s))) : {Nat.add(Impl.bit(Bool.and(B, Nat.is_lt(s, x))), _) == Impl.bit(Bool.and(B, Nat.is_lt(s, 1n+x))) : Nat}
      %Equal.sym(Bool, Bool.and(Nat.is_lt(x, nt), Nat.is_eq(x, s)), Bool.and(B, Nat.is_eq(x, s)), sp_store(x, s, nt)) : {Nat.add(Impl.bit(Bool.and(B, Nat.is_lt(s, x))), Impl.bit(_)) == Impl.bit(Bool.and(B, Nat.is_lt(s, 1n+x))) : Nat}
      sp_step_s(B, x, s)

def Laws.slot_once(L, S, s):
  +nt = Impl.live_tiles(L)
  +B = Nat.is_lt(s, nt)
  %Equal.sym(Nat, Impl.writes(S, s, L), Impl.bit(Bool.and(B, Nat.is_lt(s, S))), sp_writes(S, s, L)) : {_ == Spec.once(Nat.is_lt(s, Impl.live_slots(nt, S))) : Nat}
  %Equal.sym(Bool, Nat.is_lt(s, Nat.min(nt, S)), Bool.and(B, Nat.is_lt(s, S)), Ar.ar_min_lt(s, nt, S)) : {Impl.bit(Bool.and(B, Nat.is_lt(s, S))) == Spec.once(_) : Nat}
  sp_bit_once(Bool.and(B, Nat.is_lt(s, S)))

# ---------------------------------------------------------------------------------------------
# Combine plan

def sp_keep_case(b: Bool, -s0: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>,
    t: {b == True{} : Bool} -> {(s0 <> xs) == ys : List<&2, Nat>},
    f: {b == False{} : Bool} -> {xs == ys : List<&2, Nat>})
  -> {Impl.keep(b, s0, xs) == ys : List<&2, Nat>}:
  match b:
    case False{}:
      f({==})
    case True{}:
      t({==})

def sp_merge_in(+D: Nat, +s0: Nat, +r: Nat, h: {Nat.is_le(s0, D) == True{} : Bool})
  -> {(s0 <> Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0)) == Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0) : List<&2, Nat>}:
  %Equal.sym(Nat, Nat.sub(1n+D, s0), 1n+Nat.sub(D, s0), sp_sub_succ(D, s0, h)) : {(s0 <> Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0)) == Spec.range.go(Nat.min(1n+r, _), s0) : List<&2, Nat>}
  {==}

def sp_merge_out(+D: Nat, +s0: Nat, +r: Nat, h: {Nat.is_le(s0, D) == False{} : Bool})
  -> {Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0) == Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0) : List<&2, Nat>}:
  +hlt = Equal.trans(Bool, Nat.is_lt(D, s0), Bool.not(Nat.is_le(s0, D)), True{}, Ar.ar_lt_not_le(D, s0),
    Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_le(s0, D), False{}, h))
  +h1 = Ar.ar_lt_le(D, s0, hlt)
  +h2 = Ar.ard_rt(Nat.is_lt(D, s0), Nat.is_le(1n+D, s0), Ar.ar_lt_succ_le(D, s0), hlt)
  %Equal.sym(Nat, Nat.sub(D, s0), 0n, sp_sub_le0(D, s0, h1)) : {Spec.range.go(Nat.min(r, _), 1n+s0) == Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.sub(1n+D, s0), 0n, sp_sub_le0(1n+D, s0, h2)) : {Spec.range.go(Nat.min(r, 0n), 1n+s0) == Spec.range.go(Nat.min(1n+r, _), s0) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.min(r, 0n), 0n, sp_min_zero_r(r)) : {Spec.range.go(_, 1n+s0) == Spec.range.go(Nat.min(1n+r, 0n), s0) : List<&2, Nat>}
  {==}

# Filtering [s0, s0 + n) by 64 s <= a leaves [s0, min(s0 + n, a / 64 + 1))
def sp_merge(+n: Nat, +s0: Nat, +a: Nat)
  -> {Impl.row_filter(Impl.combine.go(n, s0), a) == Spec.range.go(Nat.min(n, Nat.sub(1n+Nat.div(a, 64n), s0)), s0) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+r:
      +D = Nat.div(a, 64n)
      %Equal.sym(List<&2, Nat>, Impl.row_filter(Impl.combine.go(r, 1n+s0), a), Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0), sp_merge(r, 1n+s0, a)) : {Impl.keep(Nat.is_le(Nat.mul(s0, 64n), a), s0, _) == Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0) : List<&2, Nat>}
      %Equal.sym(Bool, Nat.is_le(Nat.mul(s0, 64n), a), Nat.is_le(s0, D), Ar.ar_div_le(s0, a, 64n, {==})) : {Impl.keep(_, s0, Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0)) == Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0) : List<&2, Nat>}
      sp_keep_case(Nat.is_le(s0, D), s0, Spec.range.go(Nat.min(r, Nat.sub(D, s0)), 1n+s0), Spec.range.go(Nat.min(1n+r, Nat.sub(1n+D, s0)), s0),
        h => sp_merge_in(D, s0, r, h), h => sp_merge_out(D, s0, r, h))

# merged == abs_slots (row_invariant (c))
def sp_merged(+d: Nat, +q: Nat, +S: Nat, +j: Nat, +row: {Nat.is_lt(j, q) == True{} : Bool})
  -> {Impl.merged(Nat.add(d, q), S, q, j) == Spec.abs_slots(S, Nat.add(d, j)) : List<&2, Nat>}:
  +L = Nat.add(d, q)
  +a = Nat.add(d, j)
  +D = Nat.div(a, 64n)
  +nt = Impl.live_tiles(L)
  +hal = Ar.ard_tr(Nat.is_lt(a, L), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(d, j, q), row)
  +hD = sp_lt_cdiv(D, L, 64n, {==}, Ar.ar_le_lt_trans(Nat.mul(D, 64n), a, L, Ar.ard_le_mul_div(a, 64n, {==}), hal))
  +hD1 = Ar.ard_rt(Nat.is_lt(D, nt), Nat.is_le(1n+D, nt), Ar.ar_lt_succ_le(D, nt), hD)
  %Equal.sym(Nat, Nat.sub(L, q), d, sp_qabs(d, q)) : {Impl.row_filter(Impl.combine.go(Nat.min(nt, S), 0n), Nat.add(_, j)) == Spec.abs_slots(S, a) : List<&2, Nat>}
  Equal.trans(List<&2, Nat>, Impl.row_filter(Impl.combine.go(Nat.min(nt, S), 0n), a),
    Spec.range.go(Nat.min(Nat.min(nt, S), 1n+D), 0n), Spec.abs_slots(S, a),
    sp_merge(Nat.min(nt, S), 0n, a),
    Equal.cong(Nat, List<&2, Nat>, z => Spec.range.go(z, 0n), Nat.min(Nat.min(nt, S), 1n+D), Nat.min(S, 1n+D),
      sp_min_absorb(1n+D, nt, S, hD1)))

# ---------------------------------------------------------------------------------------------
# Row invariance

def Laws.row_invariant(depth, q_len, S, qpos, x, it, p, xb, row):
  +xs = xb
  +rw = row
  +sp = Ar.ard_pos(x, S, xs)
  (sp_tile(x, it, p, depth, q_len, S, qpos, sp, rw), sp_slot_once(x, p, depth, q_len, S, qpos, sp, xs, rw),
    sp_merged(depth, q_len, S, qpos, rw))

def Laws.row_invariant_rounds(d1, q1, j1, d2, q2, j2, S, x, it, p, xb, row1, row2, same):
  +xs = xb
  +r1 = row1
  +r2 = row2
  +sm = same
  +sp = Ar.ard_pos(x, S, xs)
  +a1 = Nat.add(d1, j1)
  +a2 = Nat.add(d2, j2)
  +T1 = Impl.tile_hits(x, it, p, Nat.add(d1, q1), S, q1, j1)
  +T2 = Impl.tile_hits(x, it, p, Nat.add(d2, q2), S, q2, j2)
  +C1 = Impl.cta_hits(x, p, Nat.add(d1, q1), S, q1, j1)
  +C2 = Impl.cta_hits(x, p, Nat.add(d2, q2), S, q2, j2)
  +M1 = Impl.merged(Nat.add(d1, q1), S, q1, j1)
  +M2 = Impl.merged(Nat.add(d2, q2), S, q2, j2)
  (Equal.trans(Nat, T1, Spec.once(Spec.abs_visit(S, x, it, p, a1)), T2, sp_tile(x, it, p, d1, q1, S, j1, sp, r1),
     Equal.trans(Nat, Spec.once(Spec.abs_visit(S, x, it, p, a1)), Spec.once(Spec.abs_visit(S, x, it, p, a2)), T2,
       Equal.cong(Nat, Nat, z => Spec.once(Spec.abs_visit(S, x, it, p, z)), a1, a2, sm),
       Equal.sym(Nat, T2, Spec.once(Spec.abs_visit(S, x, it, p, a2)), sp_tile(x, it, p, d2, q2, S, j2, sp, r2)))),
   Equal.trans(Nat, C1, Spec.once(Spec.abs_in_slot(S, x, p, a1)), C2, sp_slot_once(x, p, d1, q1, S, j1, sp, xs, r1),
     Equal.trans(Nat, Spec.once(Spec.abs_in_slot(S, x, p, a1)), Spec.once(Spec.abs_in_slot(S, x, p, a2)), C2,
       Equal.cong(Nat, Nat, z => Spec.once(Spec.abs_in_slot(S, x, p, z)), a1, a2, sm),
       Equal.sym(Nat, C2, Spec.once(Spec.abs_in_slot(S, x, p, a2)), sp_slot_once(x, p, d2, q2, S, j2, sp, xs, r2)))),
   Equal.trans(List<&2, Nat>, M1, Spec.abs_slots(S, a1), M2, sp_merged(d1, q1, S, j1, r1),
     Equal.trans(List<&2, Nat>, Spec.abs_slots(S, a1), Spec.abs_slots(S, a2), M2,
       Equal.cong(Nat, List<&2, Nat>, z => Spec.abs_slots(S, z), a1, a2, sm),
       Equal.sym(List<&2, Nat>, M2, Spec.abs_slots(S, a2), sp_merged(d2, q2, S, j2, r2)))))

# ---------------------------------------------------------------------------------------------
# Combine skip test

def Laws.skip_witness(depth, q_len, S, qpos, s, sb, row, kept):
  +sbx = sb
  +rw = row
  +sp = Ar.ard_pos(s, S, sbx)
  +L = Nat.add(depth, q_len)
  +a = Nat.add(depth, qpos)
  +m = Nat.mul(s, 64n)
  +hk = Ar.ard_rt(Nat.is_le(m, Nat.add(Nat.sub(L, q_len), qpos)), Nat.is_le(m, a),
    Equal.cong(Nat, Bool, z => Nat.is_le(m, Nat.add(z, qpos)), Nat.sub(L, q_len), depth, sp_qabs(depth, q_len)), kept)
  +hdiv = Equal.trans(Nat, Nat.div(m, 64n), Nat.div(Nat.add(m, 0n), 64n), s,
    Equal.cong(Nat, Nat, z => Nat.div(z, 64n), m, Nat.add(m, 0n), Equal.sym(Nat, Nat.add(m, 0n), m, Ar.ar_add_zero_r(m))),
    Ar.ard_fst({Nat.div(Nat.add(Nat.mul(s, 64n), 0n), 64n) == s : Nat}, {Nat.mod(Nat.add(Nat.mul(s, 64n), 0n), 64n) == 0n : Nat},
      Ar.ar_div_unique(s, 0n, 64n, {==})))
  +hmod = Ar.ard_snd({Nat.div(Nat.add(Nat.mul(0n, S), s), S) == 0n : Nat}, {Nat.mod(Nat.add(Nat.mul(0n, S), s), S) == s : Nat},
    Ar.ar_div_unique(0n, s, S, sbx))
  +he = sp_eq_of(Nat.mod(Nat.div(m, 64n), S), s,
    Equal.trans(Nat, Nat.mod(Nat.div(m, 64n), S), Nat.mod(s, S), s,
      Equal.cong(Nat, Nat, z => Nat.mod(z, S), Nat.div(m, 64n), s, hdiv), hmod))
  +hin = Ar.ar_and_intro(Nat.is_eq(Nat.mod(Nat.div(m, 64n), S), s), Nat.is_le(m, a), he, hk)
  %Equal.sym(Nat, Impl.cta_hits(s, m, L, S, q_len, qpos), Impl.bit(Spec.abs_in_slot(S, s, m, a)), sp_slot(s, m, depth, q_len, S, qpos, sp, sbx, rw)) : {_ == 1n : Nat}
  %Equal.sym(Bool, Spec.abs_in_slot(S, s, m, a), True{}, hin) : {Impl.bit(_) == 1n : Nat}
  {==}

# A tile of CTA s holding a position the row sees starts at or below the row: 64 s <= qa
def sp_tile_le(+s: Nat, +it: Nat, +p: Nat, +S: Nat, +qa: Nat,
    +h: {Bool.and(Nat.is_le(Impl.tile_n0(s, it, S), p),
      Bool.and(Nat.is_lt(p, Nat.add(Impl.tile_n0(s, it, S), 64n)), Nat.is_le(p, qa))) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(s, 64n), qa) == True{} : Bool}:
  +n0 = Impl.tile_n0(s, it, S)
  +R2 = Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, qa))
  +hn0 = Ar.ar_and_l(Nat.is_le(n0, p), R2, h)
  +hpa = Ar.ar_and_r(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, qa), Ar.ar_and_r(Nat.is_le(n0, p), R2, h))
  +hs = Ar.ar_le_mul_mono(s, Nat.add(s, Nat.mul(it, S)), 64n, Ar.ar_le_add_r(s, Nat.mul(it, S)))
  Ar.ar_le_trans(Nat.mul(s, 64n), p, qa, Ar.ar_le_trans(Nat.mul(s, 64n), n0, p, hs, hn0), hpa)

# A skipped slot's CTA puts nothing into the row, whatever its tile count
def sp_tiles_none(+n: Nat, +s: Nat, +p: Nat, +L: Nat, +S: Nat, +q: Nat, +j: Nat,
    +sk: {Nat.is_le(Nat.mul(s, 64n), Impl.q_abs(L, q, j)) == False{} : Bool})
  -> {Impl.tiles(n, s, p, L, S, q, j) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+it:
      +qa = Impl.q_abs(L, q, j)
      +n0 = Impl.tile_n0(s, it, S)
      +nt = Impl.live_tiles(L)
      +A = Nat.is_lt(s, nt)
      +B = Nat.is_lt(it, Impl.cta_tiles(nt, s, S))
      +R = Bool.and(Nat.is_le(n0, p), Bool.and(Nat.is_lt(p, Nat.add(n0, 64n)), Nat.is_le(p, qa)))
      +no = Ar.ar_not_true(R, h => Ar.ar_false_ne(Nat.is_le(Nat.mul(s, 64n), qa), sk, sp_tile_le(s, it, p, S, qa, h)))
      %Equal.sym(Nat, Impl.tiles(it, s, p, L, S, q, j), 0n, sp_tiles_none(it, s, p, L, S, q, j, sk)) : {Nat.add(_, Impl.tile_hits(s, it, p, L, S, q, j)) == 0n : Nat}
      %Equal.sym(Bool, R, False{}, no) : {Impl.bit(Bool.and(A, Bool.and(B, _))) == 0n : Nat}
      %Equal.sym(Bool, Bool.and(A, Bool.and(B, False{})), False{}, sp_and3_false(A, B)) : {Impl.bit(_) == 0n : Nat}
      {==}

def Laws.skip_sound(depth, q_len, S, qpos, s, p, row, skipped):
  +L = Nat.add(depth, q_len)
  sp_tiles_none(Impl.cta_tiles(Impl.live_tiles(L), s, S), s, p, L, S, q_len, qpos, skipped)
