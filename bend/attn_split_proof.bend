# Proofs of the verify-attention split/combine partition laws (attn_split_laws.bend) about the Bend
# model attn_split.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign
# proof code or answer tables. Nat arithmetic lemmas come from the proven m16 partition library.
import Base
import ./attn_split.bend as Impl
import ./attn_split_spec.bend as Spec
import ./attn_split_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def as_sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (y + (1 + bp)) - 1 == y + bp
def as_pred(+y: Nat, +bp: Nat) -> {Nat.sub(Nat.add(y, 1n+bp), 1n) == Nat.add(y, bp) : Nat}:
  %Equal.sym(Nat, Nat.add(y, 1n+bp), 1n+Nat.add(y, bp), Ar.ar_add_succ_r(y, bp)) : {Nat.sub(_, 1n) == Nat.add(y, bp) : Nat}
  as_sub_zero(Nat.add(y, bp))

# y <= ceil(y / b) * b for b >= 1
def as_up(+y: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_le(y, Nat.mul(Impl.cdiv(y, b), b)) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_le(y, Nat.mul(Impl.cdiv(y, 0n), 0n)) == True{} : Bool}, Ar.ar_false_true(pos))
    case 1n+bp:
      %Equal.sym(Nat, Nat.sub(Nat.add(y, 1n+bp), 1n), Nat.add(y, bp), as_pred(y, bp)) : {Nat.is_le(y, Nat.mul(Nat.div(_, 1n+bp), 1n+bp)) == True{} : Bool}
      +a = Nat.add(y, bp)
      +m = Nat.mul(Nat.div(a, 1n+bp), 1n+bp)
      +h1 = Ar.ard_rt(Nat.is_lt(a, Nat.mul(1n+Nat.div(a, 1n+bp), 1n+bp)), Nat.is_le(a, Nat.add(bp, m)),
        Ar.ar_lt_succ_le(a, 1n+Nat.add(bp, m)), Ar.ard_lt_next(a, 1n+bp, pos))
      +h2 = Ar.ard_rt(Nat.is_le(a, Nat.add(bp, m)), Nat.is_le(Nat.add(bp, y), Nat.add(bp, m)),
        Equal.cong(Nat, Bool, t => Nat.is_le(t, Nat.add(bp, m)), a, Nat.add(bp, y), Ar.ar_add_comm(y, bp)), h1)
      Ar.ard_rt(Nat.is_le(Nat.add(bp, y), Nat.add(bp, m)), Nat.is_le(y, m), Ar.ar_le_add_cancel(bp, y, m), h2)

def as_cpos_zero(ln: Nat, lpos: {Nat.is_lt(0n, ln) == True{} : Bool},
    h: {Nat.is_le(ln, 0n) == True{} : Bool}) -> Empty:
  match ln:
    case 0n:
      Ar.ar_false_true(lpos)
    case 1n+l:
      Ar.ar_false_true(h)

# ceil(L / S) >= 1 for L >= 1, from L <= ceil(L / S) * S
def as_cpos(ln: Nat, cc: Nat, S: Nat, lpos: {Nat.is_lt(0n, ln) == True{} : Bool},
    h: {Nat.is_le(ln, Nat.mul(cc, S)) == True{} : Bool})
  -> {Nat.is_lt(0n, cc) == True{} : Bool}:
  match cc:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, as_cpos_zero(ln, lpos, h))
    case 1n+cp:
      {==}

def as_c_le_sl(+L: Nat, +S: Nat)
  -> {Nat.is_le(Impl.cdiv(L, S), Impl.split_len(L, S)) == True{} : Bool}:
  as_up(Impl.cdiv(L, S), 64n, {==})

# split_len(L, S) >= 1
def as_sl_pos(+L: Nat, +S: Nat, +spos: {Nat.is_lt(0n, S) == True{} : Bool},
    +lpos: {Nat.is_lt(0n, L) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.split_len(L, S)) == True{} : Bool}:
  Ar.ar_lt_le_trans(0n, Impl.cdiv(L, S), Impl.split_len(L, S),
    as_cpos(L, Impl.cdiv(L, S), S, lpos, as_up(L, S, spos)), as_c_le_sl(L, S))

# L <= S * split_len(L, S): the launched splits reach the live length
def as_cover(+L: Nat, +S: Nat, +spos: {Nat.is_lt(0n, S) == True{} : Bool})
  -> {Nat.is_le(L, Nat.mul(S, Impl.split_len(L, S))) == True{} : Bool}:
  %Ar.ar_mul_comm(Impl.split_len(L, S), S) : {Nat.is_le(L, _) == True{} : Bool}
  Ar.ar_le_trans(L, Nat.mul(Impl.cdiv(L, S), S), Nat.mul(Impl.split_len(L, S), S),
    as_up(L, S, spos), Ar.ar_le_mul_mono(Impl.cdiv(L, S), Impl.split_len(L, S), S, as_c_le_sl(L, S)))

# i <= k && k < i + 1 iff i == k
def as_le_lt_eq(+i: Nat, +k: Nat)
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
      as_le_lt_eq(ip, kp)

def as_and3_false(+x: Bool, +y: Bool) -> {Bool.and(x, Bool.and(y, False{})) == False{} : Bool}:
  match x y:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def as_and_true_r(+x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# (s && x) == s when s implies x
def as_keep(+s: Bool, +x: Bool, h: {s == True{} : Bool} -> {x == True{} : Bool})
  -> {Bool.and(s, x) == s : Bool}:
  match s:
    case False{}:
      {==}
    case True{}:
      h({==})

# The split-membership conjuncts of visits, for the conjunct value s (s implies p < L), equal
# s && i == p / sl.
def as_core(+i: Nat, +p: Nat, +sl: Nat, +L: Nat, +s: Bool,
    +pos: {Nat.is_lt(0n, sl) == True{} : Bool},
    +lt: {Bool.and(s, Nat.is_lt(p, L)) == s : Bool})
  -> {Bool.and(Nat.is_le(Nat.mul(i, sl), p),
       Bool.and(Nat.is_lt(p, Nat.min(Nat.add(Nat.mul(i, sl), sl), L)), s)) ==
     Bool.and(s, Nat.is_eq(i, Nat.div(p, sl))) : Bool}:
  match s:
    case False{}:
      as_and3_false(Nat.is_le(Nat.mul(i, sl), p), Nat.is_lt(p, Nat.min(Nat.add(Nat.mul(i, sl), sl), L)))
    case True{}:
      +m = Nat.mul(i, sl)
      +k = Nat.div(p, sl)
      +z = Nat.is_lt(p, Nat.add(m, sl))
      %Equal.sym(Bool, Bool.and(Nat.is_lt(p, Nat.min(Nat.add(m, sl), L)), True{}),
        Nat.is_lt(p, Nat.min(Nat.add(m, sl), L)),
        as_and_true_r(Nat.is_lt(p, Nat.min(Nat.add(m, sl), L)))) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(i, k) : Bool}
      %Equal.sym(Bool, Nat.is_lt(p, Nat.min(Nat.add(m, sl), L)), Bool.and(z, Nat.is_lt(p, L)),
        Ar.ar_min_lt(p, Nat.add(m, sl), L)) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(i, k) : Bool}
      %Equal.sym(Bool, Nat.is_lt(p, L), True{}, lt) : {Bool.and(Nat.is_le(m, p), Bool.and(z, _)) == Nat.is_eq(i, k) : Bool}
      %Equal.sym(Bool, Bool.and(z, True{}), z, as_and_true_r(z)) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(i, k) : Bool}
      %Equal.sym(Nat, Nat.add(m, sl), Nat.add(sl, m), Ar.ar_add_comm(m, sl)) : {Bool.and(Nat.is_le(m, p), Nat.is_lt(p, _)) == Nat.is_eq(i, k) : Bool}
      %Ar.ar_div_lt(1n+i, p, sl, pos) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(i, k) : Bool}
      %Equal.sym(Bool, Nat.is_le(m, p), Nat.is_le(i, k), Ar.ar_div_le(i, p, sl, pos)) : {Bool.and(_, Nat.is_lt(k, 1n+i)) == Nat.is_eq(i, k) : Bool}
      as_le_lt_eq(i, k)

# (depth + q_len) - q_len == depth: the kernel's q_abs = L - q_len + gid is depth + gid
def as_qabs(+depth: Nat, +q_len: Nat) -> {Nat.sub(Nat.add(depth, q_len), q_len) == depth : Nat}:
  %Equal.sym(Nat, Nat.add(depth, q_len), Nat.add(q_len, depth), Ar.ar_add_comm(depth, q_len)) : {Nat.sub(_, q_len) == depth : Nat}
  Ar.ar_add_sub(q_len, depth)

def as_visit(+i: Nat, +p: Nat, +depth: Nat, +q_len: Nat, +S: Nat, +qpos: Nat,
    +pos: {Nat.is_lt(0n, Impl.split_len(Nat.add(depth, q_len), S)) == True{} : Bool},
    +lt: {Bool.and(Spec.sees(p, depth, qpos), Nat.is_lt(p, Nat.add(depth, q_len))) == Spec.sees(p, depth, qpos) : Bool})
  -> {Impl.visits(i, p, Nat.add(depth, q_len), S, q_len, qpos) ==
     Bool.and(Spec.sees(p, depth, qpos), Nat.is_eq(i, Nat.div(p, Impl.split_len(Nat.add(depth, q_len), S)))) : Bool}:
  +L = Nat.add(depth, q_len)
  +sl = Impl.split_len(L, S)
  %Equal.sym(Nat, Nat.sub(L, q_len), depth, as_qabs(depth, q_len)) : {Bool.and(Nat.is_le(Nat.mul(i, sl), p),
      Bool.and(Nat.is_lt(p, Nat.min(Nat.add(Nat.mul(i, sl), sl), L)), Nat.is_le(p, Nat.add(_, qpos)))) ==
    Bool.and(Spec.sees(p, depth, qpos), Nat.is_eq(i, Nat.div(p, sl))) : Bool}
  as_core(i, p, sl, L, Spec.sees(p, depth, qpos), pos, lt)

# add(bit(k < j), bit(j == k)) == bit(k < j + 1)
def as_step(+j: Nat, +k: Nat)
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
      as_step(jp, kp)

def as_step_s(+s: Bool, +j: Nat, +k: Nat)
  -> {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(k, j))), Impl.bit(Bool.and(s, Nat.is_eq(j, k)))) ==
     Impl.bit(Bool.and(s, Nat.is_lt(k, 1n+j))) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      as_step(j, k)

def as_zero(+s: Bool, +k: Nat) -> {0n == Impl.bit(Bool.and(s, Nat.is_lt(k, 0n))) : Nat}:
  match s k:
    case False{} _:
      {==}
    case True{} 0n:
      {==}
    case True{} 1n+kp:
      {==}

# hits(j) == bit(sees && p / sl < j)
def as_hits(+j: Nat, +p: Nat, +depth: Nat, +q_len: Nat, +S: Nat, +qpos: Nat,
    +pos: {Nat.is_lt(0n, Impl.split_len(Nat.add(depth, q_len), S)) == True{} : Bool},
    +lt: {Bool.and(Spec.sees(p, depth, qpos), Nat.is_lt(p, Nat.add(depth, q_len))) == Spec.sees(p, depth, qpos) : Bool})
  -> {Impl.hits(j, p, Nat.add(depth, q_len), S, q_len, qpos) ==
     Impl.bit(Bool.and(Spec.sees(p, depth, qpos), Nat.is_lt(Nat.div(p, Impl.split_len(Nat.add(depth, q_len), S)), j))) : Nat}:
  match j:
    case 0n:
      as_zero(Spec.sees(p, depth, qpos), Nat.div(p, Impl.split_len(Nat.add(depth, q_len), S)))
    case 1n+jp:
      +s = Spec.sees(p, depth, qpos)
      +k = Nat.div(p, Impl.split_len(Nat.add(depth, q_len), S))
      %Equal.sym(Nat, Impl.hits(jp, p, Nat.add(depth, q_len), S, q_len, qpos), Impl.bit(Bool.and(s, Nat.is_lt(k, jp))), as_hits(jp, p, depth, q_len, S, qpos, pos, lt)) : {Nat.add(_, Impl.bit(Impl.visits(jp, p, Nat.add(depth, q_len), S, q_len, qpos))) == Impl.bit(Bool.and(s, Nat.is_lt(k, 1n+jp))) : Nat}
      %Equal.sym(Bool, Impl.visits(jp, p, Nat.add(depth, q_len), S, q_len, qpos), Bool.and(s, Nat.is_eq(jp, k)), as_visit(jp, p, depth, q_len, S, qpos, pos, lt)) : {Nat.add(Impl.bit(Bool.and(s, Nat.is_lt(k, jp))), Impl.bit(_)) == Impl.bit(Bool.and(s, Nat.is_lt(k, 1n+jp))) : Nat}
      as_step_s(s, jp, k)

def as_bit_once(+s: Bool) -> {Impl.bit(s) == Spec.once(s) : Nat}:
  match s:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.attend_once(depth, q_len, S, qpos, p, spos, row):
  +sp = spos
  +L = Nat.add(depth, q_len)
  +d = Nat.add(depth, qpos)
  +hd = Ar.ard_tr(Nat.is_lt(d, L), Nat.is_lt(qpos, q_len), Ar.ar_lt_add_cancel(depth, qpos, q_len), row)
  +lpos = Ar.ar_le_lt_trans(0n, d, L, Ar.ar_h_le_zero(d), hd)
  +sl = Impl.split_len(L, S)
  +pos = as_sl_pos(L, S, sp, lpos)
  +k = Nat.div(p, sl)
  +s = Spec.sees(p, depth, qpos)
  +lt = as_keep(s, Nat.is_lt(p, L), e => Ar.ar_le_lt_trans(p, d, L, e, hd))
  +ks = as_keep(s, Nat.is_lt(k, S), e => Ar.ard_tr(Nat.is_lt(k, S), Nat.is_lt(p, Nat.mul(S, sl)),
    Ar.ar_div_lt(S, p, sl, pos),
    Ar.ar_lt_le_trans(p, L, Nat.mul(S, sl), Ar.ar_le_lt_trans(p, d, L, e, hd), as_cover(L, S, sp))))
  %Equal.sym(Nat, Impl.hits(S, p, L, S, q_len, qpos), Impl.bit(Bool.and(s, Nat.is_lt(k, S))), as_hits(S, p, depth, q_len, S, qpos, pos, lt)) : {_ == Spec.once(s) : Nat}
  %Equal.sym(Bool, Bool.and(s, Nat.is_lt(k, S)), s, ks) : {Impl.bit(_) == Spec.once(s) : Nat}
  as_bit_once(s)

# i < ceil(L / b) iff i * b < L (b >= 1)
def as_live(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(i, Impl.cdiv(L, b)) == Bool.not(Nat.is_le(L, Nat.mul(i, b))) : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(i, Impl.cdiv(L, 0n)) == Bool.not(Nat.is_le(L, Nat.mul(i, 0n))) : Bool}, Ar.ar_false_true(pos))
    case 1n+bp:
      %Equal.sym(Nat, Nat.sub(Nat.add(L, 1n+bp), 1n), Nat.add(L, bp), as_pred(L, bp)) : {Nat.is_lt(i, Nat.div(_, 1n+bp)) == Bool.not(Nat.is_le(L, Nat.mul(i, 1n+bp))) : Bool}
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

def Laws.combine_reads_written(L, S, i, spos, lpos):
  as_live(i, L, Impl.split_len(L, S), as_sl_pos(L, S, spos, lpos))

def as_not_false(+x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Ar.ar_false_true(Equal.sym(Bool, True{}, False{}, h)))
    case True{}:
      {==}

def Laws.live_in_grid(L, S, spos, lpos):
  +sp = spos
  +lp = lpos
  +lv = Impl.live(L, S)
  +r = Laws.combine_reads_written(L, S, S, sp, lp)
  +c = as_cover(L, S, sp)
  # runs(S) = not(L <= S * sl) = not(True) = False
  +f = Equal.trans(Bool, Nat.is_lt(S, lv), Impl.runs(S, L, S), False{}, r,
    Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(L, Nat.mul(S, Impl.split_len(L, S))), True{}, c))
  as_not_false(Nat.is_le(lv, S), Equal.trans(Bool, Bool.not(Nat.is_le(lv, S)), Nat.is_lt(S, lv), False{},
    Equal.sym(Bool, Nat.is_lt(S, lv), Bool.not(Nat.is_le(lv, S)), Ar.ar_lt_not_le(S, lv)), f))
