# dec_p2 (bend/err_attn_dec_p2.bend) for the live lengths 1 <= L <= 128: decided by evaluation, in four
# blocks of 32 lengths (one def each: the BendTT kernel's fuel bounds a single evaluation).
import Base
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar

# Both claims of dec_p2 at L
def p2_chk(+L: Nat) -> Bool:
  Bool.and(Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))), Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)))

# The lengths 1 + b, 2 + b, ..., k + b
def p2_seg(+k: Nat, +b: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(p2_chk(1n+b), p2_seg(p, 1n+b))

def p2_seg0() -> {p2_seg(32n, 0n) == True{} : Bool}:
  +lazy : Nat = 0n
  {==}

def p2_seg1() -> {p2_seg(32n, 32n) == True{} : Bool}:
  +lazy : Nat = 0n
  {==}

def p2_seg2() -> {p2_seg(32n, 64n) == True{} : Bool}:
  +lazy : Nat = 0n
  {==}

def p2_seg3() -> {p2_seg(32n, 96n) == True{} : Bool}:
  +lazy : Nat = 0n
  {==}

# not(x) == False gives x == True
def p2s_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Ar.ar_true_false(h))
    case True{}:
      {==}

# j < k and seg(b, k) give chk(1 + (j + b))
def p2_seg_get(+k: Nat, +b: Nat, +j: Nat, h: {p2_seg(k, b) == True{} : Bool}, jk: {Nat.is_lt(j, k) == True{} : Bool})
  -> {p2_chk(1n+Nat.add(j, b)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({p2_chk(1n+Nat.add(j, b)) == True{} : Bool},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, Ar.ar_h_lt_zero(j)), jk)))
    case 1n+p:
      match j:
        case 0n:
          Ar.ar_and_l(p2_chk(1n+b), p2_seg(p, 1n+b), h)
        case 1n+i:
          %Ar.ar_add_succ_r(i, b) : {p2_chk(1n+_) == True{} : Bool}
          p2_seg_get(p, 1n+b, i, Ar.ar_and_r(p2_chk(1n+b), p2_seg(p, 1n+b), h), jk)

# b <= p < b + 32 and seg(b, 32) give chk(1 + p)
def p2_blk(+b: Nat, +p: Nat, h: {p2_seg(32n, b) == True{} : Bool}, lo: {Nat.is_le(b, p) == True{} : Bool},
    hi: {Nat.is_lt(p, Nat.add(b, 32n)) == True{} : Bool}) -> {p2_chk(1n+p) == True{} : Bool}:
  +l = lo
  +e = Equal.trans(Nat, Nat.add(Nat.sub(p, b), b), Nat.add(b, Nat.sub(p, b)), p,
    Ar.ar_add_comm(Nat.sub(p, b), b), Ar.ar_sub_add(p, b, l))
  %e : {p2_chk(1n+_) == True{} : Bool}
  p2_seg_get(32n, b, Nat.sub(p, b), h,
    Ar.ard_tr(Nat.is_lt(Nat.sub(p, b), 32n), Nat.is_lt(p, Nat.add(b, 32n)), Ar.ar_sub_lt_iff(p, b, 32n, {==}), hi))

# is_lt(p, c) == False gives c <= p
def p2s_ge(+p: Nat, +c: Nat, e: {Nat.is_lt(p, c) == False{} : Bool}) -> {Nat.is_le(c, p) == True{} : Bool}:
  p2s_not_false(Nat.is_le(c, p), Equal.trans(Bool, Bool.not(Nat.is_le(c, p)), Nat.is_lt(p, c), False{},
    Equal.sym(Bool, Nat.is_lt(p, c), Bool.not(Nat.is_le(c, p)), Ar.ar_lt_not_le(p, c)), e))

def p2_sel3(+p: Nat, c: Bool, e: {Nat.is_lt(p, 96n) == c : Bool}, lo: {Nat.is_le(64n, p) == True{} : Bool},
    hi: {Nat.is_lt(p, 128n) == True{} : Bool}) -> {p2_chk(1n+p) == True{} : Bool}:
  match c:
    case True{}:
      p2_blk(64n, p, p2_seg2(), lo, e)
    case False{}:
      p2_blk(96n, p, p2_seg3(), p2s_ge(p, 96n, e), hi)

def p2_sel2(+p: Nat, c: Bool, e: {Nat.is_lt(p, 64n) == c : Bool}, lo: {Nat.is_le(32n, p) == True{} : Bool},
    hi: {Nat.is_lt(p, 128n) == True{} : Bool}) -> {p2_chk(1n+p) == True{} : Bool}:
  match c:
    case True{}:
      p2_blk(32n, p, p2_seg1(), lo, e)
    case False{}:
      p2_sel3(p, Nat.is_lt(p, 96n), {==}, p2s_ge(p, 64n, e), hi)

def p2_sel1(+p: Nat, c: Bool, e: {Nat.is_lt(p, 32n) == c : Bool},
    hi: {Nat.is_lt(p, 128n) == True{} : Bool}) -> {p2_chk(1n+p) == True{} : Bool}:
  match c:
    case True{}:
      p2_blk(0n, p, p2_seg0(), Ar.ar_h_le_zero(p), e)
    case False{}:
      p2_sel2(p, Nat.is_lt(p, 64n), {==}, p2s_ge(p, 32n, e), hi)

# 1 <= L <= 128 gives both claims of dec_p2
def p2_small(+L: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool}, hi: {Nat.is_le(L, 128n) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  match L:
    case 0n:
      Empty.absurd({Nat.is_le(Dec.e_OE(0n), Nat.add(Dec.s_own0(0n), Dec.s_laterk0(0n))) == True{} : Bool} &
        {Nat.is_le(Dec.e_rt(0n), Dec.s_rt(0n)) == True{} : Bool}, Ar.ar_false_true(pos))
    case 1n+p:
      +c = p2_sel1(p, Nat.is_lt(p, 32n), {==},
        Ar.ard_tr(Nat.is_lt(p, 128n), Nat.is_le(1n+p, 128n), Ar.ar_lt_succ_le(p, 128n), hi))
      (Ar.ar_and_l(Nat.is_le(Dec.e_OE(1n+p), Nat.add(Dec.s_own0(1n+p), Dec.s_laterk0(1n+p))),
         Nat.is_le(Dec.e_rt(1n+p), Dec.s_rt(1n+p)), c),
       Ar.ar_and_r(Nat.is_le(Dec.e_OE(1n+p), Nat.add(Dec.s_own0(1n+p), Dec.s_laterk0(1n+p))),
         Nat.is_le(Dec.e_rt(1n+p), Dec.s_rt(1n+p)), c))
