# dec_p2: for every live length L >= 1, elpis 3030's key-route bounds are dominated by stock 355c6ee key 0's
# (bend/err_attn_dec.bend): e_OE(L) <= own0(L) + laterk0(L) and e_rt(L) <= s_rt(L). Three ranges:
# L <= 128 by evaluation (bend/err_attn_dec_p2_small.bend), 129 <= L <= 4096 (one block-table width,
# bend/err_attn_dec_p2_c.bend), L >= 4097 (bend/err_attn_dec_p2_d.bend, _d2.bend); helpers in _lib.bend and
# _s.bend. Structural proofs only: no @unsafe definitions, axioms, holes or foreign code.
import Base
import ./err_attn_dec.bend as Dec
import ./err_attn_dec_p2_lib.bend as Lb
import ./err_attn_dec_p2_small.bend as Sm
import ./err_attn_dec_p2_c.bend as Pc
import ./err_attn_dec_p2_d.bend as Pd

def p2_big(+L: Nat, b: Bool, e: {Nat.is_le(L, 4096n) == b : Bool}, lo: {Nat.is_le(129n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  match b:
    case True{}:
      Pc.p2_c(L, lo, e)
    case False{}:
      Pd.p2_d(L, Lb.p2_lt_le(4096n, L, Lb.p2_gt(L, 4096n, e)))

def p2_split(+L: Nat, b: Bool, e: {Nat.is_le(L, 128n) == b : Bool}, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  match b:
    case True{}:
      Sm.p2_small(L, pos, e)
    case False{}:
      p2_big(L, Nat.is_le(L, 4096n), {==}, Lb.p2_lt_le(128n, L, Lb.p2_gt(L, 128n, e)))

def dec_p2(+L: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
     {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  p2_split(L, Nat.is_le(L, 128n), {==}, pos)
