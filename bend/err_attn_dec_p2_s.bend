# Helpers of dec_p2 (bend/err_attn_dec_p2.bend), stock side: s_rt(L) and own0 + laterk0 as functions of
# the split length (s_sl), split 0's k16 groups / 32-key tiles and the live splits, so that a proven value
# of s_sl can replace it; and the shift L = 129 + (L - 129) that lets own0, gtile0 and tsum0 evaluate.
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./err_attn_dec_p2_lib.bend as Lb

# s_rt(L) with split 0's groups g, tiles t and the live splits nl as parameters
def p2_srt2(+L: Nat, +g: Nat, +t: Nat, +nl: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Nat.sub(g, Dec.s_gtile0(L))), 16n),
    Nat.add(Nat.add(Nat.sub(t, 1n), 1n+Nat.sub(nl, 1n)),
      Nat.add(2n, Nat.add(Dec.s_tsum0(L), Nat.add(Nat.sub(t, 1n), 1n+Nat.sub(nl, 1n))))))

# own0 + laterk0 with split 0's groups g as a parameter
def p2_sok(+L: Nat, +g: Nat) -> Nat:
  Nat.add(Dec.s_own0(L), Nat.sub(g, Dec.s_gtile0(L)))

# s_sl(L) == v <= L: s_rt(L) is p2_srt2 at split 0's keys v
def p2_s_rw(+L: Nat, +v: Nat, eq: {Dec.s_sl(L) == v : Nat}, hv: {Nat.is_le(v, L) == True{} : Bool}, +X: Nat,
    t: {Nat.is_le(X, p2_srt2(L, St.cdiv(v, 16n), St.cdiv(v, 32n), St.cdiv(L, v))) == True{} : Bool})
  -> {Nat.is_le(X, Dec.s_rt(L)) == True{} : Bool}:
  %Equal.sym(Nat, Dec.s_sl(L), v, eq) : {Nat.is_le(X, p2_srt2(L, St.cdiv(Nat.min(L, _), 16n), St.cdiv(Nat.min(L, _), 32n), St.cdiv(L, _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.min(L, v), v, Lb.p2_min_right(L, v, hv)) : {Nat.is_le(X, p2_srt2(L, St.cdiv(_, 16n), St.cdiv(_, 32n), St.cdiv(L, v))) == True{} : Bool}
  t

def p2_ok_rw(+L: Nat, +v: Nat, eq: {Dec.s_sl(L) == v : Nat}, hv: {Nat.is_le(v, L) == True{} : Bool}, +X: Nat,
    t: {Nat.is_le(X, p2_sok(L, St.cdiv(v, 16n))) == True{} : Bool})
  -> {Nat.is_le(X, Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool}:
  %Equal.sym(Nat, Dec.s_sl(L), v, eq) : {Nat.is_le(X, p2_sok(L, St.cdiv(Nat.min(L, _), 16n))) == True{} : Bool}
  %Equal.sym(Nat, Nat.min(L, v), v, Lb.p2_min_right(L, v, hv)) : {Nat.is_le(X, p2_sok(L, St.cdiv(_, 16n))) == True{} : Bool}
  t

# 129 <= L: L's own0, gtile0 and tsum0 evaluate at 129 + (L - 129)
def p2_s_sh(+L: Nat, +g: Nat, +t: Nat, +nl: Nat, +X: Nat, lo: {Nat.is_le(129n, L) == True{} : Bool},
    h: {Nat.is_le(X, p2_srt2(Nat.add(129n, Nat.sub(L, 129n)), g, t, nl)) == True{} : Bool})
  -> {Nat.is_le(X, p2_srt2(L, g, t, nl)) == True{} : Bool}:
  %Ar.ar_sub_add(L, 129n, lo) : {Nat.is_le(X, p2_srt2(_, g, t, nl)) == True{} : Bool}
  h

def p2_ok_sh(+L: Nat, +g: Nat, +X: Nat, lo: {Nat.is_le(129n, L) == True{} : Bool},
    h: {Nat.is_le(X, p2_sok(Nat.add(129n, Nat.sub(L, 129n)), g)) == True{} : Bool})
  -> {Nat.is_le(X, p2_sok(L, g)) == True{} : Bool}:
  %Ar.ar_sub_add(L, 129n, lo) : {Nat.is_le(X, p2_sok(_, g)) == True{} : Bool}
  h
