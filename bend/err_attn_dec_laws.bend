# Contract laws of decode / verify attention after ext 3030 (model bend/err_attn_dec.bend; its header
# lists the kernels, sources and hypotheses; the stock model is bend/err_attn.bend's). Exchange rate
# x = 128, the robust class order of bend/err_bound.bend. Proofs: bend/err_attn_dec_proof.bend.
#
# These replace, for the 3030 kernels, the finding bend/err_attn_finding_laws.bend (which stays true of
# the pre-3030 kernels it models).
import Base
import ./err_bound.bend as Eb
import ./err_attn.bend as Ea
import ./err_attn_dec.bend as Dec

# THE OP LAW. For every live length L >= 1 (a row at absolute position L - 1), every live key of the
# row (CTA / slot x < 20, tile q of the CTA, group g < 4, key r < 16, position < L) and every route kind
# (q element, K value, V value, the tile coefficient cs, the gate), the 3030 path is dominated at
# x = 128 by stock 355c6ee's route of the same output element (key 0's; dec_dom_mono covers the
# denominator term used). By bend/err_bound_laws.bend dom_sigma, the 3030 worst-case rounding error
# bound of every output element is no larger than stock's, for every class-bound assignment in the
# class order.
law dec_dom:
  for +L: Nat
  for +k: Dec.DKey
  for +l: Dec.DLeaf
  for pos: {Nat.is_le(1n, L) == True{} : Bool}
  for ok: {Dec.key_ok(L, k) == True{} : Bool}
  {Eb.dom(128n, Dec.elpis_leaf(L, k, l), Ea.stock_leaf(Dec.geo_s0(L), Dec.stock_of(l))) == True{} : Bool}

# The same with the coefficients' own steps on the key routes (composite convention): 3030's cs
# (FADD + ex2) once against stock's combine weight w (FADD + FMUL + ex2) and one alpha per later tile of
# split 0. Under this convention the ex2 rescales are counted kind by kind on every key route.
law dec_dom_coef:
  for +L: Nat
  for +k: Dec.DKey
  for +l: Dec.DLeaf
  for pos: {Nat.is_le(1n, L) == True{} : Bool}
  for ok: {Dec.key_ok(L, k) == True{} : Bool}
  {Eb.dom(128n, Ea.cat(Dec.elpis_leaf(L, k, l), Dec.e_coef(l)),
     Ea.cat(Ea.stock_leaf(Dec.geo_s0(L), Dec.stock_of(l)), Dec.s_coef(L, l))) == True{} : Bool}

# Domination survives growing the dominating path: stock's denominator worst path is at least the
# term geo_s0 takes (H_route), so domination of geo_s0's route is domination of stock's actual route.
law dec_dom_mono:
  for +x: Nat
  for +e: Eb.Path
  for +s: Eb.Path
  for +s2: Eb.Path
  for d: {Eb.dom(x, e, s) == True{} : Bool}
  for le: {Dec.path_le(s, s2) == True{} : Bool}
  {Eb.dom(x, e, s2) == True{} : Bool}

# The 3030 denominator bound covers every route into it: through a key's p (xs + tile tree + folds +
# combine tree) and through a tile's cs (FMUL + FADD + folds + combine tree).
law dec_den_bound:
  for +L: Nat
  for +x: Nat
  for +q: Nat
  for +g: Nat
  for +r: Nat
  for pos: {Nat.is_le(1n, L) == True{} : Bool}
  for ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool}
  {Nat.is_le(Nat.add(2n, Nat.add(Dec.e_tsum(L, x, q, g, r), Nat.add(Dec.e_fold(L, x, q), Dec.e_depth(L, x)))), Dec.e_dr(L)) == True{} : Bool} &
  {Nat.is_le(Nat.add(2n, Nat.add(Dec.e_fold(L, x, q), Dec.e_depth(L, x))), Dec.e_dr(L)) == True{} : Bool}

# The per-key bounds behind e_rt: own groups, folds, combine-tree adds.
law dec_key_bounds:
  for +L: Nat
  for +x: Nat
  for +q: Nat
  for +g: Nat
  for +r: Nat
  for pos: {Nat.is_le(1n, L) == True{} : Bool}
  for ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool}
  {Nat.is_le(Dec.e_own(L, x, q, g), Dec.e_OE(L)) == True{} : Bool} &
  {Nat.is_le(Dec.e_fold(L, x, q), Dec.e_n0(L)) == True{} : Bool} &
  {Nat.is_le(Dec.e_depth(L, x), Dec.e_D(L)) == True{} : Bool}

# The arithmetic heart, for every L >= 1: the 3030 bounds against stock key 0's counts.
law dec_totals:
  for +L: Nat
  for pos: {Nat.is_le(1n, L) == True{} : Bool}
  {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool} &
  {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}

# 3030's score-to-p and output stages are stock's in path form; stock's geometry at L = 2 is
# bend/err_attn.bend's geo_s2.
law dec_xs_eq:
  {Dec.e_xs() == Ea.s_xs() : Eb.Path}

law dec_post_eq:
  for +lo: Bool
  {Dec.e_postb(lo) == Ea.s_postb(lo) : Eb.Path}

law dec_geo2:
  {Dec.geo_s0(2n) == Ea.geo_s2() : Ea.Geo}
