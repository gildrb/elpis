# Error-bound laws of decode attention (model bend/err_attn.bend; its header lists the served
# kernels, sources and the named hypotheses H_model, H_mma, H_zero, H_ptx, H_sass, H_common,
# H_route, H_dispatch). Exchange rate x = 128 throughout.
#
# The pre stage (q / k RMSNorm + RoPE, attn_pre_kernel vs rope_kernel) runs exactly stock's
# arithmetic: its paths are equal (pre_eq) and dominated (pre_dom). The attention core (split +
# combine) before ext 3030 is NOT dominated (bend/err_attn_finding_laws.bend); the 3030 core is proven
# dominated at every L by bend/err_attn_dec_laws.bend.
import Base
import ./err_bound.bend as Eb
import ./err_attn.bend as Ea

# ==== pre stage (attn_pre_kernel vs rope_kernel) ====

# For every norm-weight dtype, rotated or not, and every route (self / partner x input / weight /
# sum of squares at any warp and half), elpis's path equals stock's.
law pre_eq:
  for +nw: Ea.Nw
  for +r: Ea.Rot
  for +l: Ea.PreLeaf
  {Ea.elpis_pre(nw, r, l) == Ea.stock_pre(nw, r, l) : Eb.Path}

law pre_dom:
  for +nw: Ea.Nw
  for +r: Ea.Rot
  for +l: Ea.PreLeaf
  {Eb.dom(128n, Ea.elpis_pre(nw, r, l), Ea.stock_pre(nw, r, l)) == True{} : Bool}

# ==== attention core ====

# The two sides have the same geometry at L = 2 (one tile, one slot, the same denominator).
law geo2_eq:
  {Ea.geo_e2() == Ea.geo_s2() : Ea.Geo}

