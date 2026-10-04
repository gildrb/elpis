# FINDING (not a contract law) about the decode-attention kernels BEFORE ext 3030 (ext 3006 / 3007 /
# 3012 split + combine, model bend/err_attn.bend): they are NOT dominated by stock 355c6ee M = 1 decode
# at x = 128. These laws stay true of that pre-3030 kernel and document the gap that ext 3030 closes;
# the shipped 3030 kernels are proven dominated at every L by bend/err_attn_dec_laws.bend (model
# bend/err_attn_dec.bend). Proofs: bend/err_attn_finding_proof.bend.
#
# The op law
#   "for every L >= 1, every served output element and every route of it, the elpis path is
#    dominated at x = 128 by the path of some stock route of the same element"
# is FALSE. attn_not_dom proves a counterexample: at L = 2 (a row at absolute position 1) the elpis
# route AQ{0, 0, 0} (a q element through Q.K^T, P.V, the quotient and rotation position 0 of the
# combine's fp32 FFMA back-rotation) is dominated by no stock route of the same output element.
# attn_gap_rotation: the same route with stock's output stage is dominated, so at L = 2 the whole gap
# is the back-rotation. The four causes over all L (bend/err_attn_diff.py scan) are listed in the
# header of bend/err_attn.bend.
import Base
import ./err_bound.bend as Eb
import ./err_attn.bend as Ea

# No stock route of the output element (any parameters, real or not) dominates the elpis route
# AQ{0, 0, 0} at L = 2.
law attn_not_dom:
  for l: Ea.ALeaf
  {Eb.dom(128n, Ea.elpis_worst2(), Ea.stock_leaf(Ea.geo_s2(), l)) == False{} : Bool}

# The elpis route compared is a real route of the element (k16 half 0 < 2, k-step 0 < 16, rotation
# position 0 < 32); its path and stock's path of the same route.
law elpis_worst2_path:
  {Ea.elpis_worst2() == Eb.Path{39n, 37n, 6n, 0n, 0n, 2n, 1n, 0n} : Eb.Path}

law stock_worst2_path:
  {Ea.stock_leaf(Ea.geo_s2(), Ea.AQ{0n, 0n, 0n}) == Eb.Path{8n, 39n, 6n, 0n, 0n, 2n, 1n, 0n} : Eb.Path}

# Diagnosis: with stock's output stage the same elpis route is dominated by stock's AQ{0, 0, 0}.
law attn_gap_rotation:
  {Eb.dom(128n, Ea.elpis_worst2_srot(), Ea.stock_leaf(Ea.geo_s2(), Ea.AQ{0n, 0n, 0n})) == True{} : Bool}
