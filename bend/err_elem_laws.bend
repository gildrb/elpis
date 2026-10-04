# Error-bound laws of the decode norms and elementwise ops (models: bend/err_elem.bend, vocabulary:
# bend/err_bound.bend). Exchange rate x = 128 throughout. Each op law: for every leaf (input term,
# per route) of a served elpis output element, the elpis path is dominated by the path of a stock
# leaf (the witness), which is shown to be a real leaf of stock's same output; where elpis runs
# stock's arithmetic the paths are equal (and dominated by dom_refl). The models' hypotheses
# (H_model, H_sass, H_torch, H_leaf, H_shape) are named and justified in bend/err_elem.bend.
import Base
import ./err_bound.bend as Eb
import ./err_elem.bend as Ee

# ==== tensors between kernels ====

# Every tensor handed between the kernels of a block (residual stream, norm outputs, sublayer and
# MLP outputs, gate / up, activation, final norm output) has the same dtype on the elpis verify
# path as in stock M = 1 decode: elpis adds no fp32 -> fp16 conversion and drops none.
law dtype_eq:
  for t: Ee.Ten
  {Ee.elpis_dtype(t) == Ee.stock_dtype(t) : Ee.Dt}

# ==== residual adds ====

# Every elpis residual add (tail F0, 7001 RES_IN, torch add) rounds each leaf exactly as the stock
# add it replaces (one fp32 rounding, fp32 stream store).
law resid_eq:
  for e: Ee.ERes
  for l: Ee.RLeaf
  {Ee.elpis_res(e, l) == Ee.stock_res(Ee.res_witness(e), l) : Eb.Path}

law resid_dom:
  for e: Ee.ERes
  for l: Ee.RLeaf
  {Eb.dom(128n, Ee.elpis_res(e, l), Ee.stock_res(Ee.res_witness(e), l)) == True{} : Bool}

# ==== rms_norm_kernel (input norms, final norm) ====

# At the served shape the elpis kernel takes its register-resident branch.
law norm_reg_branch:
  {Ee.reg_branch() == True{} : Bool}

# Every thread owns the same number of columns, in the same order, in elpis's register branch as
# in stock's strided loop.
law norm_ncols_eq:
  for +t: Nat
  for h: {Nat.is_lt(t, Ee.nthreads()) == True{} : Bool}
  {Ee.elpis_ncols(t) == Ee.stock_ncols(t) : Nat}

# Every leaf of every output element has the same path in the elpis rms_norm_kernel as in stock's,
# for any output dtype.
law norm_plain_eq:
  for +l: Ee.NLeaf
  for d: Ee.Dt
  for h: {Ee.thread_ok(l) == True{} : Bool}
  {Ee.elpis_norm(l, d) == Ee.stock_norm(l, d) : Eb.Path}

# The input norm (attention / GDN) and the final norm: each elpis leaf is dominated by the same
# stock leaf (with each side's output dtype).
law norm_input_dom:
  for +l: Ee.NLeaf
  for h: {Ee.thread_ok(l) == True{} : Bool}
  {Eb.dom(128n, Ee.elpis_norm(l, Ee.elpis_dtype(Ee.TNormOut{})), Ee.stock_norm(l, Ee.stock_dtype(Ee.TNormOut{}))) == True{} : Bool}

law norm_final_dom:
  for +l: Ee.NLeaf
  for h: {Ee.thread_ok(l) == True{} : Bool}
  {Eb.dom(128n, Ee.elpis_norm(l, Ee.elpis_dtype(Ee.TFinalOut{})), Ee.stock_norm(l, Ee.stock_dtype(Ee.TFinalOut{}))) == True{} : Bool}

# ==== post-attention norm in the layer tail ====

# Every leaf of every output element of the tail's post-attention RMSNorm is dominated by its
# witness leaf of stock's post-attention rms_norm_kernel.
law tail_norm_dom:
  for l: Ee.TLeaf
  {Eb.dom(128n, Ee.elpis_tail(l), Ee.stock_norm(Ee.tail_witness(l), Ee.stock_dtype(Ee.TMlpIn{}))) == True{} : Bool}

# The witnesses are real leaves of stock's kernel (thread < 1024, column owned by that thread).
law tail_witness_ok:
  for l: Ee.TLeaf
  {Ee.stock_leaf_ok(Ee.tail_witness(l)) == True{} : Bool}

# ==== SiLU(gate) * up ====

# The elpis tail's activation is stock act_mul_kernel_h<ACT_SILU>'s operation list.
law act_ops_eq:
  {Ee.elpis_act_ops() == Ee.stock_act_ops() : List<Ee.AOp>}

law act_eq:
  for l: Ee.ALeaf
  {Ee.elpis_act(l) == Ee.stock_act(l) : Eb.Path}

law act_dom:
  for l: Ee.ALeaf
  {Eb.dom(128n, Ee.elpis_act(l), Ee.stock_act(l)) == True{} : Bool}
