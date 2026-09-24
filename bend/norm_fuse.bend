# Model of the served fusion of ext patch patches/exl3-ext/7001-norm-residual-fuse.patch:
# the closing residual add of transformer block i (x += y) is handed to block i + 1, whose input
# norm runs rms_norm_kernel<RES_IN> (norm.cu post-7001): r += x; y = norm(r) * w in one launch.
# Pinned source: post-images of patches/exl3-ext (series sha 6d111f2b, exl3-ext.json):
# exllamav3_ext/norm.cu, modules/transformer.py, model/model.py, model/model_ls.py,
# modules/rmsnorm.py. Line references are post-7001 unless marked `pre`.
# Float operations are template parameters (opaque): every law holds for every arithmetic.
# Proof model (lists, Nat), not a shipped artifact; the finite link to the CUDA source is
# bend/norm_fuse_diff.py (verbatim kernel lines compiled for the CPU against NORM_FUSE_TABLE.bend).
import Base
import ./norm_fuse_spec.bend as Spec

# ---- The fused kernel: rms_norm_kernel<RES_IN>, register-resident path ----
# Taken when columns <= REG_COLS * blockDim.x (norm.cu:294-295); at the served shape
# (dim 5120: 1280 columns, blockDim.x 1024 from norm.cu:431) every launch takes it.

def reg.pick(hit: Bool, +c: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      c <> rest
    case False{}:
      rest

# Columns thread t touches, in order: `for (i = 0; i < REG_COLS; ++i) { column = t + i *
# blockDim.x; if (column < columns) .. }` (norm.cu:301-304, :314-317, :327-330). The column of
# iteration i is kept as a running value c = t + i B.
def cols_reg(R: Nat, +B: Nat, +c: Nat, +n: Nat) -> List<&2, Nat>:
  match R:
    case 0n:
      Nil{}
    case 1n+r:
      reg.pick(Nat.is_lt(c, n), c, cols_reg(r, B, Nat.add(c, B), n))

# Columns of threads t .. t + k - 1, thread by thread.
def block_cols(k: Nat, +t: Nat, +R: Nat, +B: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, Nat, cols_reg(R, B, t, n), block_cols(m, 1n+t, R, B, n))

# add_resid_in (norm.cu:224-246): x4 += r4 lane by lane (input first), rounded to the residual
# dtype (fp16: __float2half_rn then back; fp32: kept); that value is stored to r and kept in x4.
def radd(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F, x: Spec.V4<F>, r: Spec.V4<F>)
    -> Spec.V4<F>:
  match x r:
    case Spec.V4{a, b, d, e} Spec.V4{p, q, s, t}:
      Spec.V4{un(Spec.Rt{}, add(a, p)), un(Spec.Rt{}, add(b, q)), un(Spec.Rt{}, add(d, s)),
        un(Spec.Rt{}, add(e, t))}

# Column c of row `row` after add_resid_in: read_in(x4[i], ..) and read_resid(r4[i], ..)
# (norm.cu:306-307) combined in the second loop (norm.cu:319).
def vsum(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, +row: Nat, +c: Nat) -> Spec.V4<F>:
  radd(~F, ~add, ~un, mem(Spec.BX{}, row, c), mem(Spec.BR{}, row, c))

# sum = sum_sq4(sum, x4[i]) over the thread's columns in i order, from 0.0f (norm.cu:312-322).
def partial(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, cols: List<&2, Nat>, +row: Nat, acc: F) -> F:
  match cols:
    case Nil{}:
      acc
    case c <> rest:
      partial(~F, ~add, ~fma, ~un, ~mem, rest, row,
        Spec.sum_sq4(~F, ~fma, acc, vsum(~F, ~add, ~un, ~mem, row, c)))

# Partial sums of threads t .. t + k - 1.
def parts(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Spec.Un -> F -> F,
    ~zero: F, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, k: Nat, +t: Nat, +R: Nat, +B: Nat,
    +n: Nat, +row: Nat) -> List<&2, F>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      partial(~F, ~add, ~fma, ~un, ~mem, cols_reg(R, B, t, n), row, zero) <>
        parts(~F, ~add, ~fma, ~un, ~zero, ~mem, m, 1n+t, R, B, n, row)

# The residual stores of thread t (WRITE64 / write_float4 in add_resid_in, norm.cu:238, :245).
def resid_writes(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, cols: List<&2, Nat>, +row: Nat)
    -> List<&2, Spec.Wr<Spec.V4<F>>>:
  match cols:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Spec.Wr{c, vsum(~F, ~add, ~un, ~mem, row, c)} <>
        resid_writes(~F, ~add, ~un, ~mem, rest, row)

# Residual stores of threads t .. t + k - 1.
def block_resid(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, k: Nat, +t: Nat, +R: Nat, +B: Nat, +n: Nat,
    +row: Nat) -> List<&2, Spec.Wr<Spec.V4<F>>>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, Spec.Wr<Spec.V4<F>>,
        resid_writes(~F, ~add, ~un, ~mem, cols_reg(R, B, t, n), row),
        block_resid(~F, ~add, ~un, ~mem, m, 1n+t, R, B, n, row))

# Third loop (norm.cu:326-332): apply_out(x4[i], w4[i], column, rmf) from the registers (the
# weights were loaded by read_w in the first loop, norm.cu:308, 248-260).
def out_writes(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~un: Spec.Un -> F -> F, ~cast: F -> O, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    cols: List<&2, Nat>, +row: Nat, +rmf: F) -> List<&2, Spec.Wr<Spec.V4<O>>>:
  match cols:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Spec.Wr{c, Spec.apply(~F, ~O, ~mul, ~un, ~cast, vsum(~F, ~add, ~un, ~mem, row, c),
        mem(Spec.BW{}, 0n, c), rmf)} <>
        out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, row, rmf)

def block_out(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~un: Spec.Un -> F -> F, ~cast: F -> O, ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>,
    sums: List<&2, F>, +t: Nat, +R: Nat, +B: Nat, +n: Nat, +row: Nat)
    -> List<&2, Spec.Wr<Spec.V4<O>>>:
  match sums:
    case Nil{}:
      Nil{}
    case s <> rest:
      List.append(&2, Spec.Wr<Spec.V4<O>>,
        out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, cols_reg(R, B, t, n), row,
          un(Spec.Rms{}, s)),
        block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, 1n+t, R, B, n, row))

# Block `row` (blockIdx.x, norm.cu:204-205) of the fused launch, blockDim.x = 32 W, n = dim / 4
# columns, REG_COLS = R: every output store, threads in order. The block reduction is the
# unchanged reduce_dyn (norm.cu:156-167, :323), the rmf line is unchanged (norm.cu:324).
def fused_out(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~fma: F -> F -> F -> F, ~un: Spec.Un -> F -> F, ~zero: F, ~cast: F -> O,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, +W: Nat, +R: Nat, +n: Nat, +row: Nat)
    -> List<&2, Spec.Wr<Spec.V4<O>>>:
  +B = Nat.mul(32n, W)
  block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem,
    Spec.reduce_dyn(~F, ~add, ~zero, W,
      parts(~F, ~add, ~fma, ~un, ~zero, ~mem, B, 0n, R, B, n, row)),
    0n, R, B, n, row)

# Every residual store of block `row` of the fused launch.
def fused_resid(~F: Data, ~add: F -> F -> F, ~un: Spec.Un -> F -> F,
    ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>, +W: Nat, +R: Nat, +n: Nat, +row: Nat)
    -> List<&2, Spec.Wr<Spec.V4<F>>>:
  +B = Nat.mul(32n, W)
  block_resid(~F, ~add, ~un, ~mem, B, 0n, R, B, n, row)

# ---- Memory events of one thread of the fused kernel (aliasing, Spec.Ev) ----

# Third loop: output stores only (apply_out, norm.cu:326-332).
def ev3(cols: List<&2, Nat>) -> List<&2, Spec.Ev>:
  match cols:
    case Nil{}:
      Nil{}
    case c <> rest:
      Spec.WrY{c} <> ev3(rest)

# Second loop: add_resid_in stores r (norm.cu:314-322), then reduce_dyn (__syncthreads,
# norm.cu:163, :323), then the third loop.
def ev2(cols: List<&2, Nat>, tail: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match cols:
    case Nil{}:
      Spec.Sync{} <> tail
    case c <> rest:
      Spec.WrR{c} <> ev2(rest, tail)

# First loop: loads x, r and w of every owned column up front (norm.cu:300-310).
def ev1(cols: List<&2, Nat>, tail: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match cols:
    case Nil{}:
      tail
    case +c <> rest:
      Spec.RdX{c} <> Spec.RdR{c} <> Spec.RdW{c} <> ev1(rest, tail)

# Program-order memory events of thread t (the register path, norm.cu:297-332).
def thread_events(+R: Nat, +B: Nat, +t: Nat, +n: Nat) -> List<&2, Spec.Ev>:
  +cols = cols_reg(R, B, t, n)
  ev1(cols, ev2(cols, ev3(cols)))

# ---- Layer chain (model.py:159-175 link_residual_deferral, model_ls.py:305-345 forward loops +
# end_residual_deferral, transformer.py:88-108 _defer_mlp_residual, :182-197 and :235-238) ----

# The input-norm step of a module that receives st from the module before it; pend: that
# module deferred its closing add (params["pending_mlp_residual"] = (x, y), transformer.py:236).
# A pending add goes into attn_norm.forward(y, residual_in = x) (transformer.py:194-195,
# rmsnorm.py:116-130); otherwise the previous block already did `x += y` (transformer.py:238).
def f_step(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H,
    ~fnorm: Nat -> S -> S -> Spec.Normed<S, H>, pend: Bool, st: Spec.Step<S>, +i: Nat)
    -> Spec.Normed<S, H>:
  match pend:
    case False{}:
      Spec.u_step(~S, ~H, ~plus, ~norm, st, i)
    case True{}:
      match st:
        case Spec.Stop{x}:
          Spec.u_step(~S, ~H, ~plus, ~norm, Spec.Stop{x}, i)
        case Spec.Half{x, y}:
          fnorm(i, y, x)

# The stream a non-TransformerBlock module receives: with a pending add it would see x without
# y (link_residual_deferral never links a block to one, model.py:173-175).
def f_pass(~S: Data, ~plus: S -> S -> S, pend: Bool, st: Spec.Step<S>) -> S:
  match pend:
    case False{}:
      Spec.settle(~S, ~plus, st)
    case True{}:
      match st:
        case Spec.Stop{x}:
          x
        case Spec.Half{x, y}:
          x

# The fused forward loop over the module list: every block's input-norm step and the stream at
# the end (end_residual_deferral applies an add still pending, model_ls.py:320-328; a loop that
# stops early, prefill_ls `break`, is a shorter module list).
def f_go(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H,
    ~fnorm: Nat -> S -> S -> Spec.Normed<S, H>, ~body: Nat -> S -> H -> Spec.Step<S>,
    ~other: Nat -> S -> S, mods: List<&2, Spec.Mod>, +i: Nat, st: Spec.Step<S>, pend: Bool)
    -> Spec.Run<S, H>:
  match mods:
    case Nil{}:
      Spec.Run{Nil{}, Spec.settle(~S, ~plus, st)}
    case Spec.Blk{link} <> rest:
      +ns = f_step(~S, ~H, ~plus, ~norm, ~fnorm, pend, st, i)
      Spec.run.cons(~S, ~H, ns,
        f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, rest, 1n+i,
          body(i, Spec.normed.x(~S, ~H, ns), Spec.normed.h(~S, ~H, ns)), link))
    case Spec.Other{} <> rest:
      f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, rest, 1n+i,
        Spec.Stop{other(i, f_pass(~S, ~plus, pend, st))}, False{})
