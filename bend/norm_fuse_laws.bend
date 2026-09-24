# Laws of the residual add + RMSNorm fusion (ext patch 7001) over the Bend model
# bend/norm_fuse.bend (fused: rms_norm_kernel<RES_IN>, register path, and the layer handshake)
# against the independent unfused reference bend/norm_fuse_spec.bend (torch `x += y`, then
# rms_norm_kernel<RES_NONE>, strided path, and the unfused layer loop).
# Every float operation (add, mul, fma, the residual-dtype rounding, the weight bias, the rmf
# line, the output cast, 0.0f) is a template parameter, opaque to the checker: an equation between
# two float results holds for every arithmetic, i.e. both sides apply the same operations to the
# same operands in the same order. The one algebraic fact used is commutativity of the residual
# add (`comm`): the fused kernel computes y + r (x4 += r4, norm.cu:227-230) where torch computes
# r + y; IEEE-754 binary32 round-to-nearest addition is commutative, so this is what makes the
# fusion bit-exact.
# Domains: blockDim.x = 32 W with W >= 1 (norm.cu:431 gives 1 <= W <= 32), n = dim / 4 columns,
# REG_COLS = R; the register path is taken when n <= R * 32 W (norm.cu:295), which every law about
# the fused kernel assumes; any row (blockIdx.x). The served shape (dim 5120: n = 1280, W = 32,
# R = 2, rows 1..16) is inside every domain (law served_shape).
import Base
import ./norm_fuse.bend as Impl
import ./norm_fuse_spec.bend as Spec

# (c) Per-thread accumulation order. Thread t of the register path visits exactly the columns of
# the strided loop the unfused kernel runs (`for (column = t; column < columns; column +=
# blockDim.x)`), in the same order, for every t, whenever the register path is taken.
law cols_order:
  for +R: Nat
  for +B: Nat
  for +t: Nat
  for +n: Nat
  for pos: {Nat.is_lt(0n, B) == True{} : Bool}
  for fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool}
  {Impl.cols_reg(R, B, t, n) == Spec.cols_loop(n, B, t, n) : List<&2, Nat>}

# (c) The per-thread partial sums of squares fed to reduce_dyn are identical (same columns, same
# sum_sq4 fma chain over the same values, thread order), for every run of k threads from t.
law partials_equal:
  for ~F: Data
  for ~add: F -> F -> F
  for ~fma: F -> F -> F -> F
  for ~un: Spec.Un -> F -> F
  for ~zero: F
  for ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>
  for ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F}
  for +k: Nat
  for +t: Nat
  for +R: Nat
  for +B: Nat
  for +n: Nat
  for +row: Nat
  for pos: {Nat.is_lt(0n, B) == True{} : Bool}
  for fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool}
  {Impl.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, R, B, n, row) ==
    Spec.parts(~F, ~add, ~fma, ~un, ~zero, ~mem, k, t, B, n, row) : List<&2, F>}

# (a) Refinement, normed output: block `row` of the fused launch issues exactly the output stores
# of the unfused norm (same thread, same column, same order, same value in every lane: the same
# per-element operations, the same reduction, the same rmf).
law refine_out:
  for ~F: Data
  for ~O: Data
  for ~add: F -> F -> F
  for ~mul: F -> F -> F
  for ~fma: F -> F -> F -> F
  for ~un: Spec.Un -> F -> F
  for ~zero: F
  for ~cast: F -> O
  for ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>
  for ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F}
  for +W: Nat
  for +R: Nat
  for +n: Nat
  for +row: Nat
  for pos: {Nat.is_lt(0n, W) == True{} : Bool}
  for fits: {Nat.is_le(n, Nat.mul(R, Nat.mul(32n, W))) == True{} : Bool}
  {Impl.fused_out(~F, ~O, ~add, ~mul, ~fma, ~un, ~zero, ~cast, ~mem, W, R, n, row) ==
    Spec.unfused_out(~F, ~O, ~add, ~mul, ~fma, ~un, ~zero, ~cast, ~mem, W, n, row)
    : List<&2, Spec.Wr<Spec.V4<O>>>}

# (a) Refinement, residual stream: after the fused launch every column j < n of row `row` of r
# holds exactly what torch's `x += y` leaves there (all four lanes).
law refine_resid:
  for ~F: Data
  for ~add: F -> F -> F
  for ~un: Spec.Un -> F -> F
  for ~mem: Spec.Buf -> Nat -> Nat -> Spec.V4<F>
  for ~comm: @a:F -> @b:F -> {add(a, b) == add(b, a) : F}
  for +W: Nat
  for +R: Nat
  for +n: Nat
  for +row: Nat
  for +j: Nat
  for pos: {Nat.is_lt(0n, W) == True{} : Bool}
  for fits: {Nat.is_le(n, Nat.mul(R, Nat.mul(32n, W))) == True{} : Bool}
  for inside: {Nat.is_lt(j, n) == True{} : Bool}
  {Spec.final(~Spec.V4<F>, Impl.fused_resid(~F, ~add, ~un, ~mem, W, R, n, row), j,
      mem(Spec.BR{}, row, j)) ==
    Spec.resid(~F, ~add, ~un, ~mem, row, j) : Spec.V4<F>}

# (b) Ownership, coverage: every column j < n is visited by thread j % B, which is in the block.
law own_cover:
  for +R: Nat
  for +B: Nat
  for +n: Nat
  for +j: Nat
  for pos: {Nat.is_lt(0n, B) == True{} : Bool}
  for fits: {Nat.is_le(n, Nat.mul(R, B)) == True{} : Bool}
  for inside: {Nat.is_lt(j, n) == True{} : Bool}
  {Spec.member(j, Impl.cols_reg(R, B, Nat.mod(j, B), n)) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(j, B), B) == True{} : Bool}

# (b) Ownership, exclusivity: a thread t < B that visits column j is thread j % B.
law own_exclusive:
  for +R: Nat
  for +B: Nat
  for +t: Nat
  for +n: Nat
  for +j: Nat
  for small: {Nat.is_lt(t, B) == True{} : Bool}
  for hit: {Spec.member(j, Impl.cols_reg(R, B, t, n)) == True{} : Bool}
  {t == Nat.mod(j, B) : Nat}

# (b) Ownership, no repeats: a thread visits a column at most once (B >= 1). With own_cover and
# own_exclusive: each column, hence each of its 4 elements, of both outputs (y and the residual
# r) is stored exactly once, by thread j % B of block `row` (the stores are one per visited column,
# Impl.resid_writes / Impl.out_writes).
law own_single:
  for +R: Nat
  for +B: Nat
  for +t: Nat
  for +n: Nat
  for +j: Nat
  for pos: {Nat.is_lt(0n, B) == True{} : Bool}
  {Nat.is_le(Spec.occ(j, Impl.cols_reg(R, B, t, n)), 1n) == True{} : Bool}

# (d) Aliasing: r is read and written in place. In every thread's program order no load of a
# residual column follows a store to that column (all loads are issued in the first loop, before
# any add_resid_in store), for every R, B, t, n; by own_exclusive no other thread touches the
# column, so no residual element is overwritten before its last read.
law alias_reads_first:
  for +R: Nat
  for +B: Nat
  for +t: Nat
  for +n: Nat
  {Spec.raw_ok(Impl.thread_events(R, B, t, n), Nil{}) == True{} : Bool}

# (e) Layer chain. For every forward-loop module list obeying link_residual_deferral's rule, every
# per-block decision to defer, every block body, every non-block module and a loop that stops
# anywhere (prefill), the fused loop (deferred adds folded into the next input norm, pending add
# applied by end_residual_deferral) shows every block the same stream and normed input as the
# unfused loop, and ends with the same stream (which is what the final norm, a non-block module,
# reads) - given that the fused input norm is the add followed by the norm, which is what
# refine_out and refine_resid establish for the kernel, row by row.
law chain:
  for ~S: Data
  for ~H: Data
  for ~plus: S -> S -> S
  for ~norm: Nat -> S -> H
  for ~fnorm: Nat -> S -> S -> Spec.Normed<S, H>
  for ~body: Nat -> S -> H -> Spec.Step<S>
  for ~other: Nat -> S -> S
  for ~fused: @i:Nat -> @x:S -> @y:S ->
    {fnorm(i, y, x) == Spec.Normed{plus(x, y), norm(i, plus(x, y))} : Spec.Normed<S, H>}
  for +mods: List<&2, Spec.Mod>
  for +x0: S
  for ok: {Spec.linked_ok(mods, False{}) == True{} : Bool}
  {Impl.f_go(~S, ~H, ~plus, ~norm, ~fnorm, ~body, ~other, mods, 0n, Spec.Stop{x0}, False{}) ==
    Spec.u_go(~S, ~H, ~plus, ~norm, ~body, ~other, mods, 0n, Spec.Stop{x0}) : Spec.Run<S, H>}

# The served shape: dim 5120 gives n = 1280 columns and W = 32 warps (blockDim.x 1024), the
# register path is taken (1280 <= 2 * 1024), and the pre-7001 `single` path was not
# (1280 > 1024): the unfused reference is the strided loop.
law served_shape:
  {Spec.warps_for(1280n) == 32n : Nat} &
  {Nat.is_le(1280n, Nat.mul(2n, Nat.mul(32n, 32n))) == True{} : Bool} &
  {Nat.is_lt(Nat.mul(32n, 32n), 1280n) == True{} : Bool}
