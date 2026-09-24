# Independent reference for the per-layer residual add + RMSNorm fusion (ext patch
# patches/exl3-ext/7001-norm-residual-fuse.patch): the UNFUSED sequence the patch replaces.
#   1. modules/transformer.py closing `x += y` (pre-7001 :195; the tree of patches/exl3 plus
#      patches/exl3-ext up to 6001): torch adds the MLP output y into the residual stream x in
#      place (x = x + y, stored in x's dtype).
#   2. The next block's input norm, attn_norm.forward(x) (pre-7001 transformer.py:156) ->
#      ext.rms_norm, res_mode RES_NONE, over the updated stream: rms_norm_kernel of the pre-7001
#      norm.cu, strided path (pre norm.cu:298-324). The pre-7001 `single` path (pre norm.cu:211,
#      :282-297) needs columns <= blockDim.x (false at the served dim 5120: 1280 float4 columns,
#      blockDim.x 1024) and visits the same single column t < columns as the loop.
# The float operations are template parameters (opaque to the checker), so every law about this
# model holds for every arithmetic. Proof model (lists, Nat), not a shipped artifact.
import Base

# One float4 column (4 consecutive elements) of a row.
type V4<-F: Data> is Data:
  V4{x: F, y: F, z: F, w: F}

# One vector store: column index and stored value.
type Wr<-A: Data> is Data:
  Wr{col: Nat, v: A}

# Device buffers: kernel input x (the sublayer output y of transformer.py), residual stream r,
# norm weight w.
type Buf is Data:
  BX{}
  BR{}
  BW{}

# Opaque unary float steps: Rt rounds to the residual dtype and widens back (identity for fp32
# residuals); Wb is `w4 += constant_bias` after the weight read (norm.cu read_w / pre-7001
# apply_out); Rms is `rsqrtf(sum / (float) dim + epsilon) * constant_scale` (norm.cu:324, :350).
type Un is Data:
  Rt{}
  Wb{}
  Rms{}

# ---- Shared helpers (pre-existing device functions, byte-identical pre/post 7001) ----

# sum_sq4 (norm.cu:117-124): four fma(v, v, acc) steps in lane order x, y, z, w.
def sum_sq4(~F: Data, ~fma: F -> F -> F -> F, acc: F, v: V4<F>) -> F:
  match v:
    case V4{+x, +y, +z, +w}:
      fma(w, w, fma(z, z, fma(y, y, fma(x, x, acc))))

# apply4 (norm.cu:126-132) after the weight read + constant_bias, then write_half4 / write_float4
# (the output cast): out = cast((x * w) * rmf) per lane.
def apply(~F: Data, ~O: Data, ~mul: F -> F -> F, ~un: Un -> F -> F, ~cast: F -> O,
    v: V4<F>, w: V4<F>, +rmf: F) -> V4<O>:
  match v w:
    case V4{a, b, c, d} V4{p, q, r, s}:
      V4{cast(mul(mul(a, un(Wb{}, p)), rmf)), cast(mul(mul(b, un(Wb{}, q)), rmf)),
        cast(mul(mul(c, un(Wb{}, r)), rmf)), cast(mul(mul(d, un(Wb{}, s)), rmf))}

# Lane l of a warp-sized list (0.0f past the end: never read in range).
def lane(~F: Data, +zero: F, xs: List<&2, F>, l: Nat) -> F:
  match xs:
    case Nil{}:
      zero
    case x <> rest:
      match l:
        case 0n:
          x
        case 1n+p:
          lane(~F, zero, rest, p)

def xor.pick(low: Bool, +l: Nat, +o: Nat) -> Nat:
  match low:
    case True{}:
      Nat.add(l, o)
    case False{}:
      Nat.sub(l, o)

# l ^ o for a power of two o: bit o of l clear -> l + o, set -> l - o.
def xor(+l: Nat, +o: Nat) -> Nat:
  xor.pick(Nat.is_eq(Nat.mod(Nat.div(l, o), 2n), 0n), l, o)

# One butterfly stage `sum += __shfl_xor_sync(0xffffffff, sum, o)` on lanes l .. l + k - 1:
# own value first, the partner lane l ^ o second.
def bstage(~F: Data, ~add: F -> F -> F, ~zero: F, k: Nat, +l: Nat, +o: Nat,
    +xs: List<&2, F>) -> List<&2, F>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      add(lane(~F, zero, xs, l), lane(~F, zero, xs, xor(l, o))) <>
        bstage(~F, ~add, ~zero, m, 1n+l, o, xs)

# `for (int offset = 16; offset > 0; offset /= 2) sum += __shfl_xor_sync(.., sum, offset)` over
# the 32 lanes of a warp (norm.cu:159, :165).
def bfly(~F: Data, ~add: F -> F -> F, ~zero: F, xs: List<&2, F>) -> List<&2, F>:
  bstage(~F, ~add, ~zero, 32n, 0n, 1n, bstage(~F, ~add, ~zero, 32n, 0n, 2n,
    bstage(~F, ~add, ~zero, 32n, 0n, 4n, bstage(~F, ~add, ~zero, 32n, 0n, 8n,
      bstage(~F, ~add, ~zero, 32n, 0n, 16n, xs)))))

# Per-warp butterflies over W warps of 32 threads (thread order).
def warps(~F: Data, ~add: F -> F -> F, ~zero: F, W: Nat, +xs: List<&2, F>)
    -> List<&2, List<&2, F>>:
  match W:
    case 0n:
      Nil{}
    case 1n+m:
      bfly(~F, ~add, ~zero, List.take(&2, F, xs, 32n)) <>
        warps(~F, ~add, ~zero, m, List.drop(&2, F, xs, 32n))

def lane0(~F: Data, +zero: F, xs: List<&2, F>) -> F:
  match xs:
    case Nil{}:
      zero
    case x <> rest:
      x

# sums[warp_id] = lane 0 of every warp (norm.cu:162).
def lane0s(~F: Data, ~zero: F, ws: List<&2, List<&2, F>>) -> List<&2, F>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      lane0(~F, zero, w) <> lane0s(~F, ~zero, rest)

# Every warp reads sums[lane_id] (or 0.0f past num_warps) and runs the same butterfly
# (norm.cu:164-165), so thread t ends with lane t % 32 of that result: W copies of it.
def repeat(~F: Data, W: Nat, +xs: List<&2, F>) -> List<&2, F>:
  match W:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, F, xs, repeat(~F, m, xs))

def reduce_dyn.fin(~F: Data, ~add: F -> F -> F, ~zero: F, one: Bool, +W: Nat,
    ws: List<&2, List<&2, F>>) -> List<&2, F>:
  match one:
    case True{}:
      List.concat(&2, F, ws)
    case False{}:
      repeat(~F, W, bfly(~F, ~add, ~zero, List.append(&2, F, lane0s(~F, ~zero, ws),
        List.replicate(F, Nat.sub(32n, W), zero))))

# reduce_dyn (norm.cu:156-167) for blockDim.x = 32 W (1 <= W <= 32): per-thread partial sums in
# thread order -> per-thread reduced sums in thread order.
def reduce_dyn(~F: Data, ~add: F -> F -> F, ~zero: F, +W: Nat, +xs: List<&2, F>)
    -> List<&2, F>:
  reduce_dyn.fin(~F, ~add, ~zero, Nat.is_eq(W, 1n), W, warps(~F, ~add, ~zero, W, xs))

# Last store to column j wins; d if none (the buffer's prior contents).
def final.pick(~A: Data, hit: Bool, v: A, d: A) -> A:
  match hit:
    case True{}:
      v
    case False{}:
      d

def final(~A: Data, ws: List<&2, Wr<A>>, +j: Nat, d: A) -> A:
  match ws:
    case Nil{}:
      d
    case Wr{c, v} <> rest:
      final(~A, rest, j, final.pick(~A, Nat.is_eq(c, j), v, d))

# ---- The unfused sequence ----

# torch `x += y` (transformer.py): residual lane r + y, stored in the residual dtype.
def tadd(~F: Data, ~add: F -> F -> F, ~un: Un -> F -> F, r: V4<F>, y: V4<F>) -> V4<F>:
  match r y:
    case V4{a, b, c, d} V4{p, q, s, t}:
      V4{un(Rt{}, add(a, p)), un(Rt{}, add(b, q)), un(Rt{}, add(c, s)), un(Rt{}, add(d, t))}

# The residual stream after step 1 (what the RES_NONE norm reads, column c of row `row`).
def resid(~F: Data, ~add: F -> F -> F, ~un: Un -> F -> F, ~mem: Buf -> Nat -> Nat -> V4<F>,
    +row: Nat, +c: Nat) -> V4<F>:
  tadd(~F, ~add, ~un, mem(BR{}, row, c), mem(BX{}, row, c))

def loop.pick(hit: Bool, +c: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      c <> rest
    case False{}:
      Nil{}

# `for (int column = t; column < columns; column += blockDim.x)` (pre norm.cu:301, :311), run with
# fuel (n iterations suffice for blockDim.x >= 1).
def cols_loop(fuel: Nat, +B: Nat, +c: Nat, +n: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      loop.pick(Nat.is_lt(c, n), c, cols_loop(f, B, Nat.add(c, B), n))

# First pass of thread t: sum = sum_sq4(sum, x4) over its columns, in loop order, from 0.0f
# (pre norm.cu:300-307).
def partial(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Un -> F -> F,
    ~mem: Buf -> Nat -> Nat -> V4<F>, cols: List<&2, Nat>, +row: Nat, acc: F) -> F:
  match cols:
    case Nil{}:
      acc
    case c <> rest:
      partial(~F, ~add, ~fma, ~un, ~mem, rest, row,
        sum_sq4(~F, ~fma, acc, resid(~F, ~add, ~un, ~mem, row, c)))

# Partial sums of threads t .. t + k - 1 (each from 0.0f).
def parts(~F: Data, ~add: F -> F -> F, ~fma: F -> F -> F -> F, ~un: Un -> F -> F, ~zero: F,
    ~mem: Buf -> Nat -> Nat -> V4<F>, k: Nat, +t: Nat, +B: Nat, +n: Nat, +row: Nat)
    -> List<&2, F>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      partial(~F, ~add, ~fma, ~un, ~mem, cols_loop(n, B, t, n), row, zero) <>
        parts(~F, ~add, ~fma, ~un, ~zero, ~mem, m, 1n+t, B, n, row)

# Second pass of thread t: re-read x (the updated stream), apply_out (weight read + constant_bias,
# apply4, store y; pre norm.cu:246-279, :311-324).
def out_writes(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F, ~un: Un -> F -> F,
    ~cast: F -> O, ~mem: Buf -> Nat -> Nat -> V4<F>, cols: List<&2, Nat>, +row: Nat, +rmf: F)
    -> List<&2, Wr<V4<O>>>:
  match cols:
    case Nil{}:
      Nil{}
    case +c <> rest:
      Wr{c, apply(~F, ~O, ~mul, ~un, ~cast, resid(~F, ~add, ~un, ~mem, row, c),
        mem(BW{}, 0n, c), rmf)} <>
        out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, row, rmf)

# Output stores of threads t, t + 1, ... given their reduced sums.
def block_out(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F, ~un: Un -> F -> F,
    ~cast: F -> O, ~mem: Buf -> Nat -> Nat -> V4<F>, sums: List<&2, F>, +t: Nat, +B: Nat,
    +n: Nat, +row: Nat) -> List<&2, Wr<V4<O>>>:
  match sums:
    case Nil{}:
      Nil{}
    case s <> rest:
      List.append(&2, Wr<V4<O>>,
        out_writes(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, cols_loop(n, B, t, n), row,
          un(Rms{}, s)),
        block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem, rest, 1n+t, B, n, row))

# Block `row` of the unfused norm, blockDim.x = 32 W, n = dim / 4 columns: every output store.
def unfused_out(~F: Data, ~O: Data, ~add: F -> F -> F, ~mul: F -> F -> F,
    ~fma: F -> F -> F -> F, ~un: Un -> F -> F, ~zero: F, ~cast: F -> O,
    ~mem: Buf -> Nat -> Nat -> V4<F>, +W: Nat, +n: Nat, +row: Nat) -> List<&2, Wr<V4<O>>>:
  +B = Nat.mul(32n, W)
  block_out(~F, ~O, ~add, ~mul, ~un, ~cast, ~mem,
    reduce_dyn(~F, ~add, ~zero, W,
      parts(~F, ~add, ~fma, ~un, ~zero, ~mem, B, 0n, B, n, row)),
    0n, B, n, row)

# ---- Launch shape (rms_norm_impl, norm.cu:426-434) ----

# threads = MIN(NUM_THREADS, CEIL_DIVIDE(dim / 4, 32) * 32), NUM_THREADS = 1024 (norm.cu:11,
# :431), as warps W = threads / 32 for n = dim / 4 columns.
def warps_for(+n: Nat) -> Nat:
  Nat.min(32n, Nat.div(Nat.add(n, 31n), 32n))

def member(+j: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case c <> rest:
      Bool.or(Nat.is_eq(c, j), member(j, rest))

def occ.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# How many times j occurs in xs.
def occ(+j: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case c <> rest:
      Nat.add(occ.bit(Nat.is_eq(c, j)), occ(j, rest))

# ---- Aliasing: program-order memory events of one thread ----

# Loads of x, r, w; residual store; block reduction barrier; output store (column indices).
type Ev is Data:
  RdX{c: Nat}
  RdR{c: Nat}
  RdW{c: Nat}
  WrR{c: Nat}
  Sync{}
  WrY{c: Nat}

def raw_ok.rd(hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      False{}
    case False{}:
      rest

# True iff no load of a residual column comes after a store to that column (in-place r: an input
# element is never overwritten before its last read); `written` holds the columns stored so far.
def raw_ok(evs: List<&2, Ev>, +written: List<&2, Nat>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> rest:
      match e:
        case RdR{+c}:
          raw_ok.rd(member(c, written), raw_ok(rest, written))
        case WrR{c}:
          raw_ok(rest, c <> written)
        case RdX{c}:
          raw_ok(rest, written)
        case RdW{c}:
          raw_ok(rest, written)
        case Sync{}:
          raw_ok(rest, written)
        case WrY{c}:
          raw_ok(rest, written)

# ---- Layer chain, unfused ----

# Forward-loop modules: a TransformerBlock (link: it defers its closing add to the next module,
# transformer.py:235-236) or any other module (embedding, final norm, head).
type Mod is Data:
  Blk{link: Bool}
  Other{}

# What a block hands on: Stop (it returned before its MLP: prefill early return,
# transformer.py:201-202, or no MLP) or Half (stream x after the attention half, MLP output y).
type Step<-S: Data> is Data:
  Stop{x: S}
  Half{x: S, y: S}

# A block's input-norm step: the stream it continues with and the normed input h.
type Normed<-S: Data, -H: Data> is Data:
  Normed{x: S, h: H}

# Every block's input-norm step in order, and the stream after the loop.
type Run<-S: Data, -H: Data> is Data:
  Run{seen: List<&2, Normed<S, H>>, x: S}

def run.cons(~S: Data, ~H: Data, +n: Normed<S, H>, r: Run<S, H>) -> Run<S, H>:
  match r:
    case Run{seen, x}:
      Run{n <> seen, x}

def normed.x(~S: Data, ~H: Data, n: Normed<S, H>) -> S:
  match n:
    case Normed{x, h}:
      x

def normed.h(~S: Data, ~H: Data, n: Normed<S, H>) -> H:
  match n:
    case Normed{x, h}:
      h

# `x += y` applied (Half) or nothing to add (Stop).
def settle(~S: Data, ~plus: S -> S -> S, st: Step<S>) -> S:
  match st:
    case Stop{x}:
      x
    case Half{x, y}:
      plus(x, y)

# Unfused input-norm step: the stream with the closing add done, then attn_norm.forward(x).
def u_step(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H, st: Step<S>, +i: Nat)
    -> Normed<S, H>:
  +x = settle(~S, ~plus, st)
  Normed{x, norm(i, x)}

# The unfused forward loop: every block adds its MLP output in place before the next module runs.
def u_go(~S: Data, ~H: Data, ~plus: S -> S -> S, ~norm: Nat -> S -> H,
    ~body: Nat -> S -> H -> Step<S>, ~other: Nat -> S -> S, mods: List<&2, Mod>, +i: Nat,
    st: Step<S>) -> Run<S, H>:
  match mods:
    case Nil{}:
      Run{Nil{}, settle(~S, ~plus, st)}
    case Blk{link} <> rest:
      +ns = u_step(~S, ~H, ~plus, ~norm, st, i)
      run.cons(~S, ~H, ns,
        u_go(~S, ~H, ~plus, ~norm, ~body, ~other, rest, 1n+i,
          body(i, normed.x(~S, ~H, ns), normed.h(~S, ~H, ns))))
    case Other{} <> rest:
      u_go(~S, ~H, ~plus, ~norm, ~body, ~other, rest, 1n+i,
        Stop{other(i, settle(~S, ~plus, st))})

# link_residual_deferral's rule (model.py:173-175): only a block directly followed by another
# TransformerBlock may defer (pend: the module before the list's head deferred).
def linked_ok(mods: List<&2, Mod>, pend: Bool) -> Bool:
  match mods:
    case Nil{}:
      True{}
    case m <> rest:
      match m:
        case Blk{link}:
          linked_ok(rest, link)
        case Other{}:
          Bool.and(Bool.not(pend), linked_ok(rest, False{}))
