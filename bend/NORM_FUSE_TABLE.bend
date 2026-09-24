# Finite differential table of the residual add + RMSNorm fusion model (bend/norm_fuse.bend and
# its unfused reference bend/norm_fuse_spec.bend), compared byte for byte by
# bend/norm_fuse_diff.py against the pinned norm.cu kernels compiled for the CPU.
# Instance: every float is a U32 hash of the operation tree that produced it (a hash algebra):
# add and mul are commutative (operands sorted, as IEEE-754 add/mul commute), fma commutes in its
# two factors only, div is ordered; no operation is associative, so any change of accumulation
# order, reduction tree, operand or element index changes the hashes. Loads are leaves
# X(row, e), R(row, e), W(e); Rt is the identity (fp32 residual stream, the served dtype); Wb adds
# constant_bias = 1.0f; Rms is rsqrtf(sum / (float) dim + 1e-6f) * 1.0f; the output cast is a
# node. Shapes: dim 96 (W = 1, reduce_dyn's one-warp return) rows 2, dim 5120 (served: W = 32,
# REG_COLS = 2) rows 16.
import Base
import ./norm_fuse.bend as Impl
import ./norm_fuse_spec.bend as Spec

def f15(+z: U32) -> U32:
  U32.xor(z, U32.shrn(z, 15n))

def st(h: U32, v: U32) -> U32:
  f15(U32.add(U32.mul(U32.xor(h, v), 2654435761), 1013904223))

def n1(t: U32, a: U32) -> U32:
  st(t, a)

def n2(t: U32, a: U32, b: U32) -> U32:
  st(st(t, a), b)

def n3(t: U32, a: U32, b: U32, c: U32) -> U32:
  st(st(st(t, a), b), c)

def hk(bits: U32) -> U32:
  n1(4, bits)

def hadd(a0: U32, b0: U32) -> U32:
  +a = a0
  +b = b0
  n2(1, U32.min(a, b), U32.max(a, b))

def hmul(a0: U32, b0: U32) -> U32:
  +a = a0
  +b = b0
  n2(2, U32.min(a, b), U32.max(a, b))

def hfma(a0: U32, b0: U32, c: U32) -> U32:
  +a = a0
  +b = b0
  n3(3, U32.min(a, b), U32.max(a, b), c)

def hcast(a: U32) -> U32:
  n1(7, a)

# Rt, Wb and Rms of a row of dim elements (dimbits: the bits of (float) dim).
def hun.go(u: Spec.Un, a: U32, dimbits: U32) -> U32:
  match u:
    case Spec.Rt{}:
      a
    case Spec.Wb{}:
      hadd(a, hk(1065353216))
    case Spec.Rms{}:
      hmul(n1(6, hadd(n2(5, a, hk(dimbits)), hk(897988541))), hk(1065353216))

# 96.0f = 0x42C00000
def hun96(u: Spec.Un, a: U32) -> U32:
  hun.go(u, a, 1119879168)

# 5120.0f = 0x45A00000
def hun5120(u: Spec.Un, a: U32) -> U32:
  hun.go(u, a, 1168113664)

def hmem.leaf(b: Spec.Buf, +row: Nat, +e: Nat) -> U32:
  match b:
    case Spec.BX{}:
      n2(8, U32.from_nat(row), U32.from_nat(e))
    case Spec.BR{}:
      n2(9, U32.from_nat(row), U32.from_nat(e))
    case Spec.BW{}:
      n1(10, U32.from_nat(e))

def hmem(b0: Spec.Buf, row0: Nat, c: Nat) -> Spec.V4<U32>:
  +b = b0
  +row = row0
  +e = Nat.mul(4n, c)
  Spec.V4{hmem.leaf(b, row, e), hmem.leaf(b, row, 1n+e), hmem.leaf(b, row, 2n+e),
    hmem.leaf(b, row, 3n+e)}

def v4(v: Spec.V4<U32>) -> String:
  match v:
    case Spec.V4{a, b, c, d}:
      U32.show(a) ++ " " ++ U32.show(b) ++ " " ++ U32.show(c) ++ " " ++ U32.show(d)

# Thread label of every store, in thread order (one per visited column).
def labels.go(cols: List<&2, Nat>, +t: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match cols:
    case Nil{}:
      rest
    case c <> more:
      t <> labels.go(more, t, rest)

def labels_reg(k: Nat, +t: Nat, +B: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      labels.go(Impl.cols_reg(2n, B, t, n), t, labels_reg(m, 1n+t, B, n))

def labels_loop(k: Nat, +t: Nat, +B: Nat, +n: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      labels.go(Spec.cols_loop(n, B, t, n), t, labels_loop(m, 1n+t, B, n))

def stores(+tag: String, +row: Nat, ts: List<&2, Nat>, ws: List<&2, Spec.Wr<Spec.V4<U32>>>)
    -> String:
  match ts ws:
    case t <> tr Spec.Wr{c, v} <> wr:
      tag ++ " row=" ++ Nat.show(row) ++ " t=" ++ Nat.show(t) ++ " c=" ++ Nat.show(c) ++ " " ++
        v4(v) ++ "\n" ++ stores(tag, row, tr, wr)
    case _ _:
      ""

# torch `x += y`: the residual stream after the add, column by column.
def torch_rows(k: Nat, +row: Nat, +c: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      "T row=" ++ Nat.show(row) ++ " c=" ++ Nat.show(c) ++ " " ++
        v4(Spec.resid(~U32, ~hadd, ~hun96, ~hmem, row, c)) ++ "\n" ++ torch_rows(m, row, 1n+c)

def row_text(~hun: Spec.Un -> U32 -> U32, +W: Nat, +n: Nat, +row: Nat) -> String:
  +B = Nat.mul(32n, W)
  stores("R", row, labels_reg(B, 0n, B, n),
      Impl.fused_resid(~U32, ~hadd, ~hun, ~hmem, W, 2n, n, row)) ++
    stores("Y", row, labels_reg(B, 0n, B, n),
      Impl.fused_out(~U32, ~U32, ~hadd, ~hmul, ~hfma, ~hun, ~(hk(0)), ~hcast, ~hmem, W, 2n, n,
        row)) ++
    torch_rows(n, row, 0n) ++
    stores("U", row, labels_loop(B, 0n, B, n),
      Spec.unfused_out(~U32, ~U32, ~hadd, ~hmul, ~hfma, ~hun, ~(hk(0)), ~hcast, ~hmem, W, n,
        row))

def rows(~hun: Spec.Un -> U32 -> U32, k: Nat, +W: Nat, +n: Nat, +row: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(row_text(~hun, W, n, row))
        rows(~hun, m, W, n, 1n+row)

def shape(~hun: Spec.Un -> U32 -> U32, +dim: Nat, +rs: Nat) -> IO(Unit):
  +n = Nat.div(dim, 4n)
  +W = Spec.warps_for(n)
  do IO<Unit>:
    IO.print("shape dim=" ++ Nat.show(dim) ++ " rows=" ++ Nat.show(rs) ++ " W=" ++ Nat.show(W))
    rows(~hun, rs, W, n, 0n)

def main() -> IO(Unit):
  do IO<Unit>:
    shape(~hun96, 96n, 2n)
    shape(~hun5120, 5120n, 16n)
