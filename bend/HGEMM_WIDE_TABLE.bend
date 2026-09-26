# Finite table of the hgemm_wide.bend model, compared line by line by hgemm_wide_diff.py against a C program
# built from the patch's own source lines (3011: hgemm_f16acc_wide.cuh, hgemm_f16acc.cu). Not a proof: the link
# between the Nat model and the CUDA text on the instances below.
import Base
import ./hgemm_wide.bend as Impl
import ./hgemm_wide_spec.bend as Spec

def nl(s: String) -> String:
  s ++ "\n"

def n(x: Nat) -> String:
  Nat.show(x)

# raster: "R G gn gm b tile_m tile_n" for every block id of the grid
def raster_b(left: Nat, +b: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      nl("R " ++ n(G) ++ " " ++ n(gn) ++ " " ++ n(gm) ++ " " ++ n(b) ++ " " ++ n(Impl.tile_m(b, G, gn, gm)) ++ " " ++
        n(Impl.tile_n(b, G, gn, gm))) ++ raster_b(r, 1n+b, G, gn, gm)

def raster(+G: Nat, +gn: Nat, +gm: Nat) -> String:
  raster_b(Nat.mul(gm, gn), 0n, G, gn, gm)

# stores: "S t i j h e row col" (in-tile, bm = bn = 0)
def st_e(left: Nat, +t: Nat, +i: Nat, +j: Nat, +h: Nat, +e: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      nl("S " ++ n(t) ++ " " ++ n(i) ++ " " ++ n(j) ++ " " ++ n(h) ++ " " ++ n(e) ++ " " ++ n(Impl.row_of(0n, t, i, h)) ++ " " ++
        n(Impl.col_of(0n, t, j, e))) ++ st_e(r, t, i, j, h, 1n+e)

def st_h(left: Nat, +t: Nat, +i: Nat, +j: Nat, +h: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      st_e(2n, t, i, j, h, 0n) ++ st_h(r, t, i, j, 1n+h)

def st_j(left: Nat, +t: Nat, +i: Nat, +j: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      st_h(2n, t, i, j, 0n) ++ st_j(r, t, i, 1n+j)

def st_i(left: Nat, +t: Nat, +i: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      st_j(8n, t, i, 0n) ++ st_i(r, t, 1n+i)

def st_t(left: Nat, +t: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      st_i(4n, t, 0n) ++ st_t(r, 1n+t)

# stage writes: "A t i dest" / "B t i dest"
def ld_i(left: Nat, +t: Nat, +i: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      nl("A " ++ n(t) ++ " " ++ n(i) ++ " " ++ n(Impl.a_dest(t, i))) ++
      nl("B " ++ n(t) ++ " " ++ n(i) ++ " " ++ n(Impl.b_dest(t, i))) ++ ld_i(r, t, 1n+i)

def ld_t(left: Nat, +t: Nat) -> String:
  match left:
    case 0n:
      ""
    case 1n+r:
      ld_i(4n, t, 0n) ++ ld_t(r, 1n+t)

# accumulation order: "K kernel K p0 p1 ; ..." partials of one element
def part(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      " " ++ n(x) ++ part(rest)

def parts(xs: List<&2, List<&2, Nat>>) -> String:
  match xs:
    case Nil{}:
      ""
    case p <> rest:
      part(p) ++ " ;" ++ parts(rest)

def korder(+K: Nat) -> String:
  nl("K wide " ++ n(K) ++ parts(Impl.wide_acc(K))) ++ nl("K served " ++ n(K) ++ parts(Impl.served_acc(K)))

# route: "Q env major minor batch M K N f route"
def env_s(e: Spec.HwEnv) -> String:
  match e:
    case Spec.HwUnset{}:
      "unset"
    case Spec.HwOne{}:
      "1"
    case Spec.HwZero{}:
      "0"
    case Spec.HwOther{}:
      "x"

def route_s(r: Spec.HwRoute) -> String:
  match r:
    case Spec.HwWide{}:
      "wide"
    case Spec.HwServed{}:
      "served"
    case Spec.HwError{}:
      "error"

def b_s(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def q(e: Spec.HwEnv, +e2: Spec.HwEnv, +ma: U32, +mi: U32, +ba: U32, +M: U32, +K: U32, +N: U32, +f: Bool) -> String:
  nl("Q " ++ env_s(e2) ++ " " ++ U32.show(ma) ++ " " ++ U32.show(mi) ++ " " ++ U32.show(ba) ++ " " ++ U32.show(M) ++ " " ++
    U32.show(K) ++ " " ++ U32.show(N) ++ " " ++ b_s(f) ++ " " ++ route_s(Impl.route(e, ma, mi, ba, M, K, N, f)))

def routes_env(e: Spec.HwEnv, +e2: Spec.HwEnv) -> String:
  q(e2, e2, 8, 6, 1, 2048, 5120, 1024, False{}) ++ q(e2, e2, 8, 6, 1, 2048, 5120, 6144, True{}) ++
  q(e2, e2, 8, 6, 1, 2048, 5120, 10240, True{}) ++ q(e2, e2, 8, 6, 1, 2048, 5120, 12288, False{}) ++
  q(e2, e2, 8, 6, 1, 1792, 5120, 17408, False{}) ++ q(e2, e2, 8, 6, 1, 1024, 6144, 5120, True{}) ++
  q(e2, e2, 8, 6, 1, 4096, 17408, 5120, True{}) ++ q(e2, e2, 8, 6, 1, 2048, 25600, 5120, False{}) ++
  q(e2, e2, 8, 6, 1, 1023, 5120, 17408, False{}) ++ q(e2, e2, 8, 6, 1, 247, 5120, 17408, False{}) ++
  q(e2, e2, 8, 6, 2, 2048, 5120, 17408, False{}) ++ q(e2, e2, 8, 9, 1, 2048, 5120, 17408, False{}) ++
  q(e2, e2, 12, 0, 1, 2048, 5120, 17408, False{}) ++ q(e2, e2, 8, 0, 1, 2048, 5120, 17408, False{}) ++
  q(e2, e2, 8, 6, 1, 2048, 5120, 17408, True{}) ++ q(e2, e2, 8, 6, 1, 2048, 5120, 1024, True{}) ++
  q(e2, e2, 8, 6, 1, 2048, 4096, 4096, False{}) ++ q(e2, e2, 8, 6, 1, 2048, 5120, 17536, False{}) ++
  q(e2, e2, 8, 6, 1, 2048, 5248, 5120, True{}) ++ q(e2, e2, 8, 6, 1, 2048, 25600, 5120, True{})

def routes() -> String:
  routes_env(Spec.HwUnset{}, Spec.HwUnset{}) ++ routes_env(Spec.HwOne{}, Spec.HwOne{}) ++
  routes_env(Spec.HwZero{}, Spec.HwZero{}) ++ routes_env(Spec.HwOther{}, Spec.HwOther{})

def grids(+M: Nat) -> String:
  nl("M " ++ n(M) ++ " " ++ n(Impl.grid_m(M)))

def table() -> String:
  raster(8n, 1n, 1n) ++ raster(8n, 3n, 5n) ++ raster(8n, 8n, 9n) ++ raster(8n, 5n, 17n) ++ raster(8n, 2n, 20n) ++
  raster(3n, 4n, 7n) ++ raster(1n, 3n, 4n) ++
  st_t(128n, 0n) ++ ld_t(128n, 0n) ++
  korder(64n) ++ korder(128n) ++ korder(320n) ++
  routes() ++
  grids(1n) ++ grids(127n) ++ grids(128n) ++ grids(129n) ++ grids(1100n) ++ grids(2048n) ++ grids(262143n)

def main() -> IO(Unit):
  IO.print(table())
