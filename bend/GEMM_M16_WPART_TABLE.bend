# Finite differential table of the slot-weighted split-K partition model (bend/gemm_m16_wpart.bend,
# ext patch 2105), compared byte for byte by bend/gemm_m16_wpart_diff.py against the patch's host
# (exl3_gemm_m16g.cu) and kernel (exl3_gemm_m16g_kernel.cuh) index expressions compiled for the CPU.
# Fixed configurations (G 164, nsm 82): the routed bundles gdn / attn at the g_weights row (100, 91)
# and at the forced (1, 1), and the draft bundles (routed at (1, 1)). Rows per configuration
# (every value is an Impl def; the printer only enumerates indices):
#   C name k= ns= G= nsm= w=w0,w1 groups= KT= total= WG= valid= mc= ws= fits=
#   S name w0,w1 start(0) .. start(G)
#   g name w0,w1 g lo= hi= nc=                  g < groups
# groups = sum n / 512, KT = k / 16, total = groups * KT. Sections are balanced trees of parallel
# calls over index ranges [base, base + 2^d); each g row starts with its newline, so the output has
# no blank lines.
import Base
import ./gemm_m16_wpart.bend as Impl

def num(+n: Nat) -> String:
  Nat.show(n)

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def join(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case +x <> rest:
      match rest:
        case Nil{}:
          num(x)
        case _:
          num(x) ++ "," ++ join(rest)

# sum n / 512 (EXL3_M16_GW)
def groups(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> rest:
      Nat.add(Nat.div(x, 512n), groups(rest))

type Name is Data:
  Gdn{}
  Attn{}
  DraftQkv{}
  DraftKv4{}
  DraftKv2{}
  DraftFc{}

def name(n: Name) -> String:
  match n:
    case Gdn{}:
      "gdn"
    case Attn{}:
      "attn"
    case DraftQkv{}:
      "draft_qkv"
    case DraftKv4{}:
      "draft_kv4"
    case DraftKv2{}:
      "draft_kv2"
    case DraftFc{}:
      "draft_fc"

# One printed configuration: name, KT, total, G, nsm, w0, w1
type Cfg is Data:
  Cfg{nm: Name, KT: Nat, total: Nat, G: Nat, nsm: Nat, w0: Nat, w1: Nat}

def c_nm(+c: Cfg) -> Name:
  match c:
    case Cfg{nm, _, _, _, _, _, _}:
      nm

def c_KT(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, KT, _, _, _, _, _}:
      KT

def c_total(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, total, _, _, _, _}:
      total

def c_G(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, _, G, _, _, _}:
      G

def c_nsm(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, _, _, nsm, _, _}:
      nsm

def c_w0(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, _, _, _, w0, _}:
      w0

def c_w1(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, _, _, _, _, w1}:
      w1

# "<name> <w0>,<w1>" row prefix
def tag(+c: Cfg) -> String:
  name(c_nm(c)) ++ " " ++ num(c_w0(c)) ++ "," ++ num(c_w1(c))

def row_s(+c: Cfg, +b: Nat) -> String:
  " " ++ num(Impl.start(b, c_total(c), c_G(c), c_nsm(c), c_w0(c), c_w1(c)))

def row_g(+c: Cfg, +g: Nat) -> String:
  +KT = c_KT(c)
  +total = c_total(c)
  +G = c_G(c)
  +nsm = c_nsm(c)
  +w0 = c_w0(c)
  +w1 = c_w1(c)
  "\ng " ++ tag(c) ++ " " ++ num(g) ++ " lo=" ++ num(Impl.first_contrib(g, KT, total, G, nsm, w0, w1)) ++
    " hi=" ++ num(Impl.last_contrib(g, KT, total, G, nsm, w0, w1)) ++
    " nc=" ++ num(Impl.nc(g, KT, total, G, nsm, w0, w1))

type Sec is Data:
  KS{}
  KG{}

def row(kind: Sec, +c: Cfg, +i: Nat) -> String:
  match kind:
    case KS{}:
      row_s(c, i)
    case KG{}:
      row_g(c, i)

def leaf(inside: Bool, +kind: Sec, +c: Cfg, +i: Nat) -> String:
  match inside:
    case True{}:
      row(kind, c, i)
    case False{}:
      ""

def tree(+kind: Sec, +c: Cfg, +d: Nat, +base: Nat, +n: Nat) -> String:
  match d:
    case 0n:
      leaf(Nat.is_lt(base, n), kind, c, base)
    case 1n+p:
      +half = Nat.pow(2n, p)
      left right = tree(kind, c, p, base, n) tree(kind, c, p, Nat.add(base, half), n)
      String.append(left, right)

# bits(m) = number of binary digits of m; depth(n) = bits(n - 1): smallest d with n <= 2^d
def bits.pick(zero: Bool, rest: Nat) -> Nat:
  match zero:
    case True{}:
      0n
    case False{}:
      1n+rest

def bits.go(fuel: Nat, +m: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      bits.pick(Nat.is_eq(m, 0n), bits.go(f, Nat.div(m, 2n)))

def depth(+n: Nat) -> Nat:
  bits.go(n, Nat.sub(n, 1n))

def section(+kind: Sec, +c: Cfg, +n: Nat) -> String:
  tree(kind, c, depth(n), 0n, n)

def table(+nm: Name, +k: Nat, +ns: List<&2, Nat>, +w0: Nat, +w1: Nat) -> IO(Unit):
  +G = Impl.grid_served()
  +nsm = Impl.nsm_served()
  +gr = groups(ns)
  +KT = Nat.div(k, 16n)
  +total = Nat.mul(gr, KT)
  +mc = Impl.max_contrib(gr, KT, G, nsm, w0, w1)
  +c : Cfg = Cfg{nm, KT, total, G, nsm, w0, w1}
  do IO<Unit>:
    IO.print("C " ++ name(nm) ++ " k=" ++ num(k) ++ " ns=" ++ join(ns) ++ " G=" ++ num(G) ++
      " nsm=" ++ num(nsm) ++ " w=" ++ num(w0) ++ "," ++ num(w1) ++ " groups=" ++ num(gr) ++
      " KT=" ++ num(KT) ++ " total=" ++ num(total) ++ " WG=" ++ num(Impl.wpre(G, nsm, w0, w1)) ++
      " valid=" ++ bit(Impl.weights_valid(total, G, nsm, w0, w1)) ++ " mc=" ++ num(mc) ++
      " ws=" ++ num(Impl.ws_bytes(gr, mc)) ++
      " fits=" ++ bit(Impl.launch_fits(gr, KT, G, nsm, w0, w1)))
    IO.print("S " ++ tag(c) ++ section(KS{}, c, 1n+G) ++ section(KG{}, c, gr))

# (name, k, widths, w0, w1): the configuration list gemm_m16_wpart_diff.py checks against the tree's
# g_routes draft rows and g_weights rows
def main() -> IO(Unit):
  do IO<Unit>:
    table(Gdn{}, 5120n, [10240n, 6144n], Impl.w0_served(), Impl.w1_served())
    table(Gdn{}, 5120n, [10240n, 6144n], 1n, 1n)
    table(Attn{}, 5120n, [12288n, 1024n, 1024n], Impl.w0_served(), Impl.w1_served())
    table(Attn{}, 5120n, [12288n, 1024n, 1024n], 1n, 1n)
    table(DraftQkv{}, 5120n, [4096n, 1024n, 1024n], 1n, 1n)
    table(DraftKv4{}, 5120n, [1024n, 1024n, 1024n, 1024n], 1n, 1n)
    table(DraftKv2{}, 5120n, [1024n, 1024n], 1n, 1n)
    table(DraftFc{}, 25600n, [5120n], 1n, 1n)
