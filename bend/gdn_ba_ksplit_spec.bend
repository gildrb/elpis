# Independent reference for the ext 5106 b/a GEMV (gdn_ba_ksplit.bend): the intended summation of one
# b/a value, the partial-slot layout and the order predicates, written without the kernel's thread
# decomposition, lane-array shuffle emulation or loop structure.
import Base
import ./gdn_ba_ksplit.bend as Impl

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# ---- element ownership: element j < 2560 of a row belongs to thread j % 512, iteration j / 512.
def owner_t(+j: Nat) -> Nat:
  Nat.mod(j, 512n)

def owner_i(+j: Nat) -> Nat:
  Nat.div(j, 512n)

# ---- the value of b (ab = 0) or a (ab = 1) of row s. Row weights: b = h, a = H + h.
def wrow(+ab: Nat, +h: Nat, +H: Nat) -> Nat:
  match ab:
    case 0n:
      h
    case 1n+z:
      Nat.add(H, h)

# Thread t's chain: its elements t, t + 512, ... (< k2) in ascending order, two fmaf each (component
# 0 then 1), from 0.0f. x2 = s * k2 + j, w2 = row * k2 + j.
def chain_el(c: Bool, +j: Nat, +s: Nat, +row: Nat, +k2: Nat, acc: Impl.Ex) -> Impl.Ex:
  match c:
    case True{}:
      Impl.Fma{Nat.add(Nat.mul(s, k2), j), Nat.add(Nat.mul(row, k2), j), 1n,
        Impl.Fma{Nat.add(Nat.mul(s, k2), j), Nat.add(Nat.mul(row, k2), j), 0n, acc}}
    case False{}:
      acc

def chain_go(fuel: Nat, +j: Nat, +s: Nat, +row: Nat, +k2: Nat, acc: Impl.Ex) -> Impl.Ex:
  match fuel:
    case 0n:
      acc
    case 1n+more:
      chain_go(more, Nat.add(j, 512n), s, row, k2, chain_el(Nat.is_lt(j, k2), j, s, row, k2, acc))

def chain(+t: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat) -> Impl.Ex:
  chain_go(5n, t, s, wrow(ab, h, H), k2, Impl.ZeroF{})

# The 32 chains of warp w, lanes l.. (the values the warp reduces).
def clanes(fuel: Nat, +l: Nat, +w: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat) -> List<&2, Impl.Ex>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+more:
      chain(Nat.add(Nat.mul(w, 32n), l), s, ab, k2, h, H) <> clanes(more, 1n+l, w, s, ab, k2, h, H)

# Offset of level n of the lane tree (n = 5 is the last addition, offset 1).
def off(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+m:
      match m:
        case 0n:
          16n
        case 1n+m2:
          match m2:
            case 0n:
              8n
            case 1n+m3:
              match m3:
                case 0n:
                  4n
                case 1n+m4:
                  match m4:
                    case 0n:
                      2n
                    case 1n+m5:
                      1n

# The warp sum of lane l after n levels: lane l plus lane l + off(n) of the level below.
def wtree(+n: Nat, +l: Nat, +w: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat) -> Impl.Ex:
  match n:
    case 0n:
      chain(Nat.add(Nat.mul(w, 32n), l), s, ab, k2, h, H)
    case 1n+m:
      Impl.Add{wtree(m, l, w, s, ab, k2, h, H), wtree(m, Nat.add(l, off(1n+m)), w, s, ab, k2, h, H)}

# Lanes a tree of n levels at lane l sums, left to right (lane indices).
def tree_lanes(+n: Nat, +l: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      l <> Nil{}
    case 1n+m:
      List.append(&2, Nat, tree_lanes(m, l), tree_lanes(m, Nat.add(l, off(1n+m))))

def ncount(+x: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      Nat.add(bit(Nat.is_eq(x, y)), ncount(x, rest))

def once_upto(fuel: Nat, +l: Nat, +xs: List<&2, Nat>) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+more:
      Bool.and(Nat.is_eq(ncount(l, xs), 1n), once_upto(more, 1n+l, xs))

# xs lists every lane 0..31 exactly once and nothing else.
def perm32(+xs: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, Nat, xs), 32n), once_upto(32n, 0n, xs))

# Warps 0..15 in order, from 0.0f, then the bias of the row weight.
def wfold(fuel: Nat, +w: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, v: Impl.Ex) -> Impl.Ex:
  match fuel:
    case 0n:
      v
    case 1n+more:
      wfold(more, 1n+w, s, ab, k2, h, H, Impl.Add{v, wtree(5n, 0n, w, s, ab, k2, h, H)})

def value(+s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, hb: Bool) -> Impl.Ex:
  Impl.with_bias(hb, wrow(ab, h, H), wfold(16n, 0n, s, ab, k2, h, H, Impl.ZeroF{}))

# ---- partial slots: warp w's partial of (row s, b|a) lives at 16 w + 8 ab + s
def slot(+w: Nat, +s: Nat, +ab: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(w, 16n), Nat.mul(ab, 8n)), s)

# ---- event order predicates
def tag(e: Impl.Ev) -> Nat:
  match e:
    case Impl.KsLoad{}:
      0n
    case Impl.State{}:
      1n
    case Impl.NormOps{}:
      2n
    case Impl.Conv{}:
      3n
    case Impl.Gemv{}:
      4n
    case Impl.KsFma{}:
      5n
    case Impl.KsTree{}:
      6n
    case Impl.PartW{}:
      7n
    case Impl.Bar{}:
      8n
    case Impl.Arrive{}:
      9n
    case Impl.WinV{}:
      10n
    case Impl.PartR{}:
      11n
    case Impl.L2{}:
      12n
    case Impl.Dot2W{}:
      13n

def count(+e: Impl.Ev, xs: List<&2, Impl.Ev>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> rest:
      Nat.add(bit(Nat.is_eq(tag(e), tag(x))), count(e, rest))

# Scanner state: 0 = no a yet, 1 = after an a, 2 = a barrier after the last a, 3 = b met in state 2
# (accept), 4 = b met otherwise (reject); 3 and 4 absorb.
def fenced_next(st: Nat, isb: Bool, isa: Bool, isbar: Bool) -> Nat:
  match st:
    case 0n:
      match isb:
        case True{}:
          4n
        case False{}:
          match isa:
            case True{}:
              1n
            case False{}:
              0n
    case 1n+m:
      match m:
        case 0n:
          match isb:
            case True{}:
              4n
            case False{}:
              match isa:
                case True{}:
                  1n
                case False{}:
                  match isbar:
                    case True{}:
                      2n
                    case False{}:
                      1n
        case 1n+m2:
          match m2:
            case 0n:
              match isb:
                case True{}:
                  3n
                case False{}:
                  match isa:
                    case True{}:
                      1n
                    case False{}:
                      2n
            case 1n+m3:
              Nat.add(3n, m3)

def fenced_go(xs: List<&2, Impl.Ev>, +a: Impl.Ev, +b: Impl.Ev, +st: Nat) -> Nat:
  match xs:
    case Nil{}:
      st
    case +x <> rest:
      fenced_go(rest, a, b, fenced_next(st, Nat.is_eq(tag(x), tag(b)), Nat.is_eq(tag(x), tag(a)), Nat.is_eq(tag(x), 8n)))

# The first b comes after an a and after a __syncthreads() that follows the last a before it.
def fenced(+a: Impl.Ev, +b: Impl.Ev, xs: List<&2, Impl.Ev>) -> Bool:
  Nat.is_eq(fenced_go(xs, a, b, 0n), 3n)
