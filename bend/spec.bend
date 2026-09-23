# Independent sequential specification. No Range or implementation calls.
# Control supplies only the shared Plan and Shape datatypes/constructors.
import Base
import ./control.bend as Control

def seq(n: Nat, +start: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      start <> seq(p, 1n+start)

# Exact order and exact length, not merely a permutation or membership check.
# An omitted, duplicated, reordered or extra element makes this uninhabited.
def Ordered(n: Nat, start: Nat, xs: List<&2, Nat>) -> Type:
  match n xs:
    case 0n Nil{}:
      Unit
    case 0n h <> t:
      Empty
    case 1n+p Nil{}:
      Empty
    case 1n+p h <> t:
      {h == start : Nat} & Ordered(p, 1n+start, t)

# The reference folds independent segment lengths into successive boundaries.
def scan(sizes: List<&2, Nat>, +offset: Nat) -> List<&2, Nat>:
  match sizes:
    case Nil{}:
      [offset]
    case size <> rest:
      offset <> scan(rest, Nat.add(offset, size))

def sizes(+dim: Nat) -> List<&2, Nat>:
  [Nat.mul(64n, dim), Nat.mul(2n, dim), Nat.mul(2n, dim), 256n,
    Nat.mul(32n, dim), Nat.mul(2n, dim), 256n, 256n]

def offsets(dim: Nat) -> List<&2, Nat>:
  scan(sizes(dim), 0n)

def dimension(shape: Control.Shape) -> Nat:
  match shape:
    case Control.Target{}:
      256n
    case Control.Draft{}:
      128n

def tile_bytes(shape: Control.Shape) -> Nat:
  match shape:
    case Control.Target{}:
      26880n
    case Control.Draft{}:
      13824n

# All boundaries stay in the head-local backing interval, including its end.
def bounded(xs: List<&2, Nat>, +end: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Nat.is_le(x, end), bounded(rest, end))

def fields() -> List<&2, Nat>:
  geometry = {[262144n, 1024n, 263168n, 128n, 2057n,
    8n, 128n, 32n, 8n, 2n, 4n, 128n, 2184n, 2304n,
    256n, 4n, 16n, 128n, 8n, 5n] : List<&2, Nat>}
  List.append(&2, Nat, geometry,
    List.append(&2, Nat,
      List.append(&2, Nat, offsets(256n), offsets(128n)), [4n, 2n, 0n, 4n]))

def native() -> Control.Plan:
  Control.Plan{fields(), seq(2056n, 1n)}

def choose(valid: Bool) -> Maybe<&2, Control.Plan>:
  match valid:
    case True{}:
      Some{native()}
    case False{}:
      None{}

# This predicate is intentionally written independently of Control.valid.
def plan(context: Nat, pool: Nat, page_size: Nat) -> Maybe<&2, Control.Plan>:
  choose(Bool.and(Nat.is_eq(context, 262144n),
    Bool.and(Nat.is_eq(pool, 263168n), Nat.is_eq(page_size, 128n))))

def rows(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      Nat.show(h) ++ "\n" ++ rows(t)

def protocol() -> String:
  "QWEN_KVARN_PLAN_V3\n" ++ rows(fields()) ++ "FREE_PAGES\n" ++
    rows(seq(2056n, 1n)) ++ "END_QWEN_KVARN_PLAN"
