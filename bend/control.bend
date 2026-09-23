# Real startup allocation/layout planner, not a model of CUDA or F32 kernels.
# Production consumes both fields and free_pages; transactions stay native.
import Base
import ./range.bend as Range

type Shape is Data:
  Target{}
  Draft{}

type Plan is Data:
  Plan{fields: List<&2, Nat>, free_pages: List<&2, Nat>}

def context() -> Nat:
  262144n

def headroom() -> Nat:
  1024n

def pool() -> Nat:
  Nat.add(context(), headroom())

def page_size() -> Nat:
  128n

def pages() -> Nat:
  1n+Nat.div(pool(), page_size())

def dimension(shape: Shape) -> Nat:
  match shape:
    case Target{}:
      256n
    case Draft{}:
      128n

def heads(shape: Shape) -> Nat:
  match shape:
    case Target{}:
      4n
    case Draft{}:
      8n

def layers(shape: Shape) -> Nat:
  match shape:
    case Target{}:
      16n
    case Draft{}:
      5n

# One head's k4v2 tile, with fp16 metadata and fixed 128-token pages.
# No rounded divisions: 64 and 32 are exactly 128/2 and 128/4.
def offsets(+dim: Nat) -> List<&2, Nat>:
  +ks = Nat.mul(64n, dim)
  +kz = Nat.add(ks, Nat.mul(2n, dim))
  +kt = Nat.add(kz, Nat.mul(2n, dim))
  +vp = Nat.add(kt, 256n)
  +vc = Nat.add(vp, Nat.mul(32n, dim))
  +vs = Nat.add(vc, Nat.mul(2n, dim))
  +vz = Nat.add(vs, 256n)
  [0n, ks, kz, kt, vp, vc, vs, vz, Nat.add(vz, 256n)]

def draft_window() -> Nat:
  Nat.add(2048n, Nat.add(page_size(), 8n))

def draft_visible() -> Nat:
  Nat.mul(Nat.div(Nat.add(draft_window(), 127n), page_size()), page_size())

def write_span() -> Nat:
  1n+Nat.div(Nat.add(127n, Nat.sub(page_size(), 1n)), page_size())

def admission_slots() -> Nat:
  Nat.add(write_span(), 2n)

# The 38 wire fields; adapter.py maps names, but does not supply their values.
def fields() -> List<&2, Nat>:
  geometry = {[context(), headroom(), pool(), page_size(), pages(),
    8n, page_size(), 32n, 8n, write_span(), admission_slots(), page_size(), draft_window(), draft_visible(),
    dimension(Target{}), heads(Target{}), layers(Target{}),
    dimension(Draft{}), heads(Draft{}), layers(Draft{})] : List<&2, Nat>}
  tiles = List.append(&2, Nat, offsets(dimension(Target{})), offsets(dimension(Draft{})))
  List.append(&2, Nat, geometry, tiles)

def native() -> Plan:
  Plan{fields(), Range.native()}

def valid(context: Nat, pool: Nat, page_size: Nat) -> Bool:
  Bool.and(Nat.is_eq(context, 262144n),
    Bool.and(Nat.is_eq(pool, 263168n), Nat.is_eq(page_size, 128n)))

def choose(valid: Bool) -> Maybe<&2, Plan>:
  match valid:
    case True{}:
      Some{native()}
    case False{}:
      None{}

def plan(context: Nat, pool: Nat, page_size: Nat) -> Maybe<&2, Plan>:
  choose(valid(context, pool, page_size))
