# Ext 3013 tree-verify KV commit (exllamav3_ext/kv_compact.cu kernel + host checks, cache/kv_compact.py kv_moves),
# transcribed over Nat at logical-slot granularity of the 8-row verify window. K = patches/exl3-ext/3013-kv-compact-rows.patch.
# A slot's content is the token row it holds (row r written at slot base + r by the tree verify). The physical mapping
# phys(pos) (K:288-289) is injective because the page indices are checked distinct (K:285-286); it is not modelled.
# Reference: kv_compact_spec.bend; laws: kv_compact_laws.bend.
import Base
import ./kv_compact_spec.bend as Spec

# K:291 [(phys(base + rows[j]), phys(base + j)) for j in range(1, count) if rows[j] != j], at logical offsets
def kv_moves.keep(c: Bool, +r: Nat, +j: Nat, rest: List<&2, Spec.Mv>) -> List<&2, Spec.Mv>:
  match c:
    case True{}:
      Spec.Mv{r, j} <> rest
    case False{}:
      rest

def kv_moves.go(rows: List<&2, Nat>, +j: Nat) -> List<&2, Spec.Mv>:
  match rows:
    case Nil{}:
      []
    case Con{+r, rest}:
      kv_moves.keep(Nat.is_ne(r, j), r, j, kv_moves.go(rest, 1n+j))

def kv_moves(rows: List<&2, Nat>) -> List<&2, Spec.Mv>:
  match rows:
    case Nil{}:
      []
    case Con{r, rest}:
      kv_moves.go(rest, 1n)

def get(xs: List<&2, Nat>, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, rest}:
      match i:
        case 0n:
          x
        case 1n+k:
          get(rest, k)

def set(xs: List<&2, Nat>, +i: Nat, +v: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      match i:
        case 0n:
          v <> rest
        case 1n+k:
          x <> set(rest, k, v)

# K:95-96 every source unit is read into registers first (row[i] = base[src[i] ...] for every move) ...
def reads(+mem: List<&2, Nat>, mv: List<&2, Spec.Mv>) -> List<&2, Nat>:
  match mv:
    case Nil{}:
      []
    case Con{Spec.Mv{s, d}, rest}:
      get(mem, s) <> reads(mem, rest)

# ... K:98-99 then every destination is written (base[dst[i] ...] = row[i]), in move order
def writes(mv: List<&2, Spec.Mv>, vals: List<&2, Nat>, mem: List<&2, Nat>) -> List<&2, Nat>:
  match mv:
    case Nil{}:
      mem
    case Con{Spec.Mv{s, +d}, rest}:
      match vals:
        case Nil{}:
          mem
        case Con{+v, vs}:
          writes(rest, vs, set(mem, d, v))

def kernel(+mem: List<&2, Nat>, +mv: List<&2, Spec.Mv>) -> List<&2, Nat>:
  writes(mv, reads(mem, mv), mem)

# K:158-163 host checks (bounds aside): src != dst, no two moves share a destination, no source is an earlier destination
def ok_prior(+s: Nat, +d: Nat, done: List<&2, Spec.Mv>) -> Bool:
  match done:
    case Nil{}:
      True{}
    case Con{Spec.Mv{+s2, +d2}, rest}:
      Bool.and(Nat.is_ne(d2, d), Bool.and(Nat.is_ne(d2, s), ok_prior(s, d, rest)))

def checks.go(mv: List<&2, Spec.Mv>, +done: List<&2, Spec.Mv>) -> Bool:
  match mv:
    case Nil{}:
      True{}
    case Con{Spec.Mv{+s, +d}, rest}:
      Bool.and(Nat.is_ne(s, d), Bool.and(ok_prior(s, d, done), checks.go(rest, Spec.Mv{s, d} <> done)))

def checks(mv: List<&2, Spec.Mv>) -> Bool:
  checks.go(mv, [])
