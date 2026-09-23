# Proof-only module. Nat.mul recurses on its FIRST argument in Bend 2.0.25;
# multiplication commutation and successor movement therefore need lemmas.
import Base
import ./query_tiles.bend as QueryTiles
import ./query_tiles_spec.bend as Spec
import ./query_tiles_laws.bend as Laws

def add_succ(n: Nat, -i: Nat) -> {Nat.add(n, 1n+i) == 1n+Nat.add(n, i) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, i) : {1n+Nat.add(p, 1n+i) == 1n+_ : Nat}
      {==}

def equal_zero(s: Nat) -> {s == Nat.add(s, 0n) : Nat}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      %equal_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

# Move a finite prefix through addition, without assuming commutativity.
def add_shift(n: Nat, +a: Nat, -b: Nat)
  -> {Nat.add(a, Nat.add(n, b)) == Nat.add(n, Nat.add(a, b)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_shift(p, a, b) : {Nat.add(a, Nat.add(1n+p, b)) == 1n+_ : Nat}
      add_succ(a, Nat.add(p, b))

def mul_succ(+n: Nat, +p: Nat)
  -> {Nat.mul(n, 1n+p) == Nat.add(n, Nat.mul(n, p)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %add_shift(k, p, Nat.mul(k, p)) :
        {Nat.mul(1n+k, 1n+p) == 1n+_ : Nat}
      %mul_succ(k, p) :
        {Nat.mul(1n+k, 1n+p) == 1n+Nat.add(p, _) : Nat}
      {==}

def mul_four_comm(+n: Nat) -> {Nat.mul(n, 4n) == Nat.mul(4n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(4n, 1n+p), 4n+Nat.mul(4n, p), mul_succ(4n, p)) :
        {Nat.mul(1n+p, 4n) == _ : Nat}
      %mul_four_comm(p) : {4n+Nat.mul(p, 4n) == 4n+_ : Nat}
      {==}

# The former residual: combine successor movement with proved commutation.
def quad_succ(+p: Nat) -> {Nat.mul(4n, 1n+p) == 4n+Nat.mul(p, 4n) : Nat}:
  %Equal.sym(Nat, Nat.mul(p, 4n), Nat.mul(4n, p), mul_four_comm(p)) :
    {Nat.mul(4n, 1n+p) == 4n+_ : Nat}
  mul_succ(4n, p)

def Laws.start_semantics(tile):
  mul_four_comm(tile)

# Independent repeated addition, not a call back into the planner.
def start_spec(tile: Nat) -> {QueryTiles.start(tile) == Spec.spec_start(tile) : Nat}:
  match tile:
    case 0n:
      {==}
    case 1n+p:
      %start_spec(p) : {4n+QueryTiles.start(p) == 4n+_ : Nat}
      {==}

def Laws.tile_block(tile):
  Equal.cong(Nat, List<&2, Nat>, row => Spec.spec_rows(4n, row),
    QueryTiles.start(tile), Spec.spec_start(tile), start_spec(tile))

def Laws.covered_exact(n, row):
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.covered_exact(p, 1n+row) :
        {row <> Laws.covered(p, 1n+row) == row <> _ : List<&2, Nat>}
      {==}

def append_nil(xs: List<&2, Nat>)
  -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_nil(t) :
        {h <> List.append(&2, Nat, t, Nil{}) == h <> _ : List<&2, Nat>}
      {==}

# Oriented for replacing a left-associated reference append with its suffix.
def append_join(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>)
  -> {List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs))
    == List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_join(t, ys, zs) :
        {h <> List.append(&2, Nat, t, List.append(&2, Nat, ys, zs))
          == h <> _ : List<&2, Nat>}
      {==}

# Arbitrary accumulator, not only the closed native plan; the production
# builder visits descending indices but prepending yields ascending output.
def starts_go_semantics(+count: Nat, +acc: List<&2, Nat>)
  -> {QueryTiles.starts_go(count, acc)
    == List.append(&2, Nat, Spec.spec_starts(count), acc) : List<&2, Nat>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %append_join(Spec.spec_starts(p), [Spec.spec_start(p)], acc) :
        {QueryTiles.starts_go(1n+p, acc) == _ : List<&2, Nat>}
      %start_spec(p) :
        {QueryTiles.starts_go(1n+p, acc)
          == List.append(&2, Nat, Spec.spec_starts(p), _ <> acc) : List<&2, Nat>}
      starts_go_semantics(p, QueryTiles.start(p) <> acc)

def Laws.starts_semantics(count):
  %append_nil(Spec.spec_starts(count)) :
    {QueryTiles.starts(count) == _ : List<&2, Nat>}
  starts_go_semantics(count, Nil{})

def flatten_append(+xs: List<&2, Nat>, +ys: List<&2, Nat>)
  -> {Laws.flatten(List.append(&2, Nat, xs, ys))
    == List.append(&2, Nat, Laws.flatten(xs), Laws.flatten(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %append_join(Laws.covered(4n, h), Laws.flatten(t), Laws.flatten(ys)) :
        {Laws.flatten(List.append(&2, Nat, h <> t, ys)) == _ : List<&2, Nat>}
      %flatten_append(t, ys) :
        {Laws.flatten(List.append(&2, Nat, h <> t, ys))
          == List.append(&2, Nat, Laws.covered(4n, h), _) : List<&2, Nat>}
      {==}

def spec_start_mul(+tile: Nat)
  -> {Spec.spec_start(tile) == Nat.mul(4n, tile) : Nat}:
  %Laws.start_semantics(tile) : {Spec.spec_start(tile) == _ : Nat}
  Equal.sym(Nat, QueryTiles.start(tile), Spec.spec_start(tile), start_spec(tile))

def flatten_spec(+count: Nat)
  -> {Laws.flatten(Spec.spec_starts(count)) == Spec.spec_tiles(count) : List<&2, Nat>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %spec_start_mul(p) :
        {Laws.flatten(Spec.spec_starts(1n+p)) == List.append(&2, Nat,
          Spec.spec_tiles(p), Spec.spec_rows(4n, _)) : List<&2, Nat>}
      %flatten_spec(p) :
        {Laws.flatten(Spec.spec_starts(1n+p)) == List.append(&2, Nat,
          _, Spec.spec_rows(4n, Spec.spec_start(p))) : List<&2, Nat>}
      %Laws.covered_exact(4n, Spec.spec_start(p)) :
        {Laws.flatten(Spec.spec_starts(1n+p)) == List.append(&2, Nat,
          Laws.flatten(Spec.spec_starts(p)), _) : List<&2, Nat>}
      flatten_append(Spec.spec_starts(p), [Spec.spec_start(p)])

# Appending four consecutive rows extends any ordered prefix by exactly four.
# This preserves exact order, not merely set membership or total cardinality.
def rows_four_end(+n: Nat, +row: Nat)
  -> {List.append(&2, Nat, Spec.spec_rows(n, row),
      Spec.spec_rows(4n, Nat.add(n, row)))
    == Spec.spec_rows(4n+n, row) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, row) :
        {row <> List.append(&2, Nat, Spec.spec_rows(p, 1n+row), Spec.spec_rows(4n, _))
          == row <> Spec.spec_rows(4n+p, 1n+row) : List<&2, Nat>}
      %rows_four_end(p, 1n+row) :
        {row <> List.append(&2, Nat, Spec.spec_rows(p, 1n+row),
          Spec.spec_rows(4n, Nat.add(p, 1n+row))) == row <> _ : List<&2, Nat>}
      {==}

def tiles_exact(+count: Nat)
  -> {Spec.spec_tiles(count) == Spec.spec_rows(Nat.mul(count, 4n), 0n) : List<&2, Nat>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %rows_four_end(Nat.mul(p, 4n), 0n) :
        {Spec.spec_tiles(1n+p) == _ : List<&2, Nat>}
      %equal_zero(Nat.mul(p, 4n)) :
        {Spec.spec_tiles(1n+p) == List.append(&2, Nat,
          Spec.spec_rows(Nat.mul(p, 4n), 0n), Spec.spec_rows(4n, _)) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.mul(p, 4n), Nat.mul(4n, p), mul_four_comm(p)) :
        {Spec.spec_tiles(1n+p) == List.append(&2, Nat,
          Spec.spec_rows(Nat.mul(p, 4n), 0n), Spec.spec_rows(4n, _)) : List<&2, Nat>}
      %tiles_exact(p) :
        {Spec.spec_tiles(1n+p) == List.append(&2, Nat,
          _, Spec.spec_rows(4n, Nat.mul(4n, p))) : List<&2, Nat>}
      {==}

def tiles_range(+count: Nat)
  -> {Spec.spec_tiles(count) == Spec.spec_rows(Nat.mul(4n, count), 0n) : List<&2, Nat>}:
  %mul_four_comm(count) :
    {Spec.spec_tiles(count) == Spec.spec_rows(_, 0n) : List<&2, Nat>}
  tiles_exact(count)

def Laws.starts_coverage(count):
  %tiles_range(count) : {Laws.flatten(QueryTiles.starts(count)) == _ : List<&2, Nat>}
  %flatten_spec(count) : {Laws.flatten(QueryTiles.starts(count)) == _ : List<&2, Nat>}
  %Laws.starts_semantics(count) :
    {Laws.flatten(QueryTiles.starts(count)) == Laws.flatten(_) : List<&2, Nat>}
  {==}

def add_one(+p: Nat) -> {Nat.add(p, 1n) == 1n+p : Nat}:
  %Equal.sym(Nat, p, Nat.add(p, 0n), equal_zero(p)) :
    {Nat.add(p, 1n) == 1n+_ : Nat}
  add_succ(p, 0n)

def lt_plus_four(n: Nat) -> {Nat.is_lt(n, 4n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_plus_four(p)

def lt_start_step(+p: Nat)
  -> {Nat.is_lt(QueryTiles.start(p), Nat.mul(4n, 1n+p)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.mul(4n, 1n+p), 4n+Nat.mul(p, 4n), quad_succ(p)) :
    {Nat.is_lt(QueryTiles.start(p), _) == True{} : Bool}
  lt_plus_four(QueryTiles.start(p))

def lt_start_next(+p: Nat)
  -> {Nat.is_lt(QueryTiles.start(p), Nat.mul(4n, Nat.add(p, 1n))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(p, 1n), 1n+p, add_one(p)) :
    {Nat.is_lt(QueryTiles.start(p), Nat.mul(4n, _)) == True{} : Bool}
  lt_start_step(p)

def Laws.starts_bounded(count):
  match count:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool,
        Nat.is_lt(QueryTiles.start(p), Nat.mul(4n, Nat.add(p, 1n))),
        True{}, lt_start_next(p)) :
        {Bool.and(_, Laws.in_bounds(p)) == True{} : Bool}
      Laws.starts_bounded(p)

# Native conclusions use the universal theorems, not disconnected sample lists.
def Laws.native_coverage():
  tiles_range(QueryTiles.tile_count())

def Laws.native_rows_exact():
  Laws.starts_coverage(QueryTiles.tile_count())

def Laws.native_starts_exact():
  {==}

def Laws.native_selected():
  {==}
