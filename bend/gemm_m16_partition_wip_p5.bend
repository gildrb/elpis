# WIP proofs: law mainloop_trace (K:275-346 main loop == Spec.trace).
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p5_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- Bool / Nat helpers ----

def p5_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p5_fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def p5_snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

def p5_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Arith.ar_true_false(h))

# b | c from a | b and b -> c.
def p5_or_mono(a: Bool, -b: Bool, -c: Bool, h: {Bool.or(a, b) == True{} : Bool},
    imp: {b == True{} : Bool} -> {c == True{} : Bool})
  -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      imp(h)

# a < b implies a != b.
def p5_lt_ne(a: Nat, b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, Arith.ar_false_true(lt))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_eq(1n+p, 0n) == False{} : Bool}, Arith.ar_false_true(lt))
    case 1n+p 1n+q:
      p5_lt_ne(p, q, lt)

# a == c and a < c is absurd.
def p5_eq_lt_absurd(-a: Nat, +c: Nat, eq: {a == c : Nat}, lt: {Nat.is_lt(a, c) == True{} : Bool})
  -> Empty:
  Arith.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(a, c), True{},
    p5_eq_lt_absurd_go(a, c, eq), lt))

def p5_eq_lt_absurd_go(-a: Nat, +c: Nat, eq: {a == c : Nat})
  -> {False{} == Nat.is_lt(a, c) : Bool}:
  %Equal.sym(Nat, a, c, eq) : {False{} == Nat.is_lt(_, c) : Bool}
  Equal.sym(Bool, Nat.is_lt(c, c), False{}, Arith.ar_lt_irrefl(c))

# i < 1 + (k + i).
def p5_lt_succ_add(+k: Nat, +i: Nat) -> {Nat.is_lt(i, 1n+Nat.add(k, i)) == True{} : Bool}:
  p5_rt(Nat.is_le(i, Nat.add(k, i)), Nat.is_lt(i, 1n+Nat.add(k, i)),
    Equal.sym(Bool, Nat.is_lt(i, 1n+Nat.add(k, i)), Nat.is_le(1n+i, 1n+Nat.add(k, i)),
      Arith.ar_lt_succ_le(i, 1n+Nat.add(k, i))),
    Arith.ar_le_add_l(k, i))

# y < k + y for k >= 1.
def p5_lt_add_pos(k: Nat, +y: Nat, kpos: {Nat.is_lt(0n, k) == True{} : Bool})
  -> {Nat.is_lt(y, Nat.add(k, y)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_lt(y, Nat.add(0n, y)) == True{} : Bool}, Arith.ar_false_true(kpos))
    case 1n+k0:
      p5_lt_succ_add(k0, y)

def p5_sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      p5_sub_self(p)

def p5_min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p5_min_le_l(p, q)

def p5_min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      Arith.ar_h_le_zero(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p5_min_le_r(p, q)

# min(a, b) is a or b.
def p5_min_split(+a: Nat, +b: Nat)
  -> {Bool.or(Nat.is_eq(Nat.min(a, b), a), Nat.is_eq(Nat.min(a, b), b)) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p5_min_split(p, q)

# min(a, b) < a forces min(a, b) == b.
def p5_min_lt_l(+a: Nat, +b: Nat, h: {Nat.is_lt(Nat.min(a, b), a) == True{} : Bool})
  -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.min(0n, b) == b : Nat}, Arith.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %p5_min_lt_l(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

def p5_max_r(+j: Nat, +x: Nat, le: {Nat.is_le(j, x) == True{} : Bool})
  -> {Nat.max(j, x) == x : Nat}:
  match j x:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.max(1n+p, 0n) == 0n : Nat}, Arith.ar_false_true(le))
    case 1n+p 1n+q:
      %p5_max_r(p, q, le) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

# n - j == (se - j) + (n - se) for j <= se <= n.
def p5_sub_split(+n: Nat, +se: Nat, +j: Nat,
    jse: {Nat.is_le(j, se) == True{} : Bool}, sen: {Nat.is_le(se, n) == True{} : Bool})
  -> {Nat.sub(n, j) == Nat.add(Nat.sub(se, j), Nat.sub(n, se)) : Nat}:
  %p5_sub_split_go(n, se, j, jse, sen) : {Nat.sub(_, j) == Nat.add(Nat.sub(se, j), Nat.sub(n, se)) : Nat}
  Arith.ar_add_sub(j, Nat.add(Nat.sub(se, j), Nat.sub(n, se)))

def p5_sub_split_go(+n: Nat, +se: Nat, +j: Nat,
    jse: {Nat.is_le(j, se) == True{} : Bool}, sen: {Nat.is_le(se, n) == True{} : Bool})
  -> {Nat.add(j, Nat.add(Nat.sub(se, j), Nat.sub(n, se))) == n : Nat}:
  %Arith.ar_add_assoc(j, Nat.sub(se, j), Nat.sub(n, se)) : {_ == n : Nat}
  %Arith.ar_sub_add(se, j, jse) : {Nat.add(_, Nat.sub(n, se)) == n : Nat}
  Arith.ar_sub_add(n, se, sen)
