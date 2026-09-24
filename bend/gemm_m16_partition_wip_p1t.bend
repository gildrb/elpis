# WIP proofs: core lemma p1_touches_range (contract, used by p2/p4).
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p1t_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# STUB-BEGIN (proven in wip_p1)
# owns(b, x) iff start(b) <= x < start(b + 1)   (G >= 1; any I)
def p1_owns_range(+b: Nat, +x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.owns(b, x, I, G) == Bool.and(Nat.is_le(Impl.start(b, I, G), x),
    Nat.is_lt(x, Impl.start(1n+b, I, G))) : Bool}:
  ?TODO
# STUB-END

# owns_some with the owned range [s, e) abstracted: owns(b, x) is replaced by s <= x < e.
def p1t_os(left: Nat, +x: Nat, +s: Nat, +e: Nat) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+r:
      Bool.or(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e)), p1t_os(r, 1n+x, s, e))

# The closed form of p1t_os(1 + l, x, s, e): [s, e) is non-empty and meets [x, x + 1 + l).
def p1t_rng(+l: Nat, +x: Nat, +s: Nat, +e: Nat) -> Bool:
  Bool.and(Nat.is_lt(s, e), Bool.and(Nat.is_lt(s, Nat.add(x, 1n+l)), Nat.is_lt(x, e)))

# owns_some agrees with p1t_os at s = start(b), e = start(b + 1).
def p1t_os_eq(left: Nat, +x: Nat, +b: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.owns_some(left, x, b, I, G) ==
    p1t_os(left, x, Impl.start(b, I, G), Impl.start(1n+b, I, G)) : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      %p1t_os_eq(r, 1n+x, b, I, G, gpos) : {Bool.or(Spec.owns(b, x, I, G), Spec.owns_some(r, 1n+x, b, I, G)) == Bool.or(Bool.and(Nat.is_le(Impl.start(b, I, G), x), Nat.is_lt(x, Impl.start(1n+b, I, G))), _) : Bool}
      %p1_owns_range(b, x, I, G, gpos) : {Bool.or(Spec.owns(b, x, I, G), Spec.owns_some(r, 1n+x, b, I, G)) == Bool.or(_, Spec.owns_some(r, 1n+x, b, I, G)) : Bool}
      {==}

def p1t_and_false_r(a: Bool) -> {False{} == Bool.and(a, False{}) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def p1t_lt0(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def p1t_lt0_and(s: Nat, -c: Bool) -> {False{} == Bool.and(Nat.is_lt(s, 0n), c) : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      {==}

# not (x < e) gives not (x + 1 < e).
def p1t_ltf(x: Nat, e: Nat, h: {Nat.is_lt(x, e) == False{} : Bool})
  -> {Nat.is_lt(1n+x, e) == False{} : Bool}:
  match x e:
    case 0n 0n:
      {==}
    case 0n 1n+ep:
      Empty.absurd({Nat.is_lt(1n, 1n+ep) == False{} : Bool},
        Arith.ar_false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+ep:
      p1t_ltf(xp, ep, h)

# Past the end of the range nothing is owned.
def p1t_past(left: Nat, +x: Nat, +s: Nat, +e: Nat, +h: {Nat.is_lt(x, e) == False{} : Bool})
  -> {p1t_os(left, x, s, e) == False{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      %Equal.sym(Bool, Nat.is_lt(x, e), False{}, h) : {Bool.or(Bool.and(Nat.is_le(s, x), _), p1t_os(r, 1n+x, s, e)) == False{} : Bool}
      %p1t_and_false_r(Nat.is_le(s, x)) : {Bool.or(_, p1t_os(r, 1n+x, s, e)) == False{} : Bool}
      p1t_past(r, 1n+x, s, e, p1t_ltf(x, e, h))

# Shifting x, s and e together changes nothing.
def p1t_shift(left: Nat, +x: Nat, +s: Nat, +e: Nat)
  -> {p1t_os(left, 1n+x, 1n+s, 1n+e) == p1t_os(left, x, s, e) : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      %p1t_shift(r, 1n+x, s, e) : {Bool.or(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e)), p1t_os(r, 2n+x, 1n+s, 1n+e)) == Bool.or(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e)), _) : Bool}
      {==}

# With s = 0: the head decides, since once x >= e nothing later is owned.
def p1t_absorb(+l: Nat, +x: Nat, +e: Nat, v: Bool, h: {Nat.is_lt(x, e) == v : Bool})
  -> {Bool.or(v, p1t_os(l, 1n+x, 0n, e)) == v : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      p1t_past(l, 1n+x, 0n, e, p1t_ltf(x, e, h))

# With x = 0 the last conjunct 0 < e is redundant next to s < e.
def p1t_fix(s: Nat, e: Nat, -d: Bool)
  -> {Bool.and(Nat.is_lt(s, e), Bool.and(d, Nat.is_lt(0n, e))) ==
    Bool.and(Nat.is_lt(s, e), Bool.and(d, True{})) : Bool}:
  match s e:
    case 0n 0n:
      {==}
    case 0n 1n+ep:
      {==}
    case 1n+sp 0n:
      {==}
    case 1n+sp 1n+ep:
      {==}

# Main characterization, by recursion on s (shifting x, s, e down together).
def p1t_main(+s: Nat, +e: Nat, +x: Nat, +l: Nat)
  -> {p1t_os(1n+l, x, s, e) == p1t_rng(l, x, s, e) : Bool}:
  match s e x l:
    case 0n 0n xv lv:
      p1t_past(1n+lv, xv, 0n, 0n, p1t_lt0(xv))
    case 1n+sp 0n xv lv:
      p1t_past(1n+lv, xv, 1n+sp, 0n, p1t_lt0(xv))
    case 0n 1n+ep 0n lv:
      {==}
    case 0n 1n+ep 1n+xp lv:
      p1t_absorb(lv, 1n+xp, 1n+ep, Nat.is_lt(1n+xp, 1n+ep), {==})
    case 1n+sp 1n+ep 0n 0n:
      %Equal.sym(Bool, Nat.is_lt(sp, 0n), False{}, p1t_lt0(sp)) : {False{} == Bool.and(Nat.is_lt(sp, ep), Bool.and(_, True{})) : Bool}
      p1t_and_false_r(Nat.is_lt(sp, ep))
    case 1n+sp 1n+ep 0n 1n+lp:
      Equal.trans(Bool, p1t_os(1n+lp, 1n, 1n+sp, 1n+ep),
        p1t_os(1n+lp, 0n, sp, ep),
        Bool.and(Nat.is_lt(sp, ep), Bool.and(Nat.is_lt(sp, 1n+lp), True{})),
        p1t_shift(1n+lp, 0n, sp, ep),
        Equal.trans(Bool, p1t_os(1n+lp, 0n, sp, ep), p1t_rng(lp, 0n, sp, ep),
          Bool.and(Nat.is_lt(sp, ep), Bool.and(Nat.is_lt(sp, 1n+lp), True{})),
          p1t_main(sp, ep, 0n, lp), p1t_fix(sp, ep, Nat.is_lt(sp, 1n+lp))))
    case 1n+sp 1n+ep 1n+xp lv:
      Equal.trans(Bool, p1t_os(1n+lv, 1n+xp, 1n+sp, 1n+ep), p1t_os(1n+lv, xp, sp, ep),
        p1t_rng(lv, 1n+xp, 1n+sp, 1n+ep),
        p1t_shift(1n+lv, xp, sp, ep), p1t_main(sp, ep, xp, lv))

# Block b touches group g iff its range [start(b), start(b + 1)) is non-empty and meets
# [g * KT, (g + 1) * KT)   (G >= 1; any KT, I)
def p1_touches_range(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.touches(b, g, KT, I, G) ==
    Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)),
      Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)))) : Bool}:
  match KT:
    case 0n:
      %Equal.sym(Nat, Nat.mul(g, 0n), 0n, Arith.ar_mul_zero_r(g)) : {False{} == Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)), Bool.and(Nat.is_lt(Impl.start(b, I, G), _), Nat.is_lt(_, Impl.start(1n+b, I, G)))) : Bool}
      %Equal.sym(Bool, Nat.is_lt(Impl.start(b, I, G), 0n), False{}, p1t_lt0(Impl.start(b, I, G))) : {False{} == Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)), Bool.and(_, Nat.is_lt(0n, Impl.start(1n+b, I, G)))) : Bool}
      p1t_and_false_r(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)))
    case 1n+k:
      %Arith.ar_add_comm(Nat.mul(g, 1n+k), 1n+k) : {Spec.touches(b, g, 1n+k, I, G) == Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)), Bool.and(Nat.is_lt(Impl.start(b, I, G), _), Nat.is_lt(Nat.mul(g, 1n+k), Impl.start(1n+b, I, G)))) : Bool}
      Equal.trans(Bool, Spec.owns_some(1n+k, Nat.mul(g, 1n+k), b, I, G),
        p1t_os(1n+k, Nat.mul(g, 1n+k), Impl.start(b, I, G), Impl.start(1n+b, I, G)),
        p1t_rng(k, Nat.mul(g, 1n+k), Impl.start(b, I, G), Impl.start(1n+b, I, G)),
        p1t_os_eq(1n+k, Nat.mul(g, 1n+k), b, I, G, gpos),
        p1t_main(Impl.start(b, I, G), Impl.start(1n+b, I, G), Nat.mul(g, 1n+k), k))
