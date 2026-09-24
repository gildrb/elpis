# Proofs of the grouped m16 GEMM (ext patch 2102) laws (gemm_m16_group_laws.bend) about the Bend
# model gemm_m16_group.bend. The block partition, slot and finisher facts reuse the generic (any
# KT, total, G) lemmas of the 2001 v2 proof (gemm_m16_partition_proof.bend, V2P); shape-specific
# v2 laws are transported to the bundle's total. Structural evidence only: no unsafe definitions,
# axioms, holes, foreign proof code or answer tables. Every def precedes its uses.
import Base
import ./gemm_m16_group.bend as Impl
import ./gemm_m16_group_spec.bend as Spec
import ./gemm_m16_group_laws.bend as Laws
import ./gemm_m16_partition.bend as V2
import ./gemm_m16_partition_spec.bend as V2Spec
import ./gemm_m16_partition_laws.bend as V2Laws
import ./gemm_m16_partition_proof.bend as V2P

# ==== small logic helpers ====

def g_fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def g_snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

# is_ge(g, a) == True gives a <= g.
def g_ge_le(+g: Nat, +a: Nat, e: {Nat.is_ge(g, a) == True{} : Bool})
  -> {Nat.is_le(a, g) == True{} : Bool}:
  V2P.p2_rt(Nat.is_ge(g, a), Nat.is_le(a, g), V2P.ar_ge_flip(g, a), e)

# is_ge(g, a) == False gives g < a.
def g_nge_lt(+g: Nat, +a: Nat, e: {Nat.is_ge(g, a) == False{} : Bool})
  -> {Nat.is_lt(g, a) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(g, a), Bool.not(Nat.is_le(a, g)), True{},
    V2P.ar_lt_not_le(g, a),
    Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_le(a, g), False{},
      Equal.trans(Bool, Nat.is_le(a, g), Nat.is_ge(g, a), False{},
        Equal.sym(Bool, Nat.is_ge(g, a), Nat.is_le(a, g), V2P.ar_ge_flip(g, a)), e)))

# ==== gbase is the prefix sum ====

def ga_go(+i: Nat, +ns: List<&2, Nat>, +acc: Nat)
  -> {Impl.gbase.go(i, ns, acc) == Nat.add(acc, Spec.before.go(i, ns)) : Nat}:
  match i:
    case 0n:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, V2P.ar_add_zero_r(acc))
    case 1n+j:
      match ns:
        case Nil{}:
          Equal.sym(Nat, Nat.add(acc, 0n), acc, V2P.ar_add_zero_r(acc))
        case +n <> rest:
          Equal.trans(Nat, Impl.gbase.go(j, rest, Nat.add(acc, Nat.div(n, 512n))),
            Nat.add(Nat.add(acc, Nat.div(n, 512n)), Spec.before.go(j, rest)),
            Nat.add(acc, Nat.add(Nat.div(n, 512n), Spec.before.go(j, rest))),
            ga_go(j, rest, Nat.add(acc, Nat.div(n, 512n))),
            V2P.ar_add_assoc(acc, Nat.div(n, 512n), Spec.before.go(j, rest)))

def Laws.gbase_prefix(ns, i):
  ga_go(i, ns, 0n)

# before(i + 1) = before(i) + ng_at(i) (ng_at is 0 past the end).
def bf_succ(+i: Nat, +ns: List<&2, Nat>)
  -> {Spec.before.go(1n+i, ns) == Nat.add(Spec.before.go(i, ns), Spec.ng_at(ns, i)) : Nat}:
  match i:
    case 0n:
      match ns:
        case Nil{}:
          {==}
        case +n <> rest:
          V2P.ar_add_zero_r(Nat.div(n, 512n))
    case 1n+j:
      match ns:
        case Nil{}:
          {==}
        case +n <> rest:
          Equal.trans(Nat, Nat.add(Nat.div(n, 512n), Spec.before.go(1n+j, rest)),
            Nat.add(Nat.div(n, 512n), Nat.add(Spec.before.go(j, rest), Spec.ng_at(rest, j))),
            Nat.add(Nat.add(Nat.div(n, 512n), Spec.before.go(j, rest)), Spec.ng_at(rest, j)),
            Equal.cong(Nat, Nat, z => Nat.add(Nat.div(n, 512n), z), Spec.before.go(1n+j, rest),
              Nat.add(Spec.before.go(j, rest), Spec.ng_at(rest, j)), bf_succ(j, rest)),
            Equal.sym(Nat, Nat.add(Nat.add(Nat.div(n, 512n), Spec.before.go(j, rest)), Spec.ng_at(rest, j)),
              Nat.add(Nat.div(n, 512n), Nat.add(Spec.before.go(j, rest), Spec.ng_at(rest, j))),
              V2P.ar_add_assoc(Nat.div(n, 512n), Spec.before.go(j, rest), Spec.ng_at(rest, j))))

# Past the last matrix, before is the whole bundle.
def bf_full(+i: Nat, +ns: List<&2, Nat>,
    h: {Nat.is_le(List.length(&2, Nat, ns), i) == True{} : Bool})
  -> {Spec.before.go(i, ns) == Spec.ngroups(ns) : Nat}:
  match i:
    case 0n:
      match ns:
        case Nil{}:
          {==}
        case n <> rest:
          Empty.absurd({Spec.before.go(0n, n <> rest) == Spec.ngroups(n <> rest) : Nat},
            V2P.ar_false_true(h))
    case 1n+j:
      match ns:
        case Nil{}:
          {==}
        case +n <> rest:
          Equal.cong(Nat, Nat, z => Nat.add(Nat.div(n, 512n), z), Spec.before.go(j, rest),
            Spec.ngroups(rest), bf_full(j, rest, h))

def Laws.groups_total(ns, bundle):
  Equal.trans(Nat, Impl.groups(ns), Spec.before.go(4n, ns), Spec.ngroups(ns),
    ga_go(4n, ns, 0n), bf_full(4n, ns, bundle))

# before is monotone: before(i) <= before(d + i).
def bf_mono(+d: Nat, +i: Nat, +ns: List<&2, Nat>)
  -> {Nat.is_le(Spec.before.go(i, ns), Spec.before.go(Nat.add(d, i), ns)) == True{} : Bool}:
  match d:
    case 0n:
      V2P.ar_le_refl(Spec.before.go(i, ns))
    case 1n+p:
      V2P.ar_le_trans(Spec.before.go(i, ns), Spec.before.go(Nat.add(p, i), ns),
        Spec.before.go(1n+Nat.add(p, i), ns), bf_mono(p, i, ns),
        V2P.p2_tr(Nat.is_le(Spec.before.go(Nat.add(p, i), ns), Spec.before.go(1n+Nat.add(p, i), ns)),
          Nat.is_le(Spec.before.go(Nat.add(p, i), ns),
            Nat.add(Spec.before.go(Nat.add(p, i), ns), Spec.ng_at(ns, Nat.add(p, i)))),
          Equal.cong(Nat, Bool, z => Nat.is_le(Spec.before.go(Nat.add(p, i), ns), z),
            Spec.before.go(1n+Nat.add(p, i), ns),
            Nat.add(Spec.before.go(Nat.add(p, i), ns), Spec.ng_at(ns, Nat.add(p, i))),
            bf_succ(Nat.add(p, i), ns)),
          V2P.ar_le_add_r(Spec.before.go(Nat.add(p, i), ns), Spec.ng_at(ns, Nat.add(p, i)))))

# i <= j gives before(i) <= before(j).
def bf_le(+i: Nat, +j: Nat, +ns: List<&2, Nat>, ij: {Nat.is_le(i, j) == True{} : Bool})
  -> {Nat.is_le(Spec.before.go(i, ns), Spec.before.go(j, ns)) == True{} : Bool}:
  %Equal.trans(Nat, Nat.add(Nat.sub(j, i), i), Nat.add(i, Nat.sub(j, i)), j, V2P.ar_add_comm(Nat.sub(j, i), i), V2P.ar_sub_add(j, i, ij)) : {Nat.is_le(Spec.before.go(i, ns), Spec.before.go(_, ns)) == True{} : Bool}
  bf_mono(Nat.sub(j, i), i, ns)

# ==== column map (K:63-70) ====

def gpre(+ns: List<&2, Nat>, +i: Nat) -> {Impl.gbase(ns, i) == Spec.before.go(i, ns) : Nat}:
  ga_go(i, ns, 0n)

# gbase[i + 1] = gbase[i] + groups of matrix i.
def gsucc(+i: Nat, +ns: List<&2, Nat>)
  -> {Impl.gbase(ns, 1n+i) == Nat.add(Impl.gbase(ns, i), Spec.ng_at(ns, i)) : Nat}:
  Equal.trans(Nat, Impl.gbase(ns, 1n+i), Spec.before.go(1n+i, ns),
    Nat.add(Impl.gbase(ns, i), Spec.ng_at(ns, i)), gpre(ns, 1n+i),
    Equal.trans(Nat, Spec.before.go(1n+i, ns), Nat.add(Spec.before.go(i, ns), Spec.ng_at(ns, i)),
      Nat.add(Impl.gbase(ns, i), Spec.ng_at(ns, i)), bf_succ(i, ns),
      Equal.cong(Nat, Nat, z => Nat.add(z, Spec.ng_at(ns, i)), Spec.before.go(i, ns),
        Impl.gbase(ns, i), Equal.sym(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), gpre(ns, i)))))

# i <= j gives gbase[i] <= gbase[j].
def gb_le(+i: Nat, +j: Nat, +ns: List<&2, Nat>, ij: {Nat.is_le(i, j) == True{} : Bool})
  -> {Nat.is_le(Impl.gbase(ns, i), Impl.gbase(ns, j)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), gpre(ns, i)) : {Nat.is_le(_, Impl.gbase(ns, j)) == True{} : Bool}
  %Equal.sym(Nat, Impl.gbase(ns, j), Spec.before.go(j, ns), gpre(ns, j)) : {Nat.is_le(Spec.before.go(i, ns), _) == True{} : Bool}
  bf_le(i, j, ns, ij)

# The K:65-69 loop with its three tests fixed: mat.pick(c3, 3, mat.pick(c2, 2, mat.pick(c1, 1, 0))).
def mv(c3: Bool, c2: Bool, c1: Bool) -> Nat:
  Impl.mat.pick(c3, 3n, Impl.mat.pick(c2, 2n, Impl.mat.pick(c1, 1n, 0n)))

def mf_go(c3: Bool, c2: Bool, c1: Bool, +ns: List<&2, Nat>, +g: Nat,
    e3: {Nat.is_ge(g, Impl.gbase(ns, 3n)) == c3 : Bool},
    e2: {Nat.is_ge(g, Impl.gbase(ns, 2n)) == c2 : Bool},
    e1: {Nat.is_ge(g, Impl.gbase(ns, 1n)) == c1 : Bool},
    lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Nat.is_le(Impl.gbase(ns, mv(c3, c2, c1)), g) == True{} : Bool} &
    {Nat.is_lt(g, Impl.gbase(ns, 1n+mv(c3, c2, c1))) == True{} : Bool}:
  match c3 c2 c1:
    case True{} _ _:
      (g_ge_le(g, Impl.gbase(ns, 3n), e3), lt4)
    case False{} True{} _:
      (g_ge_le(g, Impl.gbase(ns, 2n), e2), g_nge_lt(g, Impl.gbase(ns, 3n), e3))
    case False{} False{} True{}:
      (g_ge_le(g, Impl.gbase(ns, 1n), e1), g_nge_lt(g, Impl.gbase(ns, 2n), e2))
    case False{} False{} False{}:
      (V2P.ar_h_le_zero(g), g_nge_lt(g, Impl.gbase(ns, 1n), e1))

# For g < groups: gbase[mat(g)] <= g < gbase[mat(g) + 1].
def mat_bounds(+ns: List<&2, Nat>, +g: Nat, lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Nat.is_le(Impl.gbase(ns, Impl.mat(ns, g)), g) == True{} : Bool} &
    {Nat.is_lt(g, Impl.gbase(ns, 1n+Impl.mat(ns, g))) == True{} : Bool}:
  mf_go(Nat.is_ge(g, Impl.gbase(ns, 3n)), Nat.is_ge(g, Impl.gbase(ns, 2n)),
    Nat.is_ge(g, Impl.gbase(ns, 1n)), ns, g, {==}, {==}, {==}, lt4)

def mb_le(+ns: List<&2, Nat>, +g: Nat, lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Nat.is_le(Impl.gbase(ns, Impl.mat(ns, g)), g) == True{} : Bool}:
  g_fst({Nat.is_le(Impl.gbase(ns, Impl.mat(ns, g)), g) == True{} : Bool},
    {Nat.is_lt(g, Impl.gbase(ns, 1n+Impl.mat(ns, g))) == True{} : Bool}, mat_bounds(ns, g, lt4))

def mb_lt(+ns: List<&2, Nat>, +g: Nat, lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Nat.is_lt(g, Impl.gbase(ns, 1n+Impl.mat(ns, g))) == True{} : Bool}:
  g_snd({Nat.is_le(Impl.gbase(ns, Impl.mat(ns, g)), g) == True{} : Bool},
    {Nat.is_lt(g, Impl.gbase(ns, 1n+Impl.mat(ns, g))) == True{} : Bool}, mat_bounds(ns, g, lt4))

# gbase[i] == groups for i >= num_mats (num_mats <= 4).
def gb_full(+i: Nat, +ns: List<&2, Nat>,
    h: {Nat.is_le(List.length(&2, Nat, ns), i) == True{} : Bool})
  -> {Impl.gbase(ns, i) == Spec.ngroups(ns) : Nat}:
  Equal.trans(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), Spec.ngroups(ns), gpre(ns, i),
    bf_full(i, ns, h))

def mlen_go(c: Bool, +M: Nat, +ns: List<&2, Nat>,
    e: {Nat.is_lt(M, List.length(&2, Nat, ns)) == c : Bool},
    h: {Nat.is_lt(Impl.gbase(ns, M), Impl.gbase(ns, 4n)) == True{} : Bool},
    bundle: {Nat.is_le(List.length(&2, Nat, ns), 4n) == True{} : Bool})
  -> {Nat.is_lt(M, List.length(&2, Nat, ns)) == True{} : Bool}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({Nat.is_lt(M, List.length(&2, Nat, ns)) == True{} : Bool},
        V2P.ard_lt_self(Spec.ngroups(ns),
          V2P.p2_rt(Nat.is_lt(Impl.gbase(ns, M), Impl.gbase(ns, 4n)),
            Nat.is_lt(Spec.ngroups(ns), Spec.ngroups(ns)),
            Equal.trans(Bool, Nat.is_lt(Impl.gbase(ns, M), Impl.gbase(ns, 4n)),
              Nat.is_lt(Spec.ngroups(ns), Impl.gbase(ns, 4n)),
              Nat.is_lt(Spec.ngroups(ns), Spec.ngroups(ns)),
              Equal.cong(Nat, Bool, z => Nat.is_lt(z, Impl.gbase(ns, 4n)), Impl.gbase(ns, M),
                Spec.ngroups(ns), gb_full(M, ns, V2P.p6_nlt_le(M, List.length(&2, Nat, ns), e))),
              Equal.cong(Nat, Bool, z => Nat.is_lt(Spec.ngroups(ns), z), Impl.gbase(ns, 4n),
                Spec.ngroups(ns), gb_full(4n, ns, bundle))),
            h)))

# a <= g < a + n gives g - a < n.
def lt_local(+g: Nat, +a: Nat, +n: Nat, le: {Nat.is_le(a, g) == True{} : Bool},
    lt: {Nat.is_lt(g, Nat.add(a, n)) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(g, a), n) == True{} : Bool}:
  V2P.p2_rt(Nat.is_lt(Nat.add(a, Nat.sub(g, a)), Nat.add(a, n)), Nat.is_lt(Nat.sub(g, a), n),
    V2P.ar_lt_add_cancel(a, Nat.sub(g, a), n),
    V2P.p2_rt(Nat.is_lt(g, Nat.add(a, n)), Nat.is_lt(Nat.add(a, Nat.sub(g, a)), Nat.add(a, n)),
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, Nat.add(a, n)), g, Nat.add(a, Nat.sub(g, a)),
        Equal.sym(Nat, Nat.add(a, Nat.sub(g, a)), g, V2P.ar_sub_add(g, a, le))),
      lt))

# Forward map facts for g < groups, M = mat(g).
def fwd_local(+ns: List<&2, Nat>, +g: Nat, +lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Nat.is_lt(Impl.local(ns, g), Spec.ng_at(ns, Impl.mat(ns, g))) == True{} : Bool}:
  lt_local(g, Impl.gbase(ns, Impl.mat(ns, g)), Spec.ng_at(ns, Impl.mat(ns, g)), mb_le(ns, g, lt4),
    V2P.p2_rt(Nat.is_lt(g, Impl.gbase(ns, 1n+Impl.mat(ns, g))),
      Nat.is_lt(g, Nat.add(Impl.gbase(ns, Impl.mat(ns, g)), Spec.ng_at(ns, Impl.mat(ns, g)))),
      Equal.cong(Nat, Bool, z => Nat.is_lt(g, z), Impl.gbase(ns, 1n+Impl.mat(ns, g)),
        Nat.add(Impl.gbase(ns, Impl.mat(ns, g)), Spec.ng_at(ns, Impl.mat(ns, g))),
        gsucc(Impl.mat(ns, g), ns)),
      mb_lt(ns, g, lt4)))

def fwd_gidx(+ns: List<&2, Nat>, +g: Nat, +lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool})
  -> {Spec.gidx(ns, Impl.mat(ns, g), Impl.local(ns, g)) == g : Nat}:
  Equal.trans(Nat, Nat.add(Spec.before.go(Impl.mat(ns, g), ns), Impl.local(ns, g)),
    Nat.add(Impl.gbase(ns, Impl.mat(ns, g)), Nat.sub(g, Impl.gbase(ns, Impl.mat(ns, g)))), g,
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.sub(g, Impl.gbase(ns, Impl.mat(ns, g)))),
      Spec.before.go(Impl.mat(ns, g), ns), Impl.gbase(ns, Impl.mat(ns, g)),
      Equal.sym(Nat, Impl.gbase(ns, Impl.mat(ns, g)), Spec.before.go(Impl.mat(ns, g), ns),
        gpre(ns, Impl.mat(ns, g)))),
    V2P.ar_sub_add(g, Impl.gbase(ns, Impl.mat(ns, g)), mb_le(ns, g, lt4)))

def fwd_mat(+ns: List<&2, Nat>, +g: Nat, +lt4: {Nat.is_lt(g, Impl.gbase(ns, 4n)) == True{} : Bool},
    bundle: {Nat.is_le(List.length(&2, Nat, ns), 4n) == True{} : Bool})
  -> {Nat.is_lt(Impl.mat(ns, g), List.length(&2, Nat, ns)) == True{} : Bool}:
  mlen_go(Nat.is_lt(Impl.mat(ns, g), List.length(&2, Nat, ns)), Impl.mat(ns, g), ns, {==},
    V2P.ar_le_lt_trans(Impl.gbase(ns, Impl.mat(ns, g)), g, Impl.gbase(ns, 4n), mb_le(ns, g, lt4), lt4),
    bundle)

def Laws.group_map_forward(ns, g, bundle, inside):
  +lt4 = inside
  (fwd_mat(ns, g, lt4, bundle), (fwd_local(ns, g, lt4), fwd_gidx(ns, g, lt4)))

# ---- onto ----

def tri(c1: Bool, c2: Bool, +M: Nat, +i: Nat, e1: {Nat.is_lt(M, i) == c1 : Bool},
    e2: {Nat.is_lt(i, M) == c2 : Bool},
    no1: {Nat.is_lt(M, i) == True{} : Bool} -> Empty,
    no2: {Nat.is_lt(i, M) == True{} : Bool} -> Empty)
  -> {M == i : Nat}:
  match c1 c2:
    case True{} _:
      Empty.absurd({M == i : Nat}, no1(e1))
    case False{} True{}:
      Empty.absurd({M == i : Nat}, no2(e2))
    case False{} False{}:
      V2P.ar_le_antisym(M, i, V2P.p6_nlt_le(i, M, e2), V2P.p6_nlt_le(M, i, e1))

# a <= g, x <= a, g < x gives nothing: x <= g < x is absurd.
def no_below(+x: Nat, +a: Nat, +g: Nat, xa: {Nat.is_le(x, a) == True{} : Bool},
    ag: {Nat.is_le(a, g) == True{} : Bool}, gx: {Nat.is_lt(g, x) == True{} : Bool}) -> Empty:
  V2P.ard_lt_self(x, V2P.ar_le_lt_trans(x, g, x, V2P.ar_le_trans(x, a, g, xa, ag), gx))

# gbase[i] + l < gbase[i + 1] for l < ng_at(i).
def onto_lt(+ns: List<&2, Nat>, +i: Nat, +l: Nat,
    group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool})
  -> {Nat.is_lt(Spec.gidx(ns, i, l), Impl.gbase(ns, 1n+i)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.gbase(ns, 1n+i), Nat.add(Impl.gbase(ns, i), Spec.ng_at(ns, i)), gsucc(i, ns)) : {Nat.is_lt(Spec.gidx(ns, i, l), _) == True{} : Bool}
  %Equal.sym(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), gpre(ns, i)) : {Nat.is_lt(Nat.add(Spec.before.go(i, ns), l), Nat.add(_, Spec.ng_at(ns, i))) == True{} : Bool}
  V2P.p2_tr(Nat.is_lt(Nat.add(Spec.before.go(i, ns), l), Nat.add(Spec.before.go(i, ns), Spec.ng_at(ns, i))),
    Nat.is_lt(l, Spec.ng_at(ns, i)), V2P.ar_lt_add_cancel(Spec.before.go(i, ns), l, Spec.ng_at(ns, i)),
    group_l)

def onto_le(+ns: List<&2, Nat>, +i: Nat, +l: Nat)
  -> {Nat.is_le(Impl.gbase(ns, i), Spec.gidx(ns, i, l)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), gpre(ns, i)) : {Nat.is_le(_, Spec.gidx(ns, i, l)) == True{} : Bool}
  V2P.ar_le_add_r(Spec.before.go(i, ns), l)

# i < num_mats <= 4 gives i + 1 <= 4.
def onto_i4(+i: Nat, +ns: List<&2, Nat>, mat_i: {Nat.is_lt(i, List.length(&2, Nat, ns)) == True{} : Bool},
    bundle: {Nat.is_le(List.length(&2, Nat, ns), 4n) == True{} : Bool})
  -> {Nat.is_le(1n+i, 4n) == True{} : Bool}:
  V2P.p2_rt(Nat.is_lt(i, 4n), Nat.is_le(1n+i, 4n), V2P.ar_lt_succ_le(i, 4n),
    V2P.ar_lt_le_trans(i, List.length(&2, Nat, ns), 4n, mat_i, bundle))

def onto_groups(+ns: List<&2, Nat>, +i: Nat, +l: Nat,
    mat_i: {Nat.is_lt(i, List.length(&2, Nat, ns)) == True{} : Bool},
    bundle: {Nat.is_le(List.length(&2, Nat, ns), 4n) == True{} : Bool},
    group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool})
  -> {Nat.is_lt(Spec.gidx(ns, i, l), Impl.gbase(ns, 4n)) == True{} : Bool}:
  V2P.ar_lt_le_trans(Spec.gidx(ns, i, l), Impl.gbase(ns, 1n+i), Impl.gbase(ns, 4n),
    onto_lt(ns, i, l, group_l), gb_le(1n+i, 4n, ns, onto_i4(i, ns, mat_i, bundle)))

def onto_mat(+ns: List<&2, Nat>, +i: Nat, +l: Nat,
    +lt4: {Nat.is_lt(Spec.gidx(ns, i, l), Impl.gbase(ns, 4n)) == True{} : Bool},
    +group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool})
  -> {Impl.mat(ns, Spec.gidx(ns, i, l)) == i : Nat}:
  +g = Spec.gidx(ns, i, l)
  +M = Impl.mat(ns, g)
  +le = mb_le(ns, g, lt4)
  +lt = mb_lt(ns, g, lt4)
  tri(Nat.is_lt(M, i), Nat.is_lt(i, M), M, i, {==}, {==},
    h => no_below(Impl.gbase(ns, 1n+M), Impl.gbase(ns, i), g,
      gb_le(1n+M, i, ns, V2P.p2_rt(Nat.is_lt(M, i), Nat.is_le(1n+M, i), V2P.ar_lt_succ_le(M, i), h)),
      onto_le(ns, i, l), lt),
    h => no_below(Impl.gbase(ns, 1n+i), Impl.gbase(ns, M), g,
      gb_le(1n+i, M, ns, V2P.p2_rt(Nat.is_lt(i, M), Nat.is_le(1n+i, M), V2P.ar_lt_succ_le(i, M), h)),
      le, onto_lt(ns, i, l, group_l)))

def onto_local(+ns: List<&2, Nat>, +i: Nat, +l: Nat,
    +lt4: {Nat.is_lt(Spec.gidx(ns, i, l), Impl.gbase(ns, 4n)) == True{} : Bool},
    +group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool})
  -> {Impl.local(ns, Spec.gidx(ns, i, l)) == l : Nat}:
  %Equal.sym(Nat, Impl.mat(ns, Spec.gidx(ns, i, l)), i, onto_mat(ns, i, l, lt4, group_l)) : {Nat.sub(Spec.gidx(ns, i, l), Impl.gbase(ns, _)) == l : Nat}
  %Equal.sym(Nat, Impl.gbase(ns, i), Spec.before.go(i, ns), gpre(ns, i)) : {Nat.sub(Nat.add(Spec.before.go(i, ns), l), _) == l : Nat}
  V2P.ar_add_sub(Spec.before.go(i, ns), l)

def Laws.group_map_onto(ns, i, l, bundle, mat_i, group_l):
  +bu = bundle
  +mi = mat_i
  +gl = group_l
  +lt4 = onto_groups(ns, i, l, mi, bu, gl)
  (lt4, (onto_mat(ns, i, l, lt4, gl), onto_local(ns, i, l, lt4, gl)))

# ---- widths ----

def wmod(+ns: List<&2, Nat>, +i: Nat, ok: {Spec.widths_ok(ns) == True{} : Bool},
    lt: {Nat.is_lt(i, List.length(&2, Nat, ns)) == True{} : Bool})
  -> {Nat.mod(Spec.width(ns, i), 512n) == 0n : Nat}:
  match ns:
    case Nil{}:
      Empty.absurd({Nat.mod(Spec.width(Nil{}, i), 512n) == 0n : Nat},
        V2P.ar_true_false(Equal.trans(Bool, True{}, Nat.is_lt(i, 0n), False{},
          Equal.sym(Bool, Nat.is_lt(i, 0n), True{}, lt), V2P.p6_lt_zero(i))))
    case +n <> rest:
      match i:
        case 0n:
          V2P.ar_eq_true(Nat.mod(n, 512n), 0n,
            V2P.ar_and_l(Nat.is_eq(Nat.mod(n, 512n), 0n), Spec.widths_ok(rest),
              V2P.ar_and_r(Nat.is_le(512n, n),
                Bool.and(Nat.is_eq(Nat.mod(n, 512n), 0n), Spec.widths_ok(rest)), ok)))
        case 1n+j:
          wmod(rest, j,
            V2P.ar_and_r(Nat.is_eq(Nat.mod(n, 512n), 0n), Spec.widths_ok(rest),
              V2P.ar_and_r(Nat.is_le(512n, n),
                Bool.and(Nat.is_eq(Nat.mod(n, 512n), 0n), Spec.widths_ok(rest)), ok)),
            lt)

# (w / 512) * 512 == w when w % 512 == 0.
def div_mul_exact(+w: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool},
    z: {Nat.mod(w, b) == 0n : Nat})
  -> {Nat.mul(Nat.div(w, b), b) == w : Nat}:
  %V2P.ar_add_zero_r(Nat.mul(Nat.div(w, b), b)) : {_ == w : Nat}
  %z : {Nat.add(Nat.mul(Nat.div(w, b), b), _) == w : Nat}
  V2P.ard_dm_eq(w, b, pos)

def Laws.group_map_width(ns, g, bundle, widths, inside):
  +lt4 = inside
  +M = Impl.mat(ns, g)
  %Equal.sym(Nat, Impl.gbase(ns, 1n+M), Nat.add(Impl.gbase(ns, M), Spec.ng_at(ns, M)), gsucc(M, ns)) : {Nat.mul(Nat.sub(_, Impl.gbase(ns, M)), 512n) == Spec.width(ns, M) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(Impl.gbase(ns, M), Spec.ng_at(ns, M)), Impl.gbase(ns, M)), Spec.ng_at(ns, M), V2P.ar_add_sub(Impl.gbase(ns, M), Spec.ng_at(ns, M))) : {Nat.mul(_, 512n) == Spec.width(ns, M) : Nat}
  div_mul_exact(Spec.width(ns, M), 512n, {==}, wmod(ns, M, widths, fwd_mat(ns, g, lt4, bundle)))

# ==== iteration ownership and block partition ====

# Every iteration x < I has exactly one owner (G >= 1; any I).
def own1(+x: Nat, +I: Nat, +G: Nat, +gp: {Nat.is_lt(0n, G) == True{} : Bool},
    inside: {Nat.is_lt(x, I) == True{} : Bool})
  -> {V2Spec.owners(G, x, I, G) == 1n : Nat}:
  %Equal.sym(Nat, V2Spec.owners(G, x, I, G), V2Spec.bit(Nat.is_lt(x, V2.start(G, I, G))), V2P.p1l_owners_start(G, x, I, G, gp)) : {_ == 1n : Nat}
  %Equal.sym(Nat, V2.start(G, I, G), I, V2P.p1l_start_full(I, G, gp)) : {V2Spec.bit(Nat.is_lt(x, _)) == 1n : Nat}
  %Equal.sym(Bool, Nat.is_lt(x, I), True{}, inside) : {V2Spec.bit(_) == 1n : Nat}
  {==}

# g < groups and t < KT give g * KT + t < groups * KT.
def it_lt(+g: Nat, +t: Nat, +KT: Nat, +Gr: Nat, group: {Nat.is_lt(g, Gr) == True{} : Bool},
    tile: {Nat.is_lt(t, KT) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(g, KT), t), Nat.mul(Gr, KT)) == True{} : Bool}:
  V2P.ar_lt_le_trans(Nat.add(Nat.mul(g, KT), t), Nat.mul(1n+g, KT), Nat.mul(Gr, KT),
    V2P.p2_addr_step(g, KT, t, tile), V2P.p2_m_le(g, Gr, KT, group))

def Laws.tile_owned_once(ns, k, G, i, l, t, grid, bundle, mat_i, group_l, tile_t):
  +gp = grid
  +bu = bundle
  +mi = mat_i
  +gl = group_l
  +tt = tile_t
  +lt4 = onto_groups(ns, i, l, mi, bu, gl)
  +xin = it_lt(Spec.gidx(ns, i, l), t, Impl.kt(k), Impl.groups(ns), lt4, tt)
  (xin, (own1(Nat.add(Nat.mul(Spec.gidx(ns, i, l), Impl.kt(k)), t), Impl.total(ns, k), G, gp, xin),
    (V2P.p3_dec_qr(Spec.gidx(ns, i, l), t, Impl.kt(k), tt),
      (onto_mat(ns, i, l, lt4, gl), onto_local(ns, i, l, lt4, gl)))))

def Laws.tile_decode(ns, k, x, shaped, inside):
  +kp = V2P.p2_kt_pos(k, shaped)
  (V2P.p2_rt(Nat.is_lt(x, Nat.mul(Impl.groups(ns), Impl.kt(k))),
      Nat.is_lt(Nat.div(x, Impl.kt(k)), Impl.groups(ns)),
      Equal.sym(Bool, Nat.is_lt(Nat.div(x, Impl.kt(k)), Impl.groups(ns)),
        Nat.is_lt(x, Nat.mul(Impl.groups(ns), Impl.kt(k))),
        V2P.ar_div_lt(Impl.groups(ns), x, Impl.kt(k), kp)),
      inside),
    (V2P.p3_rem_lt(x, Impl.kt(k), kp),
      V2P.ar_sub_add(x, Nat.mul(Nat.div(x, Impl.kt(k)), Impl.kt(k)),
        V2P.p9_div_mul_le(x, Impl.kt(k), kp))))

def Laws.blocks_own_ranges(ns, k, G, b, x, grid, inside):
  +gp = grid
  +ins = inside
  (Equal.sym(Bool, V2Spec.owns(b, x, Impl.total(ns, k), G),
      Bool.and(Nat.is_le(V2.start(b, Impl.total(ns, k), G), x),
        Nat.is_lt(x, V2.start(1n+b, Impl.total(ns, k), G))),
      V2P.p1_owns_range(b, x, Impl.total(ns, k), G, gp)),
    (V2P.p1l_owner_owns(x, Impl.total(ns, k), G, gp, ins),
      V2P.p1_owner_lt(x, Impl.total(ns, k), G, gp, ins)))

def Laws.mainloop_trace(s, e, KT, ordered, tiles):
  V2Laws.mainloop_trace(s, e, KT, ordered, tiles)

# ---- the bundle's total is v2's total for (mats = groups, n = 512) ----

def mul_ng512(+a: Nat) -> {Nat.mul(a, V2.ng(512n)) == a : Nat}:
  Equal.trans(Nat, Nat.mul(a, 1n), Nat.mul(1n, a), a, V2P.ar_mul_comm(a, 1n), V2P.ar_mul_one_l(a))

def tot_eq(+ns: List<&2, Nat>, +k: Nat)
  -> {V2.total(Impl.groups(ns), 512n, k) == Impl.total(ns, k) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(z, V2.kt(k)), Nat.mul(Impl.groups(ns), V2.ng(512n)),
    Impl.groups(ns), mul_ng512(Impl.groups(ns)))

# Transport of a Bool fact along T2 == T.
def tr_b(-T2: Nat, -T: Nat, e: {T2 == T : Nat}, -F: Nat -> Bool, h: {F(T) == True{} : Bool})
  -> {F(T2) == True{} : Bool}:
  %Equal.sym(Nat, T2, T, e) : {F(_) == True{} : Bool}
  h

def Laws.flush_once_iff_touches(ns, k, G, g, b, grid, shaped):
  %tot_eq(ns, k) : {V2Spec.flushes(V2.mainloop(V2.start(b, _, G), V2.start(1n+b, _, G), V2.kt(k)), g) == V2Spec.bit(V2Spec.touches(b, g, V2.kt(k), _, G)) : Nat}
  V2Laws.flush_once_iff_touches(Impl.groups(ns), 512n, k, G, g, b, grid, shaped)

# ---- contributors, slots ----

# launch_fits gives G <= total.
def fits_of(+ns: List<&2, Nat>, +k: Nat, +G: Nat, +sb: Nat,
    launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool})
  -> {Nat.is_le(G, Impl.total(ns, k)) == True{} : Bool}:
  g_ge_le(Impl.total(ns, k), G,
    V2P.ar_and_l(Nat.is_ge(Impl.total(ns, k), G),
      Nat.is_le(Nat.mul(Nat.mul(Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G)),
        Impl.slot_floats()), 4n), sb), launch))

# launch_fits gives the workspace bound.
def ws_of(+ns: List<&2, Nat>, +k: Nat, +G: Nat, +sb: Nat,
    launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.mul(Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G)),
      Impl.slot_floats()), 4n), sb) == True{} : Bool}:
  V2P.ar_and_r(Nat.is_ge(Impl.total(ns, k), G),
    Nat.is_le(Nat.mul(Nat.mul(Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G)),
      Impl.slot_floats()), 4n), sb), launch)

def Laws.contributors_contiguous(ns, k, G, sb, g, b, grid, shaped, launch, group):
  +gp = grid
  +fp = fits_of(ns, k, G, sb, launch)
  +kp = V2P.p2_kt_pos(k, shaped)
  (V2P.p2_contig1(b, g, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp),
    (V2P.p2_lo_le_hi(g, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp),
      V2P.p2_hi_lt(g, Impl.kt(k), Impl.total(ns, k), G, gp, kp,
        V2P.p2_m_le(g, Impl.groups(ns), Impl.kt(k), group))))

def slot_off_lt(+ns: List<&2, Nat>, +k: Nat, +G: Nat, +g: Nat, +b: Nat,
    +gp: {Nat.is_lt(0n, G) == True{} : Bool},
    +fp: {Nat.is_le(G, Impl.total(ns, k)) == True{} : Bool},
    +kp: {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool},
    +tc: {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
    Impl.nc(g, Impl.kt(k), Impl.total(ns, k), G)) == True{} : Bool}:
  V2P.p2_off_lt_nc(b, g, Impl.kt(k), Impl.total(ns, k), G,
    V2P.p2_lo_le_b(b, g, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tc),
    V2P.p2_b_le_hi(b, g, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tc))

def slot_addr_lt(+ns: List<&2, Nat>, +k: Nat, +G: Nat, +g: Nat, +b: Nat,
    +gp: {Nat.is_lt(0n, G) == True{} : Bool},
    +fp: {Nat.is_le(G, Impl.total(ns, k)) == True{} : Bool},
    +kp: {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool},
    +gr: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool},
    +tc: {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool})
  -> {Nat.is_lt(Impl.address(g, Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), b,
      Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
    Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G))) == True{} : Bool}:
  V2P.p2_addr_lt(g, Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G),
    Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
    V2P.p2_off_lt_mc(b, g, Impl.groups(ns), Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tc, gr), gr)

def Laws.slot_in_range(ns, k, G, sb, g, b, grid, shaped, launch, group, contributor):
  +gp = grid
  +fp = fits_of(ns, k, G, sb, launch)
  +gr = group
  +tc = contributor
  +kp = V2P.p2_kt_pos(k, shaped)
  (slot_off_lt(ns, k, G, g, b, gp, fp, kp, tc),
    (V2P.p2_nc_le_mc(g, Impl.groups(ns), Impl.kt(k), Impl.total(ns, k), G, gr),
      slot_addr_lt(ns, k, G, g, b, gp, fp, kp, gr, tc)))

# The v2 injection over launch groups g, h < groups.
def slot_inj_v2(+ns: List<&2, Nat>, +k: Nat, +G: Nat, +g: Nat, +b: Nat, +h: Nat, +c: Nat,
    +gp: {Nat.is_lt(0n, G) == True{} : Bool},
    +fp: {Nat.is_le(G, Impl.total(ns, k)) == True{} : Bool},
    +kp: {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool},
    +gg: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool},
    +gh: {Nat.is_lt(h, Impl.groups(ns)) == True{} : Bool},
    +tb: {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool},
    +tc: {V2Spec.touches(c, h, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool},
    same: {Impl.address(g, Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), b,
        Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)) ==
      Impl.address(h, Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), c,
        Impl.b_lo(h, Impl.kt(k), Impl.total(ns, k), G)) : Nat})
  -> {g == h : Nat} & {b == c : Nat}:
  V2P.p2_inj_finish(b, c, g, h, Impl.kt(k), Impl.total(ns, k), G,
    V2P.ar_divmod_inj(g, Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)), h,
      Nat.sub(c, Impl.b_lo(h, Impl.kt(k), Impl.total(ns, k), G)),
      Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G),
      V2P.p2_off_lt_mc(b, g, Impl.groups(ns), Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tb, gg),
      V2P.p2_off_lt_mc(c, h, Impl.groups(ns), Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tc, gh),
      same),
    V2P.p2_lo_le_b(b, g, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tb),
    V2P.p2_lo_le_b(c, h, Impl.kt(k), Impl.total(ns, k), G, gp, fp, kp, tc))

def Laws.slot_injective(ns, k, G, sb, i, l, b, i2, l2, c, grid, shaped, bundle, launch, mat_i,
    group_l, mat_i2, group_l2, touch_b, touch_c, same):
  +gp = grid
  +fp = fits_of(ns, k, G, sb, launch)
  +kp = V2P.p2_kt_pos(k, shaped)
  +bu = bundle
  +mi = mat_i
  +gl = group_l
  +mi2 = mat_i2
  +gl2 = group_l2
  +tb = touch_b
  +tc = touch_c
  +sm = same
  +g1 = Spec.gidx(ns, i, l)
  +g2 = Spec.gidx(ns, i2, l2)
  +lt1 = onto_groups(ns, i, l, mi, bu, gl)
  +lt2 = onto_groups(ns, i2, l2, mi2, bu, gl2)
  +eg = g_fst({g1 == g2 : Nat}, {b == c : Nat},
    slot_inj_v2(ns, k, G, g1, b, g2, c, gp, fp, kp, lt1, lt2, tb, tc, sm))
  (Equal.trans(Nat, i, Impl.mat(ns, g1), i2,
      Equal.sym(Nat, Impl.mat(ns, g1), i, onto_mat(ns, i, l, lt1, gl)),
      Equal.trans(Nat, Impl.mat(ns, g1), Impl.mat(ns, g2), i2,
        Equal.cong(Nat, Nat, z => Impl.mat(ns, z), g1, g2, eg), onto_mat(ns, i2, l2, lt2, gl2))),
    (Equal.trans(Nat, l, Impl.local(ns, g1), l2,
        Equal.sym(Nat, Impl.local(ns, g1), l, onto_local(ns, i, l, lt1, gl)),
        Equal.trans(Nat, Impl.local(ns, g1), Impl.local(ns, g2), l2,
          Equal.cong(Nat, Nat, z => Impl.local(ns, z), g1, g2, eg), onto_local(ns, i2, l2, lt2, gl2))),
      g_snd({g1 == g2 : Nat}, {b == c : Nat},
        slot_inj_v2(ns, k, G, g1, b, g2, c, gp, fp, kp, lt1, lt2, tb, tc, sm))))

# ---- workspace ----

# (A * S + Y) + Z < (A + 1) * S when Y + Z < S.
def lt_block(+A: Nat, +S: Nat, +Y: Nat, +Z: Nat,
    inner: {Nat.is_lt(Nat.add(Y, Z), S) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.add(Nat.mul(A, S), Y), Z), Nat.mul(1n+A, S)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(A, S), Y), Z), Nat.add(Nat.mul(A, S), Nat.add(Y, Z)), V2P.ar_add_assoc(Nat.mul(A, S), Y, Z)) : {Nat.is_lt(_, Nat.mul(1n+A, S)) == True{} : Bool}
  %V2P.ar_add_comm(Nat.mul(A, S), S) : {Nat.is_lt(Nat.add(Nat.mul(A, S), Nat.add(Y, Z)), _) == True{} : Bool}
  V2P.p2_tr(Nat.is_lt(Nat.add(Nat.mul(A, S), Nat.add(Y, Z)), Nat.add(Nat.mul(A, S), S)),
    Nat.is_lt(Nat.add(Y, Z), S), V2P.ar_lt_add_cancel(Nat.mul(A, S), Nat.add(Y, Z), S), inner)

# x < y gives (x + 1) * S <= y * S.
def succ_mul_le(+x: Nat, +y: Nat, +S: Nat, h: {Nat.is_lt(x, y) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(1n+x, S), Nat.mul(y, S)) == True{} : Bool}:
  V2P.ar_le_mul_mono(1n+x, y, S, V2P.p2_rt(Nat.is_lt(x, y), Nat.is_le(1n+x, y), V2P.ar_lt_succ_le(x, y), h))

def Laws.workspace_fit(ns, k, G, sb, g, b, row, col, grid, shaped, launch, group, contributor,
    row16, col512):
  +gp = grid
  +la = launch
  +fp = fits_of(ns, k, G, sb, la)
  +kp = V2P.p2_kt_pos(k, shaped)
  +gr = group
  +tc = contributor
  +A = Impl.address(g, Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), b,
    Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G))
  +MC = Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G))
  +idx = Impl.flush_float(A, row, col)
  +inner = V2P.ar_lt_le_trans(Nat.add(Nat.mul(row, 512n), col), Nat.mul(1n+row, 512n),
    Impl.slot_floats(), V2P.p2_addr_step(row, 512n, col, col512), V2P.p2_m_le(row, 16n, 512n, row16))
  +hi = V2P.ar_le_trans(1n+idx, Nat.mul(1n+A, Impl.slot_floats()), Nat.mul(MC, Impl.slot_floats()),
    V2P.p2_rt(Nat.is_lt(idx, Nat.mul(1n+A, Impl.slot_floats())),
      Nat.is_le(1n+idx, Nat.mul(1n+A, Impl.slot_floats())),
      V2P.ar_lt_succ_le(idx, Nat.mul(1n+A, Impl.slot_floats())),
      lt_block(A, Impl.slot_floats(), Nat.mul(row, 512n), col, inner)),
    succ_mul_le(A, MC, Impl.slot_floats(), slot_addr_lt(ns, k, G, g, b, gp, fp, kp, gr, tc)))
  V2P.ar_le_trans(Nat.mul(1n+idx, 4n), Nat.mul(Nat.mul(MC, Impl.slot_floats()), 4n), sb,
    V2P.ar_le_mul_mono(1n+idx, Nat.mul(MC, Impl.slot_floats()), 4n, hi), ws_of(ns, k, G, sb, la))

# (((P + R) + H) + C) + L == ((P + C) + R) + (H + L)
def rearr(+P: Nat, +R: Nat, +H: Nat, +C: Nat, +L: Nat)
  -> {Nat.add(Nat.add(Nat.add(Nat.add(P, R), H), C), L) ==
    Nat.add(Nat.add(Nat.add(P, C), R), Nat.add(H, L)) : Nat}:
  +N = Nat.add(P, Nat.add(C, Nat.add(R, Nat.add(H, L))))
  +lhs = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(P, R), H), C), L),
    Nat.add(Nat.add(Nat.add(P, R), H), Nat.add(C, L)), N,
    V2P.ar_add_assoc(Nat.add(Nat.add(P, R), H), C, L),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(P, R), H), Nat.add(C, L)),
      Nat.add(Nat.add(P, R), Nat.add(H, Nat.add(C, L))), N,
      V2P.ar_add_assoc(Nat.add(P, R), H, Nat.add(C, L)),
      Equal.trans(Nat, Nat.add(Nat.add(P, R), Nat.add(H, Nat.add(C, L))),
        Nat.add(P, Nat.add(R, Nat.add(H, Nat.add(C, L)))), N,
        V2P.ar_add_assoc(P, R, Nat.add(H, Nat.add(C, L))),
        Equal.cong(Nat, Nat, z => Nat.add(P, z), Nat.add(R, Nat.add(H, Nat.add(C, L))),
          Nat.add(C, Nat.add(R, Nat.add(H, L))),
          Equal.trans(Nat, Nat.add(R, Nat.add(H, Nat.add(C, L))), Nat.add(R, Nat.add(C, Nat.add(H, L))),
            Nat.add(C, Nat.add(R, Nat.add(H, L))),
            Equal.cong(Nat, Nat, z => Nat.add(R, z), Nat.add(H, Nat.add(C, L)), Nat.add(C, Nat.add(H, L)),
              V2P.ar_h_add_swap(H, C, L)),
            V2P.ar_h_add_swap(R, C, Nat.add(H, L)))))))
  +rhs = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(P, C), R), Nat.add(H, L)),
    Nat.add(Nat.add(P, C), Nat.add(R, Nat.add(H, L))), N,
    V2P.ar_add_assoc(Nat.add(P, C), R, Nat.add(H, L)),
    V2P.ar_add_assoc(P, C, Nat.add(R, Nat.add(H, L))))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(P, R), H), C), L), N,
    Nat.add(Nat.add(Nat.add(P, C), R), Nat.add(H, L)), lhs,
    Equal.sym(Nat, Nat.add(Nat.add(Nat.add(P, C), R), Nat.add(H, L)), N, rhs))

def Laws.finish_reads_slots(g, mc, lo, c, r, ch, lane, e):
  %Equal.sym(Nat, Nat.sub(Nat.add(lo, c), lo), c, V2P.ar_add_sub(lo, c)) : {Impl.finish_float(g, mc, c, r, ch, lane, e) == Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(g, mc), _), Impl.slot_floats()), Nat.mul(r, 512n)), Nat.add(Nat.mul(ch, 128n), Nat.add(Nat.mul(lane, 4n), e))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(g, mc), c), Impl.slot_floats()), Nat.add(Nat.mul(Nat.mul(g, mc), Impl.slot_floats()), Nat.mul(c, Impl.slot_floats())), V2P.ar_mul_add_l(Nat.mul(g, mc), c, Impl.slot_floats())) : {Impl.finish_float(g, mc, c, r, ch, lane, e) == Nat.add(Nat.add(_, Nat.mul(r, 512n)), Nat.add(Nat.mul(ch, 128n), Nat.add(Nat.mul(lane, 4n), e))) : Nat}
  rearr(Nat.mul(Nat.mul(g, mc), Impl.slot_floats()), Nat.mul(r, 512n), Nat.mul(ch, 128n),
    Nat.mul(c, Impl.slot_floats()), Nat.add(Nat.mul(lane, 4n), e))

# ---- finisher, reduction ----

def Laws.finish_jobs_once(ns, m, x, G, grid):
  V2Laws.finish_jobs_once(x, G, Impl.jobs(Impl.groups(ns), m), grid)

def Laws.reduction_order(ns, k, G, sb, g, order, ws, grid, shaped, launch, group, room, touching,
    complete):
  +gr = Impl.groups(ns)
  +T = Impl.total(ns, k)
  +T2 = V2.total(gr, 512n, k)
  %tot_eq(ns, k) : {Some{V2.finish(V2.arrive(order, ws, V2.b_lo(g, V2.kt(k), _, G)), V2.nc(g, V2.kt(k), _, G))} == V2Spec.reduce(g, V2.kt(k), _, G) : Maybe<&2, V2Spec.Sum>}
  V2Laws.reduction_order(gr, 512n, k, G, g, order, ws, grid, shaped,
    tr_b(T2, T, tot_eq(ns, k), z => Nat.is_le(G, z), fits_of(ns, k, G, sb, launch)),
    tr_b(V2.groups(gr, 512n), gr, mul_ng512(gr), z => Nat.is_lt(g, z), group),
    tr_b(T2, T, tot_eq(ns, k), z => Nat.is_le(V2.nc(g, V2.kt(k), z, G), List.length(&2, V2Spec.Sum, ws)),
      room),
    tr_b(T2, T, tot_eq(ns, k), z => V2Spec.all_touch(order, g, V2.kt(k), z, G), touching),
    tr_b(T2, T, tot_eq(ns, k), z => V2Spec.all_arrived(G, order, g, V2.kt(k), z, G), complete))

# ---- one-matrix bundles ----

def sm_groups(+n: Nat) -> {V2.groups(1n, n) == Impl.groups(n <> Nil{}) : Nat}:
  V2P.ar_mul_one_l(V2.ng(n))

def sm_total(+n: Nat, +k: Nat) -> {V2.total(1n, n, k) == Impl.total(n <> Nil{}, k) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.mul(z, V2.kt(k)), V2.groups(1n, n), Impl.groups(n <> Nil{}),
    sm_groups(n))

def sm_mc(+n: Nat, +k: Nat, +G: Nat)
  -> {Impl.max_contrib(Impl.groups(n <> Nil{}), Impl.kt(k), G) ==
    V2.max_contrib(V2.groups(1n, n), V2.kt(k), V2.total(1n, n, k), G) : Nat}:
  %Equal.sym(Nat, V2.groups(1n, n), Impl.groups(n <> Nil{}), sm_groups(n)) : {Impl.max_contrib(Impl.groups(n <> Nil{}), Impl.kt(k), G) == V2.max_contrib(_, V2.kt(k), Nat.mul(_, V2.kt(k)), G) : Nat}
  {==}

def sm_fin(+n: Nat, +k: Nat, +G: Nat, +g: Nat, +order: List<&2, Nat>, +ws: List<&2, V2Spec.Sum>)
  -> {Impl.finish(Impl.arrive(order, ws, Impl.b_lo(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)),
      Impl.nc(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)) ==
    V2.finish(V2.arrive(order, ws, V2.b_lo(g, V2.kt(k), V2.total(1n, n, k), G)),
      V2.nc(g, V2.kt(k), V2.total(1n, n, k), G)) : V2Spec.Sum}:
  %Equal.sym(Nat, V2.groups(1n, n), Impl.groups(n <> Nil{}), sm_groups(n)) : {Impl.finish(Impl.arrive(order, ws, Impl.b_lo(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)), Impl.nc(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)) == V2.finish(V2.arrive(order, ws, V2.b_lo(g, V2.kt(k), Nat.mul(_, V2.kt(k)), G)), V2.nc(g, V2.kt(k), Nat.mul(_, V2.kt(k)), G)) : V2Spec.Sum}
  {==}

def Laws.single_matrix_is_v2(n, k, G, g, order, ws):
  (Equal.sym(Nat, V2.total(1n, n, k), Impl.total(n <> Nil{}, k), sm_total(n, k)),
    (sm_mc(n, k, G), sm_fin(n, k, G, g, order, ws)))

def sm_mat(+n: Nat, +g: Nat, group: {Nat.is_lt(g, Impl.groups(n <> Nil{})) == True{} : Bool})
  -> {Impl.mat(n <> Nil{}, g) == 0n : Nat}:
  +hc = Equal.trans(Bool, Nat.is_ge(g, V2.ng(n)), Nat.is_le(V2.ng(n), g), False{},
    V2P.ar_ge_flip(g, V2.ng(n)),
    V2P.p4_not_t_f(Nat.is_le(V2.ng(n), g),
      Equal.trans(Bool, Bool.not(Nat.is_le(V2.ng(n), g)), Nat.is_lt(g, V2.ng(n)), True{},
        Equal.sym(Bool, Nat.is_lt(g, V2.ng(n)), Bool.not(Nat.is_le(V2.ng(n), g)),
          V2P.ar_lt_not_le(g, V2.ng(n))),
        group)))
  %Equal.sym(Bool, Nat.is_ge(g, V2.ng(n)), False{}, hc) : {Impl.mat.pick(_, 3n, Impl.mat.pick(_, 2n, Impl.mat.pick(_, 1n, 0n))) == 0n : Nat}
  {==}

def sm_local(+n: Nat, +g: Nat, +group: {Nat.is_lt(g, Impl.groups(n <> Nil{})) == True{} : Bool})
  -> {Impl.local(n <> Nil{}, g) == g : Nat}:
  %Equal.sym(Nat, Impl.mat(n <> Nil{}, g), 0n, sm_mat(n, g, group)) : {Nat.sub(g, Impl.gbase(n <> Nil{}, _)) == g : Nat}
  V2P.ar_sub_zero_r(g)

def Laws.single_matrix_map(n, g, group):
  +gr = group
  (sm_mat(n, g, gr), sm_local(n, g, gr))

# ---- finisher tasks ----

def jg(j: V2Spec.Job) -> Nat:
  match j:
    case V2Spec.Job{g, r, ch}:
      g

def jr(j: V2Spec.Job) -> Nat:
  match j:
    case V2Spec.Job{g, r, ch}:
      r

def jc(j: V2Spec.Job) -> Nat:
  match j:
    case V2Spec.Job{g, r, ch}:
      ch

def jd_ok(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {V2Spec.job_ok(Impl.job(x, m), gr, m) == True{} : Bool}:
  g_fst({V2Spec.job_ok(Impl.job(x, m), gr, m) == True{} : Bool},
    {V2Spec.encode(Impl.job(x, m), m) == x : Nat}, V2Laws.finish_job_decode(gr, m, x, inside))

def jd_enc(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {V2Spec.encode(Impl.job(x, m), m) == x : Nat}:
  g_snd({V2Spec.job_ok(Impl.job(x, m), gr, m) == True{} : Bool},
    {V2Spec.encode(Impl.job(x, m), m) == x : Nat}, V2Laws.finish_job_decode(gr, m, x, inside))

def jd_g(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {Nat.is_lt(jg(Impl.job(x, m)), gr) == True{} : Bool}:
  V2P.ar_and_l(Nat.is_lt(jg(Impl.job(x, m)), gr),
    Bool.and(Nat.is_lt(jr(Impl.job(x, m)), m), Nat.is_lt(jc(Impl.job(x, m)), 4n)),
    jd_ok(gr, m, x, inside))

def jd_rc(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(jr(Impl.job(x, m)), m), Nat.is_lt(jc(Impl.job(x, m)), 4n)) == True{} : Bool}:
  V2P.ar_and_r(Nat.is_lt(jg(Impl.job(x, m)), gr),
    Bool.and(Nat.is_lt(jr(Impl.job(x, m)), m), Nat.is_lt(jc(Impl.job(x, m)), 4n)),
    jd_ok(gr, m, x, inside))

def jd_r(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {Nat.is_lt(jr(Impl.job(x, m)), m) == True{} : Bool}:
  V2P.ar_and_l(Nat.is_lt(jr(Impl.job(x, m)), m), Nat.is_lt(jc(Impl.job(x, m)), 4n),
    jd_rc(gr, m, x, inside))

def jd_c(+gr: Nat, +m: Nat, +x: Nat, +inside: {Nat.is_lt(x, Impl.jobs(gr, m)) == True{} : Bool})
  -> {Nat.is_lt(jc(Impl.job(x, m)), 4n) == True{} : Bool}:
  V2P.ar_and_r(Nat.is_lt(jr(Impl.job(x, m)), m), Nat.is_lt(jc(Impl.job(x, m)), 4n),
    jd_rc(gr, m, x, inside))

# a * 512 + c * 128 == (a * 4 + c) * 128
def col_q(+a: Nat, +c: Nat)
  -> {Nat.add(Nat.mul(a, 512n), Nat.mul(c, 128n)) == Nat.mul(Nat.add(Nat.mul(a, 4n), c), 128n) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(a, 4n), c), 128n), Nat.add(Nat.mul(a, 512n), Nat.mul(c, 128n)),
    Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(a, 4n), c), 128n),
      Nat.add(Nat.mul(Nat.mul(a, 4n), 128n), Nat.mul(c, 128n)),
      Nat.add(Nat.mul(a, 512n), Nat.mul(c, 128n)),
      V2P.ar_mul_add_l(Nat.mul(a, 4n), c, 128n),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(c, 128n)), Nat.mul(Nat.mul(a, 4n), 128n),
        Nat.mul(a, 512n), V2P.ar_mul_assoc(a, 4n, 128n))))

def eq_le(+X: Nat, +W: Nat, E: {X == W : Nat}) -> {Nat.is_le(X, W) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(X, W), Nat.is_le(W, W), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, W), X, W, E), V2P.ar_le_refl(W))

def mod_mul128(+q: Nat) -> {Nat.mod(Nat.mul(q, 128n), 128n) == 0n : Nat}:
  %V2P.ar_add_zero_r(Nat.mul(q, 128n)) : {Nat.mod(_, 128n) == 0n : Nat}
  g_snd({Nat.div(Nat.add(Nat.mul(q, 128n), 0n), 128n) == q : Nat},
    {Nat.mod(Nat.add(Nat.mul(q, 128n), 0n), 128n) == 0n : Nat}, V2P.ar_div_unique(q, 0n, 128n, {==}))

# The task's first column: (local * 4 + ch) * 128.
def fp_mod(+L: Nat, +C: Nat) -> {Nat.mod(Nat.add(Nat.mul(L, 512n), Nat.mul(C, 128n)), 128n) == 0n : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mul(L, 512n), Nat.mul(C, 128n)), Nat.mul(Nat.add(Nat.mul(L, 4n), C), 128n), col_q(L, C)) : {Nat.mod(_, 128n) == 0n : Nat}
  mod_mul128(Nat.add(Nat.mul(L, 4n), C))

# L < ng, C < 4, ng * 512 == W give L * 512 + C * 128 + 128 <= W.
def fp_end(+L: Nat, +C: Nat, +ng: Nat, +W: Nat, lt: {Nat.is_lt(L, ng) == True{} : Bool},
    c4: {Nat.is_lt(C, 4n) == True{} : Bool}, wq: {Nat.mul(ng, 512n) == W : Nat})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.mul(L, 512n), Nat.mul(C, 128n)), 128n), W) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.mul(L, 512n), Nat.mul(C, 128n)), Nat.mul(Nat.add(Nat.mul(L, 4n), C), 128n), col_q(L, C)) : {Nat.is_le(Nat.add(_, 128n), W) == True{} : Bool}
  %V2P.ar_add_comm(128n, Nat.mul(Nat.add(Nat.mul(L, 4n), C), 128n)) : {Nat.is_le(_, W) == True{} : Bool}
  V2P.ar_le_trans(Nat.mul(1n+Nat.add(Nat.mul(L, 4n), C), 128n), Nat.mul(Nat.mul(ng, 4n), 128n), W,
    succ_mul_le(Nat.add(Nat.mul(L, 4n), C), Nat.mul(ng, 4n), 128n, it_lt(L, C, 4n, ng, lt, c4)),
    eq_le(Nat.mul(Nat.mul(ng, 4n), 128n), W,
      Equal.trans(Nat, Nat.mul(Nat.mul(ng, 4n), 128n), Nat.mul(ng, 512n), W,
        V2P.ar_mul_assoc(ng, 4n, 128n), wq)))

def Laws.finish_place(ns, m, x, bundle, widths, inside):
  +bu = bundle
  +ins = inside
  +gr = Impl.groups(ns)
  +G0 = jg(Impl.job(x, m))
  +hg = jd_g(gr, m, x, ins)
  +M = Impl.mat(ns, G0)
  (fwd_mat(ns, G0, hg, bu),
    (jd_r(gr, m, x, ins),
      (fp_mod(Impl.local(ns, G0), jc(Impl.job(x, m))),
        fp_end(Impl.local(ns, G0), jc(Impl.job(x, m)), Spec.ng_at(ns, M), Spec.width(ns, M),
          fwd_local(ns, G0, hg), jd_c(gr, m, x, ins),
          div_mul_exact(Spec.width(ns, M), 512n, {==}, wmod(ns, M, widths, fwd_mat(ns, G0, hg, bu)))))))

# (q / 4) * 512 + (q % 4) * 128 == q * 128
def colq_full(+q: Nat)
  -> {Nat.add(Nat.mul(Nat.div(q, 4n), 512n), Nat.mul(Nat.mod(q, 4n), 128n)) == Nat.mul(q, 128n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(q, 4n), 512n), Nat.mul(Nat.mod(q, 4n), 128n)),
    Nat.mul(Nat.add(Nat.mul(Nat.div(q, 4n), 4n), Nat.mod(q, 4n)), 128n), Nat.mul(q, 128n),
    col_q(Nat.div(q, 4n), Nat.mod(q, 4n)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), Nat.add(Nat.mul(Nat.div(q, 4n), 4n), Nat.mod(q, 4n)), q,
      V2P.ard_dm_eq(q, 4n, {==})))

def fpo_l(+ns: List<&2, Nat>, +i: Nat, +q: Nat,
    chunk_q: {Nat.is_lt(q, Nat.mul(Spec.ng_at(ns, i), 4n)) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(q, 4n), Spec.ng_at(ns, i)) == True{} : Bool}:
  V2P.p2_tr(Nat.is_lt(Nat.div(q, 4n), Spec.ng_at(ns, i)), Nat.is_lt(q, Nat.mul(Spec.ng_at(ns, i), 4n)),
    V2P.ar_div_lt(Spec.ng_at(ns, i), q, 4n, {==}), chunk_q)

def fpo_ok(+ns: List<&2, Nat>, +m: Nat, +i: Nat, +r: Nat, +q: Nat,
    lt4: {Nat.is_lt(Spec.gidx(ns, i, Nat.div(q, 4n)), Impl.groups(ns)) == True{} : Bool},
    row_r: {Nat.is_lt(r, m) == True{} : Bool})
  -> {V2Spec.job_ok(V2Spec.Job{Spec.gidx(ns, i, Nat.div(q, 4n)), r, Nat.mod(q, 4n)}, Impl.groups(ns), m)
    == True{} : Bool}:
  V2P.ar_and_intro(Nat.is_lt(Spec.gidx(ns, i, Nat.div(q, 4n)), Impl.groups(ns)),
    Bool.and(Nat.is_lt(r, m), Nat.is_lt(Nat.mod(q, 4n), 4n)), lt4,
    V2P.ar_and_intro(Nat.is_lt(r, m), Nat.is_lt(Nat.mod(q, 4n), 4n), row_r, V2P.ard_dm_lt(q, 4n, {==})))

def fpo_place(+ns: List<&2, Nat>, +m: Nat, +i: Nat, +r: Nat, +q: Nat,
    +lt4: {Nat.is_lt(Spec.gidx(ns, i, Nat.div(q, 4n)), Impl.groups(ns)) == True{} : Bool},
    +hl: {Nat.is_lt(Nat.div(q, 4n), Spec.ng_at(ns, i)) == True{} : Bool},
    +row_r: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Impl.place(ns, V2Spec.encode(V2Spec.Job{Spec.gidx(ns, i, Nat.div(q, 4n)), r, Nat.mod(q, 4n)}, m), m)
    == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}:
  +g = Spec.gidx(ns, i, Nat.div(q, 4n))
  +j = {V2Spec.Job{g, r, Nat.mod(q, 4n)} : V2Spec.Job}
  %Equal.sym(V2Spec.Job, Impl.job(V2Spec.encode(j, m), m), j, g_fst({Impl.job(V2Spec.encode(j, m), m) == j : V2Spec.Job}, {Nat.is_lt(V2Spec.encode(j, m), Impl.jobs(Impl.groups(ns), m)) == True{} : Bool}, V2Laws.finish_job_encode(Impl.groups(ns), m, j, fpo_ok(ns, m, i, r, q, lt4, row_r)))) : {Impl.place.of(_, ns) == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}
  %Equal.sym(Nat, Impl.mat(ns, g), i, onto_mat(ns, i, Nat.div(q, 4n), lt4, hl)) : {Spec.Place{_, r, Nat.add(Nat.mul(Impl.local(ns, g), 512n), Nat.mul(Nat.mod(q, 4n), 128n))} == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}
  %Equal.sym(Nat, Impl.local(ns, g), Nat.div(q, 4n), onto_local(ns, i, Nat.div(q, 4n), lt4, hl)) : {Spec.Place{i, r, Nat.add(Nat.mul(_, 512n), Nat.mul(Nat.mod(q, 4n), 128n))} == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}
  %Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(q, 4n), 512n), Nat.mul(Nat.mod(q, 4n), 128n)), Nat.mul(q, 128n), colq_full(q)) : {Spec.Place{i, r, _} == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}
  {==}

def Laws.finish_place_onto(ns, m, i, r, q, bundle, mat_i, row_r, chunk_q):
  +hl = fpo_l(ns, i, q, chunk_q)
  +lt4 = onto_groups(ns, i, Nat.div(q, 4n), mat_i, bundle, hl)
  +rr = row_r
  +j = {V2Spec.Job{Spec.gidx(ns, i, Nat.div(q, 4n)), r, Nat.mod(q, 4n)} : V2Spec.Job}
  (g_snd({Impl.job(V2Spec.encode(j, m), m) == j : V2Spec.Job},
      {Nat.is_lt(V2Spec.encode(j, m), Impl.jobs(Impl.groups(ns), m)) == True{} : Bool},
      V2Laws.finish_job_encode(Impl.groups(ns), m, j, fpo_ok(ns, m, i, r, q, lt4, rr))),
    fpo_place(ns, m, i, r, q, lt4, hl, rr))

def enc_cong(+g1: Nat, +r1: Nat, +c1: Nat, +g2: Nat, +r2: Nat, +c2: Nat, +m: Nat,
    eg: {g1 == g2 : Nat}, er: {r1 == r2 : Nat}, ec: {c1 == c2 : Nat})
  -> {V2Spec.encode(V2Spec.Job{g1, r1, c1}, m) == V2Spec.encode(V2Spec.Job{g2, r2, c2}, m) : Nat}:
  %eg : {V2Spec.encode(V2Spec.Job{g1, r1, c1}, m) == V2Spec.encode(V2Spec.Job{_, r2, c2}, m) : Nat}
  %er : {V2Spec.encode(V2Spec.Job{g1, r1, c1}, m) == V2Spec.encode(V2Spec.Job{g1, _, c2}, m) : Nat}
  %ec : {V2Spec.encode(V2Spec.Job{g1, r1, c1}, m) == V2Spec.encode(V2Spec.Job{g1, r1, _}, m) : Nat}
  {==}

def mul_cancel(+a: Nat, +b: Nat, +c: Nat, +pos: {Nat.is_lt(0n, c) == True{} : Bool},
    +e: {Nat.mul(a, c) == Nat.mul(b, c) : Nat})
  -> {a == b : Nat}:
  V2P.ar_le_antisym(a, b,
    V2P.p2_rt(Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)), Nat.is_le(a, b), V2P.ar_mul_le_cancel(a, b, c, pos),
      eq_le(Nat.mul(a, c), Nat.mul(b, c), e)),
    V2P.p2_rt(Nat.is_le(Nat.mul(b, c), Nat.mul(a, c)), Nat.is_le(b, a), V2P.ar_mul_le_cancel(b, a, c, pos),
      eq_le(Nat.mul(b, c), Nat.mul(a, c), Equal.sym(Nat, Nat.mul(a, c), Nat.mul(b, c), e))))

# Equal task columns give equal (local, chunk).
def col_inj(+L1: Nat, +C1: Nat, +L2: Nat, +C2: Nat, c1: {Nat.is_lt(C1, 4n) == True{} : Bool},
    c2: {Nat.is_lt(C2, 4n) == True{} : Bool},
    e: {Nat.add(Nat.mul(L1, 512n), Nat.mul(C1, 128n)) == Nat.add(Nat.mul(L2, 512n), Nat.mul(C2, 128n)) : Nat})
  -> {L1 == L2 : Nat} & {C1 == C2 : Nat}:
  V2P.ar_divmod_inj(L1, C1, L2, C2, 4n, c1, c2,
    mul_cancel(Nat.add(Nat.mul(L1, 4n), C1), Nat.add(Nat.mul(L2, 4n), C2), 128n, {==},
      Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(L1, 4n), C1), 128n),
        Nat.add(Nat.mul(L1, 512n), Nat.mul(C1, 128n)), Nat.mul(Nat.add(Nat.mul(L2, 4n), C2), 128n),
        Equal.sym(Nat, Nat.add(Nat.mul(L1, 512n), Nat.mul(C1, 128n)),
          Nat.mul(Nat.add(Nat.mul(L1, 4n), C1), 128n), col_q(L1, C1)),
        Equal.trans(Nat, Nat.add(Nat.mul(L1, 512n), Nat.mul(C1, 128n)),
          Nat.add(Nat.mul(L2, 512n), Nat.mul(C2, 128n)), Nat.mul(Nat.add(Nat.mul(L2, 4n), C2), 128n),
          e, col_q(L2, C2)))))

def Laws.finish_place_injective(ns, m, x, y, bundle, inside_x, inside_y, same):
  +ix = inside_x
  +iy = inside_y
  +sm = same
  +gr = Impl.groups(ns)
  +Gx = jg(Impl.job(x, m))
  +Gy = jg(Impl.job(y, m))
  +hgx = jd_g(gr, m, x, ix)
  +hgy = jd_g(gr, m, y, iy)
  +eM = Equal.cong(Spec.Place, Nat, p => Spec.place_mat(p), Impl.place(ns, x, m), Impl.place(ns, y, m), sm)
  +eR = Equal.cong(Spec.Place, Nat, p => Spec.place_r(p), Impl.place(ns, x, m), Impl.place(ns, y, m), sm)
  +eC = Equal.cong(Spec.Place, Nat, p => Spec.place_col0(p), Impl.place(ns, x, m), Impl.place(ns, y, m), sm)
  +eL = g_fst({Impl.local(ns, Gx) == Impl.local(ns, Gy) : Nat}, {jc(Impl.job(x, m)) == jc(Impl.job(y, m)) : Nat},
    col_inj(Impl.local(ns, Gx), jc(Impl.job(x, m)), Impl.local(ns, Gy), jc(Impl.job(y, m)),
      jd_c(gr, m, x, ix), jd_c(gr, m, y, iy), eC))
  +eCh = g_snd({Impl.local(ns, Gx) == Impl.local(ns, Gy) : Nat}, {jc(Impl.job(x, m)) == jc(Impl.job(y, m)) : Nat},
    col_inj(Impl.local(ns, Gx), jc(Impl.job(x, m)), Impl.local(ns, Gy), jc(Impl.job(y, m)),
      jd_c(gr, m, x, ix), jd_c(gr, m, y, iy), eC))
  +eG = Equal.trans(Nat, Gx, Spec.gidx(ns, Impl.mat(ns, Gx), Impl.local(ns, Gx)), Gy,
    Equal.sym(Nat, Spec.gidx(ns, Impl.mat(ns, Gx), Impl.local(ns, Gx)), Gx, fwd_gidx(ns, Gx, hgx)),
    Equal.trans(Nat, Spec.gidx(ns, Impl.mat(ns, Gx), Impl.local(ns, Gx)),
      Spec.gidx(ns, Impl.mat(ns, Gy), Impl.local(ns, Gy)), Gy,
      Equal.trans(Nat, Spec.gidx(ns, Impl.mat(ns, Gx), Impl.local(ns, Gx)),
        Spec.gidx(ns, Impl.mat(ns, Gy), Impl.local(ns, Gx)),
        Spec.gidx(ns, Impl.mat(ns, Gy), Impl.local(ns, Gy)),
        Equal.cong(Nat, Nat, z => Spec.gidx(ns, z, Impl.local(ns, Gx)), Impl.mat(ns, Gx), Impl.mat(ns, Gy), eM),
        Equal.cong(Nat, Nat, z => Spec.gidx(ns, Impl.mat(ns, Gy), z), Impl.local(ns, Gx), Impl.local(ns, Gy), eL)),
      fwd_gidx(ns, Gy, hgy)))
  Equal.trans(Nat, x, V2Spec.encode(Impl.job(x, m), m), y,
    Equal.sym(Nat, V2Spec.encode(Impl.job(x, m), m), x, jd_enc(gr, m, x, ix)),
    Equal.trans(Nat, V2Spec.encode(Impl.job(x, m), m), V2Spec.encode(Impl.job(y, m), m), y,
      enc_cong(Gx, jr(Impl.job(x, m)), jc(Impl.job(x, m)), Gy, jr(Impl.job(y, m)), jc(Impl.job(y, m)), m,
        eG, eR, eCh),
      jd_enc(gr, m, y, iy)))

# ==== prologue input transform ====

def Laws.prologue_jobs_once(nm, m, k, w, G, grid):
  V2Laws.finish_jobs_once(w, G, Impl.total_warps(nm, m, k), grid)

# k % 128 == 0 gives (k / 128) * 128 == k.
def kq(+k: Nat, aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool})
  -> {Nat.mul(Nat.div(k, 128n), 128n) == k : Nat}:
  div_mul_exact(k, 128n, {==}, V2P.ar_eq_true(Nat.mod(k, 128n), 0n, aligned))

def div_mul128(+X: Nat) -> {Nat.div(Nat.mul(X, 128n), 128n) == X : Nat}:
  %V2P.ar_add_zero_r(Nat.mul(X, 128n)) : {Nat.div(_, 128n) == X : Nat}
  g_fst({Nat.div(Nat.add(Nat.mul(X, 128n), 0n), 128n) == X : Nat},
    {Nat.mod(Nat.add(Nat.mul(X, 128n), 0n), 128n) == 0n : Nat}, V2P.ar_div_unique(X, 0n, 128n, {==}))

# m * k == (m * (k / 128)) * 128
def mk_eq(+m: Nat, +k: Nat, +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool})
  -> {Nat.mul(m, k) == Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n) : Nat}:
  Equal.trans(Nat, Nat.mul(m, k), Nat.mul(m, Nat.mul(Nat.div(k, 128n), 128n)),
    Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n),
    Equal.cong(Nat, Nat, z => Nat.mul(m, z), k, Nat.mul(Nat.div(k, 128n), 128n),
      Equal.sym(Nat, Nat.mul(Nat.div(k, 128n), 128n), k, kq(k, aligned))),
    Equal.sym(Nat, Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n), Nat.mul(m, Nat.mul(Nat.div(k, 128n), 128n)),
      V2P.ar_mul_assoc(m, Nat.div(k, 128n), 128n)))

# per_mat = m * (k / 128)
def pm_eq(+m: Nat, +k: Nat, +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool})
  -> {Impl.per_mat(m, k) == Nat.mul(m, Nat.div(k, 128n)) : Nat}:
  %Equal.sym(Nat, Nat.mul(m, k), Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n), mk_eq(m, k, aligned)) : {Nat.div(_, 128n) == Nat.mul(m, Nat.div(k, 128n)) : Nat}
  div_mul128(Nat.mul(m, Nat.div(k, 128n)))

# cell_index(i, r, c) == i * per_mat + (r * KB + c)
def w_split(+m: Nat, +k: Nat, +i: Nat, +r: Nat, +c: Nat)
  -> {Spec.cell_index(m, k, i, r, c) ==
    Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)) : Nat}:
  +KB = Nat.div(k, 128n)
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(i, m), r), KB), c),
    Nat.add(Nat.add(Nat.mul(Nat.mul(i, m), KB), Nat.mul(r, KB)), c),
    Nat.add(Nat.mul(i, Nat.mul(m, KB)), Nat.add(Nat.mul(r, KB), c)),
    Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.mul(Nat.add(Nat.mul(i, m), r), KB),
      Nat.add(Nat.mul(Nat.mul(i, m), KB), Nat.mul(r, KB)), V2P.ar_mul_add_l(Nat.mul(i, m), r, KB)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(i, m), KB), Nat.mul(r, KB)), c),
      Nat.add(Nat.mul(Nat.mul(i, m), KB), Nat.add(Nat.mul(r, KB), c)),
      Nat.add(Nat.mul(i, Nat.mul(m, KB)), Nat.add(Nat.mul(r, KB), c)),
      V2P.ar_add_assoc(Nat.mul(Nat.mul(i, m), KB), Nat.mul(r, KB), c),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(Nat.mul(r, KB), c)), Nat.mul(Nat.mul(i, m), KB),
        Nat.mul(i, Nat.mul(m, KB)), V2P.ar_mul_assoc(i, m, KB))))

def pr_mat(+m: Nat, +k: Nat, +i: Nat, +r: Nat, +c: Nat,
    +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool},
    rest_lt: {Nat.is_lt(Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), Nat.mul(m, Nat.div(k, 128n))) == True{} : Bool})
  -> {Impl.pro_mat(Spec.cell_index(m, k, i, r, c), Impl.per_mat(m, k)) == i : Nat}:
  %Equal.sym(Nat, Impl.per_mat(m, k), Nat.mul(m, Nat.div(k, 128n)), pm_eq(m, k, aligned)) : {Nat.div(Spec.cell_index(m, k, i, r, c), _) == i : Nat}
  %Equal.sym(Nat, Spec.cell_index(m, k, i, r, c), Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)), w_split(m, k, i, r, c)) : {Nat.div(_, Nat.mul(m, Nat.div(k, 128n))) == i : Nat}
  g_fst({Nat.div(Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)), Nat.mul(m, Nat.div(k, 128n))) == i : Nat},
    {Nat.mod(Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)), Nat.mul(m, Nat.div(k, 128n))) == Nat.add(Nat.mul(r, Nat.div(k, 128n)), c) : Nat},
    V2P.ar_div_unique(i, Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), Nat.mul(m, Nat.div(k, 128n)), rest_lt))

def pr_r(+m: Nat, +k: Nat, +i: Nat, +r: Nat, +c: Nat,
    +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool},
    +rest_lt: {Nat.is_lt(Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), Nat.mul(m, Nat.div(k, 128n))) == True{} : Bool})
  -> {Impl.pro_r(Spec.cell_index(m, k, i, r, c), Impl.per_mat(m, k)) ==
    Nat.add(Nat.mul(r, Nat.div(k, 128n)), c) : Nat}:
  %Equal.sym(Nat, Impl.pro_mat(Spec.cell_index(m, k, i, r, c), Impl.per_mat(m, k)), i, pr_mat(m, k, i, r, c, aligned, rest_lt)) : {Nat.sub(Spec.cell_index(m, k, i, r, c), Nat.mul(_, Impl.per_mat(m, k))) == Nat.add(Nat.mul(r, Nat.div(k, 128n)), c) : Nat}
  %Equal.sym(Nat, Impl.per_mat(m, k), Nat.mul(m, Nat.div(k, 128n)), pm_eq(m, k, aligned)) : {Nat.sub(Spec.cell_index(m, k, i, r, c), Nat.mul(i, _)) == Nat.add(Nat.mul(r, Nat.div(k, 128n)), c) : Nat}
  %Equal.sym(Nat, Spec.cell_index(m, k, i, r, c), Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)), w_split(m, k, i, r, c)) : {Nat.sub(_, Nat.mul(i, Nat.mul(m, Nat.div(k, 128n)))) == Nat.add(Nat.mul(r, Nat.div(k, 128n)), c) : Nat}
  V2P.ar_add_sub(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c))

# (r * KB + c) * 128 == r * k + c * 128
def rk_eq(+k: Nat, +r: Nat, +c: Nat, +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool})
  -> {Nat.mul(Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), 128n) == Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), 128n),
    Nat.add(Nat.mul(Nat.mul(r, Nat.div(k, 128n)), 128n), Nat.mul(c, 128n)),
    Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)),
    V2P.ar_mul_add_l(Nat.mul(r, Nat.div(k, 128n)), c, 128n),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(c, 128n)), Nat.mul(Nat.mul(r, Nat.div(k, 128n)), 128n),
      Nat.mul(r, k),
      Equal.trans(Nat, Nat.mul(Nat.mul(r, Nat.div(k, 128n)), 128n), Nat.mul(r, Nat.mul(Nat.div(k, 128n), 128n)),
        Nat.mul(r, k), V2P.ar_mul_assoc(r, Nat.div(k, 128n), 128n),
        Equal.cong(Nat, Nat, z => Nat.mul(r, z), Nat.mul(Nat.div(k, 128n), 128n), k, kq(k, aligned)))))

def pc_lt(+nm: Nat, +m: Nat, +k: Nat, +i: Nat, +r: Nat, +c: Nat,
    +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool},
    mat_i: {Nat.is_lt(i, nm) == True{} : Bool},
    rest_lt: {Nat.is_lt(Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), Nat.mul(m, Nat.div(k, 128n))) == True{} : Bool})
  -> {Nat.is_lt(Spec.cell_index(m, k, i, r, c), Impl.total_warps(nm, m, k)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.per_mat(m, k), Nat.mul(m, Nat.div(k, 128n)), pm_eq(m, k, aligned)) : {Nat.is_lt(Spec.cell_index(m, k, i, r, c), Nat.mul(nm, _)) == True{} : Bool}
  %Equal.sym(Nat, Spec.cell_index(m, k, i, r, c), Nat.add(Nat.mul(i, Nat.mul(m, Nat.div(k, 128n))), Nat.add(Nat.mul(r, Nat.div(k, 128n)), c)), w_split(m, k, i, r, c)) : {Nat.is_lt(_, Nat.mul(nm, Nat.mul(m, Nat.div(k, 128n)))) == True{} : Bool}
  it_lt(i, Nat.add(Nat.mul(r, Nat.div(k, 128n)), c), Nat.mul(m, Nat.div(k, 128n)), nm, mat_i, rest_lt)

def Laws.prologue_cover(nm, m, k, i, r, c, aligned, mat_i, row_r, block_c):
  +al = aligned
  +bc = block_c
  +KB = Nat.div(k, 128n)
  +rest = Nat.add(Nat.mul(r, KB), c)
  +rl = V2P.ar_lt_le_trans(rest, Nat.mul(1n+r, KB), Nat.mul(m, KB),
    V2P.p2_addr_step(r, KB, c, bc), V2P.p2_m_le(r, m, KB, row_r))
  +w = Spec.cell_index(m, k, i, r, c)
  +PMt = Impl.per_mat(m, k)
  +pm = pr_mat(m, k, i, r, c, al, rl)
  +pr = pr_r(m, k, i, r, c, al, rl)
  +rk = rk_eq(k, r, c, al)
  +ra = Equal.trans(Nat, Nat.mul(Impl.pro_r(w, PMt), 128n), Nat.mul(rest, 128n),
    Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), Impl.pro_r(w, PMt), rest, pr), rk)
  +small = V2P.p2_rt(Nat.is_lt(Nat.mul(c, 128n), Nat.mul(KB, 128n)), Nat.is_lt(Nat.mul(c, 128n), k),
    Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.mul(c, 128n), z), Nat.mul(KB, 128n), k, kq(k, al)),
    V2P.p2_tr(Nat.is_lt(Nat.mul(c, 128n), Nat.mul(KB, 128n)), Nat.is_lt(c, KB),
      V2P.ar_mul_lt_cancel(c, KB, 128n, {==}), bc))
  (pc_lt(nm, m, k, i, r, c, al, mat_i, rl),
    (pm,
      (Equal.trans(Nat, Impl.pro_xh(m, k, w),
          Nat.add(Nat.mul(Nat.mul(i, m), k), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
          Spec.xh_cell(m, k, i, r, c),
          Equal.trans(Nat, Impl.pro_xh(m, k, w),
            Nat.add(Nat.mul(Nat.mul(i, m), k), Nat.mul(Impl.pro_r(w, PMt), 128n)),
            Nat.add(Nat.mul(Nat.mul(i, m), k), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
            Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.mul(z, m), k), Nat.mul(Impl.pro_r(w, PMt), 128n)),
              Impl.pro_mat(w, PMt), i, pm),
            Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(Nat.mul(i, m), k), z),
              Nat.mul(Impl.pro_r(w, PMt), 128n), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)), ra)),
          Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(i, m), k), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
            Nat.add(Nat.mul(i, Nat.mul(m, k)), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
            Spec.xh_cell(m, k, i, r, c),
            Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
              Nat.mul(Nat.mul(i, m), k), Nat.mul(i, Nat.mul(m, k)), V2P.ar_mul_assoc(i, m, k)),
            Equal.sym(Nat, Spec.xh_cell(m, k, i, r, c),
              Nat.add(Nat.mul(i, Nat.mul(m, k)), Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))),
              V2P.ar_add_assoc(Nat.mul(i, Nat.mul(m, k)), Nat.mul(r, k), Nat.mul(c, 128n))))),
        (ra,
          Equal.trans(Nat, Impl.pro_suh(m, k, w), Nat.mod(Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)), k),
            Nat.mul(c, 128n),
            Equal.cong(Nat, Nat, z => Nat.mod(z, k), Nat.mul(Impl.pro_r(w, PMt), 128n),
              Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)), ra),
            g_snd({Nat.div(Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)), k) == r : Nat},
              {Nat.mod(Nat.add(Nat.mul(r, k), Nat.mul(c, 128n)), k) == Nat.mul(c, 128n) : Nat},
              V2P.ar_div_unique(r, Nat.mul(c, 128n), k, small)))))))

def pos_of(+nm: Nat, +pm: Nat, +w: Nat, h: {Nat.is_lt(w, Nat.mul(nm, pm)) == True{} : Bool})
  -> {Nat.is_lt(0n, pm) == True{} : Bool}:
  match pm:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        V2P.ar_true_false(Equal.trans(Bool, True{}, Nat.is_lt(w, 0n), False{},
          Equal.trans(Bool, True{}, Nat.is_lt(w, Nat.mul(nm, 0n)), Nat.is_lt(w, 0n),
            Equal.sym(Bool, Nat.is_lt(w, Nat.mul(nm, 0n)), True{}, h),
            Equal.cong(Nat, Bool, z => Nat.is_lt(w, z), Nat.mul(nm, 0n), 0n, V2P.ar_mul_zero_r(nm))),
          V2P.p6_lt_zero(w))))
    case 1n+p:
      {==}

# pro_xh(w) == 128 w for w < total_warps
def pw_eq(+nm: Nat, +m: Nat, +k: Nat, +w: Nat,
    +aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool},
    +inside: {Nat.is_lt(w, Impl.total_warps(nm, m, k)) == True{} : Bool})
  -> {Impl.pro_xh(m, k, w) == Nat.mul(w, 128n) : Nat}:
  +PMt = Impl.per_mat(m, k)
  +M = Nat.div(w, PMt)
  +R = Nat.sub(w, Nat.mul(M, PMt))
  +pos = pos_of(nm, PMt, w, inside)
  +pm128 = Equal.trans(Nat, Nat.mul(m, k), Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n), Nat.mul(PMt, 128n),
    mk_eq(m, k, aligned),
    Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), Nat.mul(m, Nat.div(k, 128n)), PMt,
      Equal.sym(Nat, PMt, Nat.mul(m, Nat.div(k, 128n)), pm_eq(m, k, aligned))))
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(M, m), k), Nat.mul(R, 128n)),
    Nat.add(Nat.mul(Nat.mul(M, PMt), 128n), Nat.mul(R, 128n)), Nat.mul(w, 128n),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(R, 128n)), Nat.mul(Nat.mul(M, m), k), Nat.mul(Nat.mul(M, PMt), 128n),
      Equal.trans(Nat, Nat.mul(Nat.mul(M, m), k), Nat.mul(M, Nat.mul(m, k)), Nat.mul(Nat.mul(M, PMt), 128n),
        V2P.ar_mul_assoc(M, m, k),
        Equal.trans(Nat, Nat.mul(M, Nat.mul(m, k)), Nat.mul(M, Nat.mul(PMt, 128n)), Nat.mul(Nat.mul(M, PMt), 128n),
          Equal.cong(Nat, Nat, z => Nat.mul(M, z), Nat.mul(m, k), Nat.mul(PMt, 128n), pm128),
          Equal.sym(Nat, Nat.mul(Nat.mul(M, PMt), 128n), Nat.mul(M, Nat.mul(PMt, 128n)),
            V2P.ar_mul_assoc(M, PMt, 128n))))),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(M, PMt), 128n), Nat.mul(R, 128n)),
      Nat.mul(Nat.add(Nat.mul(M, PMt), R), 128n), Nat.mul(w, 128n),
      Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(M, PMt), R), 128n),
        Nat.add(Nat.mul(Nat.mul(M, PMt), 128n), Nat.mul(R, 128n)), V2P.ar_mul_add_l(Nat.mul(M, PMt), R, 128n)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), Nat.add(Nat.mul(M, PMt), R), w,
        V2P.ar_sub_add(w, Nat.mul(M, PMt), V2P.p9_div_mul_le(w, PMt, pos)))))

def pw_bound(+nm: Nat, +m: Nat, +k: Nat, +w: Nat,
    inside: {Nat.is_lt(w, Impl.total_warps(nm, m, k)) == True{} : Bool},
    eq: {Impl.pro_xh(m, k, w) == Nat.mul(w, 128n) : Nat},
    tail: {Nat.mul(Nat.mul(nm, Impl.per_mat(m, k)), 128n) == Nat.mul(Nat.mul(nm, m), k) : Nat})
  -> {Nat.is_le(Nat.add(Impl.pro_xh(m, k, w), 128n), Nat.mul(Nat.mul(nm, m), k)) == True{} : Bool}:
  %Equal.sym(Nat, Impl.pro_xh(m, k, w), Nat.mul(w, 128n), eq) : {Nat.is_le(Nat.add(_, 128n), Nat.mul(Nat.mul(nm, m), k)) == True{} : Bool}
  %V2P.ar_add_comm(128n, Nat.mul(w, 128n)) : {Nat.is_le(_, Nat.mul(Nat.mul(nm, m), k)) == True{} : Bool}
  V2P.ar_le_trans(Nat.mul(1n+w, 128n), Nat.mul(Nat.mul(nm, Impl.per_mat(m, k)), 128n), Nat.mul(Nat.mul(nm, m), k),
    succ_mul_le(w, Nat.mul(nm, Impl.per_mat(m, k)), 128n, inside),
    eq_le(Nat.mul(Nat.mul(nm, Impl.per_mat(m, k)), 128n), Nat.mul(Nat.mul(nm, m), k), tail))

def Laws.prologue_writes(nm, m, k, w, aligned, inside):
  +al = aligned
  +ins = inside
  +PMt = Impl.per_mat(m, k)
  +eq = pw_eq(nm, m, k, w, al, ins)
  +tail = Equal.trans(Nat, Nat.mul(Nat.mul(nm, PMt), 128n), Nat.mul(nm, Nat.mul(PMt, 128n)),
    Nat.mul(Nat.mul(nm, m), k), V2P.ar_mul_assoc(nm, PMt, 128n),
    Equal.trans(Nat, Nat.mul(nm, Nat.mul(PMt, 128n)), Nat.mul(nm, Nat.mul(m, k)), Nat.mul(Nat.mul(nm, m), k),
      Equal.cong(Nat, Nat, z => Nat.mul(nm, z), Nat.mul(PMt, 128n), Nat.mul(m, k),
        Equal.trans(Nat, Nat.mul(PMt, 128n), Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n), Nat.mul(m, k),
          Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), PMt, Nat.mul(m, Nat.div(k, 128n)), pm_eq(m, k, al)),
          Equal.sym(Nat, Nat.mul(m, k), Nat.mul(Nat.mul(m, Nat.div(k, 128n)), 128n), mk_eq(m, k, al)))),
      Equal.sym(Nat, Nat.mul(Nat.mul(nm, m), k), Nat.mul(nm, Nat.mul(m, k)), V2P.ar_mul_assoc(nm, m, k))))
  (eq, pw_bound(nm, m, k, w, ins, eq, tail))

# ==== weight issue cursor ====

def is_step(w: Bool, +g: Nat, +kt: Nat, +KT: Nat, +ns: List<&2, Nat>, +warp: Nat, +lane: Nat,
    small: {Nat.is_lt(kt, KT) == True{} : Bool}, pos: {Nat.is_lt(0n, KT) == True{} : Bool},
    hb: {Nat.is_eq(1n+kt, KT) == w : Bool})
  -> {Impl.Iss{V2.advance.pick(w, g, 1n+kt), Impl.issue.ptr(w, True{}, ns, 1n+g, warp, lane,
      Impl.WPtr{Impl.mat(ns, g), Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g))),
        Impl.row_bytes(ns, g)})} ==
    Impl.wsite(ns, 1n+Nat.add(Nat.mul(g, KT), kt), KT, warp, lane) : Impl.Iss}:
  match w:
    case True{}:
      %V2P.p3_step_pick(True{}, g, kt, KT, small, pos, hb) : {Impl.Iss{V2.Cursor{1n+g, 0n}, Impl.WPtr{Impl.mat(ns, 1n+g), Impl.wsrc(ns, 1n+g, warp, lane), Impl.row_bytes(ns, 1n+g)}} == Impl.wsite.of(_, ns, warp, lane) : Impl.Iss}
      %Equal.sym(Nat, Nat.add(Impl.wsrc(ns, 1n+g, warp, lane), 0n), Impl.wsrc(ns, 1n+g, warp, lane), V2P.ar_add_zero_r(Impl.wsrc(ns, 1n+g, warp, lane))) : {Impl.Iss{V2.Cursor{1n+g, 0n}, Impl.WPtr{Impl.mat(ns, 1n+g), Impl.wsrc(ns, 1n+g, warp, lane), Impl.row_bytes(ns, 1n+g)}} == Impl.Iss{V2.Cursor{1n+g, 0n}, Impl.WPtr{Impl.mat(ns, 1n+g), _, Impl.row_bytes(ns, 1n+g)}} : Impl.Iss}
      {==}
    case False{}:
      %V2P.p3_step_pick(False{}, g, kt, KT, small, pos, hb) : {Impl.Iss{V2.Cursor{g, 1n+kt}, Impl.WPtr{Impl.mat(ns, g), Nat.add(Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g))), Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g)}} == Impl.wsite.of(_, ns, warp, lane) : Impl.Iss}
      %Equal.trans(Nat, Nat.add(Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g))), Impl.row_bytes(ns, g)), Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.add(Nat.mul(kt, Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g))), Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.add(Impl.row_bytes(ns, g), Nat.mul(kt, Impl.row_bytes(ns, g)))), V2P.ar_add_assoc(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g)), Equal.cong(Nat, Nat, z => Nat.add(Impl.wsrc(ns, g, warp, lane), z), Nat.add(Nat.mul(kt, Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g)), Nat.add(Impl.row_bytes(ns, g), Nat.mul(kt, Impl.row_bytes(ns, g))), V2P.ar_add_comm(Nat.mul(kt, Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g)))) : {Impl.Iss{V2.Cursor{g, 1n+kt}, Impl.WPtr{Impl.mat(ns, g), Nat.add(Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g))), Impl.row_bytes(ns, g)), Impl.row_bytes(ns, g)}} == Impl.Iss{V2.Cursor{g, 1n+kt}, Impl.WPtr{Impl.mat(ns, g), _, Impl.row_bytes(ns, g)}} : Impl.Iss}
      {==}

def is_go(+j: Nat, +s: Nat, +n: Nat, +KT: Nat, +ns: List<&2, Nat>, +warp: Nat, +lane: Nat,
    +pos: {Nat.is_lt(0n, KT) == True{} : Bool}, +lt: {Nat.is_lt(j, n) == True{} : Bool})
  -> {Impl.issued(j, s, n, KT, ns, warp, lane) == Impl.wsite(ns, Nat.add(s, j), KT, warp, lane) : Impl.Iss}:
  match j:
    case 0n:
      %Equal.sym(Nat, Nat.add(s, 0n), s, V2P.ar_add_zero_r(s)) : {Impl.wsite(ns, s, KT, warp, lane) == Impl.wsite(ns, _, KT, warp, lane) : Impl.Iss}
      {==}
    case 1n+i:
      +x = Nat.add(s, i)
      +q = Nat.div(x, KT)
      +r = Nat.sub(x, Nat.mul(q, KT))
      +ih = is_go(i, s, n, KT, ns, warp, lane, pos, V2P.ar_lt_trans(i, 1n+i, n, V2P.p6_lt_succ(i), lt))
      %Equal.sym(Impl.Iss, Impl.issued(i, s, n, KT, ns, warp, lane), Impl.wsite(ns, x, KT, warp, lane), ih) : {Impl.issue.step(_, i, n, KT, ns, warp, lane) == Impl.wsite(ns, Nat.add(s, 1n+i), KT, warp, lane) : Impl.Iss}
      %Equal.sym(Nat, Nat.add(s, 1n+i), 1n+x, V2P.ar_add_succ_r(s, i)) : {Impl.issue.step(Impl.wsite(ns, x, KT, warp, lane), i, n, KT, ns, warp, lane) == Impl.wsite(ns, _, KT, warp, lane) : Impl.Iss}
      %Equal.sym(Bool, Nat.is_lt(1n+i, n), True{}, lt) : {Impl.Iss{V2.advance(V2.Cursor{q, r}, KT), Impl.issue.ptr(Nat.is_eq(1n+r, KT), _, ns, 1n+q, warp, lane, Impl.WPtr{Impl.mat(ns, q), Nat.add(Impl.wsrc(ns, q, warp, lane), Nat.mul(r, Impl.row_bytes(ns, q))), Impl.row_bytes(ns, q)})} == Impl.wsite(ns, 1n+x, KT, warp, lane) : Impl.Iss}
      %V2P.ar_sub_add(x, Nat.mul(q, KT), V2P.p9_div_mul_le(x, KT, pos)) : {Impl.Iss{V2.advance(V2.Cursor{q, r}, KT), Impl.issue.ptr(Nat.is_eq(1n+r, KT), True{}, ns, 1n+q, warp, lane, Impl.WPtr{Impl.mat(ns, q), Nat.add(Impl.wsrc(ns, q, warp, lane), Nat.mul(r, Impl.row_bytes(ns, q))), Impl.row_bytes(ns, q)})} == Impl.wsite(ns, 1n+_, KT, warp, lane) : Impl.Iss}
      is_step(Nat.is_eq(1n+r, KT), q, r, KT, ns, warp, lane, V2P.p3_rem_lt(x, KT, pos), pos, {==})

def Laws.issue_site(s, n, KT, j, ns, warp, lane, tiles, issuing):
  +t = tiles
  is_go(j, s, n, KT, ns, warp, lane, t, issuing)

# ---- weight site bounds ----

# rb(g) == (ng_at(mat) * 32) * 128
def rb_eq(+ns: List<&2, Nat>, +g: Nat)
  -> {Impl.row_bytes(ns, g) == Nat.mul(Nat.mul(Spec.ng_at(ns, Impl.mat(ns, g)), 32n), 128n) : Nat}:
  +M = Impl.mat(ns, g)
  Equal.cong(Nat, Nat, z => Nat.mul(Nat.mul(z, 32n), 128n), Nat.sub(Impl.gbase(ns, 1n+M), Impl.gbase(ns, M)),
    Spec.ng_at(ns, M),
    Equal.trans(Nat, Nat.sub(Impl.gbase(ns, 1n+M), Impl.gbase(ns, M)),
      Nat.sub(Nat.add(Impl.gbase(ns, M), Spec.ng_at(ns, M)), Impl.gbase(ns, M)), Spec.ng_at(ns, M),
      Equal.cong(Nat, Nat, z => Nat.sub(z, Impl.gbase(ns, M)), Impl.gbase(ns, 1n+M),
        Nat.add(Impl.gbase(ns, M), Spec.ng_at(ns, M)), gsucc(M, ns)),
      V2P.ar_add_sub(Impl.gbase(ns, M), Spec.ng_at(ns, M))))

# (x + 1) * S written as x * S + S.
def succ_mul_r(+x: Nat, +S: Nat) -> {Nat.add(Nat.mul(x, S), S) == Nat.mul(1n+x, S) : Nat}:
  V2P.ar_add_comm(Nat.mul(x, S), S)

# (L * 32 + w * 4) + 4 <= ng * 32 for L < ng, w < 8.
def ws_q(+L: Nat, +w: Nat, +ng: Nat, lt: {Nat.is_lt(L, ng) == True{} : Bool},
    w8: {Nat.is_lt(w, 8n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.mul(L, 32n), Nat.mul(w, 4n)), 4n), Nat.mul(ng, 32n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(L, 32n), Nat.mul(w, 4n)), 4n), Nat.add(Nat.mul(L, 32n), Nat.add(Nat.mul(w, 4n), 4n)), V2P.ar_add_assoc(Nat.mul(L, 32n), Nat.mul(w, 4n), 4n)) : {Nat.is_le(_, Nat.mul(ng, 32n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.mul(w, 4n), 4n), Nat.mul(1n+w, 4n), succ_mul_r(w, 4n)) : {Nat.is_le(Nat.add(Nat.mul(L, 32n), _), Nat.mul(ng, 32n)) == True{} : Bool}
  V2P.ar_le_trans(Nat.add(Nat.mul(L, 32n), Nat.mul(1n+w, 4n)), Nat.add(Nat.mul(L, 32n), 32n), Nat.mul(ng, 32n),
    V2P.p2_tr(Nat.is_le(Nat.add(Nat.mul(L, 32n), Nat.mul(1n+w, 4n)), Nat.add(Nat.mul(L, 32n), 32n)),
      Nat.is_le(Nat.mul(1n+w, 4n), 32n), V2P.ar_le_add_cancel(Nat.mul(L, 32n), Nat.mul(1n+w, 4n), 32n),
      V2P.p2_m_le(w, 8n, 4n, w8)),
    V2P.ar_le_trans(Nat.add(Nat.mul(L, 32n), 32n), Nat.mul(1n+L, 32n), Nat.mul(ng, 32n),
      eq_le(Nat.add(Nat.mul(L, 32n), 32n), Nat.mul(1n+L, 32n), succ_mul_r(L, 32n)),
      succ_mul_le(L, ng, 32n, lt)))

# wsrc + 16 <= (ng * 32) * 128
def ws_a(+L: Nat, +w: Nat, +lane: Nat, +ng: Nat, lt: {Nat.is_lt(L, ng) == True{} : Bool},
    w8: {Nat.is_lt(w, 8n) == True{} : Bool}, l32: {Nat.is_lt(lane, 32n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(L, 32n), Nat.mul(w, 4n)), 128n), Nat.mul(lane, 16n)), 16n),
    Nat.mul(Nat.mul(ng, 32n), 128n)) == True{} : Bool}:
  +Q = Nat.add(Nat.mul(L, 32n), Nat.mul(w, 4n))
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Q, 128n), Nat.mul(lane, 16n)), 16n), Nat.add(Nat.mul(Q, 128n), Nat.add(Nat.mul(lane, 16n), 16n)), V2P.ar_add_assoc(Nat.mul(Q, 128n), Nat.mul(lane, 16n), 16n)) : {Nat.is_le(_, Nat.mul(Nat.mul(ng, 32n), 128n)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.mul(lane, 16n), 16n), Nat.mul(1n+lane, 16n), succ_mul_r(lane, 16n)) : {Nat.is_le(Nat.add(Nat.mul(Q, 128n), _), Nat.mul(Nat.mul(ng, 32n), 128n)) == True{} : Bool}
  V2P.ar_le_trans(Nat.add(Nat.mul(Q, 128n), Nat.mul(1n+lane, 16n)), Nat.mul(Nat.add(Q, 4n), 128n),
    Nat.mul(Nat.mul(ng, 32n), 128n),
    V2P.ar_le_trans(Nat.add(Nat.mul(Q, 128n), Nat.mul(1n+lane, 16n)), Nat.add(Nat.mul(Q, 128n), Nat.mul(4n, 128n)),
      Nat.mul(Nat.add(Q, 4n), 128n),
      V2P.p2_tr(Nat.is_le(Nat.add(Nat.mul(Q, 128n), Nat.mul(1n+lane, 16n)), Nat.add(Nat.mul(Q, 128n), Nat.mul(4n, 128n))),
        Nat.is_le(Nat.mul(1n+lane, 16n), Nat.mul(4n, 128n)),
        V2P.ar_le_add_cancel(Nat.mul(Q, 128n), Nat.mul(1n+lane, 16n), Nat.mul(4n, 128n)),
        V2P.p2_m_le(lane, 32n, 16n, l32)),
      eq_le(Nat.add(Nat.mul(Q, 128n), Nat.mul(4n, 128n)), Nat.mul(Nat.add(Q, 4n), 128n),
        Equal.sym(Nat, Nat.mul(Nat.add(Q, 4n), 128n), Nat.add(Nat.mul(Q, 128n), Nat.mul(4n, 128n)),
          V2P.ar_mul_add_l(Q, 4n, 128n)))),
    V2P.ar_le_mul_mono(Nat.add(Q, 4n), Nat.mul(ng, 32n), 128n, ws_q(L, w, ng, lt, w8)))

# (W + kt * rb) + 16 <= KT * rb when W + 16 <= rb and kt < KT.
def ws_b(+W: Nat, +kt: Nat, +rb: Nat, +KT: Nat, a: {Nat.is_le(Nat.add(W, 16n), rb) == True{} : Bool},
    tile: {Nat.is_lt(kt, KT) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(W, Nat.mul(kt, rb)), 16n), Nat.mul(KT, rb)) == True{} : Bool}:
  %Equal.cong(Nat, Nat, z => Nat.add(z, 16n), Nat.add(Nat.mul(kt, rb), W), Nat.add(W, Nat.mul(kt, rb)), V2P.ar_add_comm(Nat.mul(kt, rb), W)) : {Nat.is_le(_, Nat.mul(KT, rb)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(kt, rb), W), 16n), Nat.add(Nat.mul(kt, rb), Nat.add(W, 16n)), V2P.ar_add_assoc(Nat.mul(kt, rb), W, 16n)) : {Nat.is_le(_, Nat.mul(KT, rb)) == True{} : Bool}
  V2P.ar_le_trans(Nat.add(Nat.mul(kt, rb), Nat.add(W, 16n)), Nat.mul(1n+kt, rb), Nat.mul(KT, rb),
    V2P.ar_le_trans(Nat.add(Nat.mul(kt, rb), Nat.add(W, 16n)), Nat.add(Nat.mul(kt, rb), rb), Nat.mul(1n+kt, rb),
      V2P.p2_tr(Nat.is_le(Nat.add(Nat.mul(kt, rb), Nat.add(W, 16n)), Nat.add(Nat.mul(kt, rb), rb)),
        Nat.is_le(Nat.add(W, 16n), rb), V2P.ar_le_add_cancel(Nat.mul(kt, rb), Nat.add(W, 16n), rb), a),
      eq_le(Nat.add(Nat.mul(kt, rb), rb), Nat.mul(1n+kt, rb), succ_mul_r(kt, rb))),
    succ_mul_le(kt, KT, rb, tile))

def div_mul16(+X: Nat) -> {Nat.div(Nat.mul(X, 16n), 16n) == X : Nat}:
  %V2P.ar_add_zero_r(Nat.mul(X, 16n)) : {Nat.div(_, 16n) == X : Nat}
  g_fst({Nat.div(Nat.add(Nat.mul(X, 16n), 0n), 16n) == X : Nat},
    {Nat.mod(Nat.add(Nat.mul(X, 16n), 0n), 16n) == 0n : Nat}, V2P.ar_div_unique(X, 0n, 16n, {==}))

def Laws.weight_site_in_matrix(ns, k, g, kt, warp, lane, bundle, widths, inside, tile, warp8, lane32):
  +lt4 = inside
  +M = Impl.mat(ns, g)
  +ng = Spec.ng_at(ns, M)
  +rbe = rb_eq(ns, g)
  +wd = div_mul_exact(Spec.width(ns, M), 512n, {==}, wmod(ns, M, widths, fwd_mat(ns, g, lt4, bundle)))
  (ws_b(Impl.wsrc(ns, g, warp, lane), kt, Impl.row_bytes(ns, g), Impl.kt(k),
      V2P.p2_tr(Nat.is_le(Nat.add(Impl.wsrc(ns, g, warp, lane), 16n), Impl.row_bytes(ns, g)),
        Nat.is_le(Nat.add(Impl.wsrc(ns, g, warp, lane), 16n), Nat.mul(Nat.mul(ng, 32n), 128n)),
        Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(Impl.wsrc(ns, g, warp, lane), 16n), z),
          Impl.row_bytes(ns, g), Nat.mul(Nat.mul(ng, 32n), 128n), rbe),
        ws_a(Impl.local(ns, g), warp, lane, ng, fwd_local(ns, g, lt4), warp8, lane32)),
      tile),
    Equal.trans(Nat, Impl.row_bytes(ns, g), Nat.mul(Nat.mul(ng, 32n), 128n),
      Nat.mul(Nat.div(Spec.width(ns, M), 16n), 128n), rbe,
      Equal.cong(Nat, Nat, z => Nat.mul(z, 128n), Nat.mul(ng, 32n), Nat.div(Spec.width(ns, M), 16n),
        Equal.sym(Nat, Nat.div(Spec.width(ns, M), 16n), Nat.mul(ng, 32n),
          Equal.trans(Nat, Nat.div(Spec.width(ns, M), 16n), Nat.div(Nat.mul(Nat.mul(ng, 32n), 16n), 16n),
            Nat.mul(ng, 32n),
            Equal.cong(Nat, Nat, z => Nat.div(z, 16n), Spec.width(ns, M), Nat.mul(Nat.mul(ng, 32n), 16n),
              Equal.trans(Nat, Spec.width(ns, M), Nat.mul(ng, 512n), Nat.mul(Nat.mul(ng, 32n), 16n),
                Equal.sym(Nat, Nat.mul(ng, 512n), Spec.width(ns, M), wd),
                Equal.sym(Nat, Nat.mul(Nat.mul(ng, 32n), 16n), Nat.mul(ng, 512n), V2P.ar_mul_assoc(ng, 32n, 16n)))),
            div_mul16(Nat.mul(ng, 32n)))))))
