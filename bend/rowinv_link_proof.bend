# Proofs of bend/rowinv_link_laws.bend. The composition is an induction over the layers (the
# served launch of layer l against layer l of the 1-row-round reference) with the invariant
# "every row's layer input is the reference value at the row's absolute prefix"; inside a layer,
# an induction over the row's ancestors shows that the served context (committed state advanced
# by the gathered rows' entries) is the reference's committed state before the row's position.
# Tools: causality of the reference (take commutes with every layer), the snoc forms of a layer's
# state and last output, and the path obligations. Arithmetic from gemm_m16_partition_proof.
import Base
import ./rowinv_link.bend as Impl
import ./rowinv_link_spec.bend as Spec
import ./rowinv_link_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

# ---------------------------------------------------------------- arithmetic (rewrite forms)

def ri_zr(+a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(a, 0n), a, Ar.ar_add_zero_r(a))

def ri_sr(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Ar.ar_add_succ_r(a, b))

# ---------------------------------------------------------------- generic lists

# Nothing is below 0
def ri_lt_zero(+k: Nat, h: {Nat.is_lt(k, 0n) == True{} : Bool}) -> Empty:
  Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, Ar.ar_h_lt_zero(k)), h))

def ri_app_nil(~A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, A>, List<&2, A>, x => h <> x, List.append(&2, A, t, Nil{}), t, ri_app_nil(~A, t))

def ri_app_assoc(~A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>)
  -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, A>, List<&2, A>, x => h <> x,
        List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)),
        ri_app_assoc(~A, t, ys, zs))

def ri_len_app(~A: Data, xs: List<&2, A>, +ys: List<&2, A>)
  -> {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, A, List.append(&2, A, t, ys)),
        Nat.add(List.length(&2, A, t), List.length(&2, A, ys)), ri_len_app(~A, t, ys))

# take (xs ++ ys) (|xs| + k) == xs ++ take ys k
def ri_take_app(~A: Data, xs: List<&2, A>, +ys: List<&2, A>, +k: Nat)
  -> {List.take(&2, A, List.append(&2, A, xs, ys), Nat.add(List.length(&2, A, xs), k)) ==
      List.append(&2, A, xs, List.take(&2, A, ys, k)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, A>, List<&2, A>, x => h <> x,
        List.take(&2, A, List.append(&2, A, t, ys), Nat.add(List.length(&2, A, t), k)),
        List.append(&2, A, t, List.take(&2, A, ys, k)), ri_take_app(~A, t, ys, k))

def ri_take_nil(~A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, 0n) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def ri_take_len(~A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, List.length(&2, A, xs)) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      Equal.cong(List<&2, A>, List<&2, A>, x => h <> x, List.take(&2, A, t, List.length(&2, A, t)), t, ri_take_len(~A, t))

# |take xs k| == k for k <= |xs|
def ri_len_take(~A: Data, xs: List<&2, A>, +k: Nat, h: {Nat.is_le(k, List.length(&2, A, xs)) == True{} : Bool})
  -> {List.length(&2, A, List.take(&2, A, xs, k)) == k : Nat}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Empty.absurd({List.length(&2, A, List.take(&2, A, Nil{}, 1n+j)) == 1n+j : Nat}, Ar.ar_false_true(h))
    case +x <> t:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, A, List.take(&2, A, t, j)), j, ri_len_take(~A, t, j, h))

# take xs (1 + k) == take xs k ++ [at xs k] for k < |xs|
def ri_take_snoc(~A: Data, ~z: A, xs: List<&2, A>, +k: Nat, h: {Nat.is_lt(k, List.length(&2, A, xs)) == True{} : Bool})
  -> {List.take(&2, A, xs, 1n+k) == List.append(&2, A, List.take(&2, A, xs, k), [Impl.at(~A, ~z, xs, k)]) : List<&2, A>}:
  match xs:
    case Nil{}:
      Empty.absurd({List.take(&2, A, Nil{}, 1n+k) == List.append(&2, A, List.take(&2, A, Nil{}, k), [Impl.at(~A, ~z, Nil{}, k)]) : List<&2, A>},
        ri_lt_zero(k, h))
    case +x <> t:
      match k:
        case 0n:
          %Equal.sym(List<&2, A>, List.take(&2, A, t, 0n), Nil{}, ri_take_nil(~A, t)) : {x <> _ == [x] : List<&2, A>}
          {==}
        case 1n+j:
          Equal.cong(List<&2, A>, List<&2, A>, y => x <> y, List.take(&2, A, t, 1n+j),
            List.append(&2, A, List.take(&2, A, t, j), [Impl.at(~A, ~z, t, j)]), ri_take_snoc(~A, ~z, t, j, h))

# The same for a path (nthn)
def ri_take_snoc_n(xs: List<&2, Nat>, +k: Nat, h: {Nat.is_lt(k, List.length(&2, Nat, xs)) == True{} : Bool})
  -> {List.take(&2, Nat, xs, 1n+k) == List.append(&2, Nat, List.take(&2, Nat, xs, k), [Impl.nthn(xs, k)]) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      Empty.absurd({List.take(&2, Nat, Nil{}, 1n+k) == List.append(&2, Nat, List.take(&2, Nat, Nil{}, k), [Impl.nthn(Nil{}, k)]) : List<&2, Nat>},
        ri_lt_zero(k, h))
    case +x <> t:
      match k:
        case 0n:
          %Equal.sym(List<&2, Nat>, List.take(&2, Nat, t, 0n), Nil{}, ri_take_nil(~Nat, t)) : {x <> _ == [x] : List<&2, Nat>}
          {==}
        case 1n+j:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, y => x <> y, List.take(&2, Nat, t, 1n+j),
            List.append(&2, Nat, List.take(&2, Nat, t, j), [Impl.nthn(t, j)]), ri_take_snoc_n(t, j, h))

# last.go over a snoc is the snoc'd element
def ri_last_go_snoc(~V: Data, xs: List<&2, V>, -p: V, +y: V)
  -> {Spec.last.go(~V, List.append(&2, V, xs, [y]), p) == y : V}:
  match xs:
    case Nil{}:
      {==}
    case a <> t:
      ri_last_go_snoc(~V, t, a, y)

def ri_last_snoc(~V: Data, ~z: V, xs: List<&2, V>, +y: V) -> {Spec.last(~V, ~z, List.append(&2, V, xs, [y])) == y : V}:
  match xs:
    case Nil{}:
      {==}
    case a <> t:
      ri_last_go_snoc(~V, t, a, y)

# ---------------------------------------------------------------- the reference: lengths, causality

def ri_len_lo(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +l: Nat, +c: C, +i: Nat)
  -> {List.length(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i)) == List.length(&2, V, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(Nat, Nat, y => 1n+y,
        List.length(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i)),
        List.length(&2, V, rest),
        ri_len_lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i))

def ri_len_up(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, cs: List<&2, C>, +l: Nat, +xs: List<&2, V>, +i: Nat)
  -> {List.length(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, cs, l, xs, i)) == List.length(&2, V, xs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      Equal.trans(Nat,
        List.length(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), i)),
        List.length(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i)),
        List.length(&2, V, xs),
        ri_len_up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), i),
        ri_len_lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i))

def ri_len_embs(~V: Data, ~emb: U32 -> V, w: List<&2, U32>) -> {List.length(&2, V, Spec.embs(~V, ~emb, w)) == List.length(&2, U32, w) : Nat}:
  match w:
    case Nil{}:
      {==}
    case x <> rest:
      Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, V, Spec.embs(~V, ~emb, rest)), List.length(&2, U32, rest), ri_len_embs(~V, ~emb, rest))

def ri_embs_take(~V: Data, ~emb: U32 -> V, w: List<&2, U32>, +k: Nat)
  -> {List.take(&2, V, Spec.embs(~V, ~emb, w), k) == Spec.embs(~V, ~emb, List.take(&2, U32, w, k)) : List<&2, V>}:
  match w:
    case Nil{}:
      {==}
    case +x <> rest:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(List<&2, V>, List<&2, V>, y => emb(x) <> y, List.take(&2, V, Spec.embs(~V, ~emb, rest), j),
            Spec.embs(~V, ~emb, List.take(&2, U32, rest, j)), ri_embs_take(~V, ~emb, rest, j))

# A layer is causal: the first k outputs are the outputs of the first k inputs.
def ri_lo_take(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +k: Nat, +l: Nat, +c: C, +i: Nat)
  -> {List.take(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), k) ==
      Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.take(&2, V, xs, k), l, c, i) : List<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(List<&2, V>, List<&2, V>, y => F(l, plan(l, i, 1n, 0n, 0n), c, x) <> y,
            List.take(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i), j),
            Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.take(&2, V, rest, j), l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i),
            ri_lo_take(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, j, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i))

# ... hence so is every stack of layers.
def ri_up_take(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, cs: List<&2, C>, +l: Nat, +xs: List<&2, V>, +k: Nat, +i: Nat)
  -> {List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, cs, l, xs, i), k) ==
      Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, cs, l, List.take(&2, V, xs, k), i) : List<&2, V>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      Equal.trans(List<&2, V>,
        List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), i), k),
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, List.take(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), k), i),
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.take(&2, V, xs, k), l, c, i), i),
        ri_up_take(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), k, i),
        Equal.cong(List<&2, V>, List<&2, V>, y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, y, i),
          List.take(&2, V, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), k),
          Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.take(&2, V, xs, k), l, c, i),
          ri_lo_take(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, k, l, c, i)))

# Stacking one more layer: up (pre ++ [c]) == lo after up pre (layer index l + |pre|).
def ri_up_snoc(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, pre: List<&2, C>, +c: C, +l: Nat, +xs: List<&2, V>, +i: Nat)
  -> {Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), l, xs, i) ==
      Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, l, xs, i),
        Nat.add(l, List.length(&2, C, pre)), c, i) : List<&2, V>}:
  match pre:
    case Nil{}:
      %ri_zr(l) : {Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i) ==
        Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, _, c, i) : List<&2, V>}
      {==}
    case +p <> +rest:
      %ri_sr(l, List.length(&2, C, rest)) : {Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, rest, [c]), 1n+l,
          Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, p, i), i) ==
        Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan,
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, p, i), i), _, c, i) : List<&2, V>}
      ri_up_snoc(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, c, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, p, i), i)

# The state after the first 1 + k inputs: one more entry after the first k (position i + k).
def ri_ls_step(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~z: V, ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C,
    ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +k: Nat, +l: Nat, +c: C, +i: Nat,
    h: {Nat.is_lt(k, List.length(&2, V, xs)) == True{} : Bool})
  -> {Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, xs, 1n+k), l, c, i) ==
      adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, xs, k), l, c, i),
        ent(l, plan(l, Nat.add(i, k), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, xs, 1n+k)))) : C}:
  match xs:
    case Nil{}:
      Empty.absurd({Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Nil{}, 1n+k), l, c, i) ==
        adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Nil{}, k), l, c, i),
          ent(l, plan(l, Nat.add(i, k), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Nil{}, 1n+k)))) : C}, ri_lt_zero(k, h))
    case +x <> rest:
      match rest:
        case Nil{}:
          match k:
            case 0n:
              %ri_zr(i) : {Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, [x], 1n), l, c, i) ==
                adv(l, c, ent(l, plan(l, _, 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, [x], 1n)))) : C}
              {==}
            case 1n+j:
              Empty.absurd({Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, [x], 2n+j), l, c, i) ==
                adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, [x], 1n+j), l, c, i),
                  ent(l, plan(l, Nat.add(i, 1n+j), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, [x], 2n+j)))) : C}, ri_lt_zero(j, h))
        case +y <> more:
          match k:
            case 0n:
              %ri_zr(i) : {Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, x <> y <> more, 1n), l, c, i) ==
                adv(l, c, ent(l, plan(l, _, 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, x <> y <> more, 1n)))) : C}
              {==}
            case 1n+j:
              %ri_sr(i, j) : {Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, x <> y <> more, 2n+j), l, c, i) ==
                adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, x <> y <> more, 1n+j), l, c, i),
                  ent(l, plan(l, _, 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, x <> y <> more, 2n+j)))) : C}
              ri_ls_step(~V, ~E, ~C, ~P, ~z, ~ent, ~adv, ~plan, y <> more, j, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i, h)

# The last output of a layer over 1 + k inputs: F at position i + k from the state after the first
# k inputs, on the last input.
def ri_lo_last(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~z: V, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +k: Nat, +l: Nat, +c: C, +i: Nat,
    h: {List.length(&2, V, xs) == 1n+k : Nat})
  -> {Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i)) ==
      F(l, plan(l, Nat.add(i, k), 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, xs, k), l, c, i),
        Spec.last(~V, ~z, xs)) : V}:
  match xs:
    case Nil{}:
      Empty.absurd({Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Nil{}, l, c, i)) ==
        F(l, plan(l, Nat.add(i, k), 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Nil{}, k), l, c, i),
          Spec.last(~V, ~z, Nil{})) : V}, Ar.ar_zero_succ(k, h))
    case +x <> rest:
      match rest:
        case Nil{}:
          match k:
            case 0n:
              %ri_zr(i) : {Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, [x], l, c, i)) ==
                F(l, plan(l, _, 1n, 0n, 0n), c, Spec.last(~V, ~z, [x])) : V}
              {==}
            case 1n+j:
              Empty.absurd({Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, [x], l, c, i)) ==
                F(l, plan(l, Nat.add(i, 1n+j), 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, [x], 1n+j), l, c, i),
                  Spec.last(~V, ~z, [x])) : V}, Ar.ar_zero_succ(j, Ar.ar_succ_inj(0n, 1n+j, h)))
        case +y <> more:
          match k:
            case 0n:
              Empty.absurd({Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, x <> y <> more, l, c, i)) ==
                F(l, plan(l, Nat.add(i, 0n), 1n, 0n, 0n), c, Spec.last(~V, ~z, x <> y <> more)) : V},
                Ar.ar_zero_succ(List.length(&2, V, more), Equal.sym(Nat, 1n+List.length(&2, V, more), 0n, Ar.ar_succ_inj(1n+List.length(&2, V, more), 0n, h))))
            case 1n+j:
              %ri_sr(i, j) : {Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, x <> y <> more, l, c, i)) ==
                F(l, plan(l, _, 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, x <> y <> more, 1n+j), l, c, i),
                  Spec.last(~V, ~z, x <> y <> more)) : V}
              ri_lo_last(~V, ~E, ~C, ~P, ~z, ~F, ~ent, ~adv, ~plan, y <> more, j, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i,
                Ar.ar_succ_inj(List.length(&2, V, y <> more), 1n+j, h))

# ---------------------------------------------------------------- the served model: lists

def ri_sub1_le(+n: Nat) -> {Nat.is_le(Nat.sub(n, 1n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, Ar.ar_sub_zero_r(p)) : {Nat.is_le(_, 1n+p) == True{} : Bool}
      Ar.ar_h_le_succ(p)

# r0 < r0 + (1 + k)
def ri_lt_add(+r0: Nat, +k: Nat) -> {Nat.is_lt(r0, Nat.add(r0, 1n+k)) == True{} : Bool}:
  match r0:
    case 0n:
      {==}
    case 1n+q:
      ri_lt_add(q, k)

def ri_ctx_snoc(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, ~pth: T -> Nat -> List<&2, Nat>,
    rows: List<&2, Nat>, +a: Nat, +l: Nat, +c: C, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>)
  -> {Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.append(&2, Nat, rows, [a]), l, c, sh, base, m, vals) ==
      adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, rows, l, c, sh, base, m, vals),
        ent(l, plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), Impl.at(~V, ~z, vals, a))) : C}:
  match rows:
    case Nil{}:
      {==}
    case +b <> rest:
      ri_ctx_snoc(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, rest, a, l,
        adv(l, c, ent(l, plan(l, base, m, b, Impl.dep(~T, ~pth, sh, b)), Impl.at(~V, ~z, vals, b))), sh, base, m, vals)

def ri_stream_take(+toks: List<&2, U32>, ps: List<&2, Nat>, +k: Nat)
  -> {Impl.stream(toks, List.take(&2, Nat, ps, k)) == List.take(&2, U32, Impl.stream(toks, ps), k) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case +a <> rest:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(List<&2, U32>, List<&2, U32>, y => Impl.at(~U32, ~0, toks, a) <> y,
            Impl.stream(toks, List.take(&2, Nat, rest, j)), List.take(&2, U32, Impl.stream(toks, rest), j),
            ri_stream_take(toks, rest, j))

def ri_stream_app(+toks: List<&2, U32>, ps: List<&2, Nat>, +qs: List<&2, Nat>)
  -> {Impl.stream(toks, List.append(&2, Nat, ps, qs)) == List.append(&2, U32, Impl.stream(toks, ps), Impl.stream(toks, qs)) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case +a <> rest:
      Equal.cong(List<&2, U32>, List<&2, U32>, y => Impl.at(~U32, ~0, toks, a) <> y,
        Impl.stream(toks, List.append(&2, Nat, rest, qs)), List.append(&2, U32, Impl.stream(toks, rest), Impl.stream(toks, qs)),
        ri_stream_app(toks, rest, qs))

def ri_len_stream(+toks: List<&2, U32>, ps: List<&2, Nat>)
  -> {List.length(&2, U32, Impl.stream(toks, ps)) == List.length(&2, Nat, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case a <> rest:
      Equal.cong(Nat, Nat, y => 1n+y, List.length(&2, U32, Impl.stream(toks, rest)), List.length(&2, Nat, rest), ri_len_stream(toks, rest))

def ri_embs_snoc(~V: Data, ~emb: U32 -> V, xs: List<&2, U32>, +y: U32)
  -> {Spec.embs(~V, ~emb, List.append(&2, U32, xs, [y])) == List.append(&2, V, Spec.embs(~V, ~emb, xs), [emb(y)]) : List<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      Equal.cong(List<&2, V>, List<&2, V>, t => emb(x) <> t, Spec.embs(~V, ~emb, List.append(&2, U32, rest, [y])),
        List.append(&2, V, Spec.embs(~V, ~emb, rest), [emb(y)]), ri_embs_snoc(~V, ~emb, rest, y))

def ri_drop_zero(~A: Data, xs: List<&2, A>) -> {List.drop(&2, A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

# drop xs r == at xs r <> drop xs (1 + r) for r < |xs|
def ri_drop_at(~A: Data, ~z: A, xs: List<&2, A>, +r: Nat, h: {Nat.is_lt(r, List.length(&2, A, xs)) == True{} : Bool})
  -> {List.drop(&2, A, xs, r) == Impl.at(~A, ~z, xs, r) <> List.drop(&2, A, xs, 1n+r) : List<&2, A>}:
  match xs:
    case Nil{}:
      Empty.absurd({List.drop(&2, A, Nil{}, r) == Impl.at(~A, ~z, Nil{}, r) <> List.drop(&2, A, Nil{}, 1n+r) : List<&2, A>}, ri_lt_zero(r, h))
    case +x <> t:
      match r:
        case 0n:
          %Equal.sym(List<&2, A>, List.drop(&2, A, t, 0n), t, ri_drop_zero(~A, t)) : {x <> t == x <> _ : List<&2, A>}
          {==}
        case 1n+q:
          ri_drop_at(~A, ~z, t, q, h)

def ri_drop_len(~A: Data, xs: List<&2, A>) -> {List.drop(&2, A, xs, List.length(&2, A, xs)) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      ri_drop_len(~A, t)

# ---------------------------------------------------------------- the invariant: reference values of the rows

# The reference layer input of row r after the layers pre: the last reference value of its absolute
# prefix (decode stream u, then the tokens along its path).
def rv(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T,
    +r: Nat) -> V:
  Spec.last(~V, ~z, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
    Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0))

def rows(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>,
    +toks: List<&2, U32>, +sh: T) -> List<&2, V>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r) <>
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k1, 1n+r, pre, n0, u, toks, sh)

def ri_at_rows(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>,
    +toks: List<&2, U32>, +sh: T, +j: Nat, h: {Nat.is_lt(j, k) == True{} : Bool})
  -> {Impl.at(~V, ~z, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k, r, pre, n0, u, toks, sh), j) ==
      rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, Nat.add(r, j)) : V}:
  match k:
    case 0n:
      Empty.absurd({Impl.at(~V, ~z, Nil{}, j) ==
        rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, Nat.add(r, j)) : V}, ri_lt_zero(j, h))
    case 1n+k1:
      match j:
        case 0n:
          %ri_zr(r) : {rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r) ==
            rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, _) : V}
          {==}
        case 1n+q:
          %ri_sr(r, q) : {Impl.at(~V, ~z, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k1, 1n+r, pre, n0, u, toks, sh), q) ==
            rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, _) : V}
          ri_at_rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k1, 1n+r, pre, n0, u, toks, sh, q, h)

def ri_at_heads(~V: Data, ~P: Data, ~T: Data, ~z: V, ~head: P -> V -> U32, ~hp: Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>, +j: Nat,
    h: {Nat.is_lt(j, k) == True{} : Bool})
  -> {Impl.at(~U32, ~0, Impl.heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k, r, sh, base, m, vals), j) ==
      head(hp(base, m, Nat.add(r, j), Impl.dep(~T, ~pth, sh, Nat.add(r, j))), Impl.at(~V, ~z, vals, Nat.add(r, j))) : U32}:
  match k:
    case 0n:
      Empty.absurd({Impl.at(~U32, ~0, Nil{}, j) ==
        head(hp(base, m, Nat.add(r, j), Impl.dep(~T, ~pth, sh, Nat.add(r, j))), Impl.at(~V, ~z, vals, Nat.add(r, j))) : U32}, ri_lt_zero(j, h))
    case 1n+k1:
      match j:
        case 0n:
          %ri_zr(r) : {head(hp(base, m, r, Impl.dep(~T, ~pth, sh, r)), Impl.at(~V, ~z, vals, r)) ==
            head(hp(base, m, _, Impl.dep(~T, ~pth, sh, _)), Impl.at(~V, ~z, vals, _)) : U32}
          {==}
        case 1n+q:
          %ri_sr(r, q) : {Impl.at(~U32, ~0, Impl.heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k1, 1n+r, sh, base, m, vals), q) ==
            head(hp(base, m, _, Impl.dep(~T, ~pth, sh, _)), Impl.at(~V, ~z, vals, _)) : U32}
          ri_at_heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k1, 1n+r, sh, base, m, vals, q, h)

# ---------------------------------------------------------------- the obligations as types

def OPlan(~P: Data, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P) -> Type:
  @l:Nat -> @base:Nat -> @m:Nat -> @r:Nat -> @d:Nat -> {Nat.is_le(d, r) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} -> {Nat.is_le(m, 8n) == True{} : Bool} ->
    {plan(l, base, m, r, d) == plan(l, Nat.add(base, d), 1n, 0n, 0n) : P}

def OHead(~P: Data, ~hp: Nat -> Nat -> Nat -> Nat -> P) -> Type:
  @base:Nat -> @m:Nat -> @r:Nat -> @d:Nat -> {Nat.is_le(d, r) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} -> {Nat.is_le(m, 8n) == True{} : Bool} ->
    {hp(base, m, r, d) == hp(Nat.add(base, d), 1n, 0n, 0n) : P}

def OGat(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool) -> Type:
  @l:Nat -> @sh:T -> @m:Nat -> @r:Nat -> {ok(sh, m) == True{} : Bool} ->
    {Nat.is_lt(r, m) == True{} : Bool} ->
    {gat(l, sh, r) == List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)) : List<&2, Nat>}

def WLast(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool) -> Type:
  @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Impl.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]), pth(sh, r))) == ok(sh, m) : Bool}

def WPre(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool) -> Type:
  @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {ok(sh, m) == True{} : Bool} -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {pth(sh, Impl.nthn(pth(sh, r), j)) == List.take(&2, Nat, pth(sh, r), 1n+j) : List<&2, Nat>}

def WRng(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool) -> Type:
  @sh:T -> @m:Nat -> @r:Nat -> @j:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_lt(Impl.nthn(pth(sh, r), j), m)) == ok(sh, m) : Bool}

def WDep(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool) -> Type:
  @sh:T -> @m:Nat -> @r:Nat -> {Nat.is_lt(r, m) == True{} : Bool} ->
    {Bool.and(ok(sh, m), Nat.is_le(Impl.dep(~T, ~pth, sh, r), r)) == ok(sh, m) : Bool}

# ---------------------------------------------------------------- the guarded obligations, unguarded

# From "ok implies b" (Bool.and(ok, b) == ok) and ok == True: b == True.
def ri_unguard(-o: Bool, -b: Bool, g: {Bool.and(o, b) == o : Bool}, hok: {o == True{} : Bool}) -> {b == True{} : Bool}:
  %hok : {Bool.and(_, b) == _ : Bool}
  g

# Soundness of the row-list equality check.
def ri_nle_sound(xs: List<&2, Nat>, ys: List<&2, Nat>, h: {Impl.nat_list_eq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> yr:
          Empty.absurd({Nil{} == y <> yr : List<&2, Nat>}, Ar.ar_false_true(h))
    case +x <> +xr:
      match ys:
        case Nil{}:
          Empty.absurd({x <> xr == Nil{} : List<&2, Nat>}, Ar.ar_false_true(h))
        case +y <> +yr:
          +h2 = h
          +ex = Ar.ar_eq_true(x, y, Ar.ar_and_l(Nat.is_eq(x, y), Impl.nat_list_eq(xr, yr), h2))
          +er = ri_nle_sound(xr, yr, Ar.ar_and_r(Nat.is_eq(x, y), Impl.nat_list_eq(xr, yr), h2))
          %ex : {x <> xr == _ <> yr : List<&2, Nat>}
          %er : {x <> xr == x <> _ : List<&2, Nat>}
          {==}

def ri_w_last(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~w_last: WLast(~T, ~pth, ~ok),
    +sh: T, +m: Nat, +r: Nat, +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool})
  -> {List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]) == pth(sh, r) : List<&2, Nat>}:
  ri_nle_sound(List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]), pth(sh, r),
    ri_unguard(ok(sh, m), Impl.nat_list_eq(List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), Impl.dep(~T, ~pth, sh, r)), [r]), pth(sh, r)),
      w_last(sh, m, r, hr), hok))

def ri_w_rng(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~w_rng: WRng(~T, ~pth, ~ok),
    +sh: T, +m: Nat, +r: Nat, +j: Nat, +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool},
    +hj: {Nat.is_lt(j, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool})
  -> {Nat.is_lt(Impl.nthn(pth(sh, r), j), m) == True{} : Bool}:
  ri_unguard(ok(sh, m), Nat.is_lt(Impl.nthn(pth(sh, r), j), m), w_rng(sh, m, r, j, hr, hj), hok)

def ri_w_dep(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~w_dep: WDep(~T, ~pth, ~ok),
    +sh: T, +m: Nat, +r: Nat, +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Nat.is_le(Impl.dep(~T, ~pth, sh, r), r) == True{} : Bool}:
  ri_unguard(ok(sh, m), Nat.is_le(Impl.dep(~T, ~pth, sh, r), r), w_dep(sh, m, r, hr), hok)

# ---------------------------------------------------------------- per-row facts from the path obligations

def ri_lt_s(+n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ri_lt_s(p)

# |path| == 1 + depth
def ri_len_path(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~w_last: WLast(~T, ~pth, ~ok),
    +sh: T, +m: Nat, +r: Nat, +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool})
  -> {List.length(&2, Nat, pth(sh, r)) == 1n+Impl.dep(~T, ~pth, sh, r) : Nat}:
  +d = Impl.dep(~T, ~pth, sh, r)
  +e1 = Equal.cong(List<&2, Nat>, Nat, y => List.length(&2, Nat, y), pth(sh, r),
    List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), d), [r]),
    Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), d), [r]), pth(sh, r), ri_w_last(~T, ~pth, ~ok, ~w_last, sh, m, r, hok, hr)))
  +e2 = ri_len_app(~Nat, List.take(&2, Nat, pth(sh, r), d), [r])
  +e3 = Equal.cong(Nat, Nat, y => Nat.add(y, 1n), List.length(&2, Nat, List.take(&2, Nat, pth(sh, r), d)), d,
    ri_len_take(~Nat, pth(sh, r), d, ri_sub1_le(List.length(&2, Nat, pth(sh, r)))))
  +e4 = Equal.trans(Nat, Nat.add(d, 1n), 1n+Nat.add(d, 0n), 1n+d, Ar.ar_add_succ_r(d, 0n),
    Equal.cong(Nat, Nat, y => 1n+y, Nat.add(d, 0n), d, Ar.ar_add_zero_r(d)))
  Equal.trans(Nat, List.length(&2, Nat, pth(sh, r)), List.length(&2, Nat, List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), d), [r])), 1n+d, e1,
    Equal.trans(Nat, List.length(&2, Nat, List.append(&2, Nat, List.take(&2, Nat, pth(sh, r), d), [r])),
      Nat.add(List.length(&2, Nat, List.take(&2, Nat, pth(sh, r), d)), 1n), 1n+d, e2,
      Equal.trans(Nat, Nat.add(List.length(&2, Nat, List.take(&2, Nat, pth(sh, r), d)), 1n), Nat.add(d, 1n), 1n+d, e3, e4)))

# The reference values of row r's absolute prefix: |Y| == |u| + |path|
def ri_len_Y(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +r: Nat)
  -> {List.length(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0)) ==
      Nat.add(List.length(&2, U32, u), List.length(&2, Nat, pth(sh, r))) : Nat}:
  +w = List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))
  Equal.trans(Nat, List.length(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0)),
    List.length(&2, V, Spec.embs(~V, ~emb, w)), Nat.add(List.length(&2, U32, u), List.length(&2, Nat, pth(sh, r))),
    ri_len_up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0),
    Equal.trans(Nat, List.length(&2, V, Spec.embs(~V, ~emb, w)), List.length(&2, U32, w),
      Nat.add(List.length(&2, U32, u), List.length(&2, Nat, pth(sh, r))), ri_len_embs(~V, ~emb, w),
      Equal.trans(Nat, List.length(&2, U32, w), Nat.add(List.length(&2, U32, u), List.length(&2, U32, Impl.stream(toks, pth(sh, r)))),
        Nat.add(List.length(&2, U32, u), List.length(&2, Nat, pth(sh, r))), ri_len_app(~U32, u, Impl.stream(toks, pth(sh, r))),
        Equal.cong(Nat, Nat, y => Nat.add(List.length(&2, U32, u), y), List.length(&2, U32, Impl.stream(toks, pth(sh, r))),
          List.length(&2, Nat, pth(sh, r)), ri_len_stream(toks, pth(sh, r))))))

# The first |u| + k reference values of row r's prefix are those of the prefix u ++ stream(take path k).
def ri_Y_take(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +r: Nat, +k: Nat)
  -> {Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pth(sh, r), k)))), n0) ==
      List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0), Nat.add(List.length(&2, U32, u), k)) : List<&2, V>}:
  +s = Impl.stream(toks, pth(sh, r))
  +w = List.append(&2, U32, u, s)
  +K = Nat.add(List.length(&2, U32, u), k)
  +e1 = Equal.cong(List<&2, U32>, List<&2, V>, y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, y)), n0),
    Impl.stream(toks, List.take(&2, Nat, pth(sh, r), k)), List.take(&2, U32, s, k), ri_stream_take(toks, pth(sh, r), k))
  +e2 = Equal.cong(List<&2, U32>, List<&2, V>, y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, y), n0),
    List.append(&2, U32, u, List.take(&2, U32, s, k)), List.take(&2, U32, w, K),
    Equal.sym(List<&2, U32>, List.take(&2, U32, w, K), List.append(&2, U32, u, List.take(&2, U32, s, k)), ri_take_app(~U32, u, s, k)))
  +e3 = Equal.cong(List<&2, V>, List<&2, V>, y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, y, n0),
    Spec.embs(~V, ~emb, List.take(&2, U32, w, K)), List.take(&2, V, Spec.embs(~V, ~emb, w), K),
    Equal.sym(List<&2, V>, List.take(&2, V, Spec.embs(~V, ~emb, w), K), Spec.embs(~V, ~emb, List.take(&2, U32, w, K)), ri_embs_take(~V, ~emb, w, K)))
  +e4 = Equal.sym(List<&2, V>,
    List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0), K),
    Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, List.take(&2, V, Spec.embs(~V, ~emb, w), K), n0),
    ri_up_take(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), K, n0))
  Equal.trans(List<&2, V>,
    Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pth(sh, r), k)))), n0),
    Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, List.take(&2, U32, s, k))), n0),
    List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0), K), e1,
    Equal.trans(List<&2, V>,
      Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, List.take(&2, U32, s, k))), n0),
      Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.take(&2, U32, w, K)), n0),
      List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0), K), e2,
      Equal.trans(List<&2, V>,
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.take(&2, U32, w, K)), n0),
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, List.take(&2, V, Spec.embs(~V, ~emb, w), K), n0),
        List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, w), n0), K), e3, e4)))

# ---------------------------------------------------------------- inside one layer

# adv / ent congruence
def ri_cong_adv(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, -l: Nat,
    -c1: C, -c2: C, -p1: P, -p2: P, -v1: V, -v2: V, h1: {c1 == c2 : C}, h2: {p1 == p2 : P}, h3: {v1 == v2 : V})
  -> {adv(l, c1, ent(l, p1, v1)) == adv(l, c2, ent(l, p2, v2)) : C}:
  %h1 : {adv(l, c1, ent(l, p1, v1)) == adv(l, _, ent(l, p2, v2)) : C}
  %h2 : {adv(l, c1, ent(l, p1, v1)) == adv(l, c1, ent(l, _, v2)) : C}
  %h3 : {adv(l, c1, ent(l, p1, v1)) == adv(l, c1, ent(l, p1, _)) : C}
  {==}

# Claim A: over the first k <= dep(r) entries of row r's path, the served context (the committed
# state of layer l advanced by those rows' entries, each computed by its own launch coordinates)
# is the reference state after the first |u| + k decode positions of r's absolute prefix.
def ri_anc(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~o_plan: OPlan(~P, ~plan), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    k: Nat, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat, +r: Nat, +l: Nat, +c: C,
    +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool},
    +hk: {Nat.is_le(k, Impl.dep(~T, ~pth, sh, r)) == True{} : Bool})
  -> {Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pth(sh, r), k), l,
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), l, c, n0),
        sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)) ==
      Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0), Nat.add(List.length(&2, U32, u), k)), l, c, n0) : C}:
  match k:
    case 0n:
      +Y = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0)
      +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0)
      +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
      # take Y (|u| + 0) == Xu: causality, then u ++ stream(take path 0) == u
      +t0 = ri_Y_take(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r, 0n)
      +t1 = Equal.cong(List<&2, Nat>, List<&2, V>,
        y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, y))), n0),
        List.take(&2, Nat, pth(sh, r), 0n), Nil{}, ri_take_nil(~Nat, pth(sh, r)))
      +t2 = Equal.cong(List<&2, U32>, List<&2, V>,
        y => Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, y), n0),
        List.append(&2, U32, u, Nil{}), u, ri_app_nil(~U32, u))
      +tx = Equal.trans(List<&2, V>, List.take(&2, V, Y, Nat.add(List.length(&2, U32, u), 0n)),
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pth(sh, r), 0n)))), n0),
        Xu,
        Equal.sym(List<&2, V>,
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pth(sh, r), 0n)))), n0),
          List.take(&2, V, Y, Nat.add(List.length(&2, U32, u), 0n)), t0),
        Equal.trans(List<&2, V>,
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pth(sh, r), 0n)))), n0),
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Nil{})), n0),
          Xu, t1, t2))
      %Equal.sym(List<&2, Nat>, List.take(&2, Nat, pth(sh, r), 0n), Nil{}, ri_take_nil(~Nat, pth(sh, r))) :
        {Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, _, l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0),
          sh, Nat.add(n0, List.length(&2, U32, u)), m, V0) ==
         Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, Nat.add(List.length(&2, U32, u), 0n)), l, c, n0) : C}
      Equal.cong(List<&2, V>, C, y => Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, y, l, c, n0), Xu,
        List.take(&2, V, Y, Nat.add(List.length(&2, U32, u), 0n)),
        Equal.sym(List<&2, V>, List.take(&2, V, Y, Nat.add(List.length(&2, U32, u), 0n)), Xu, tx))
    case 1n+j:
      +j = j
      +d = Impl.dep(~T, ~pth, sh, r)
      +pi = pth(sh, r)
      +U = List.length(&2, U32, u)
      +base = Nat.add(n0, U)
      +Y = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi))), n0)
      +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0)
      +cl = Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0)
      +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
      +K0 = Nat.add(U, j)
      # j < dep(r) < |path|
      +jlt = Equal.trans(Bool, Nat.is_lt(j, d), Nat.is_le(1n+j, d), True{}, Ar.ar_lt_succ_le(j, d), hk)
      +lenpi = ri_len_path(~T, ~pth, ~ok, ~w_last, sh, m, r, hok, hr)
      +jltpi = Equal.trans(Bool, Nat.is_lt(j, List.length(&2, Nat, pi)), Nat.is_lt(j, 1n+d), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(j, y), List.length(&2, Nat, pi), 1n+d, lenpi),
        Ar.ar_lt_trans(j, d, 1n+d, jlt, ri_lt_s(d)))
      +a = Impl.nthn(pi, j)
      # the j-th ancestor's path is the first j + 1 entries of r's: depth j, a row of the round, j <= a
      +prea = w_pre(sh, m, r, j, hok, hr, jlt)
      +lt1 = Equal.trans(Bool, Nat.is_le(1n+j, List.length(&2, Nat, pi)), Nat.is_lt(j, List.length(&2, Nat, pi)), True{},
        Equal.sym(Bool, Nat.is_lt(j, List.length(&2, Nat, pi)), Nat.is_le(1n+j, List.length(&2, Nat, pi)), Ar.ar_lt_succ_le(j, List.length(&2, Nat, pi))), jltpi)
      +depa = Equal.trans(Nat, Impl.dep(~T, ~pth, sh, a), Nat.sub(List.length(&2, Nat, List.take(&2, Nat, pi, 1n+j)), 1n), j,
        Equal.cong(List<&2, Nat>, Nat, y => Nat.sub(List.length(&2, Nat, y), 1n), pth(sh, a), List.take(&2, Nat, pi, 1n+j), prea),
        Equal.trans(Nat, Nat.sub(List.length(&2, Nat, List.take(&2, Nat, pi, 1n+j)), 1n), Nat.sub(1n+j, 1n), j,
          Equal.cong(Nat, Nat, y => Nat.sub(y, 1n), List.length(&2, Nat, List.take(&2, Nat, pi, 1n+j)), 1n+j, ri_len_take(~Nat, pi, 1n+j, lt1)),
          Ar.ar_sub_zero_r(j)))
      +alt = ri_w_rng(~T, ~pth, ~ok, ~w_rng, sh, m, r, j, hok, hr, jlt)
      +jlea = Equal.trans(Bool, Nat.is_le(j, a), Nat.is_le(Impl.dep(~T, ~pth, sh, a), a), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, a), j, Impl.dep(~T, ~pth, sh, a), Equal.sym(Nat, Impl.dep(~T, ~pth, sh, a), j, depa)),
        ri_w_dep(~T, ~pth, ~ok, ~w_dep, sh, m, a, hok, alt))
      # the served entry of a: plan at the absolute position, value = the reference value there
      +eplan = Equal.trans(P, plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), plan(l, base, m, a, j), plan(l, Nat.add(n0, K0), 1n, 0n, 0n),
        Equal.cong(Nat, P, y => plan(l, base, m, a, y), Impl.dep(~T, ~pth, sh, a), j, depa),
        Equal.trans(P, plan(l, base, m, a, j), plan(l, Nat.add(base, j), 1n, 0n, 0n), plan(l, Nat.add(n0, K0), 1n, 0n, 0n),
          o_plan(l, base, m, a, j, jlea, alt, h8),
          Equal.cong(Nat, P, y => plan(l, y, 1n, 0n, 0n), Nat.add(base, j), Nat.add(n0, K0), Ar.ar_add_assoc(n0, U, j))))
      +K1 = Nat.add(U, 1n+j)
      +k1s = Ar.ar_add_succ_r(U, j)
      +eval = Equal.trans(V, Impl.at(~V, ~z, V0, a), rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, a),
        Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)),
        ri_at_rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh, a, alt),
        Equal.trans(V, rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, a),
          Spec.last(~V, ~z, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
            Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pi, 1n+j)))), n0)),
          Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)),
          Equal.cong(List<&2, Nat>, V, y => Spec.last(~V, ~z, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
            Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, y))), n0)), pth(sh, a), List.take(&2, Nat, pi, 1n+j), prea),
          Equal.trans(V, Spec.last(~V, ~z, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
              Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pi, 1n+j)))), n0)),
            Spec.last(~V, ~z, List.take(&2, V, Y, K1)), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)),
            Equal.cong(List<&2, V>, V, y => Spec.last(~V, ~z, y),
              Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, List.take(&2, Nat, pi, 1n+j)))), n0),
              List.take(&2, V, Y, K1),
              ri_Y_take(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r, 1n+j)),
            Equal.cong(Nat, V, y => Spec.last(~V, ~z, List.take(&2, V, Y, y)), K1, 1n+K0, k1s))))
      # served side: ctx over take(path, 1 + j) = one more entry after the IH's
      +ih = ri_anc(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~o_plan, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        j, pre, n0, u, toks, sh, m, r, l, c, hok, hr, h8, Ar.ar_lt_le(j, d, jlt))
      +L1 = Equal.trans(C,
        Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, 1n+j), l, cl, sh, base, m, V0),
        Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.append(&2, Nat, List.take(&2, Nat, pi, j), [a]), l, cl, sh, base, m, V0),
        adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, j), l, cl, sh, base, m, V0),
          ent(l, plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), Impl.at(~V, ~z, V0, a))),
        Equal.cong(List<&2, Nat>, C, y => Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, y, l, cl, sh, base, m, V0),
          List.take(&2, Nat, pi, 1n+j), List.append(&2, Nat, List.take(&2, Nat, pi, j), [a]), ri_take_snoc_n(pi, j, jltpi)),
        ri_ctx_snoc(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, j), a, l, cl, sh, base, m, V0))
      +L2 = ri_cong_adv(~V, ~E, ~C, ~P, ~ent, ~adv, l,
        Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, j), l, cl, sh, base, m, V0),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
        plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), plan(l, Nat.add(n0, K0), 1n, 0n, 0n),
        Impl.at(~V, ~z, V0, a), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)), ih, eplan, eval)
      # reference side: one more position
      +hY = Equal.trans(Bool, Nat.is_lt(K0, List.length(&2, V, Y)), Nat.is_lt(K0, Nat.add(U, List.length(&2, Nat, pi))), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(K0, y), List.length(&2, V, Y), Nat.add(U, List.length(&2, Nat, pi)),
          ri_len_Y(~V, ~E, ~C, ~P, ~T, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r)),
        Equal.trans(Bool, Nat.is_lt(K0, Nat.add(U, List.length(&2, Nat, pi))), Nat.is_lt(j, List.length(&2, Nat, pi)), True{},
          Ar.ar_lt_add_cancel(U, j, List.length(&2, Nat, pi)), jltpi))
      +R = Equal.trans(C, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K1), l, c, n0),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, 1n+K0), l, c, n0),
        adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
          ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))),
        Equal.cong(Nat, C, y => Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, y), l, c, n0), K1, 1n+K0, k1s),
        ri_ls_step(~V, ~E, ~C, ~P, ~z, ~ent, ~adv, ~plan, Y, K0, l, c, n0, hY))
      Equal.trans(C, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, 1n+j), l, cl, sh, base, m, V0),
        adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, j), l, cl, sh, base, m, V0),
          ent(l, plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), Impl.at(~V, ~z, V0, a))),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K1), l, c, n0), L1,
        Equal.trans(C, adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, j), l, cl, sh, base, m, V0),
            ent(l, plan(l, base, m, a, Impl.dep(~T, ~pth, sh, a)), Impl.at(~V, ~z, V0, a))),
          adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
            ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))),
          Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K1), l, c, n0), L2,
          Equal.sym(C, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K1), l, c, n0),
            adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
              ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))), R)))

def ri_cong_F(~V: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, -l: Nat, -p1: P, -p2: P, -c1: C, -c2: C,
    -v1: V, -v2: V, h1: {p1 == p2 : P}, h2: {c1 == c2 : C}, h3: {v1 == v2 : V})
  -> {F(l, p1, c1, v1) == F(l, p2, c2, v2) : V}:
  %h1 : {F(l, p1, c1, v1) == F(l, _, c2, v2) : V}
  %h2 : {F(l, p1, c1, v1) == F(l, p1, _, v2) : V}
  %h3 : {F(l, p1, c1, v1) == F(l, p1, c1, _) : V}
  {==}

def ri_cong_cons(~A: Data, -a: A, -b: A, -xs: List<&2, A>, -ys: List<&2, A>, h1: {a == b : A}, h2: {xs == ys : List<&2, A>})
  -> {a <> xs == b <> ys : List<&2, A>}:
  %h1 : {a <> xs == _ <> ys : List<&2, A>}
  %h2 : {a <> xs == a <> _ : List<&2, A>}
  {==}

# One row of one layer launch: the served output of row r is the reference's last output of r's
# absolute prefix at layer l (O_gat, Claim A, O_plan, and the last output of a reference layer).
def ri_row(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool,
    ~o_plan: OPlan(~P, ~plan), ~o_gat: OGat(~T, ~pth, ~gat, ~ok), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat, +r: Nat, +l: Nat, +c: C,
    +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {F(l, plan(l, Nat.add(n0, List.length(&2, U32, u)), m, r, Impl.dep(~T, ~pth, sh, r)),
        Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r), l,
          Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), l, c, n0),
          sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)),
        Impl.at(~V, ~z, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh), r)) ==
      Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0), l, c, n0)) : V}:
  +d = Impl.dep(~T, ~pth, sh, r)
  +pi = pth(sh, r)
  +U = List.length(&2, U32, u)
  +base = Nat.add(n0, U)
  +Y = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi))), n0)
  +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0)
  +cl = Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0)
  +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
  +K = Nat.add(U, d)
  +g = o_gat(l, sh, m, r, hok, hr)
  +A = ri_anc(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~o_plan, ~w_last, ~w_pre, ~w_rng, ~w_dep,
    d, pre, n0, u, toks, sh, m, r, l, c, hok, hr, h8, Ar.ar_le_refl(d))
  +ctxe = Equal.trans(C, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r), l, cl, sh, base, m, V0),
    Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), l, cl, sh, base, m, V0),
    Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K), l, c, n0),
    Equal.cong(List<&2, Nat>, C, y => Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, y, l, cl, sh, base, m, V0),
      gat(l, sh, r), List.take(&2, Nat, pi, d), g), A)
  +pl = Equal.trans(P, plan(l, base, m, r, d), plan(l, Nat.add(base, d), 1n, 0n, 0n), plan(l, Nat.add(n0, K), 1n, 0n, 0n),
    o_plan(l, base, m, r, d, ri_w_dep(~T, ~pth, ~ok, ~w_dep, sh, m, r, hok, hr), hr, h8),
    Equal.cong(Nat, P, y => plan(l, y, 1n, 0n, 0n), Nat.add(base, d), Nat.add(n0, K), Ar.ar_add_assoc(n0, U, d)))
  +ate = ri_at_rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh, r, hr)
  +lenY = Equal.trans(Nat, List.length(&2, V, Y), Nat.add(U, List.length(&2, Nat, pi)), 1n+K,
    ri_len_Y(~V, ~E, ~C, ~P, ~T, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r),
    Equal.trans(Nat, Nat.add(U, List.length(&2, Nat, pi)), Nat.add(U, 1n+d), 1n+K,
      Equal.cong(Nat, Nat, y => Nat.add(U, y), List.length(&2, Nat, pi), 1n+d, ri_len_path(~T, ~pth, ~ok, ~w_last, sh, m, r, hok, hr)),
      Ar.ar_add_succ_r(U, d)))
  +lol = ri_lo_last(~V, ~E, ~C, ~P, ~z, ~F, ~ent, ~adv, ~plan, Y, K, l, c, n0, lenY)
  Equal.trans(V,
    F(l, plan(l, base, m, r, d), Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r), l, cl, sh, base, m, V0), Impl.at(~V, ~z, V0, r)),
    F(l, plan(l, Nat.add(n0, K), 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K), l, c, n0), Spec.last(~V, ~z, Y)),
    Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Y, l, c, n0)),
    ri_cong_F(~V, ~C, ~P, ~F, l, plan(l, base, m, r, d), plan(l, Nat.add(n0, K), 1n, 0n, 0n),
      Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r), l, cl, sh, base, m, V0),
      Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K), l, c, n0),
      Impl.at(~V, ~z, V0, r), Spec.last(~V, ~z, Y), pl, ctxe, ate),
    Equal.sym(V, Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Y, l, c, n0)),
      F(l, plan(l, Nat.add(n0, K), 1n, 0n, 0n), Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K), l, c, n0), Spec.last(~V, ~z, Y)), lol))

# One layer launch (rows r0 .. r0 + k - 1): the served outputs are the reference values after one
# more layer (l = |pre|).
def ri_layer(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool,
    ~o_plan: OPlan(~P, ~plan), ~o_gat: OGat(~T, ~pth, ~gat, ~ok), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    k: Nat, +r0: Nat, +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat, +l: Nat, +c: C,
    +hok: {ok(sh, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool},
    +hb: {Nat.is_le(Nat.add(r0, k), m) == True{} : Bool}, +hl: {l == List.length(&2, C, pre) : Nat})
  -> {Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, k, r0, l,
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), l, c, n0),
        sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)) ==
      rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k, r0, List.append(&2, C, pre, [c]), n0, u, toks, sh) : List<&2, V>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      +k1 = k1
      +cl = Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), l, c, n0)
      +base = Nat.add(n0, List.length(&2, U32, u))
      +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
      +w = Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r0))))
      +hr = Ar.ar_lt_le_trans(r0, Nat.add(r0, 1n+k1), m, ri_lt_add(r0, k1), hb)
      +row = ri_row(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        pre, n0, u, toks, sh, m, r0, l, c, hok, hr, h8)
      # up (pre ++ [c]) == lo (up pre) at layer |pre| == l
      +us = Equal.trans(List<&2, V>,
        Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), l, c, n0),
        Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), List.length(&2, C, pre), c, n0),
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, w, n0),
        Equal.cong(Nat, List<&2, V>, y => Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), y, c, n0),
          l, List.length(&2, C, pre), hl),
        Equal.sym(List<&2, V>, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, w, n0),
          Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), List.length(&2, C, pre), c, n0),
          ri_up_snoc(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, c, 0n, w, n0)))
      +hd = Equal.trans(V,
        F(l, plan(l, base, m, r0, Impl.dep(~T, ~pth, sh, r0)), Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r0), l, cl, sh, base, m, V0),
          Impl.at(~V, ~z, V0, r0)),
        Spec.last(~V, ~z, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), l, c, n0)),
        rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, List.append(&2, C, pre, [c]), n0, u, toks, sh, r0),
        row, Equal.cong(List<&2, V>, V, y => Spec.last(~V, ~z, y),
          Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, w, n0), l, c, n0),
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, w, n0), us))
      +hb2 = Equal.trans(Bool, Nat.is_le(Nat.add(1n+r0, k1), m), Nat.is_le(Nat.add(r0, 1n+k1), m), True{},
        Equal.cong(Nat, Bool, y => Nat.is_le(y, m), 1n+Nat.add(r0, k1), Nat.add(r0, 1n+k1), ri_sr(r0, k1)), hb)
      +tl = ri_layer(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        k1, 1n+r0, pre, n0, u, toks, sh, m, l, c, hok, h8, hb2, hl)
      ri_cong_cons(~V,
        F(l, plan(l, base, m, r0, Impl.dep(~T, ~pth, sh, r0)), Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r0), l, cl, sh, base, m, V0),
          Impl.at(~V, ~z, V0, r0)),
        rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, List.append(&2, C, pre, [c]), n0, u, toks, sh, r0),
        Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, k1, 1n+r0, l, cl, sh, base, m, V0),
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k1, 1n+r0, List.append(&2, C, pre, [c]), n0, u, toks, sh),
        hd, tl)

# ---------------------------------------------------------------- across layers

# The layers of suf (after those of pre, l = |pre|): the served forward from the reference values
# after pre, with the committed states the 1-row rounds over u leave, gives the reference values
# after pre ++ suf.
def ri_fwd(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool,
    ~o_plan: OPlan(~P, ~plan), ~o_gat: OGat(~T, ~pth, ~gat, ~ok), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    suf: List<&2, C>, +pre: List<&2, C>, +l: Nat, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat,
    +hok: {ok(sh, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool}, +hl: {l == List.length(&2, C, pre) : Nat})
  -> {Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
        Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, suf, l,
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), n0),
        l, sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)) ==
      rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, List.append(&2, C, pre, suf), n0, u, toks, sh) : List<&2, V>}:
  match suf:
    case Nil{}:
      Equal.cong(List<&2, C>, List<&2, V>, y => rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, y, n0, u, toks, sh),
        pre, List.append(&2, C, pre, Nil{}), Equal.sym(List<&2, C>, List.append(&2, C, pre, Nil{}), pre, ri_app_nil(~C, pre)))
    case +c <> +rest:
      +base = Nat.add(n0, List.length(&2, U32, u))
      +xu = Spec.embs(~V, ~emb, u)
      +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xu, n0)
      +pc = List.append(&2, C, pre, [c])
      +Xu2 = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xu, n0)
      +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
      +V1 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pc, n0, u, toks, sh)
      +lay = ri_layer(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        m, 0n, pre, n0, u, toks, sh, m, l, c, hok, h8, Ar.ar_le_refl(m), hl)
      +us = Equal.trans(List<&2, V>, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0),
        Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, List.length(&2, C, pre), c, n0), Xu2,
        Equal.cong(Nat, List<&2, V>, y => Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, y, c, n0), l, List.length(&2, C, pre), hl),
        Equal.sym(List<&2, V>, Xu2, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, List.length(&2, C, pre), c, n0),
          ri_up_snoc(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, c, 0n, xu, n0)))
      +hl2 = Equal.trans(Nat, 1n+l, 1n+List.length(&2, C, pre), List.length(&2, C, pc),
        Equal.cong(Nat, Nat, y => 1n+y, l, List.length(&2, C, pre), hl),
        Equal.sym(Nat, List.length(&2, C, pc), 1n+List.length(&2, C, pre),
          Equal.trans(Nat, List.length(&2, C, pc), Nat.add(List.length(&2, C, pre), 1n), 1n+List.length(&2, C, pre),
            ri_len_app(~C, pre, [c]),
            Equal.trans(Nat, Nat.add(List.length(&2, C, pre), 1n), 1n+Nat.add(List.length(&2, C, pre), 0n), 1n+List.length(&2, C, pre),
              Ar.ar_add_succ_r(List.length(&2, C, pre), 0n),
              Equal.cong(Nat, Nat, y => 1n+y, Nat.add(List.length(&2, C, pre), 0n), List.length(&2, C, pre), Ar.ar_add_zero_r(List.length(&2, C, pre)))))))
      +ih = ri_fwd(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        rest, pc, 1n+l, n0, u, toks, sh, m, hok, h8, hl2)
      # rewrite the layer's output and the next committed states, then the IH, then reassociate
      %Equal.sym(List<&2, V>, Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l,
          Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0), sh, base, m, V0), V1, lay) : {Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
          1n+l, sh, base, m, _) ==
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, List.append(&2, C, pre, c <> rest), n0, u, toks, sh) : List<&2, V>}
      %Equal.sym(List<&2, V>, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), Xu2, us) :
        {Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, _, n0), 1n+l, sh, base, m, V1) ==
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, List.append(&2, C, pre, c <> rest), n0, u, toks, sh) : List<&2, V>}
      Equal.trans(List<&2, V>,
        Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Xu2, n0), 1n+l, sh, base, m, V1),
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, List.append(&2, C, pc, rest), n0, u, toks, sh),
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, List.append(&2, C, pre, c <> rest), n0, u, toks, sh),
        ih,
        Equal.cong(List<&2, C>, List<&2, V>, y => rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, y, n0, u, toks, sh),
          List.append(&2, C, pc, rest), List.append(&2, C, pre, c <> rest), ri_app_assoc(~C, pre, [c], rest)))

# Layer 0: the served embeddings are the reference layer-0 values (the last token of every row's
# prefix is the row's own token, W_last).
def ri_rows0(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~w_last: WLast(~T, ~pth, ~ok),
    k: Nat, +r0: Nat, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T,
    +hok: {ok(sh, List.length(&2, U32, toks)) == True{} : Bool}, +hb: {Nat.add(r0, k) == List.length(&2, U32, toks) : Nat})
  -> {Impl.embs(~V, ~emb, List.drop(&2, U32, toks, r0)) ==
      rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k, r0, Nil{}, n0, u, toks, sh) : List<&2, V>}:
  match k:
    case 0n:
      +e = Equal.trans(Nat, r0, Nat.add(r0, 0n), List.length(&2, U32, toks), ri_zr(r0), hb)
      %Equal.sym(Nat, r0, List.length(&2, U32, toks), e) : {Impl.embs(~V, ~emb, List.drop(&2, U32, toks, _)) == Nil{} : List<&2, V>}
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, toks, List.length(&2, U32, toks)), Nil{}, ri_drop_len(~U32, toks)) :
        {Impl.embs(~V, ~emb, _) == Nil{} : List<&2, V>}
      {==}
    case 1n+k1:
      +k1 = k1
      +m = List.length(&2, U32, toks)
      +hr = Equal.trans(Bool, Nat.is_lt(r0, m), Nat.is_lt(r0, Nat.add(r0, 1n+k1)), True{},
        Equal.cong(Nat, Bool, y => Nat.is_lt(r0, y), m, Nat.add(r0, 1n+k1), Equal.sym(Nat, Nat.add(r0, 1n+k1), m, hb)), ri_lt_add(r0, k1))
      +pi = pth(sh, r0)
      +d = Impl.dep(~T, ~pth, sh, r0)
      +A = Impl.stream(toks, List.take(&2, Nat, pi, d))
      +t = Impl.at(~U32, ~0, toks, r0)
      # u ++ stream(path r0) == (u ++ A) ++ [t]
      +ws = Equal.trans(List<&2, U32>, List.append(&2, U32, u, Impl.stream(toks, pi)),
        List.append(&2, U32, u, List.append(&2, U32, A, [t])), List.append(&2, U32, List.append(&2, U32, u, A), [t]),
        Equal.cong(List<&2, U32>, List<&2, U32>, y => List.append(&2, U32, u, y), Impl.stream(toks, pi), List.append(&2, U32, A, [t]),
          Equal.trans(List<&2, U32>, Impl.stream(toks, pi), Impl.stream(toks, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r0])),
            List.append(&2, U32, A, [t]),
            Equal.cong(List<&2, Nat>, List<&2, U32>, y => Impl.stream(toks, y), pi, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r0]),
              Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r0]), pi, ri_w_last(~T, ~pth, ~ok, ~w_last, sh, m, r0, hok, hr))),
            ri_stream_app(toks, List.take(&2, Nat, pi, d), [r0]))),
        Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, u, A), [t]), List.append(&2, U32, u, List.append(&2, U32, A, [t])),
          ri_app_assoc(~U32, u, A, [t])))
      +hd = Equal.sym(V, Spec.last(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi)))), emb(t),
        Equal.trans(V, Spec.last(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi)))),
          Spec.last(~V, ~z, List.append(&2, V, Spec.embs(~V, ~emb, List.append(&2, U32, u, A)), [emb(t)])), emb(t),
          Equal.trans(V, Spec.last(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi)))),
            Spec.last(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, List.append(&2, U32, u, A), [t]))),
            Spec.last(~V, ~z, List.append(&2, V, Spec.embs(~V, ~emb, List.append(&2, U32, u, A)), [emb(t)])),
            Equal.cong(List<&2, U32>, V, y => Spec.last(~V, ~z, Spec.embs(~V, ~emb, y)), List.append(&2, U32, u, Impl.stream(toks, pi)),
              List.append(&2, U32, List.append(&2, U32, u, A), [t]), ws),
            Equal.cong(List<&2, V>, V, y => Spec.last(~V, ~z, y), Spec.embs(~V, ~emb, List.append(&2, U32, List.append(&2, U32, u, A), [t])),
              List.append(&2, V, Spec.embs(~V, ~emb, List.append(&2, U32, u, A)), [emb(t)]), ri_embs_snoc(~V, ~emb, List.append(&2, U32, u, A), t))),
          ri_last_snoc(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, u, A)), emb(t))))
      +hb2 = Equal.trans(Nat, Nat.add(1n+r0, k1), Nat.add(r0, 1n+k1), m, ri_sr(r0, k1), hb)
      +tl = ri_rows0(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~w_last, k1, 1n+r0, n0, u, toks, sh, hok, hb2)
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, toks, r0), t <> List.drop(&2, U32, toks, 1n+r0), ri_drop_at(~U32, ~0, toks, r0, hr)) : {Impl.embs(~V, ~emb, _) ==
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, 1n+k1, r0, Nil{}, n0, u, toks, sh) : List<&2, V>}
      ri_cong_cons(~V, emb(t), Spec.last(~V, ~z, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi)))),
        Impl.embs(~V, ~emb, List.drop(&2, U32, toks, 1n+r0)),
        rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, k1, 1n+r0, Nil{}, n0, u, toks, sh), hd, tl)

# ---------------------------------------------------------------- the commit of a round (law commit_path)

# Claim A over the WHOLE path (the row itself included): the committed state of layer l advanced by
# the entries of every row on r's path, each as the round computed it, is the reference state after
# all |u| + |path| decode positions of r's absolute prefix.
def ri_anc_full(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool, ~o_plan: OPlan(~P, ~plan), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    +pre: List<&2, C>, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat, +r: Nat, +l: Nat, +c: C,
    +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, pth(sh, r), l,
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), l, c, n0),
        sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)) ==
      Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n,
        Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0), l, c, n0) : C}:
  +d = Impl.dep(~T, ~pth, sh, r)
  +pi = pth(sh, r)
  +U = List.length(&2, U32, u)
  +base = Nat.add(n0, U)
  +Y = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pi))), n0)
  +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0)
  +cl = Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0)
  +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
  +K0 = Nat.add(U, d)
  # every proper ancestor (Claim A at k = depth)
  +ih = ri_anc(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~o_plan, ~w_last, ~w_pre, ~w_rng, ~w_dep,
    d, pre, n0, u, toks, sh, m, r, l, c, hok, hr, h8, Ar.ar_le_refl(d))
  # the path is the ancestors followed by r
  +wl = ri_w_last(~T, ~pth, ~ok, ~w_last, sh, m, r, hok, hr)
  +L1 = Equal.trans(C, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, pi, l, cl, sh, base, m, V0),
    Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r]), l, cl, sh, base, m, V0),
    adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), l, cl, sh, base, m, V0),
      ent(l, plan(l, base, m, r, Impl.dep(~T, ~pth, sh, r)), Impl.at(~V, ~z, V0, r))),
    Equal.cong(List<&2, Nat>, C, y => Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, y, l, cl, sh, base, m, V0),
      pi, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r]), Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, pi, d), [r]), pi, wl)),
    ri_ctx_snoc(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), r, l, cl, sh, base, m, V0))
  # r's entry: plan at its absolute position, value = the reference value there
  +eplan = Equal.trans(P, plan(l, base, m, r, d), plan(l, Nat.add(base, d), 1n, 0n, 0n), plan(l, Nat.add(n0, K0), 1n, 0n, 0n),
    o_plan(l, base, m, r, d, ri_w_dep(~T, ~pth, ~ok, ~w_dep, sh, m, r, hok, hr), hr, h8),
    Equal.cong(Nat, P, y => plan(l, y, 1n, 0n, 0n), Nat.add(base, d), Nat.add(n0, K0), Ar.ar_add_assoc(n0, U, d)))
  +lenY = Equal.trans(Nat, List.length(&2, V, Y), Nat.add(U, List.length(&2, Nat, pi)), 1n+K0,
    ri_len_Y(~V, ~E, ~C, ~P, ~T, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pre, n0, u, toks, sh, r),
    Equal.trans(Nat, Nat.add(U, List.length(&2, Nat, pi)), Nat.add(U, 1n+d), 1n+K0,
      Equal.cong(Nat, Nat, y => Nat.add(U, y), List.length(&2, Nat, pi), 1n+d, ri_len_path(~T, ~pth, ~ok, ~w_last, sh, m, r, hok, hr)),
      Ar.ar_add_succ_r(U, d)))
  +tY = Equal.trans(List<&2, V>, List.take(&2, V, Y, 1n+K0), List.take(&2, V, Y, List.length(&2, V, Y)), Y,
    Equal.cong(Nat, List<&2, V>, y => List.take(&2, V, Y, y), 1n+K0, List.length(&2, V, Y), Equal.sym(Nat, List.length(&2, V, Y), 1n+K0, lenY)),
    ri_take_len(~V, Y))
  +hY = Equal.trans(Bool, Nat.is_lt(K0, List.length(&2, V, Y)), Nat.is_lt(K0, 1n+K0), True{},
    Equal.cong(Nat, Bool, y => Nat.is_lt(K0, y), List.length(&2, V, Y), 1n+K0, lenY), ri_lt_s(K0))
  +eval = Equal.trans(V, Impl.at(~V, ~z, V0, r), Spec.last(~V, ~z, Y), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)),
    ri_at_rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh, r, hr),
    Equal.cong(List<&2, V>, V, y => Spec.last(~V, ~z, y), Y, List.take(&2, V, Y, 1n+K0), Equal.sym(List<&2, V>, List.take(&2, V, Y, 1n+K0), Y, tY)))
  +L2 = ri_cong_adv(~V, ~E, ~C, ~P, ~ent, ~adv, l,
    Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), l, cl, sh, base, m, V0),
    Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
    plan(l, base, m, r, d), plan(l, Nat.add(n0, K0), 1n, 0n, 0n),
    Impl.at(~V, ~z, V0, r), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)), ih, eplan, eval)
  +R = ri_ls_step(~V, ~E, ~C, ~P, ~z, ~ent, ~adv, ~plan, Y, K0, l, c, n0, hY)
  Equal.trans(C, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, pi, l, cl, sh, base, m, V0),
    adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), l, cl, sh, base, m, V0),
      ent(l, plan(l, base, m, r, d), Impl.at(~V, ~z, V0, r))),
    Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Y, l, c, n0), L1,
    Equal.trans(C, adv(l, Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, List.take(&2, Nat, pi, d), l, cl, sh, base, m, V0),
        ent(l, plan(l, base, m, r, d), Impl.at(~V, ~z, V0, r))),
      adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
        ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))),
      Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Y, l, c, n0), L2,
      Equal.trans(C, adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
          ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, 1n+K0), l, c, n0),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Y, l, c, n0),
        Equal.sym(C, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, 1n+K0), l, c, n0),
          adv(l, Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, List.take(&2, V, Y, K0), l, c, n0),
            ent(l, plan(l, Nat.add(n0, K0), 1n, 0n, 0n), Spec.last(~V, ~z, List.take(&2, V, Y, 1n+K0)))), R),
        Equal.cong(List<&2, V>, C, y => Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, y, l, c, n0), List.take(&2, V, Y, 1n+K0), Y, tY))))

# up (pre ++ [c]) at layer |pre| is one more reference layer after up pre (l = |pre|).
def ri_lo_up(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, +pre: List<&2, C>, +c: C, +l: Nat, +xs: List<&2, V>, +n0: Nat,
    hl: {l == List.length(&2, C, pre) : Nat})
  -> {Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xs, n0), l, c, n0) ==
      Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, xs, n0) : List<&2, V>}:
  Equal.trans(List<&2, V>,
    Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xs, n0), l, c, n0),
    Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xs, n0), List.length(&2, C, pre), c, n0),
    Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, xs, n0),
    Equal.cong(Nat, List<&2, V>, y => Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xs, n0), y, c, n0),
      l, List.length(&2, C, pre), hl),
    Equal.sym(List<&2, V>, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, List.append(&2, C, pre, [c]), 0n, xs, n0),
      Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xs, n0), List.length(&2, C, pre), c, n0),
      ri_up_snoc(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, c, 0n, xs, n0)))

# 1 + l == |pre ++ [c]| from l == |pre|
def ri_len_snoc(~C: Data, +pre: List<&2, C>, +c: C, +l: Nat, hl: {l == List.length(&2, C, pre) : Nat})
  -> {1n+l == List.length(&2, C, List.append(&2, C, pre, [c])) : Nat}:
  Equal.trans(Nat, 1n+l, 1n+List.length(&2, C, pre), List.length(&2, C, List.append(&2, C, pre, [c])),
    Equal.cong(Nat, Nat, y => 1n+y, l, List.length(&2, C, pre), hl),
    Equal.sym(Nat, List.length(&2, C, List.append(&2, C, pre, [c])), 1n+List.length(&2, C, pre),
      Equal.trans(Nat, List.length(&2, C, List.append(&2, C, pre, [c])), Nat.add(List.length(&2, C, pre), 1n), 1n+List.length(&2, C, pre),
        ri_len_app(~C, pre, [c]),
        Equal.trans(Nat, Nat.add(List.length(&2, C, pre), 1n), 1n+Nat.add(List.length(&2, C, pre), 0n), 1n+List.length(&2, C, pre),
          Ar.ar_add_succ_r(List.length(&2, C, pre), 0n),
          Equal.cong(Nat, Nat, y => 1n+y, Nat.add(List.length(&2, C, pre), 0n), List.length(&2, C, pre), Ar.ar_add_zero_r(List.length(&2, C, pre)))))))

# The commit over the layers of suf (after those of pre, l = |pre|): from the 1-row-rounds states of u
# and the round's reference layer inputs, it leaves the 1-row-rounds states of u ++ stream(path r).
def ri_commit(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, ~ok: T -> Nat -> Bool,
    ~o_plan: OPlan(~P, ~plan), ~o_gat: OGat(~T, ~pth, ~gat, ~ok), ~w_last: WLast(~T, ~pth, ~ok),
    ~w_pre: WPre(~T, ~pth, ~ok), ~w_rng: WRng(~T, ~pth, ~ok), ~w_dep: WDep(~T, ~pth, ~ok),
    suf: List<&2, C>, +pre: List<&2, C>, +l: Nat, +n0: Nat, +u: List<&2, U32>, +toks: List<&2, U32>, +sh: T, +m: Nat, +r: Nat,
    +hok: {ok(sh, m) == True{} : Bool}, +hr: {Nat.is_lt(r, m) == True{} : Bool}, +h8: {Nat.is_le(m, 8n) == True{} : Bool},
    +hl: {l == List.length(&2, C, pre) : Nat})
  -> {Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
        Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, suf, l,
          Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, u), n0), n0),
        l, pth(sh, r), sh, Nat.add(n0, List.length(&2, U32, u)), m, rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)) ==
      Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, suf, l,
        Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))), n0), n0)
      : List<&2, C>}:
  match suf:
    case Nil{}:
      {==}
    case +c <> +rest:
      +base = Nat.add(n0, List.length(&2, U32, u))
      +xu = Spec.embs(~V, ~emb, u)
      +xw = Spec.embs(~V, ~emb, List.append(&2, U32, u, Impl.stream(toks, pth(sh, r))))
      +Xu = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xu, n0)
      +Xw = Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, 0n, xw, n0)
      +pc = List.append(&2, C, pre, [c])
      +V0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pre, n0, u, toks, sh)
      +V1 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pc, n0, u, toks, sh)
      +cl = Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xu, l, c, n0)
      +hd = ri_anc_full(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~o_plan, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        pre, n0, u, toks, sh, m, r, l, c, hok, hr, h8)
      +lay = ri_layer(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        m, 0n, pre, n0, u, toks, sh, m, l, c, hok, h8, Ar.ar_le_refl(m), hl)
      +usu = ri_lo_up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, c, l, xu, n0, hl)
      +usw = ri_lo_up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pre, c, l, xw, n0, hl)
      +ih = ri_commit(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
        rest, pc, 1n+l, n0, u, toks, sh, m, r, hok, hr, h8, ri_len_snoc(~C, pre, c, l, hl))
      # the tail: the next layer's inputs (ri_layer) and states (one more reference layer), then the IH
      +tl = Equal.trans(List<&2, C>,
        Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
          1n+l, pth(sh, r), sh, base, m, Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, cl, sh, base, m, V0)),
        Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xu, n0), n0),
          1n+l, pth(sh, r), sh, base, m, V1),
        Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xw, l, c, n0), n0),
        Equal.trans(List<&2, C>,
          Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
            Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
            1n+l, pth(sh, r), sh, base, m, Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, cl, sh, base, m, V0)),
          Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
            Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
            1n+l, pth(sh, r), sh, base, m, V1),
          Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
            Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xu, n0), n0),
            1n+l, pth(sh, r), sh, base, m, V1),
          Equal.cong(List<&2, V>, List<&2, C>, y => Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
              Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
              1n+l, pth(sh, r), sh, base, m, y),
            Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, cl, sh, base, m, V0), V1, lay),
          Equal.cong(List<&2, V>, List<&2, C>, y => Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
              Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, y, n0), 1n+l, pth(sh, r), sh, base, m, V1),
            Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xu, n0), usu)),
        Equal.trans(List<&2, C>,
          Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
            Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xu, n0), n0),
            1n+l, pth(sh, r), sh, base, m, V1),
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xw, n0), n0),
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xw, l, c, n0), n0),
          ih,
          Equal.cong(List<&2, V>, List<&2, C>, y => Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, y, n0),
            Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xw, n0), Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xw, l, c, n0),
            Equal.sym(List<&2, V>, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xw, l, c, n0), Spec.up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pc, 0n, xw, n0), usw))))
      ri_cong_cons(~C,
        Impl.ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, pth(sh, r), l, cl, sh, base, m, V0),
        Spec.ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, Xw, l, c, n0),
        Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xu, l, c, n0), n0),
          1n+l, pth(sh, r), sh, base, m, Impl.layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, cl, sh, base, m, V0)),
        Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Spec.lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, Xw, l, c, n0), n0),
        hd, tl)

# ---------------------------------------------------------------- the laws

def Laws.compose(V, E, C, P, T, z, emb, F, ent, adv, head, plan, hp, pth, gat, ok, o_plan, o_head, o_gat, w_last, w_pre, w_rng,
    w_dep, pcs, n0, u, cs, toks, sh, r, commit_, shape_, rows8_, row_):
  +commit = commit_
  +shape = shape_
  +rows8 = rows8_
  +row = row_
  +m = List.length(&2, U32, toks)
  +U = List.length(&2, U32, u)
  +base = Nat.add(n0, U)
  +d = Impl.dep(~T, ~pth, sh, r)
  +w = List.append(&2, U32, u, Impl.stream(toks, pth(sh, r)))
  +R0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, Nil{}, n0, u, toks, sh)
  +RL = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pcs, n0, u, toks, sh)
  # the served embeddings are the layer-0 reference values; all layers give the reference values
  +e0 = Equal.trans(List<&2, V>, Impl.embs(~V, ~emb, toks), Impl.embs(~V, ~emb, List.drop(&2, U32, toks, 0n)), R0,
    Equal.cong(List<&2, U32>, List<&2, V>, y => Impl.embs(~V, ~emb, y), toks, List.drop(&2, U32, toks, 0n),
      Equal.sym(List<&2, U32>, List.drop(&2, U32, toks, 0n), toks, ri_drop_zero(~U32, toks))),
    ri_rows0(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~w_last, m, 0n, n0, u, toks, sh, shape, {==}))
  +fw = ri_fwd(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
    pcs, Nil{}, 0n, n0, u, toks, sh, m, shape, rows8, {==})
  +FW = Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, cs, 0n, sh, base, m, Impl.embs(~V, ~emb, toks))
  +efw = Equal.trans(List<&2, V>, FW,
    Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
      Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u), 0n, sh, base, m, R0),
    RL,
    Equal.trans(List<&2, V>, FW,
      Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
        Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u), 0n, sh, base, m, Impl.embs(~V, ~emb, toks)),
      Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
        Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u), 0n, sh, base, m, R0),
      Equal.cong(List<&2, C>, List<&2, V>, y => Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, y, 0n, sh, base, m, Impl.embs(~V, ~emb, toks)),
        cs, Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u), commit),
      Equal.cong(List<&2, V>, List<&2, V>, y => Impl.fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat,
          Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u), 0n, sh, base, m, y),
        Impl.embs(~V, ~emb, toks), R0, e0)),
    fw)
  # the row's final value, its head plan at the absolute position, and the position arithmetic
  +eat = Equal.trans(V, Impl.at(~V, ~z, FW, r), Impl.at(~V, ~z, RL, r),
    rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pcs, n0, u, toks, sh, r),
    Equal.cong(List<&2, V>, V, y => Impl.at(~V, ~z, y, r), FW, RL, efw),
    ri_at_rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, pcs, n0, u, toks, sh, r, row))
  +lenw = Equal.trans(Nat, List.length(&2, U32, w), Nat.add(U, List.length(&2, U32, Impl.stream(toks, pth(sh, r)))), 1n+Nat.add(U, d),
    ri_len_app(~U32, u, Impl.stream(toks, pth(sh, r))),
    Equal.trans(Nat, Nat.add(U, List.length(&2, U32, Impl.stream(toks, pth(sh, r)))), Nat.add(U, 1n+d), 1n+Nat.add(U, d),
      Equal.cong(Nat, Nat, y => Nat.add(U, y), List.length(&2, U32, Impl.stream(toks, pth(sh, r))), 1n+d,
        Equal.trans(Nat, List.length(&2, U32, Impl.stream(toks, pth(sh, r))), List.length(&2, Nat, pth(sh, r)), 1n+d,
          ri_len_stream(toks, pth(sh, r)), ri_len_path(~T, ~pth, ~ok, ~w_last, sh, m, r, shape, row))),
      Ar.ar_add_succ_r(U, d)))
  +pos = Equal.trans(Nat, Nat.add(base, d), Nat.add(n0, Nat.add(U, d)), Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)),
    Ar.ar_add_assoc(n0, U, d),
    Equal.cong(Nat, Nat, y => Nat.add(n0, y), Nat.add(U, d), Nat.sub(List.length(&2, U32, w), 1n),
      Equal.trans(Nat, Nat.add(U, d), Nat.sub(1n+Nat.add(U, d), 1n), Nat.sub(List.length(&2, U32, w), 1n),
        Equal.sym(Nat, Nat.sub(Nat.add(U, d), 0n), Nat.add(U, d), Ar.ar_sub_zero_r(Nat.add(U, d))),
        Equal.cong(Nat, Nat, y => Nat.sub(y, 1n), 1n+Nat.add(U, d), List.length(&2, U32, w),
          Equal.sym(Nat, List.length(&2, U32, w), 1n+Nat.add(U, d), lenw)))))
  +ehp = Equal.trans(P, hp(base, m, r, d), hp(Nat.add(base, d), 1n, 0n, 0n), hp(Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)), 1n, 0n, 0n),
    o_head(base, m, r, d, ri_w_dep(~T, ~pth, ~ok, ~w_dep, sh, m, r, shape, row), row, rows8),
    Equal.cong(Nat, P, y => hp(y, 1n, 0n, 0n), Nat.add(base, d), Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)), pos))
  +eh = ri_at_heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, m, 0n, sh, base, m, FW, r, row)
  %Equal.sym(U32, Impl.at(~U32, ~0, Impl.heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, m, 0n, sh, base, m, FW), r),
      head(hp(base, m, r, d), Impl.at(~V, ~z, FW, r)), eh) : {_ == Spec.ref(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, pcs, n0, w) : U32}
  %Equal.sym(P, hp(base, m, r, d), hp(Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)), 1n, 0n, 0n), ehp) : {head(_, Impl.at(~V, ~z, FW, r)) == Spec.ref(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, pcs, n0, w) : U32}
  %Equal.sym(V, Impl.at(~V, ~z, FW, r), rv(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, pcs, n0, u, toks, sh, r), eat) : {head(hp(Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)), 1n, 0n, 0n), _) ==
    Spec.ref(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, pcs, n0, w) : U32}
  {==}

def Laws.commit_path(V, E, C, P, T, z, emb, F, ent, adv, plan, pth, gat, ok, o_plan, o_gat, w_last, w_pre, w_rng, w_dep,
    pcs, n0, u, cs, toks, sh, r, commit_, shape_, rows8_, row_):
  +commit = commit_
  +shape = shape_
  +rows8 = rows8_
  +row = row_
  +m = List.length(&2, U32, toks)
  +base = Nat.add(n0, List.length(&2, U32, u))
  +pi = pth(sh, r)
  +CU = Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, u)
  +R0 = rows(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, m, 0n, Nil{}, n0, u, toks, sh)
  # the served embeddings are the layer-0 reference values
  +e0 = Equal.trans(List<&2, V>, Impl.embs(~V, ~emb, toks), Impl.embs(~V, ~emb, List.drop(&2, U32, toks, 0n)), R0,
    Equal.cong(List<&2, U32>, List<&2, V>, y => Impl.embs(~V, ~emb, y), toks, List.drop(&2, U32, toks, 0n),
      Equal.sym(List<&2, U32>, List.drop(&2, U32, toks, 0n), toks, ri_drop_zero(~U32, toks))),
    ri_rows0(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~ok, ~w_last, m, 0n, n0, u, toks, sh, shape, {==}))
  +ec = ri_commit(~V, ~E, ~C, ~P, ~T, ~z, ~emb, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, ~ok, ~o_plan, ~o_gat, ~w_last, ~w_pre, ~w_rng, ~w_dep,
    pcs, Nil{}, 0n, n0, u, toks, sh, m, r, shape, row, rows8, {==})
  Equal.trans(List<&2, C>,
    Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, cs, 0n, pi, sh, base, m, Impl.embs(~V, ~emb, toks)),
    Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, CU, 0n, pi, sh, base, m, R0),
    Spec.committed(~V, ~E, ~C, ~P, ~emb, ~F, ~ent, ~adv, ~plan, pcs, n0, List.append(&2, U32, u, Impl.stream(toks, pi))),
    Equal.trans(List<&2, C>,
      Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, cs, 0n, pi, sh, base, m, Impl.embs(~V, ~emb, toks)),
      Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, CU, 0n, pi, sh, base, m, Impl.embs(~V, ~emb, toks)),
      Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, CU, 0n, pi, sh, base, m, R0),
      Equal.cong(List<&2, C>, List<&2, C>, y => Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, y, 0n, pi, sh, base, m, Impl.embs(~V, ~emb, toks)),
        cs, CU, commit),
      Equal.cong(List<&2, V>, List<&2, C>, y => Impl.commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, CU, 0n, pi, sh, base, m, y),
        Impl.embs(~V, ~emb, toks), R0, e0)),
    ec)


# ---------------------------------------------------------------- witnesses, ~rinv, the starting state

def Laws.plan_leak_differs():
  ({==}, {==}, {==}, {==})

def Laws.gather_drop_differs():
  {==}

def Laws.ref_rinv(V, E, C, P, z, emb, F, ent, adv, head, plan, hp, pf, n0, row, isref, p, r):
  +p = p
  Equal.trans(U32, row(p, r), Spec.ref_prefix(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, ~pf, ~n0, p), row(p, 0n),
    isref(p, r), Equal.sym(U32, row(p, 0n), Spec.ref_prefix(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, ~pf, ~n0, p), isref(p, 0n)))

def ri_states_nil(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, cs: List<&2, C>, +l: Nat, +i: Nat)
  -> {Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, cs, l, Nil{}, i) == cs : List<&2, C>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      Equal.cong(List<&2, C>, List<&2, C>, y => c <> y, Spec.states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, Nil{}, i), rest,
        ri_states_nil(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, i))

def Laws.committed_prefill(V, E, C, P, emb, F, ent, adv, plan, pcs, n0):
  ri_states_nil(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pcs, 0n, n0)
