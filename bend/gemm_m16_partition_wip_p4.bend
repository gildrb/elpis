# WIP proofs: law reduction_order. Laws.contributors_contiguous (wip_p2) is called.
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p4_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# STUB-BEGIN (proven in wip_p2)
def Laws.contributors_contiguous(mats, n, k, G, g, b, grid, shaped, fits, group):
  ?TODO
# STUB-END

# ---- small helpers ----

def p4_ne(+x: Nat, -y: Nat, same: {x == y : Nat},
    diff: {Nat.is_eq(x, y) == False{} : Bool}) -> Empty:
  Arith.ar_true_false(Equal.trans(Bool, True{}, Nat.is_eq(x, x), False{},
    Equal.sym(Bool, Nat.is_eq(x, x), True{}, Arith.ar_eq_refl(x)),
    Equal.trans(Bool, Nat.is_eq(x, x), Nat.is_eq(x, y), False{},
      Equal.cong(Nat, Bool, z => Nat.is_eq(x, z), x, y, same), diff)))

# ---- workspace store / slot_at ----

def p4_store_len(ws: List<&2, Spec.Sum>, i: Nat, v: Spec.Sum)
  -> {List.length(&2, Spec.Sum, Impl.store(ws, i, v)) == List.length(&2, Spec.Sum, ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          %p4_store_len(rest, j, v) : {1n+List.length(&2, Spec.Sum, Impl.store(rest, j, v)) == 1n+_ : Nat}
          {==}

def p4_ss_eq(ws: List<&2, Spec.Sum>, i: Nat, v: Spec.Sum,
    h: {Nat.is_lt(i, List.length(&2, Spec.Sum, ws)) == True{} : Bool})
  -> {Impl.slot_at(Impl.store(ws, i, v), i) == v : Spec.Sum}:
  match ws:
    case Nil{}:
      match i:
        case 0n:
          Empty.absurd({Impl.slot_at(Nil{}, 0n) == v : Spec.Sum}, Arith.ar_false_true(h))
        case 1n+j:
          Empty.absurd({Impl.slot_at(Nil{}, 1n+j) == v : Spec.Sum}, Arith.ar_false_true(h))
    case w <> rest:
      match i:
        case 0n:
          {==}
        case 1n+j:
          p4_ss_eq(rest, j, v, h)

def p4_ss_ne(ws: List<&2, Spec.Sum>, i: Nat, j: Nat, v: Spec.Sum,
    ne: {Nat.is_eq(i, j) == False{} : Bool})
  -> {Impl.slot_at(Impl.store(ws, i, v), j) == Impl.slot_at(ws, j) : Spec.Sum}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      match i j:
        case 0n 0n:
          Empty.absurd({Impl.slot_at(v <> rest, 0n) == w : Spec.Sum}, Arith.ar_true_false(ne))
        case 0n 1n+q:
          {==}
        case 1n+p 0n:
          {==}
        case 1n+p 1n+q:
          p4_ss_ne(rest, p, q, v, ne)

# ---- arrive: every arrived block's slot holds its partial ----

# Every element of the order is >= L.
def p4_all_ge(order: List<&2, Nat>, +L: Nat) -> Bool:
  match order:
    case Nil{}:
      True{}
    case +a <> rest:
      Bool.and(Nat.is_le(L, a), p4_all_ge(rest, L))

def p4_sub_inj(+a: Nat, +b: Nat, +L: Nat, hLa: {Nat.is_le(L, a) == True{} : Bool},
    hLb: {Nat.is_le(L, b) == True{} : Bool}, e: {Nat.sub(a, L) == Nat.sub(b, L) : Nat})
  -> {a == b : Nat}:
  Equal.trans(Nat, a, Nat.add(L, Nat.sub(a, L)), b,
    Equal.sym(Nat, Nat.add(L, Nat.sub(a, L)), a, Arith.ar_sub_add(a, L, hLa)),
    Equal.trans(Nat, Nat.add(L, Nat.sub(a, L)), Nat.add(L, Nat.sub(b, L)), b,
      Equal.cong(Nat, Nat, z => Nat.add(L, z), Nat.sub(a, L), Nat.sub(b, L), e),
      Arith.ar_sub_add(b, L, hLb)))

# Block a == b stores Part{b} into slot b - L.
def p4_slot_hit(+a: Nat, +b: Nat, +L: Nat, +ws: List<&2, Spec.Sum>, e: {b == a : Nat},
    hlen: {Nat.is_lt(Nat.sub(b, L), List.length(&2, Spec.Sum, ws)) == True{} : Bool})
  -> {Impl.slot_at(Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), Nat.sub(b, L)) ==
    Spec.Part{b} : Spec.Sum}:
  %e : {Impl.slot_at(Impl.store(ws, Nat.sub(_, L), Spec.Part{_}), Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum}
  p4_ss_eq(ws, Nat.sub(b, L), Spec.Part{b}, hlen)

# A store by block a (L <= a) keeps slot b - L holding Part{b}.
def p4_keep_slot(x: Bool, +a: Nat, +b: Nat, +L: Nat, +ws: List<&2, Spec.Sum>,
    hx: {Nat.is_eq(a, b) == x : Bool},
    hLa: {Nat.is_le(L, a) == True{} : Bool}, hLb: {Nat.is_le(L, b) == True{} : Bool},
    hlen: {Nat.is_lt(Nat.sub(b, L), List.length(&2, Spec.Sum, ws)) == True{} : Bool},
    hs: {Impl.slot_at(ws, Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum})
  -> {Impl.slot_at(Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), Nat.sub(b, L)) ==
    Spec.Part{b} : Spec.Sum}:
  match x:
    case True{}:
      p4_slot_hit(a, b, L, ws, Equal.sym(Nat, a, b, Arith.ar_eq_true(a, b, hx)), hlen)
    case False{}:
      Equal.trans(Spec.Sum,
        Impl.slot_at(Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), Nat.sub(b, L)),
        Impl.slot_at(ws, Nat.sub(b, L)), Spec.Part{b},
        p4_ss_ne(ws, Nat.sub(a, L), Nat.sub(b, L), Spec.Part{a},
          Arith.ar_eq_false(Nat.sub(a, L), Nat.sub(b, L),
            e => p4_ne(a, b, p4_sub_inj(a, b, L, hLa, hLb, e), hx))),
        hs)

def p4_len_step(+ws: List<&2, Spec.Sum>, +i: Nat, +v: Spec.Sum, +j: Nat,
    hlen: {Nat.is_lt(j, List.length(&2, Spec.Sum, ws)) == True{} : Bool})
  -> {Nat.is_lt(j, List.length(&2, Spec.Sum, Impl.store(ws, i, v))) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(j, List.length(&2, Spec.Sum, Impl.store(ws, i, v))),
    Nat.is_lt(j, List.length(&2, Spec.Sum, ws)), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(j, z),
      List.length(&2, Spec.Sum, Impl.store(ws, i, v)), List.length(&2, Spec.Sum, ws),
      p4_store_len(ws, i, v)),
    hlen)

# Once slot b - L holds Part{b}, later arrivals (all >= L) keep it.
def p4_keep(+order: List<&2, Nat>, +ws: List<&2, Spec.Sum>, +L: Nat, +b: Nat,
    +hL: {Nat.is_le(L, b) == True{} : Bool},
    +hlen: {Nat.is_lt(Nat.sub(b, L), List.length(&2, Spec.Sum, ws)) == True{} : Bool},
    +hall: {p4_all_ge(order, L) == True{} : Bool},
    hs: {Impl.slot_at(ws, Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum})
  -> {Impl.slot_at(Impl.arrive(order, ws, L), Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum}:
  match order:
    case Nil{}:
      hs
    case +a <> rest:
      p4_keep(rest, Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), L, b, hL,
        p4_len_step(ws, Nat.sub(a, L), Spec.Part{a}, Nat.sub(b, L), hlen),
        Arith.ar_and_r(Nat.is_le(L, a), p4_all_ge(rest, L), hall),
        p4_keep_slot(Nat.is_eq(a, b), a, b, L, ws, {==},
          Arith.ar_and_l(Nat.is_le(L, a), p4_all_ge(rest, L), hall), hL, hlen, hs))

def p4_hit_step(x: Bool, +a: Nat, +b: Nat, +L: Nat, +ws: List<&2, Spec.Sum>,
    -rest: List<&2, Nat>, hx: {Nat.is_eq(a, b) == x : Bool},
    hlen: {Nat.is_lt(Nat.sub(b, L), List.length(&2, Spec.Sum, ws)) == True{} : Bool},
    harr: {Bool.or(x, Spec.arrived(rest, b)) == True{} : Bool},
    ih: {Spec.arrived(rest, b) == True{} : Bool} ->
      {Impl.slot_at(Impl.arrive(rest, Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), L),
        Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum},
    kp: {Impl.slot_at(Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), Nat.sub(b, L)) ==
        Spec.Part{b} : Spec.Sum} ->
      {Impl.slot_at(Impl.arrive(rest, Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), L),
        Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum})
  -> {Impl.slot_at(Impl.arrive(rest, Impl.store(ws, Nat.sub(a, L), Spec.Part{a}), L),
    Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum}:
  match x:
    case True{}:
      kp(p4_slot_hit(a, b, L, ws, Equal.sym(Nat, a, b, Arith.ar_eq_true(a, b, hx)), hlen))
    case False{}:
      ih(harr)

# An arrived block b (L <= b, slot in range) ends with Part{b} in slot b - L.
def p4_hit(+order: List<&2, Nat>, +ws: List<&2, Spec.Sum>, +L: Nat, +b: Nat,
    +hL: {Nat.is_le(L, b) == True{} : Bool},
    +hlen: {Nat.is_lt(Nat.sub(b, L), List.length(&2, Spec.Sum, ws)) == True{} : Bool},
    +hall: {p4_all_ge(order, L) == True{} : Bool},
    harr: {Spec.arrived(order, b) == True{} : Bool})
  -> {Impl.slot_at(Impl.arrive(order, ws, L), Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum}:
  match order:
    case Nil{}:
      Empty.absurd({Impl.slot_at(ws, Nat.sub(b, L)) == Spec.Part{b} : Spec.Sum},
        Arith.ar_false_true(harr))
    case +a <> rest:
      +ws2 = Impl.store(ws, Nat.sub(a, L), Spec.Part{a})
      +hlen2 = p4_len_step(ws, Nat.sub(a, L), Spec.Part{a}, Nat.sub(b, L), hlen)
      +hall2 = Arith.ar_and_r(Nat.is_le(L, a), p4_all_ge(rest, L), hall)
      p4_hit_step(Nat.is_eq(a, b), a, b, L, ws, rest, {==}, hlen, harr,
        h => p4_hit(rest, ws2, L, b, hL, hlen2, hall2, h),
        s => p4_keep(rest, ws2, L, b, hL, hlen2, hall2, s))

# ---- ascending fold over the contiguous range [L, H] ----

def p4_le_succ(b: Nat) -> {Nat.is_le(b, 1n+b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      p4_le_succ(p)

def p4_lt_succ(b: Nat) -> {Nat.is_lt(b, 1n+b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      p4_lt_succ(p)

def p4_not_t_f(x: Bool, h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Arith.ar_false_true(h))
    case False{}:
      {==}

def p4_and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Block b lies in [L, H].
def p4_in(+L: Nat, +H: Nat, +b: Nat) -> Bool:
  Bool.and(Nat.is_le(L, b), Nat.is_le(b, H))

# fold_touching with touches(b) replaced by b in [L, H].
def p4_rng(left: Nat, +b: Nat, +L: Nat, +H: Nat, acc: Maybe<&2, Spec.Sum>)
  -> Maybe<&2, Spec.Sum>:
  match left:
    case 0n:
      acc
    case 1n+rest:
      p4_rng(rest, 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc))

# v + Part{b} + Part{b + 1} + ... (left terms), summed left to right.
def p4_asc(left: Nat, +b: Nat, v: Spec.Sum) -> Spec.Sum:
  match left:
    case 0n:
      v
    case 1n+rest:
      p4_asc(rest, 1n+b, Spec.Add{v, Spec.Part{b}})

def p4_split(+a: Nat, +r: Nat, +b: Nat, +L: Nat, +H: Nat, +acc: Maybe<&2, Spec.Sum>)
  -> {p4_rng(Nat.add(a, r), b, L, H, acc) ==
    p4_rng(r, Nat.add(a, b), L, H, p4_rng(a, b, L, H, acc)) : Maybe<&2, Spec.Sum>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Spec.Sum>,
        p4_rng(Nat.add(p, r), 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc)),
        p4_rng(r, Nat.add(p, 1n+b), L, H,
          p4_rng(p, 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc))),
        p4_rng(r, 1n+Nat.add(p, b), L, H,
          p4_rng(p, 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc))),
        p4_split(p, r, 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc)),
        Equal.cong(Nat, Maybe<&2, Spec.Sum>,
          z => p4_rng(r, z, L, H,
            p4_rng(p, 1n+b, L, H, Spec.fold_step(p4_in(L, H, b), b, acc))),
          Nat.add(p, 1n+b), 1n+Nat.add(p, b), Arith.ar_add_succ_r(p, b)))

# Blocks b .. b + a - 1 all below L leave acc unchanged.
def p4_pre(+a: Nat, +b: Nat, +L: Nat, +H: Nat, +acc: Maybe<&2, Spec.Sum>,
    +h: {Nat.is_le(Nat.add(a, b), L) == True{} : Bool})
  -> {p4_rng(a, b, L, H, acc) == acc : Maybe<&2, Spec.Sum>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +hlt = Equal.trans(Bool, Nat.is_lt(b, L), Nat.is_le(1n+b, L), True{},
        Arith.ar_lt_succ_le(b, L),
        Arith.ar_le_trans(1n+b, 1n+Nat.add(p, b), L, Arith.ar_le_add_l(p, b), h))
      +hf = p4_not_t_f(Nat.is_le(L, b),
        Equal.trans(Bool, Bool.not(Nat.is_le(L, b)), Nat.is_lt(b, L), True{},
          Equal.sym(Bool, Nat.is_lt(b, L), Bool.not(Nat.is_le(L, b)),
            Arith.ar_lt_not_le(b, L)),
          hlt))
      +hin = Equal.cong(Bool, Bool, z => Bool.and(z, Nat.is_le(b, H)), Nat.is_le(L, b),
        False{}, hf)
      %Equal.sym(Bool, p4_in(L, H, b), False{}, hin) : {p4_rng(p, 1n+b, L, H, Spec.fold_step(_, b, acc)) == acc : Maybe<&2, Spec.Sum>}
      p4_pre(p, 1n+b, L, H, acc,
        Equal.trans(Bool, Nat.is_le(Nat.add(p, 1n+b), L), Nat.is_le(1n+Nat.add(p, b), L),
          True{},
          Equal.cong(Nat, Bool, z => Nat.is_le(z, L), Nat.add(p, 1n+b), 1n+Nat.add(p, b),
            Arith.ar_add_succ_r(p, b)),
          h))

# Blocks past H leave acc unchanged.
def p4_post(+a: Nat, +b: Nat, +L: Nat, +H: Nat, +acc: Maybe<&2, Spec.Sum>,
    +h: {Nat.is_lt(H, b) == True{} : Bool})
  -> {p4_rng(a, b, L, H, acc) == acc : Maybe<&2, Spec.Sum>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +hf = p4_not_t_f(Nat.is_le(b, H),
        Equal.trans(Bool, Bool.not(Nat.is_le(b, H)), Nat.is_lt(H, b), True{},
          Equal.sym(Bool, Nat.is_lt(H, b), Bool.not(Nat.is_le(b, H)),
            Arith.ar_lt_not_le(H, b)),
          h))
      +hin = Equal.trans(Bool, p4_in(L, H, b), Bool.and(Nat.is_le(L, b), False{}), False{},
        Equal.cong(Bool, Bool, z => Bool.and(Nat.is_le(L, b), z), Nat.is_le(b, H), False{},
          hf),
        p4_and_f(Nat.is_le(L, b)))
      %Equal.sym(Bool, p4_in(L, H, b), False{}, hin) : {p4_rng(p, 1n+b, L, H, Spec.fold_step(_, b, acc)) == acc : Maybe<&2, Spec.Sum>}
      p4_post(p, 1n+b, L, H, acc, Arith.ar_lt_trans(H, b, 1n+b, h, p4_lt_succ(b)))

# Blocks b .. b + a - 1 all inside [L, H] extend Some{v} one partial at a time.
def p4_mid(+a: Nat, +b: Nat, +L: Nat, +H: Nat, +v: Spec.Sum,
    +hL: {Nat.is_le(L, b) == True{} : Bool},
    +hH: {Nat.is_le(Nat.add(a, b), 1n+H) == True{} : Bool})
  -> {p4_rng(a, b, L, H, Some{v}) == Some{p4_asc(a, b, v)} : Maybe<&2, Spec.Sum>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +hin = Arith.ar_and_intro(Nat.is_le(L, b), Nat.is_le(b, H), hL,
        Arith.ar_le_trans(b, Nat.add(p, b), H, Arith.ar_le_add_l(p, b), hH))
      %Equal.sym(Bool, p4_in(L, H, b), True{}, hin) : {p4_rng(p, 1n+b, L, H, Spec.fold_step(_, b, Some{v})) == Some{p4_asc(p, 1n+b, Spec.Add{v, Spec.Part{b}})} : Maybe<&2, Spec.Sum>}
      p4_mid(p, 1n+b, L, H, Spec.Add{v, Spec.Part{b}},
        Arith.ar_le_trans(L, b, 1n+b, hL, p4_le_succ(b)),
        Equal.trans(Bool, Nat.is_le(Nat.add(p, 1n+b), 1n+H), Nat.is_le(1n+Nat.add(p, b), 1n+H),
          True{},
          Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+H), Nat.add(p, 1n+b), 1n+Nat.add(p, b),
            Arith.ar_add_succ_r(p, b)),
          hH))

# From block b (L <= b, b + d = H + 1) on, m >= d more blocks sum exactly blocks b .. H.
def p4_rest(+m: Nat, +d: Nat, +b: Nat, +L: Nat, +H: Nat, +v: Spec.Sum,
    +hL: {Nat.is_le(L, b) == True{} : Bool},
    +hd: {Nat.add(d, b) == 1n+H : Nat},
    hm: {Nat.is_le(d, m) == True{} : Bool})
  -> {p4_rng(m, b, L, H, Some{v}) == Some{p4_asc(d, b, v)} : Maybe<&2, Spec.Sum>}:
  %Arith.ar_sub_add(m, d, hm) : {p4_rng(_, b, L, H, Some{v}) == Some{p4_asc(d, b, v)} : Maybe<&2, Spec.Sum>}
  Equal.trans(Maybe<&2, Spec.Sum>,
    p4_rng(Nat.add(d, Nat.sub(m, d)), b, L, H, Some{v}),
    p4_rng(Nat.sub(m, d), Nat.add(d, b), L, H, p4_rng(d, b, L, H, Some{v})),
    Some{p4_asc(d, b, v)},
    p4_split(d, Nat.sub(m, d), b, L, H, Some{v}),
    Equal.trans(Maybe<&2, Spec.Sum>,
      p4_rng(Nat.sub(m, d), Nat.add(d, b), L, H, p4_rng(d, b, L, H, Some{v})),
      p4_rng(Nat.sub(m, d), Nat.add(d, b), L, H, Some{p4_asc(d, b, v)}),
      Some{p4_asc(d, b, v)},
      Equal.cong(Maybe<&2, Spec.Sum>, Maybe<&2, Spec.Sum>,
        z => p4_rng(Nat.sub(m, d), Nat.add(d, b), L, H, z),
        p4_rng(d, b, L, H, Some{v}), Some{p4_asc(d, b, v)},
        p4_mid(d, b, L, H, v, hL,
          Equal.trans(Bool, Nat.is_le(Nat.add(d, b), 1n+H), Nat.is_le(1n+H, 1n+H), True{},
            Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+H), Nat.add(d, b), 1n+H, hd),
            Arith.ar_le_refl(1n+H)))),
      p4_post(Nat.sub(m, d), Nat.add(d, b), L, H, Some{p4_asc(d, b, v)},
        Equal.trans(Bool, Nat.is_lt(H, Nat.add(d, b)), Nat.is_lt(H, 1n+H), True{},
          Equal.cong(Nat, Bool, z => Nat.is_lt(H, z), Nat.add(d, b), 1n+H, hd),
          p4_lt_succ(H)))))

# From block L on (acc None), m >= d + 1 blocks sum exactly blocks L .. H.
def p4_start(+m: Nat, +L: Nat, +H: Nat, +d: Nat,
    +hLH: {Nat.is_le(L, H) == True{} : Bool},
    +hd: {Nat.add(d, 1n+L) == 1n+H : Nat},
    hm: {Nat.is_le(1n+d, m) == True{} : Bool})
  -> {p4_rng(m, L, L, H, None{}) == Some{p4_asc(d, 1n+L, Spec.Part{L})}
    : Maybe<&2, Spec.Sum>}:
  match m:
    case 0n:
      Empty.absurd({None{} == Some{p4_asc(d, 1n+L, Spec.Part{L})} : Maybe<&2, Spec.Sum>},
        Arith.ar_false_true(hm))
    case 1n+p:
      +hin = Arith.ar_and_intro(Nat.is_le(L, L), Nat.is_le(L, H), Arith.ar_le_refl(L), hLH)
      %Equal.sym(Bool, p4_in(L, H, L), True{}, hin) : {p4_rng(p, 1n+L, L, H, Spec.fold_step(_, L, None{})) == Some{p4_asc(d, 1n+L, Spec.Part{L})} : Maybe<&2, Spec.Sum>}
      p4_rest(p, d, 1n+L, L, H, Spec.Part{L}, p4_le_succ(L), hd, hm)

# The whole grid 0 .. G - 1 (L <= H < G) sums exactly blocks L .. H, ascending.
def p4_whole(+G: Nat, +L: Nat, +H: Nat,
    +hLH: {Nat.is_le(L, H) == True{} : Bool},
    +hHG: {Nat.is_lt(H, G) == True{} : Bool})
  -> {p4_rng(G, 0n, L, H, None{}) == Some{p4_asc(Nat.sub(H, L), 1n+L, Spec.Part{L})}
    : Maybe<&2, Spec.Sum>}:
  +hLG = Arith.ar_lt_le(L, G, Arith.ar_le_lt_trans(L, H, G, hLH, hHG))
  +m = Nat.sub(G, L)
  +d = Nat.sub(H, L)
  +hd = Equal.trans(Nat, Nat.add(d, 1n+L), 1n+Nat.add(d, L), 1n+H,
    Arith.ar_add_succ_r(d, L),
    Equal.cong(Nat, Nat, z => 1n+z, Nat.add(d, L), H,
      Equal.trans(Nat, Nat.add(d, L), Nat.add(L, d), H, Arith.ar_add_comm(d, L),
        Arith.ar_sub_add(H, L, hLH))))
  +hm = Equal.trans(Bool, Nat.is_le(1n+d, m), Nat.is_lt(d, m), True{},
    Equal.sym(Bool, Nat.is_lt(d, m), Nat.is_le(1n+d, m), Arith.ar_lt_succ_le(d, m)),
    Equal.trans(Bool, Nat.is_lt(d, m), Nat.is_lt(Nat.add(L, d), G), True{},
      Arith.ar_lt_sub_iff(G, L, d),
      Equal.trans(Bool, Nat.is_lt(Nat.add(L, d), G), Nat.is_lt(H, G), True{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(z, G), Nat.add(L, d), H,
          Arith.ar_sub_add(H, L, hLH)),
        hHG)))
  +hpre = Equal.trans(Bool, Nat.is_le(Nat.add(L, 0n), L), Nat.is_le(L, L), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, L), Nat.add(L, 0n), L, Arith.ar_add_zero_r(L)),
    Arith.ar_le_refl(L))
  %Arith.ar_sub_add(G, L, hLG) : {p4_rng(_, 0n, L, H, None{}) == Some{p4_asc(d, 1n+L, Spec.Part{L})} : Maybe<&2, Spec.Sum>}
  Equal.trans(Maybe<&2, Spec.Sum>,
    p4_rng(Nat.add(L, m), 0n, L, H, None{}),
    p4_rng(m, Nat.add(L, 0n), L, H, p4_rng(L, 0n, L, H, None{})),
    Some{p4_asc(d, 1n+L, Spec.Part{L})},
    p4_split(L, m, 0n, L, H, None{}),
    Equal.trans(Maybe<&2, Spec.Sum>,
      p4_rng(m, Nat.add(L, 0n), L, H, p4_rng(L, 0n, L, H, None{})),
      p4_rng(m, Nat.add(L, 0n), L, H, None{}),
      Some{p4_asc(d, 1n+L, Spec.Part{L})},
      Equal.cong(Maybe<&2, Spec.Sum>, Maybe<&2, Spec.Sum>,
        z => p4_rng(m, Nat.add(L, 0n), L, H, z),
        p4_rng(L, 0n, L, H, None{}), None{}, p4_pre(L, 0n, L, H, None{}, hpre)),
      Equal.trans(Maybe<&2, Spec.Sum>,
        p4_rng(m, Nat.add(L, 0n), L, H, None{}),
        p4_rng(m, L, L, H, None{}),
        Some{p4_asc(d, 1n+L, Spec.Part{L})},
        Equal.cong(Nat, Maybe<&2, Spec.Sum>, z => p4_rng(m, z, L, H, None{}),
          Nat.add(L, 0n), L, Arith.ar_add_zero_r(L)),
        p4_start(m, L, H, d, hLH, hd, hm))))

# ---- finish: the slot-order sum is the ascending fold ----

# Blocks b0 .. b0 + cnt - 1 have all arrived.
def p4_all_arr(cnt: Nat, +b0: Nat, +order: List<&2, Nat>) -> Bool:
  match cnt:
    case 0n:
      True{}
    case 1n+c:
      Bool.and(Spec.arrived(order, b0), p4_all_arr(c, 1n+b0, order))

# Slot c holds Part{c + L} once block c + L has arrived.
def p4_slot_c(+c: Nat, +order: List<&2, Nat>, +ws: List<&2, Spec.Sum>, +L: Nat,
    +hall: {p4_all_ge(order, L) == True{} : Bool},
    harr: {Spec.arrived(order, Nat.add(c, L)) == True{} : Bool},
    hlen: {Nat.is_lt(c, List.length(&2, Spec.Sum, ws)) == True{} : Bool})
  -> {Impl.slot_at(Impl.arrive(order, ws, L), c) == Spec.Part{Nat.add(c, L)} : Spec.Sum}:
  +e = Equal.trans(Nat, Nat.sub(Nat.add(c, L), L), Nat.sub(Nat.add(L, c), L), c,
    Equal.cong(Nat, Nat, z => Nat.sub(z, L), Nat.add(c, L), Nat.add(L, c),
      Arith.ar_add_comm(c, L)),
    Arith.ar_add_sub(L, c))
  Equal.trans(Spec.Sum, Impl.slot_at(Impl.arrive(order, ws, L), c),
    Impl.slot_at(Impl.arrive(order, ws, L), Nat.sub(Nat.add(c, L), L)), Spec.Part{Nat.add(c, L)},
    Equal.cong(Nat, Spec.Sum, z => Impl.slot_at(Impl.arrive(order, ws, L), z), c,
      Nat.sub(Nat.add(c, L), L), Equal.sym(Nat, Nat.sub(Nat.add(c, L), L), c, e)),
    p4_hit(order, ws, L, Nat.add(c, L), Arith.ar_le_add_l(c, L),
      Equal.trans(Bool, Nat.is_lt(Nat.sub(Nat.add(c, L), L), List.length(&2, Spec.Sum, ws)),
        Nat.is_lt(c, List.length(&2, Spec.Sum, ws)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(z, List.length(&2, Spec.Sum, ws)),
          Nat.sub(Nat.add(c, L), L), c, e),
        hlen),
      hall, harr))

# finish.go over slots c .. c + a - 1 adds Part{c + L} .. Part{c + a - 1 + L} in order.
def p4_fin(+a: Nat, +c: Nat, +v: Spec.Sum, +order: List<&2, Nat>, +ws: List<&2, Spec.Sum>,
    +L: Nat, +hall: {p4_all_ge(order, L) == True{} : Bool},
    +harr: {p4_all_arr(a, Nat.add(c, L), order) == True{} : Bool},
    +hlen: {Nat.is_le(Nat.add(a, c), List.length(&2, Spec.Sum, ws)) == True{} : Bool})
  -> {Impl.finish.go(a, c, v, Impl.arrive(order, ws, L)) == p4_asc(a, Nat.add(c, L), v)
    : Spec.Sum}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +hltc = Equal.trans(Bool, Nat.is_lt(c, List.length(&2, Spec.Sum, ws)),
        Nat.is_le(1n+c, List.length(&2, Spec.Sum, ws)), True{},
        Arith.ar_lt_succ_le(c, List.length(&2, Spec.Sum, ws)),
        Arith.ar_le_trans(1n+c, 1n+Nat.add(p, c), List.length(&2, Spec.Sum, ws),
          Arith.ar_le_add_l(p, c), hlen))
      +hs = p4_slot_c(c, order, ws, L, hall,
        Arith.ar_and_l(Spec.arrived(order, Nat.add(c, L)),
          p4_all_arr(p, 1n+Nat.add(c, L), order), harr),
        hltc)
      %Equal.sym(Spec.Sum, Impl.slot_at(Impl.arrive(order, ws, L), c), Spec.Part{Nat.add(c, L)}, hs) : {Impl.finish.go(p, 1n+c, Spec.Add{v, _}, Impl.arrive(order, ws, L)) == p4_asc(p, 1n+Nat.add(c, L), Spec.Add{v, Spec.Part{Nat.add(c, L)}}) : Spec.Sum}
      p4_fin(p, 1n+c, Spec.Add{v, Spec.Part{Nat.add(c, L)}}, order, ws, L, hall,
        Arith.ar_and_r(Spec.arrived(order, Nat.add(c, L)),
          p4_all_arr(p, 1n+Nat.add(c, L), order), harr),
        Equal.trans(Bool, Nat.is_le(Nat.add(p, 1n+c), List.length(&2, Spec.Sum, ws)),
          Nat.is_le(1n+Nat.add(p, c), List.length(&2, Spec.Sum, ws)), True{},
          Equal.cong(Nat, Bool, z => Nat.is_le(z, List.length(&2, Spec.Sum, ws)),
            Nat.add(p, 1n+c), 1n+Nat.add(p, c), Arith.ar_add_succ_r(p, c)),
          hlen))

# ---- all_arrived: every touching block below the count has arrived ----

def p4_lt_zero(b: Nat, h: {Nat.is_lt(b, 0n) == True{} : Bool}) -> Empty:
  match b:
    case 0n:
      Arith.ar_false_true(h)
    case 1n+p:
      Arith.ar_false_true(h)

def p4_not_f_t(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Arith.ar_true_false(h))

def p4_or_not(x: Bool, -y: Bool, hx: {x == True{} : Bool},
    h: {Bool.or(Bool.not(x), y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      Empty.absurd({y == True{} : Bool}, Arith.ar_false_true(hx))

def p4_arr_step(x: Bool, +b: Nat, +c: Nat, +order: List<&2, Nat>, +g: Nat, +KT: Nat,
    +I: Nat, +G: Nat, hx: {Nat.is_lt(b, c) == x : Bool},
    hm: {Nat.is_le(b, c) == True{} : Bool},
    ht: {Spec.touches(b, g, KT, I, G) == True{} : Bool},
    hr: {Bool.or(Bool.not(Spec.touches(c, g, KT, I, G)), Spec.arrived(order, c)) == True{}
      : Bool},
    ih: {Nat.is_lt(b, c) == True{} : Bool} -> {Spec.arrived(order, b) == True{} : Bool})
  -> {Spec.arrived(order, b) == True{} : Bool}:
  match x:
    case True{}:
      ih(hx)
    case False{}:
      +e = Arith.ar_le_antisym(c, b,
        p4_not_f_t(Nat.is_le(c, b),
          Equal.trans(Bool, Bool.not(Nat.is_le(c, b)), Nat.is_lt(b, c), False{},
            Equal.sym(Bool, Nat.is_lt(b, c), Bool.not(Nat.is_le(c, b)),
              Arith.ar_lt_not_le(b, c)),
            hx)),
        hm)
      %e : {Spec.arrived(order, _) == True{} : Bool}
      p4_or_not(Spec.touches(c, g, KT, I, G), Spec.arrived(order, c),
        Equal.trans(Bool, Spec.touches(c, g, KT, I, G), Spec.touches(b, g, KT, I, G), True{},
          Equal.cong(Nat, Bool, z => Spec.touches(z, g, KT, I, G), c, b, e), ht),
        hr)

def p4_arr(+count: Nat, +order: List<&2, Nat>, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +b: Nat, +h: {Spec.all_arrived(count, order, g, KT, I, G) == True{} : Bool},
    hb: {Nat.is_lt(b, count) == True{} : Bool},
    +ht: {Spec.touches(b, g, KT, I, G) == True{} : Bool})
  -> {Spec.arrived(order, b) == True{} : Bool}:
  match count:
    case 0n:
      Empty.absurd({Spec.arrived(order, b) == True{} : Bool}, p4_lt_zero(b, hb))
    case 1n+c:
      p4_arr_step(Nat.is_lt(b, c), b, c, order, g, KT, I, G, {==},
        Equal.trans(Bool, Nat.is_le(b, c), Nat.is_lt(b, 1n+c), True{},
          Equal.sym(Bool, Nat.is_lt(b, 1n+c), Nat.is_le(1n+b, 1n+c),
            Arith.ar_lt_succ_le(b, 1n+c)),
          hb),
        ht,
        Arith.ar_and_r(Spec.all_arrived(c, order, g, KT, I, G),
          Bool.or(Bool.not(Spec.touches(c, g, KT, I, G)), Spec.arrived(order, c)), h),
        hc => p4_arr(c, order, g, KT, I, G, b,
          Arith.ar_and_l(Spec.all_arrived(c, order, g, KT, I, G),
            Bool.or(Bool.not(Spec.touches(c, g, KT, I, G)), Spec.arrived(order, c)), h),
          hc, ht))

# ---- the law's context: touches(b) == b in [b_lo, b_hi] ----

def p4_fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def p4_snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

def p4_ct(+mats: Nat, +n: Nat, +k: Nat, +G: Nat, +g: Nat, +b: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool})
  -> {Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
    p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), b) : Bool}:
  p4_fst({Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
      p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
        Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), b) : Bool},
    {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool} &
    {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool},
    Laws.contributors_contiguous(mats, n, k, G, g, b, grid, shaped, fits, group))

def p4_cc23(+mats: Nat, +n: Nat, +k: Nat, +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool})
  -> {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool} &
    {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool}:
  p4_snd({Spec.touches(0n, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
      p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
        Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), 0n) : Bool},
    {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool} &
    {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool},
    Laws.contributors_contiguous(mats, n, k, G, g, 0n, grid, shaped, fits, group))

# b_lo <= b_hi
def p4_hLH(+mats: Nat, +n: Nat, +k: Nat, +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool})
  -> {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool}:
  p4_fst({Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool},
    {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool},
    p4_cc23(mats, n, k, G, g, grid, shaped, fits, group))

# b_hi < G
def p4_hHG(+mats: Nat, +n: Nat, +k: Nat, +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool})
  -> {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool}:
  p4_snd({Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool},
    {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool},
    p4_cc23(mats, n, k, G, g, grid, shaped, fits, group))

def p4_conv_fold(+left: Nat, +b: Nat, +acc: Maybe<&2, Spec.Sum>, +mats: Nat, +n: Nat,
    +k: Nat, +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool})
  -> {Spec.fold_touching(left, b, g, Impl.kt(k), Impl.total(mats, n, k), G, acc) ==
    p4_rng(left, b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), acc) : Maybe<&2, Spec.Sum>}:
  match left:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Spec.Sum>,
        Spec.fold_touching(p, 1n+b, g, Impl.kt(k), Impl.total(mats, n, k), G,
          Spec.fold_step(Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G), b, acc)),
        p4_rng(p, 1n+b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Spec.fold_step(Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G), b, acc)),
        p4_rng(p, 1n+b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Spec.fold_step(p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
            Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), b), b, acc)),
        p4_conv_fold(p, 1n+b,
          Spec.fold_step(Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G), b, acc),
          mats, n, k, G, g, grid, shaped, fits, group),
        Equal.cong(Bool, Maybe<&2, Spec.Sum>,
          z => p4_rng(p, 1n+b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
            Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), Spec.fold_step(z, b, acc)),
          Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G),
          p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
            Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), b),
          p4_ct(mats, n, k, G, g, b, grid, shaped, fits, group)))

def p4_conv_ge(+order: List<&2, Nat>, +mats: Nat, +n: Nat, +k: Nat, +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool},
    +h: {Spec.all_touch(order, g, Impl.kt(k), Impl.total(mats, n, k), G) == True{} : Bool})
  -> {p4_all_ge(order, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{}
    : Bool}:
  match order:
    case Nil{}:
      {==}
    case +a <> rest:
      +hin = Equal.trans(Bool,
        p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), a),
        Spec.touches(a, g, Impl.kt(k), Impl.total(mats, n, k), G), True{},
        Equal.sym(Bool, Spec.touches(a, g, Impl.kt(k), Impl.total(mats, n, k), G),
          p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
            Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), a),
          p4_ct(mats, n, k, G, g, a, grid, shaped, fits, group)),
        Arith.ar_and_l(Spec.touches(a, g, Impl.kt(k), Impl.total(mats, n, k), G),
          Spec.all_touch(rest, g, Impl.kt(k), Impl.total(mats, n, k), G), h))
      Arith.ar_and_intro(
        Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), a),
        p4_all_ge(rest, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)),
        Arith.ar_and_l(Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), a),
          Nat.is_le(a, Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)), hin),
        p4_conv_ge(rest, mats, n, k, G, g, grid, shaped, fits, group,
          Arith.ar_and_r(Spec.touches(a, g, Impl.kt(k), Impl.total(mats, n, k), G),
            Spec.all_touch(rest, g, Impl.kt(k), Impl.total(mats, n, k), G), h)))

# Blocks b0 .. b0 + a - 1 inside [b_lo, b_hi] have all arrived.
def p4_mk_arr(+a: Nat, +b0: Nat, +order: List<&2, Nat>, +mats: Nat, +n: Nat, +k: Nat,
    +G: Nat, +g: Nat,
    +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, k) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool},
    +group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool},
    +hc: {Spec.all_arrived(G, order, g, Impl.kt(k), Impl.total(mats, n, k), G) == True{}
      : Bool},
    +hL: {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), b0) == True{} : Bool},
    +hH: {Nat.is_le(Nat.add(a, b0), 1n+Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G))
      == True{} : Bool})
  -> {p4_all_arr(a, b0, order) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +hHG = p4_hHG(mats, n, k, G, g, grid, shaped, fits, group)
      +hbH = Arith.ar_le_trans(b0, Nat.add(p, b0),
        Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), Arith.ar_le_add_l(p, b0), hH)
      +ht = Equal.trans(Bool, Spec.touches(b0, g, Impl.kt(k), Impl.total(mats, n, k), G),
        p4_in(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
          Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), b0), True{},
        p4_ct(mats, n, k, G, g, b0, grid, shaped, fits, group),
        Arith.ar_and_intro(Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), b0),
          Nat.is_le(b0, Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)), hL, hbH))
      Arith.ar_and_intro(Spec.arrived(order, b0), p4_all_arr(p, 1n+b0, order),
        p4_arr(G, order, g, Impl.kt(k), Impl.total(mats, n, k), G, b0, hc,
          Arith.ar_le_lt_trans(b0, Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G,
            hbH, hHG),
          ht),
        p4_mk_arr(p, 1n+b0, order, mats, n, k, G, g, grid, shaped, fits, group, hc,
          Arith.ar_le_trans(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), b0, 1n+b0,
            hL, p4_le_succ(b0)),
          Equal.trans(Bool,
            Nat.is_le(Nat.add(p, 1n+b0), 1n+Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)),
            Nat.is_le(1n+Nat.add(p, b0), 1n+Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)),
            True{},
            Equal.cong(Nat, Bool,
              z => Nat.is_le(z, 1n+Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)),
              Nat.add(p, 1n+b0), 1n+Nat.add(p, b0), Arith.ar_add_succ_r(p, b0)),
            hH)))

def p4_sub1(+d: Nat) -> {Nat.sub(Nat.add(d, 1n), 1n) == d : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(d, 1n), 1n), Nat.sub(Nat.add(1n, d), 1n), d,
    Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.add(d, 1n), Nat.add(1n, d),
      Arith.ar_add_comm(d, 1n)),
    Arith.ar_sub_zero_r(d))

# ---- reduction_order ----

def Laws.reduction_order(mats, n, k, G, g, order, ws, grid, shaped, fits, group, room,
    touching, complete):
  +gr = grid
  +sh = shaped
  +fi = fits
  +gp = group
  +rm = room
  +hLH = p4_hLH(mats, n, k, G, g, gr, sh, fi, gp)
  +hHG = p4_hHG(mats, n, k, G, g, gr, sh, fi, gp)
  +L = Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)
  +H = Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)
  +d = Nat.sub(H, L)
  +W = Impl.arrive(order, ws, L)
  +hall = p4_conv_ge(order, mats, n, k, G, g, gr, sh, fi, gp, touching)
  +harr = p4_mk_arr(1n+d, L, order, mats, n, k, G, g, gr, sh, fi, gp, complete,
    Arith.ar_le_refl(L),
    Equal.trans(Bool, Nat.is_le(Nat.add(d, L), H), Nat.is_le(H, H), True{},
      Equal.cong(Nat, Bool, z => Nat.is_le(z, H), Nat.add(d, L), H,
        Equal.trans(Nat, Nat.add(d, L), Nat.add(L, d), H, Arith.ar_add_comm(d, L),
          Arith.ar_sub_add(H, L, hLH))),
      Arith.ar_le_refl(H)))
  +hs0 = p4_slot_c(0n, order, ws, L, hall,
    Arith.ar_and_l(Spec.arrived(order, L), p4_all_arr(d, 1n+L, order), harr),
    Equal.trans(Bool, Nat.is_lt(0n, List.length(&2, Spec.Sum, ws)),
      Nat.is_le(1n, List.length(&2, Spec.Sum, ws)), True{},
      Arith.ar_lt_succ_le(0n, List.length(&2, Spec.Sum, ws)),
      Arith.ar_le_trans(1n, Nat.add(d, 1n), List.length(&2, Spec.Sum, ws),
        Arith.ar_le_add_l(d, 1n), rm)))
  %Equal.sym(Nat, Nat.sub(Nat.add(d, 1n), 1n), d, p4_sub1(d)) : {Some{Impl.finish.go(_, 1n, Impl.slot_at(W, 0n), W)} == Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G) : Maybe<&2, Spec.Sum>}
  %Equal.sym(Spec.Sum, Impl.slot_at(W, 0n), Spec.Part{L}, hs0) : {Some{Impl.finish.go(d, 1n, _, W)} == Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G) : Maybe<&2, Spec.Sum>}
  Equal.trans(Maybe<&2, Spec.Sum>, Some{Impl.finish.go(d, 1n, Spec.Part{L}, W)},
    Some{p4_asc(d, 1n+L, Spec.Part{L})},
    Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G),
    Equal.cong(Spec.Sum, Maybe<&2, Spec.Sum>, z => Some{z},
      Impl.finish.go(d, 1n, Spec.Part{L}, W), p4_asc(d, 1n+L, Spec.Part{L}),
      p4_fin(d, 1n, Spec.Part{L}, order, ws, L, hall,
        Arith.ar_and_r(Spec.arrived(order, L), p4_all_arr(d, 1n+L, order), harr), rm)),
    Equal.sym(Maybe<&2, Spec.Sum>, Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G),
      Some{p4_asc(d, 1n+L, Spec.Part{L})},
      Equal.trans(Maybe<&2, Spec.Sum>,
        Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G),
        p4_rng(G, 0n, L, H, None{}), Some{p4_asc(d, 1n+L, Spec.Part{L})},
        p4_conv_fold(G, 0n, None{}, mats, n, k, G, g, gr, sh, fi, gp),
        p4_whole(G, L, H, hLH, hHG))))
