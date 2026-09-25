# Proofs of the ext 5106 b/a GEMV laws (gdn_ba_ksplit_laws.bend) about the Bend model gdn_ba_ksplit.bend.
# Structural evidence only: no unsafe definitions, axioms, holes or foreign proof code. Finite facts
# (lane tree, event orders) are decided by the checker's evaluation; the index and order laws are
# proven for symbolic k2, h, H, rows and threads from the Nat library of gemm_m16_partition_proof.bend,
# so no proof expands the served 2560-element rows. Every def precedes its uses.
import Base
import ./gdn_ba_ksplit.bend as Impl
import ./gdn_ba_ksplit_spec.bend as Spec
import ./gdn_ba_ksplit_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def kb_fst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def kb_snd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

# ==== (2) warp tree and lane coverage: decided by evaluation (w, s, ab, k2, h, H stay symbolic) ====

def Laws.warp_tree(w, s, ab, k2, h, H):
  {==}

def Laws.tree_lanes_once():
  {==}

# ==== (3) barriers: finite case split over KS in {1, 2} and the block role ====

def kb_bar12(+ks: Nat, +own: Bool, k1: {Nat.is_lt(0n, ks) == True{} : Bool}, k3: {Nat.is_lt(ks, 3n) == True{} : Bool})
  -> {Spec.fenced(Impl.PartW{}, Impl.PartR{}, Impl.prog(ks, own)) == True{} : Bool} &
  {Spec.fenced(Impl.PartR{}, Impl.Dot2W{}, Impl.prog(ks, own)) == True{} : Bool} &
  {Spec.count(Impl.PartW{}, Impl.prog(ks, own)) == 1n : Nat} &
  {Spec.count(Impl.PartR{}, Impl.prog(ks, own)) == 1n : Nat}:
  match ks own:
    case 0n _:
      Empty.absurd({Spec.fenced(Impl.PartW{}, Impl.PartR{}, Impl.prog(0n, own)) == True{} : Bool} &
        {Spec.fenced(Impl.PartR{}, Impl.Dot2W{}, Impl.prog(0n, own)) == True{} : Bool} &
        {Spec.count(Impl.PartW{}, Impl.prog(0n, own)) == 1n : Nat} &
        {Spec.count(Impl.PartR{}, Impl.prog(0n, own)) == 1n : Nat}, Ar.ar_false_true(k1))
    case 1n True{}:
      ({==}, {==}, {==}, {==})
    case 1n False{}:
      ({==}, {==}, {==}, {==})
    case 2n True{}:
      ({==}, {==}, {==}, {==})
    case 2n False{}:
      ({==}, {==}, {==}, {==})
    case 3n+q _:
      Empty.absurd({Spec.fenced(Impl.PartW{}, Impl.PartR{}, Impl.prog(3n+q, own)) == True{} : Bool} &
        {Spec.fenced(Impl.PartR{}, Impl.Dot2W{}, Impl.prog(3n+q, own)) == True{} : Bool} &
        {Spec.count(Impl.PartW{}, Impl.prog(3n+q, own)) == 1n : Nat} &
        {Spec.count(Impl.PartR{}, Impl.prog(3n+q, own)) == 1n : Nat},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, Ar.ar_h_lt_zero(q)), k3)))

def Laws.barrier_ksplit(ks, own, k1, k3):
  kb_bar12(ks, own, k1, k3)

def Laws.barrier_ks0(own):
  match own:
    case True{}:
      {==}
    case False{}:
      {==}

# ==== (4) launcher fallback ====

def kb_pick_t(+c: Bool, +x: Nat, +y: Nat, e: {c == True{} : Bool}) -> {Impl.pick(c, x, y) == x : Nat}:
  %Equal.sym(Bool, c, True{}, e) : {Impl.pick(_, x, y) == x : Nat}
  {==}

def kb_pick_f(+c: Bool, +x: Nat, +y: Nat, e: {c == False{} : Bool}) -> {Impl.pick(c, x, y) == y : Nat}:
  %Equal.sym(Bool, c, False{}, e) : {Impl.pick(_, x, y) == y : Nat}
  {==}

def Laws.fallback_ks0(ks, S, k, big):
  kb_pick_t(Bool.or(Nat.is_lt(8n, S), Nat.is_lt(2560n, Nat.div(k, 2n))), 0n, ks, big)

# a <= b gives (b < a) == False
def kb_lt_false(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(b, a), Bool.not(Nat.is_le(a, b)), Ar.ar_lt_not_le(b, a)) : {_ == False{} : Bool}
  %Equal.sym(Bool, Nat.is_le(a, b), True{}, h) : {Bool.not(_) == False{} : Bool}
  {==}

def Laws.covered_ks(ks, S, k, s8, k2):
  +f1 = kb_lt_false(S, 8n, s8)
  +f2 = kb_lt_false(Nat.div(k, 2n), 2560n, k2)
  +c = Equal.trans(Bool, Bool.or(Nat.is_lt(8n, S), Nat.is_lt(2560n, Nat.div(k, 2n))),
    Bool.or(False{}, Nat.is_lt(2560n, Nat.div(k, 2n))), False{},
    Equal.cong(Bool, Bool, x => Bool.or(x, Nat.is_lt(2560n, Nat.div(k, 2n))), Nat.is_lt(8n, S), False{}, f1),
    f2)
  kb_pick_f(Bool.or(Nat.is_lt(8n, S), Nat.is_lt(2560n, Nat.div(k, 2n))), 0n, ks, c)

# ==== (1) element ownership ====

# warp * 32 + lane of thread t is t
def kb_wl(+t: Nat) -> {Nat.add(Nat.mul(Nat.div(t, 32n), 32n), Nat.mod(t, 32n)) == t : Nat}:
  Ar.ard_dm_eq(t, 32n, {==})

# ks_j(t, i) == t + 512 i
def kb_j(+t: Nat, +i: Nat) -> {Impl.ks_j(t, i) == Nat.add(t, Nat.mul(i, 512n)) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(i, 512n)),
    Nat.add(Nat.mul(Nat.div(t, 32n), 32n), Nat.mod(t, 32n)), t, kb_wl(t))

# ks_j(t, i) == i * 512 + t (the divmod form)
def kb_jdm(+t: Nat, +i: Nat) -> {Impl.ks_j(t, i) == Nat.add(Nat.mul(i, 512n), t) : Nat}:
  Equal.trans(Nat, Impl.ks_j(t, i), Nat.add(t, Nat.mul(i, 512n)), Nat.add(Nat.mul(i, 512n), t),
    kb_j(t, i), Ar.ar_add_comm(t, Nat.mul(i, 512n)))

def Laws.own_into(t, i, tr, ir):
  +tr1 = tr
  +e = kb_jdm(t, i)
  +dv = kb_fst({Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n) == i : Nat},
    {Nat.mod(Nat.add(Nat.mul(i, 512n), t), 512n) == t : Nat}, Ar.ar_div_unique(i, t, 512n, tr1))
  +md = kb_snd({Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n) == i : Nat},
    {Nat.mod(Nat.add(Nat.mul(i, 512n), t), 512n) == t : Nat}, Ar.ar_div_unique(i, t, 512n, tr1))
  # i * 512 + t < 5 * 512: (i * 512 + t) / 512 == i < 5
  +lt = Ar.ard_tr(Nat.is_lt(Nat.add(Nat.mul(i, 512n), t), Nat.mul(5n, 512n)),
    Nat.is_lt(Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n), 5n),
    Equal.sym(Bool, Nat.is_lt(Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n), 5n),
      Nat.is_lt(Nat.add(Nat.mul(i, 512n), t), Nat.mul(5n, 512n)),
      Ar.ar_div_lt(5n, Nat.add(Nat.mul(i, 512n), t), 512n, {==})),
    Equal.trans(Bool, Nat.is_lt(Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n), 5n), Nat.is_lt(i, 5n), True{},
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, 5n), Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n), i, dv), ir))
  (kb_j(t, i),
   Equal.trans(Bool, Nat.is_lt(Impl.ks_j(t, i), 2560n), Nat.is_lt(Nat.add(Nat.mul(i, 512n), t), 2560n), True{},
     Equal.cong(Nat, Bool, z => Nat.is_lt(z, 2560n), Impl.ks_j(t, i), Nat.add(Nat.mul(i, 512n), t), e), lt),
   Equal.trans(Nat, Spec.owner_t(Impl.ks_j(t, i)), Nat.mod(Nat.add(Nat.mul(i, 512n), t), 512n), t,
     Equal.cong(Nat, Nat, z => Nat.mod(z, 512n), Impl.ks_j(t, i), Nat.add(Nat.mul(i, 512n), t), e), md),
   Equal.trans(Nat, Spec.owner_i(Impl.ks_j(t, i)), Nat.div(Nat.add(Nat.mul(i, 512n), t), 512n), i,
     Equal.cong(Nat, Nat, z => Nat.div(z, 512n), Impl.ks_j(t, i), Nat.add(Nat.mul(i, 512n), t), e), dv))

def Laws.own_onto(j, jr):
  +t = Nat.mod(j, 512n)
  +i = Nat.div(j, 512n)
  (Ar.ard_dm_lt(j, 512n, {==}),
   Ar.ard_tr(Nat.is_lt(i, 5n), Nat.is_lt(j, Nat.mul(5n, 512n)), Ar.ar_div_lt(5n, j, 512n, {==}), jr),
   Equal.trans(Nat, Impl.ks_j(t, i), Nat.add(Nat.mul(i, 512n), t), j, kb_jdm(t, i), Ar.ard_dm_eq(j, 512n, {==})))

# ==== (2, 3) partial slots ====

def kb_m16(+w: Nat) -> {Nat.mul(Nat.mul(w, 2n), 8n) == Nat.mul(w, 16n) : Nat}:
  Ar.ar_mul_assoc(w, 2n, 8n)

# the kernel's slot expression (writer and reader share it) is the reference slot
def kb_slot(+w: Nat, +s: Nat, +ab: Nat)
  -> {Nat.add(Nat.add(Nat.mul(Nat.mul(w, 2n), 8n), Nat.mul(ab, 8n)), s) == Spec.slot(w, s, ab) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(Nat.add(z, Nat.mul(ab, 8n)), s), Nat.mul(Nat.mul(w, 2n), 8n), Nat.mul(w, 16n), kb_m16(w))

# decode of 16 w + r, r = c8 + s < 16, c8 = 8 ab for a concrete ab, the slot also written q8 * 8 + s
def kb_dec(+w: Nat, +s: Nat, +c8: Nat, +abv: Nat, +q8: Nat,
    +rlt: {Nat.is_lt(Nat.add(c8, s), 16n) == True{} : Bool},
    +s8: {Nat.is_lt(s, 8n) == True{} : Bool},
    dab: {Nat.div(Nat.add(c8, s), 8n) == abv : Nat},
    q8e: {Nat.add(Nat.add(Nat.mul(w, 16n), c8), s) == Nat.add(Nat.mul(q8, 8n), s) : Nat})
  -> {Nat.div(Nat.add(Nat.add(Nat.mul(w, 16n), c8), s), 16n) == w : Nat} &
  {Nat.div(Nat.mod(Nat.add(Nat.add(Nat.mul(w, 16n), c8), s), 16n), 8n) == abv : Nat} &
  {Nat.mod(Nat.add(Nat.add(Nat.mul(w, 16n), c8), s), 8n) == s : Nat}:
  +M = Nat.mul(w, 16n)
  +X = Nat.add(Nat.add(M, c8), s)
  +r = Nat.add(c8, s)
  +asc = Ar.ar_add_assoc(M, c8, s)
  +d16 = kb_fst({Nat.div(Nat.add(Nat.mul(w, 16n), r), 16n) == w : Nat}, {Nat.mod(Nat.add(Nat.mul(w, 16n), r), 16n) == r : Nat},
    Ar.ar_div_unique(w, r, 16n, rlt))
  +m16 = kb_snd({Nat.div(Nat.add(Nat.mul(w, 16n), r), 16n) == w : Nat}, {Nat.mod(Nat.add(Nat.mul(w, 16n), r), 16n) == r : Nat},
    Ar.ar_div_unique(w, r, 16n, rlt))
  +mr = Equal.trans(Nat, Nat.mod(X, 16n), Nat.mod(Nat.add(M, r), 16n), r,
    Equal.cong(Nat, Nat, z => Nat.mod(z, 16n), X, Nat.add(M, r), asc), m16)
  +m8 = kb_snd({Nat.div(Nat.add(Nat.mul(q8, 8n), s), 8n) == q8 : Nat}, {Nat.mod(Nat.add(Nat.mul(q8, 8n), s), 8n) == s : Nat},
    Ar.ar_div_unique(q8, s, 8n, s8))
  (Equal.trans(Nat, Nat.div(X, 16n), Nat.div(Nat.add(M, r), 16n), w,
     Equal.cong(Nat, Nat, z => Nat.div(z, 16n), X, Nat.add(M, r), asc), d16),
   Equal.trans(Nat, Nat.div(Nat.mod(X, 16n), 8n), Nat.div(r, 8n), abv,
     Equal.cong(Nat, Nat, z => Nat.div(z, 8n), Nat.mod(X, 16n), r, mr), dab),
   Equal.trans(Nat, Nat.mod(X, 8n), Nat.mod(Nat.add(Nat.mul(q8, 8n), s), 8n), s,
     Equal.cong(Nat, Nat, z => Nat.mod(z, 8n), X, Nat.add(Nat.mul(q8, 8n), s), q8e), m8))

def kb_dec_ab(+w: Nat, +s: Nat, +ab: Nat, +s8: {Nat.is_lt(s, 8n) == True{} : Bool}, a2: {Nat.is_lt(ab, 2n) == True{} : Bool})
  -> {Impl.dec_w(Spec.slot(w, s, ab)) == w : Nat} &
  {Impl.dec_ab(Spec.slot(w, s, ab)) == ab : Nat} &
  {Impl.dec_s(Spec.slot(w, s, ab)) == s : Nat}:
  match ab:
    case 0n:
      +M = Nat.mul(w, 16n)
      +W2 = Nat.mul(w, 2n)
      +q8e = Equal.cong(Nat, Nat, z => Nat.add(z, s), Nat.add(M, 0n), Nat.mul(W2, 8n),
        Equal.trans(Nat, Nat.add(M, 0n), M, Nat.mul(W2, 8n), Ar.ar_add_zero_r(M), Equal.sym(Nat, Nat.mul(W2, 8n), M, kb_m16(w))))
      +d0 = kb_fst({Nat.div(Nat.add(Nat.mul(0n, 8n), s), 8n) == 0n : Nat}, {Nat.mod(Nat.add(Nat.mul(0n, 8n), s), 8n) == s : Nat},
        Ar.ar_div_unique(0n, s, 8n, s8))
      kb_dec(w, s, 0n, 0n, W2, Ar.ar_lt_trans(s, 8n, 16n, s8, {==}), s8, d0, q8e)
    case 1n+z1:
      match z1:
        case 0n:
          +M = Nat.mul(w, 16n)
          +W2 = Nat.mul(w, 2n)
          +mal = Ar.ar_mul_add_l(W2, 1n, 8n)
          +me = Equal.trans(Nat, Nat.mul(Nat.add(W2, 1n), 8n), Nat.add(Nat.mul(W2, 8n), 8n), Nat.add(M, 8n),
            mal, Equal.cong(Nat, Nat, z => Nat.add(z, 8n), Nat.mul(W2, 8n), M, kb_m16(w)))
          +q8e = Equal.cong(Nat, Nat, z => Nat.add(z, s), Nat.add(M, 8n), Nat.mul(Nat.add(W2, 1n), 8n),
            Equal.sym(Nat, Nat.mul(Nat.add(W2, 1n), 8n), Nat.add(M, 8n), me))
          +d1 = kb_fst({Nat.div(Nat.add(Nat.mul(1n, 8n), s), 8n) == 1n : Nat}, {Nat.mod(Nat.add(Nat.mul(1n, 8n), s), 8n) == s : Nat},
            Ar.ar_div_unique(1n, s, 8n, s8))
          kb_dec(w, s, 8n, 1n, Nat.add(W2, 1n), s8, s8, d1, q8e)
        case 1n+q:
          Empty.absurd({Impl.dec_w(Spec.slot(w, s, 2n+q)) == w : Nat} &
            {Impl.dec_ab(Spec.slot(w, s, 2n+q)) == 2n+q : Nat} &
            {Impl.dec_s(Spec.slot(w, s, 2n+q)) == s : Nat},
            Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{},
              Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, Ar.ar_h_lt_zero(q)), a2)))

def kb_pack(+w: Nat, +s: Nat, +ab: Nat,
    d: {Impl.dec_w(Spec.slot(w, s, ab)) == w : Nat} &
      {Impl.dec_ab(Spec.slot(w, s, ab)) == ab : Nat} &
      {Impl.dec_s(Spec.slot(w, s, ab)) == s : Nat})
  -> {Impl.wslot(w, s, ab) == Spec.slot(w, s, ab) : Nat} &
  {Impl.rslot(w, s, ab) == Spec.slot(w, s, ab) : Nat} &
  {Impl.dec_w(Spec.slot(w, s, ab)) == w : Nat} &
  {Impl.dec_ab(Spec.slot(w, s, ab)) == ab : Nat} &
  {Impl.dec_s(Spec.slot(w, s, ab)) == s : Nat}:
  (a1, rest) = d
  (kb_slot(w, s, ab), kb_slot(w, s, ab), a1, rest)

def Laws.slot_decode(w, s, ab, s8, a2):
  kb_pack(w, s, ab, kb_dec_ab(w, s, ab, s8, a2))

# ==== (2) the per-thread chain: projecting the kernel's per-row accumulator arrays onto one task ====

# one row's update of the i loop is a conditional fma pair on that row's accumulator
def kb_a0(c: Bool, +s0: Nat, +j: Nat, +k2: Nat, +h: Nat, +H: Nat, +ab: Nat, +b: Impl.Ex, +a: Impl.Ex, +R: List<&2, Impl.P>,
    +R2: List<&2, Impl.P>)
  -> {Impl.get_p(Impl.upd(c, s0, j, k2, h, H, b, a) <> R, 0n, ab) ==
    Spec.chain_el(c, j, s0, Spec.wrow(ab, h, H), k2, Impl.get_p(Impl.P{b, a} <> R2, 0n, ab)) : Impl.Ex}:
  match c ab:
    case True{} 0n:
      {==}
    case True{} 1n+z:
      {==}
    case False{} 0n:
      {==}
    case False{} 1n+z:
      {==}

# srows: entry n of the list (row s0 + n) is its old value under the conditional fma pair of that row
def kb_a(xs: List<&2, Impl.P>, +n: Nat, +ab: Nat, +s0: Nat, +S: Nat, +j: Nat, +k2: Nat, +h: Nat, +H: Nat,
    nl: {Nat.is_lt(n, List.length(&2, Impl.P, xs)) == True{} : Bool})
  -> {Impl.get_p(Impl.srows(xs, s0, S, j, k2, h, H), n, ab) ==
    Spec.chain_el(Nat.is_lt(Nat.add(n, s0), S), j, Nat.add(n, s0), Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)) : Impl.Ex}:
  match xs n:
    case Nil{} _:
      Empty.absurd({Impl.get_p(Impl.srows(Nil{}, s0, S, j, k2, h, H), n, ab) ==
        Spec.chain_el(Nat.is_lt(Nat.add(n, s0), S), j, Nat.add(n, s0), Spec.wrow(ab, h, H), k2, Impl.get_p(Nil{}, n, ab)) : Impl.Ex},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(n, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, Ar.ar_h_lt_zero(n)), nl)))
    case (Impl.P{+b, +a} <> +rest) 0n:
      kb_a0(Nat.is_lt(s0, S), s0, j, k2, h, H, ab, b, a, Impl.srows(rest, 1n+s0, S, j, k2, h, H), rest)
    case (Impl.P{b, a} <> +rest) 1n+m:
      +ih = kb_a(rest, m, ab, 1n+s0, S, j, k2, h, H, nl)
      +sh = Ar.ar_add_succ_r(m, s0)
      %sh : {Impl.get_p(Impl.srows(rest, 1n+s0, S, j, k2, h, H), m, ab) ==
        Spec.chain_el(Nat.is_lt(_, S), j, _, Spec.wrow(ab, h, H), k2, Impl.get_p(rest, m, ab)) : Impl.Ex}
      ih

def kb_len_srows(xs: List<&2, Impl.P>, +s0: Nat, +S: Nat, +j: Nat, +k2: Nat, +h: Nat, +H: Nat)
  -> {List.length(&2, Impl.P, Impl.srows(xs, s0, S, j, k2, h, H)) == List.length(&2, Impl.P, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Impl.P{b, a} <> +rest:
      %Equal.sym(Nat, List.length(&2, Impl.P, Impl.srows(rest, 1n+s0, S, j, k2, h, H)), List.length(&2, Impl.P, rest),
        kb_len_srows(rest, 1n+s0, S, j, k2, h, H)) : {1n+_ == 1n+List.length(&2, Impl.P, rest) : Nat}
      {==}

def kb_len_ig(c: Bool, +j: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, xs: List<&2, Impl.P>)
  -> {List.length(&2, Impl.P, Impl.iguard(c, j, S, k2, h, H, xs)) == List.length(&2, Impl.P, xs) : Nat}:
  match c:
    case True{}:
      kb_len_srows(xs, 0n, S, j, k2, h, H)
    case False{}:
      {==}

# iguard: the guarded update (j < k2) of every row, projected on row n < S
def kb_b(c: Bool, +j: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, +xs: List<&2, Impl.P>, +n: Nat, +ab: Nat,
    nl: {Nat.is_lt(n, List.length(&2, Impl.P, xs)) == True{} : Bool}, ns: {Nat.is_lt(n, S) == True{} : Bool})
  -> {Impl.get_p(Impl.iguard(c, j, S, k2, h, H, xs), n, ab) ==
    Spec.chain_el(c, j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)) : Impl.Ex}:
  match c:
    case True{}:
      +a0 = kb_a(xs, n, ab, 0n, S, j, k2, h, H, nl)
      +z0 = Ar.ar_add_zero_r(n)
      %ns : {Impl.get_p(Impl.srows(xs, 0n, S, j, k2, h, H), n, ab) ==
        Spec.chain_el(_, j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)) : Impl.Ex}
      %z0 : {Impl.get_p(Impl.srows(xs, 0n, S, j, k2, h, H), n, ab) ==
        Spec.chain_el(Nat.is_lt(_, S), j, _, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)) : Impl.Ex}
      a0
    case False{}:
      {==}

# ks_j(t, 1 + i) == ks_j(t, i) + 512
def kb_j_succ(+t: Nat, +i: Nat, +j: Nat, ej: {Impl.ks_j(t, i) == j : Nat})
  -> {Impl.ks_j(t, 1n+i) == Nat.add(j, 512n) : Nat}:
  +A = Nat.add(Nat.mul(Nat.div(t, 32n), 32n), Nat.mod(t, 32n))
  +B = Nat.mul(i, 512n)
  +c1 = Equal.cong(Nat, Nat, z => Nat.add(A, z), Nat.add(512n, B), Nat.add(B, 512n), Ar.ar_add_comm(512n, B))
  +c2 = Equal.sym(Nat, Nat.add(Nat.add(A, B), 512n), Nat.add(A, Nat.add(B, 512n)), Ar.ar_add_assoc(A, B, 512n))
  +c3 = Equal.cong(Nat, Nat, z => Nat.add(z, 512n), Nat.add(A, B), j, ej)
  Equal.trans(Nat, Nat.add(A, Nat.add(512n, B)), Nat.add(Nat.add(A, B), 512n), Nat.add(j, 512n),
    Equal.trans(Nat, Nat.add(A, Nat.add(512n, B)), Nat.add(A, Nat.add(B, 512n)), Nat.add(Nat.add(A, B), 512n), c1, c2), c3)

# the i loop, projected on row n < S: the reference chain from element j = ks_j(t, i) on
def kb_c(fuel: Nat, +i: Nat, +t: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, +xs: List<&2, Impl.P>, +n: Nat, +ab: Nat,
    +j: Nat, +ej: {Impl.ks_j(t, i) == j : Nat},
    +nl: {Nat.is_lt(n, List.length(&2, Impl.P, xs)) == True{} : Bool}, +ns: {Nat.is_lt(n, S) == True{} : Bool})
  -> {Impl.get_p(Impl.iloop(fuel, i, t, S, k2, h, H, xs), n, ab) ==
    Spec.chain_go(fuel, j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)) : Impl.Ex}:
  match fuel:
    case 0n:
      {==}
    case 1n+more:
      +c = Nat.is_lt(Impl.ks_j(t, i), k2)
      +xs2 = Impl.iguard(c, Impl.ks_j(t, i), S, k2, h, H, xs)
      +nl2 = Equal.trans(Bool, Nat.is_lt(n, List.length(&2, Impl.P, xs2)), Nat.is_lt(n, List.length(&2, Impl.P, xs)), True{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(n, z), List.length(&2, Impl.P, xs2), List.length(&2, Impl.P, xs),
          kb_len_ig(c, Impl.ks_j(t, i), S, k2, h, H, xs)), nl)
      +ih = kb_c(more, 1n+i, t, S, k2, h, H, xs2, n, ab, Nat.add(j, 512n), kb_j_succ(t, i, j, ej), nl2, ns)
      +bb = kb_b(c, Impl.ks_j(t, i), S, k2, h, H, xs, n, ab, nl, ns)
      # rewrite ks_j(t, i) to j inside the guarded fma pair
      +bj = Equal.trans(Impl.Ex, Impl.get_p(xs2, n, ab),
        Spec.chain_el(c, Impl.ks_j(t, i), n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)),
        Spec.chain_el(Nat.is_lt(j, k2), j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)), bb,
        Equal.cong(Nat, Impl.Ex, +z => Spec.chain_el(Nat.is_lt(z, k2), z, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)),
          Impl.ks_j(t, i), j, ej))
      Equal.trans(Impl.Ex, Impl.get_p(Impl.iloop(more, 1n+i, t, S, k2, h, H, xs2), n, ab),
        Spec.chain_go(more, Nat.add(j, 512n), n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs2, n, ab)),
        Spec.chain_go(more, Nat.add(j, 512n), n, Spec.wrow(ab, h, H), k2,
          Spec.chain_el(Nat.is_lt(j, k2), j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab))),
        ih,
        Equal.cong(Impl.Ex, Impl.Ex, v => Spec.chain_go(more, Nat.add(j, 512n), n, Spec.wrow(ab, h, H), k2, v),
          Impl.get_p(xs2, n, ab), Spec.chain_el(Nat.is_lt(j, k2), j, n, Spec.wrow(ab, h, H), k2, Impl.get_p(xs, n, ab)), bj))

def kb_zeros(n: Nat, +s: Nat, +ab: Nat) -> {Impl.get_p(Impl.zeros(n), s, ab) == Impl.Zero{} : Impl.Ex}:
  match n s:
    case 0n _:
      {==}
    case 1n+m 0n:
      match ab:
        case 0n:
          {==}
        case 1n+z:
          {==}
    case 1n+m 1n+q:
      kb_zeros(m, q, ab)

def kb_j0(+t: Nat) -> {Impl.ks_j(t, 0n) == t : Nat}:
  +A = Nat.add(Nat.mul(Nat.div(t, 32n), 32n), Nat.mod(t, 32n))
  Equal.trans(Nat, Nat.add(A, 0n), A, t, Ar.ar_add_zero_r(A), kb_wl(t))

def Laws.chain_row(t, S, s, ab, k2, h, H, sr, s8):
  +c = kb_c(5n, 0n, t, S, k2, h, H, Impl.zeros(8n), s, ab, t, kb_j0(t), s8, sr)
  %kb_zeros(8n, s, ab) : {Impl.acc(t, S, s, ab, k2, h, H) == Spec.chain_go(5n, t, s, Spec.wrow(ab, h, H), k2, _) : Impl.Ex}
  c

# ==== (2, 3) the reduction ====

# the lane values the kernel reduces are the reference chains
def kb_d(+fuel: Nat, +l: Nat, +w: Nat, +S: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat,
    +sr: {Nat.is_lt(s, S) == True{} : Bool}, +s8: {Nat.is_lt(s, 8n) == True{} : Bool})
  -> {Impl.wlanes(fuel, l, w, S, s, ab, k2, h, H) == Spec.clanes(fuel, l, w, s, ab, k2, h, H) : List<&2, Impl.Ex>}:
  match fuel:
    case 0n:
      {==}
    case 1n+more:
      +T = Nat.add(Nat.mul(w, 32n), l)
      +wl = Impl.wlanes(more, 1n+l, w, S, s, ab, k2, h, H)
      +cl = Spec.clanes(more, 1n+l, w, s, ab, k2, h, H)
      +av = Impl.acc(T, S, s, ab, k2, h, H)
      +cv = Spec.chain(T, s, ab, k2, h, H)
      Equal.trans(List<&2, Impl.Ex>, av <> wl, av <> cl, cv <> cl,
        Equal.cong(List<&2, Impl.Ex>, List<&2, Impl.Ex>, xs => av <> xs, wl, cl, kb_d(more, 1n+l, w, S, s, ab, k2, h, H, sr, s8)),
        Equal.cong(Impl.Ex, List<&2, Impl.Ex>, x => x <> cl, av, cv, Laws.chain_row(T, S, s, ab, k2, h, H, sr, s8)))

# a written slot reads back as the tree of its warp's lanes
def kb_sr(c: Bool, +q: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, e: {c == True{} : Bool})
  -> {Impl.smem_row(c, q, S, k2, h, H) ==
    Impl.tree(Impl.wlanes(32n, 0n, Impl.dec_w(q), S, Impl.dec_s(q), Impl.dec_ab(q), k2, h, H)) : Impl.Ex}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Impl.smem_row(False{}, q, S, k2, h, H) ==
        Impl.tree(Impl.wlanes(32n, 0n, Impl.dec_w(q), S, Impl.dec_s(q), Impl.dec_ab(q), k2, h, H)) : Impl.Ex}, Ar.ar_false_true(e))

def kb_sd(-A: Type, -B: Type, -C: Type, -D: Type, -E: Type, p: A & B & C & D & E) -> B & C & D & E:
  (x, rest) = p
  rest

# the partial thread s reads for warp w: the reference lane tree of warp w, task (s, b|a)
def kb_s(+w: Nat, +S: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat,
    +sr: {Nat.is_lt(s, S) == True{} : Bool}, +s8: {Nat.is_lt(s, 8n) == True{} : Bool}, +a2: {Nat.is_lt(ab, 2n) == True{} : Bool})
  -> {Impl.smem(Impl.rslot(w, s, ab), S, k2, h, H) == Spec.wtree(5n, 0n, w, s, ab, k2, h, H) : Impl.Ex}:
  +Q = Spec.slot(w, s, ab)
  +RQ = Impl.rslot(w, s, ab)
  -TA = {Impl.wslot(w, s, ab) == Q : Nat}
  -TB = {RQ == Q : Nat}
  -TC = {Impl.dec_w(Q) == w : Nat}
  -TD = {Impl.dec_ab(Q) == ab : Nat}
  -TE = {Impl.dec_s(Q) == s : Nat}
  +rq = kb_fst(TB, TC & TD & TE, kb_sd(TA, TB, TC, TD, TE, Laws.slot_decode(w, s, ab, s8, a2)))
  +dw = kb_fst(TC, TD & TE, kb_snd(TB, TC & TD & TE, kb_sd(TA, TB, TC, TD, TE, Laws.slot_decode(w, s, ab, s8, a2))))
  +da = kb_fst(TD, TE, kb_snd(TC, TD & TE, kb_snd(TB, TC & TD & TE, kb_sd(TA, TB, TC, TD, TE, Laws.slot_decode(w, s, ab, s8, a2)))))
  +ds = kb_snd(TD, TE, kb_snd(TC, TD & TE, kb_snd(TB, TC & TD & TE, kb_sd(TA, TB, TC, TD, TE, Laws.slot_decode(w, s, ab, s8, a2)))))
  +ceq = Equal.trans(Bool, Nat.is_lt(Impl.dec_s(Q), S), Nat.is_lt(s, S), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, S), Impl.dec_s(Q), s, ds), sr)
  +t0 = Impl.tree(Impl.wlanes(32n, 0n, Impl.dec_w(Q), S, Impl.dec_s(Q), Impl.dec_ab(Q), k2, h, H))
  +t1 = Impl.tree(Impl.wlanes(32n, 0n, w, S, Impl.dec_s(Q), Impl.dec_ab(Q), k2, h, H))
  +t2 = Impl.tree(Impl.wlanes(32n, 0n, w, S, s, Impl.dec_ab(Q), k2, h, H))
  +t3 = Impl.tree(Impl.wlanes(32n, 0n, w, S, s, ab, k2, h, H))
  +t4 = Impl.tree(Spec.clanes(32n, 0n, w, s, ab, k2, h, H))
  +e0 = Equal.cong(Nat, Impl.Ex, z => Impl.smem(z, S, k2, h, H), RQ, Q, rq)
  +e1 = kb_sr(Nat.is_lt(Impl.dec_s(Q), S), Q, S, k2, h, H, ceq)
  +e2 = Equal.cong(Nat, Impl.Ex, z => Impl.tree(Impl.wlanes(32n, 0n, z, S, Impl.dec_s(Q), Impl.dec_ab(Q), k2, h, H)), Impl.dec_w(Q), w, dw)
  +e3 = Equal.cong(Nat, Impl.Ex, z => Impl.tree(Impl.wlanes(32n, 0n, w, S, z, Impl.dec_ab(Q), k2, h, H)), Impl.dec_s(Q), s, ds)
  +e4 = Equal.cong(Nat, Impl.Ex, z => Impl.tree(Impl.wlanes(32n, 0n, w, S, s, z, k2, h, H)), Impl.dec_ab(Q), ab, da)
  +e5 = Equal.cong(List<&2, Impl.Ex>, Impl.Ex, xs => Impl.tree(xs), Impl.wlanes(32n, 0n, w, S, s, ab, k2, h, H),
    Spec.clanes(32n, 0n, w, s, ab, k2, h, H), kb_d(32n, 0n, w, S, s, ab, k2, h, H, sr, s8))
  +e6 = Laws.warp_tree(w, s, ab, k2, h, H)
  Equal.trans(Impl.Ex, Impl.smem(RQ, S, k2, h, H), Impl.smem(Q, S, k2, h, H), Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e0,
    Equal.trans(Impl.Ex, Impl.smem(Q, S, k2, h, H), t0, Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e1,
      Equal.trans(Impl.Ex, t0, t1, Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e2,
        Equal.trans(Impl.Ex, t1, t2, Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e3,
          Equal.trans(Impl.Ex, t2, t3, Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e4,
            Equal.trans(Impl.Ex, t3, t4, Spec.wtree(5n, 0n, w, s, ab, k2, h, H), e5, e6))))))

# thread s's loop over the 16 warp partials is the reference warp fold
def kb_r(+fuel: Nat, +w: Nat, +s: Nat, +ab: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, +v: Impl.Ex,
    +sr: {Nat.is_lt(s, S) == True{} : Bool}, +s8: {Nat.is_lt(s, 8n) == True{} : Bool}, +a2: {Nat.is_lt(ab, 2n) == True{} : Bool})
  -> {Impl.rsum(fuel, w, s, ab, S, k2, h, H, v) == Spec.wfold(fuel, w, s, ab, k2, h, H, v) : Impl.Ex}:
  match fuel:
    case 0n:
      {==}
    case 1n+more:
      +x0 = Impl.smem(Impl.rslot(w, s, ab), S, k2, h, H)
      +x1 = Spec.wtree(5n, 0n, w, s, ab, k2, h, H)
      Equal.trans(Impl.Ex, Impl.rsum(more, 1n+w, s, ab, S, k2, h, H, Impl.Add{v, x0}),
        Impl.rsum(more, 1n+w, s, ab, S, k2, h, H, Impl.Add{v, x1}),
        Spec.wfold(more, 1n+w, s, ab, k2, h, H, Impl.Add{v, x1}),
        Equal.cong(Impl.Ex, Impl.Ex, x => Impl.rsum(more, 1n+w, s, ab, S, k2, h, H, Impl.Add{v, x}), x0, x1,
          kb_s(w, S, s, ab, k2, h, H, sr, s8, a2)),
        kb_r(more, 1n+w, s, ab, S, k2, h, H, Impl.Add{v, x1}, sr, s8, a2))

def kb_pick_row(+ab: Nat, +h: Nat, +H: Nat)
  -> {Impl.pick(Nat.is_eq(ab, 0n), h, Nat.add(H, h)) == Spec.wrow(ab, h, H) : Nat}:
  match ab:
    case 0n:
      {==}
    case 1n+z:
      {==}

def Laws.task_value(S, s, ab, k2, h, H, hb, sr, s8, a2):
  +sr1 = sr
  +s81 = s8
  +a21 = a2
  +o0 = Impl.pick(Nat.is_eq(ab, 0n), h, Nat.add(H, h))
  +o1 = Spec.wrow(ab, h, H)
  +r0 = Impl.rsum(16n, 0n, s, ab, S, k2, h, H, Impl.Zero{})
  +r1 = Spec.wfold(16n, 0n, s, ab, k2, h, H, Impl.Zero{})
  Equal.trans(Impl.Ex, Impl.with_bias(hb, o0, r0), Impl.with_bias(hb, o1, r0), Impl.with_bias(hb, o1, r1),
    Equal.cong(Nat, Impl.Ex, o => Impl.with_bias(hb, o, r0), o0, o1, kb_pick_row(ab, h, H)),
    Equal.cong(Impl.Ex, Impl.Ex, v => Impl.with_bias(hb, o1, v), r0, r1, kb_r(16n, 0n, s, ab, S, k2, h, H, Impl.Zero{}, sr1, s81, a21)))
