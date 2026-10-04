# Proofs of bend/err_prefill_laws.bend: computation, case analysis, structural induction and the core error-bound
# laws (err_bound_laws.bend: dom_add, dom_refl) and Nat order laws (nat_order_laws.bend). No @unsafe definitions,
# axioms, holes or foreign code; every def precedes its uses.
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as EbL
import ./err_bound_proof.bend as EbP
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./hgemm_wide.bend as HW
import ./hgemm_wide_spec.bend as HWS
import ./hgemm_wide_laws.bend as HWL
import ./hgemm_wide_proof.bend as HWP
import ./err_prefill.bend as Ep
import ./err_prefill_laws.bend as Laws

# ==== path algebra ====

def path_eq8(+a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat, +a5: Nat, +a6: Nat, +a7: Nat, +a8: Nat,
    +b1: Nat, +b2: Nat, +b3: Nat, +b4: Nat, +b5: Nat, +b6: Nat, +b7: Nat, +b8: Nat,
    e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, e4: {a4 == b4 : Nat},
    e5: {a5 == b5 : Nat}, e6: {a6 == b6 : Nat}, e7: {a7 == b7 : Nat}, e8: {a8 == b8 : Nat})
  -> {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{b1, b2, b3, b4, b5, b6, b7, b8} : Eb.Path}:
  %e1 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{_, b2, b3, b4, b5, b6, b7, b8} : Eb.Path}
  %e2 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, _, b3, b4, b5, b6, b7, b8} : Eb.Path}
  %e3 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, _, b4, b5, b6, b7, b8} : Eb.Path}
  %e4 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, a3, _, b5, b6, b7, b8} : Eb.Path}
  %e5 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, a3, a4, _, b6, b7, b8} : Eb.Path}
  %e6 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, a3, a4, a5, _, b7, b8} : Eb.Path}
  %e7 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, a3, a4, a5, a6, _, b8} : Eb.Path}
  %e8 : {Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} == Eb.Path{a1, a2, a3, a4, a5, a6, a7, _} : Eb.Path}
  {==}

# concatenation is a multiset sum: p + (q + r) = q + (p + r)
def padd_swap(p: Eb.Path, q: Eb.Path, r: Eb.Path) -> {Eb.add(p, Eb.add(q, r)) == Eb.add(q, Eb.add(p, r)) : Eb.Path}:
  match p q r:
    case Eb.Path{+a1, +b1, +c1, +d1, +h1, +e1, +f1, +g1} Eb.Path{+a2, +b2, +c2, +d2, +h2, +e2, +f2, +g2} Eb.Path{+a3, +b3, +c3, +d3, +h3, +e3, +f3, +g3}:
      path_eq8(Nat.add(a1, Nat.add(a2, a3)), Nat.add(b1, Nat.add(b2, b3)), Nat.add(c1, Nat.add(c2, c3)),
        Nat.add(d1, Nat.add(d2, d3)), Nat.add(h1, Nat.add(h2, h3)), Nat.add(e1, Nat.add(e2, e3)),
        Nat.add(f1, Nat.add(f2, f3)), Nat.add(g1, Nat.add(g2, g3)),
        Nat.add(a2, Nat.add(a1, a3)), Nat.add(b2, Nat.add(b1, b3)), Nat.add(c2, Nat.add(c1, c3)),
        Nat.add(d2, Nat.add(d1, d3)), Nat.add(h2, Nat.add(h1, h3)), Nat.add(e2, Nat.add(e1, e3)),
        Nat.add(f2, Nat.add(f1, f3)), Nat.add(g2, Nat.add(g1, g3)),
        NO.add_swap(a1, a2, a3), NO.add_swap(b1, b2, b3), NO.add_swap(c1, c2, c3), NO.add_swap(d1, d2, d3),
        NO.add_swap(h1, h2, h3), NO.add_swap(e1, e2, e3), NO.add_swap(f1, f2, f3), NO.add_swap(g1, g2, g3))

# ==== concrete segment dominations ====

def d_lr() -> {Eb.dom(128n, Ep.e_row_later(), Ep.s_row_later()) == True{} : Bool}:
  {==}

def d_dl() -> {Eb.dom(128n, Ep.den_later(), Ep.s_row_later()) == True{} : Bool}:
  {==}

# ==== 1. score segments ====

def Laws.score_eq(interior, s):
  match interior:
    case True{}:
      {==}
    case False{}:
      {==}

# ==== 2. stock's worst leaf ====

def sw_t(+T: Nat, +h: Bool)
  -> {Eb.dom(128n, Ep.rep_add(T, Ep.den_later(), Ep.s_last(h)), Ep.rep_add(T, Ep.s_row_later(), Ep.s_last(False{}))) == True{} : Bool}:
  match T:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+t:
      EbL.dom_add(128n, Ep.den_later(), Ep.s_row_later(), Ep.rep_add(t, Ep.den_later(), Ep.s_last(h)),
        Ep.rep_add(t, Ep.s_row_later(), Ep.s_last(False{})), d_dl(), sw_t(t, h))

def sw_a(+A: Nat, +T: Nat, +h: Bool)
  -> {Eb.dom(128n, Ep.stock_leaf(T, A, h), Ep.stock_leaf(0n, Nat.add(A, T), False{})) == True{} : Bool}:
  match A:
    case 0n:
      sw_t(T, h)
    case 1n+a:
      EbL.dom_add(128n, Ep.s_row_later(), Ep.s_row_later(), Ep.stock_leaf(T, a, h),
        Ep.stock_leaf(0n, Nat.add(a, T), False{}), EbL.dom_refl(128n, Ep.s_row_later()), sw_a(a, T, h))

def Laws.stock_worst(T, A, h):
  sw_a(A, T, h)

# ==== 3. TRUE vs unsplit stock, n >= 3 ====

# leaf in tile 0 with 2 + a later tiles
def lq(+a: Nat, +h: Bool)
  -> {Eb.dom(128n, Eb.add(Ep.e_row_later(), Eb.add(Ep.e_row_later(), Ep.e_inner(a, False{}, h))),
      Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(), Ep.rep_add(a, Ep.s_row_later(), Ep.s_last(False{}))))) == True{} : Bool}:
  match a:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+b:
      EbL.dom_add(128n, Ep.e_row_later(), Ep.s_row_later(),
        Eb.add(Ep.e_row_later(), Eb.add(Ep.e_row_later(), Ep.e_inner(b, False{}, h))),
        Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(), Ep.rep_add(b, Ep.s_row_later(), Ep.s_last(False{})))),
        d_lr(), lq(b, h))

# leaf in tile 1 with 1 + a later tiles
def lr0(+a: Nat, +h: Bool)
  -> {Eb.dom(128n, Eb.add(Ep.den_later(), Eb.add(Ep.e_row_later(), Ep.e_inner(a, True{}, h))),
      Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(), Ep.rep_add(a, Ep.s_row_later(), Ep.s_last(False{}))))) == True{} : Bool}:
  match a:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+b:
      +Y = Eb.add(Ep.e_row_later(), Ep.e_inner(b, True{}, h))
      +RS = Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(),
        Ep.rep_add(b, Ep.s_row_later(), Ep.s_last(False{})))))
      %padd_swap(Ep.e_row_later(), Ep.den_later(), Y) : {Eb.dom(128n, _, RS) == True{} : Bool}
      EbL.dom_add(128n, Ep.e_row_later(), Ep.s_row_later(), Eb.add(Ep.den_later(), Y),
        Eb.add(Ep.s_row_later(), Eb.add(Ep.s_row_later(), Ep.rep_add(b, Ep.s_row_later(), Ep.s_last(False{})))),
        d_lr(), lr0(b, h))

# leaf in tile 1 + t with 1 + a later tiles
def l2(+t: Nat, +a: Nat, +h: Bool)
  -> {Eb.dom(128n, Ep.elpis_leaf(1n+t, 1n+a, h), Ep.stock_leaf(0n, Nat.add(1n+t, 1n+a), False{})) == True{} : Bool}:
  match t:
    case 0n:
      lr0(a, h)
    case 1n+u:
      EbL.dom_add(128n, Ep.den_later(), Ep.s_row_later(), Ep.elpis_leaf(1n+u, 1n+a, h),
        Ep.stock_leaf(0n, Nat.add(1n+u, 1n+a), False{}), d_dl(), l2(u, a, h))

# leaf in tile 2 + t, the row's last tile
def l3(+t: Nat, +h: Bool)
  -> {Eb.dom(128n, Ep.elpis_leaf(2n+t, 0n, h), Ep.stock_leaf(0n, Nat.add(2n+t, 0n), False{})) == True{} : Bool}:
  match t:
    case 0n:
      match h:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+u:
      EbL.dom_add(128n, Ep.den_later(), Ep.s_row_later(), Ep.elpis_leaf(2n+u, 0n, h),
        Ep.stock_leaf(0n, Nat.add(2n+u, 0n), False{}), d_dl(), l3(u, h))

def Core(T: Nat, A: Nat, h: Bool) -> Type:
  {Eb.dom(128n, Ep.elpis_leaf(T, A, h), Ep.stock_leaf(0n, Nat.add(T, A), False{})) == True{} : Bool}

# T = 1 + t, A = 0: the leaf is in the row's last tile, which needs t >= 1
def core_last(+t: Nat, +h: Bool, big: {Nat.is_le(2n, Nat.add(1n+t, 0n)) == True{} : Bool}) -> Core(1n+t, 0n, h):
  match t:
    case 0n:
      Empty.absurd(Core(1n, 0n, h), NO.false_true(big))
    case 1n+u:
      l3(u, h)

def core_t1(+A: Nat, +t: Nat, +h: Bool, big: {Nat.is_le(2n, Nat.add(1n+t, A)) == True{} : Bool}) -> Core(1n+t, A, h):
  match A:
    case 1n+a:
      l2(t, a, h)
    case 0n:
      core_last(t, h, big)

def core(+T: Nat, +A: Nat, +h: Bool, big: {Nat.is_le(2n, Nat.add(T, A)) == True{} : Bool}) -> Core(T, A, h):
  match T:
    case 0n:
      match A:
        case 0n:
          Empty.absurd(Core(0n, 0n, h), NO.false_true(big))
        case 1n+a:
          match a:
            case 0n:
              Empty.absurd(Core(0n, 1n, h), NO.false_true(big))
            case 1n+b:
              lq(b, h)
    case 1n+t:
      core_t1(A, t, h, big)

def Laws.pv_unsplit_dom(T, A, h, c, big):
  EbL.dom_add(128n, c, c, Ep.elpis_leaf(T, A, h), Ep.stock_leaf(0n, Nat.add(T, A), False{}),
    EbL.dom_refl(128n, c), core(T, A, h, big))

# ==== 4-5. GDN prefill conv ====

def Laws.conv_trace_eq(K, j, b):
  match j:
    case 0n:
      {==}
    case 1n+i:
      {==}

def Laws.conv_path_eq(K, j, b):
  %Laws.conv_trace_eq(K, j, b) : {Ep.st_path(Ep.elpis_conv(K, j, b)) == Ep.st_path(_) : Eb.Path}
  {==}

def Laws.conv_route_long(r):
  ({==}, {==})

def lt_false(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_lt(0n, 1n+bp) == False{} : Bool}, NO.false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      lt_false(ap, bp, h)

def Laws.conv_route_short(r, fc, short):
  %Equal.sym(Bool, Nat.is_lt(256n, r), False{}, lt_false(256n, r, short)) :
    {Ep.pick(Bool.and(_, fc), Ep.KFused{}, Ep.stock_route(r)) == Ep.stock_route(r) : Ep.Kern}
  {==}

# ==== 6. prefill GEMM ====

def gemm_eq_k(+L: Nat,
    k: {HW.wide_acc(Nat.mul(L, 64n)) == HWS.slices(Nat.mul(L, 2n), 0n) : List<&2, List<&2, Nat>>} &
      {HW.served_acc(Nat.mul(L, 64n)) == HWS.slices(Nat.mul(L, 2n), 0n) : List<&2, List<&2, Nat>>})
  -> {Ep.wide_paths(Nat.mul(L, 64n)) == Ep.served_paths(Nat.mul(L, 64n)) : List<&2, Eb.Path>}:
  (e1, e2) = k
  +SL = HWS.slices(Nat.mul(L, 2n), 0n)
  %Equal.sym(List<&2, List<&2, Nat>>, HW.wide_acc(Nat.mul(L, 64n)), SL, e1) :
    {Ep.gemm_paths(_, True{}) == Ep.gemm_paths(HW.served_acc(Nat.mul(L, 64n)), True{}) : List<&2, Eb.Path>}
  %Equal.sym(List<&2, List<&2, Nat>>, HW.served_acc(Nat.mul(L, 64n)), SL, e2) :
    {Ep.gemm_paths(SL, True{}) == Ep.gemm_paths(_, True{}) : List<&2, Eb.Path>}
  {==}

def Laws.gemm_paths_eq(L):
  gemm_eq_k(L, HWL.k_order(L))
