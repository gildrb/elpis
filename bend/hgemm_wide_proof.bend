# Proofs of the wide-tile prefill GEMM laws (hgemm_wide_laws.bend) about the model hgemm_wide.bend. Structural
# evidence only: no unsafe definitions, axioms, holes or answer tables. Nat lemmas from the m16 partition proof
# (gemm_m16_partition_proof.bend, alias Ar). Every def precedes its uses.
import Base
import ./gemm_m16_partition_proof.bend as Ar
import ./hgemm_wide.bend as Impl
import ./hgemm_wide_spec.bend as Spec
import ./hgemm_wide_laws.bend as Laws

# ==== (4) route ====

def Laws.route_table():
  {==}

def Laws.route_fits():
  {==}

# The table search of the patch is the reference membership test, for any list.
def hw_shape_in(xs: List<&2, Spec.HwShape>, +K: U32, +N: U32, +f: Bool)
  -> {Impl.shape_in(xs, K, N, f) == Spec.member(xs, Spec.HwShape{K, N, f}) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Spec.HwShape{+k, +n, +g} <> rest:
      Equal.cong(Bool, Bool, x => Bool.or(Bool.and(U32.is_eq(k, K), Bool.and(U32.is_eq(n, N), Bool.not(Bool.xor(g, f)))), x),
        Impl.shape_in(rest, K, N, f), Spec.member(rest, Spec.HwShape{K, N, f}), hw_shape_in(rest, K, N, f))

# The nested early returns of wide_route are the conjunction.
def hw_route_on(a: Bool, b: Bool, c: Bool, d: Bool)
  -> {Impl.route_on(a, b, c, d) == Spec.pick(Bool.and(a, Bool.and(b, Bool.and(c, d)))) : Spec.HwRoute}:
  match a b c d:
    case False{} _ _ _:
      {==}
    case True{} False{} _ _:
      {==}
    case True{} True{} False{} _:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{}:
      {==}

def hw_route_hit(+K: U32, +N: U32, +f: Bool)
  -> {Impl.shape_in(Impl.wide_shapes(), K, N, f) == Spec.member(Spec.served_shapes(), Spec.HwShape{K, N, f}) : Bool}:
  %Laws.route_table() : {Impl.shape_in(Impl.wide_shapes(), K, N, f) == Spec.member(_, Spec.HwShape{K, N, f}) : Bool}
  hw_shape_in(Impl.wide_shapes(), K, N, f)

def hw_route_on_eq(+d: Bool, +u: Bool, +l: Bool, +K: U32, +N: U32, +f: Bool)
  -> {Impl.route_on(d, u, l, Impl.shape_in(Impl.wide_shapes(), K, N, f)) ==
      Spec.pick(Bool.and(d, Bool.and(u, Bool.and(l, Spec.member(Spec.served_shapes(), Spec.HwShape{K, N, f}))))) : Spec.HwRoute}:
  %hw_route_hit(K, N, f) : {Impl.route_on(d, u, l, Impl.shape_in(Impl.wide_shapes(), K, N, f)) ==
      Spec.pick(Bool.and(d, Bool.and(u, Bool.and(l, _)))) : Spec.HwRoute}
  hw_route_on(d, u, l, Impl.shape_in(Impl.wide_shapes(), K, N, f))

def Laws.route_total(env, major, minor, batch, M, K, N, f):
  match env:
    case Spec.HwUnset{}:
      hw_route_on_eq(Bool.and(U32.is_eq(major, 8), U32.is_eq(minor, 6)), U32.is_eq(batch, 1), U32.is_ge(M, 1024), K, N, f)
    case Spec.HwOne{}:
      hw_route_on_eq(Bool.and(U32.is_eq(major, 8), U32.is_eq(minor, 6)), U32.is_eq(batch, 1), U32.is_ge(M, 1024), K, N, f)
    case Spec.HwZero{}:
      {==}
    case Spec.HwOther{}:
      {==}

# ==== (2) accumulation order ====

def hw_wide_eq(n: Nat, +kt: Nat)
  -> {Impl.wide_kt(n, kt) == Spec.slices(n, Nat.mul(kt, 32n)) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+rest:
      +X = Nat.mul(kt, 32n)
      %Ar.ar_add_zero_r(X) : {[Nat.add(X, 0n), Nat.add(X, 16n)] <> Impl.wide_kt(rest, 1n+kt) ==
        [_, Nat.add(X, 16n)] <> Spec.slices(rest, Nat.add(X, 32n)) : List<&2, List<&2, Nat>>}
      %Ar.ar_add_comm(32n, X) : {[Nat.add(X, 0n), Nat.add(X, 16n)] <> Impl.wide_kt(rest, 1n+kt) ==
        [Nat.add(X, 0n), Nat.add(X, 16n)] <> Spec.slices(rest, _) : List<&2, List<&2, Nat>>}
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, t => [Nat.add(X, 0n), Nat.add(X, 16n)] <> t,
        Impl.wide_kt(rest, 1n+kt), Spec.slices(rest, Nat.add(32n, X)), hw_wide_eq(rest, 1n+kt))

def hw_served_eq(+n: Nat, +kt: Nat)
  -> {Impl.served_loop(n, 4n, False{}, kt, 0n, Nil{}) == Spec.slices(Nat.mul(n, 2n), Nat.mul(kt, 64n)) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+t:
      +Y = Nat.mul(kt, 64n)
      +P0 = {[Nat.add(Y, 0n), Nat.add(Y, 16n)] : List<&2, Nat>}
      +P1 = {[Nat.add(Y, 32n), Nat.add(Y, 48n)] : List<&2, Nat>}
      %Ar.ar_add_zero_r(Y) : {P0 <> P1 <> Impl.served_loop(t, 4n, False{}, 1n+kt, 0n, Nil{}) ==
        [_, Nat.add(Y, 16n)] <> [Nat.add(Y, 32n), Nat.add(Nat.add(Y, 32n), 16n)] <>
        Spec.slices(Nat.mul(t, 2n), Nat.add(Nat.add(Y, 32n), 32n)) : List<&2, List<&2, Nat>>}
      %Equal.sym(Nat, Nat.add(Nat.add(Y, 32n), 16n), Nat.add(Y, 48n), Ar.ar_add_assoc(Y, 32n, 16n)) : {P0 <> P1 <> Impl.served_loop(t, 4n, False{}, 1n+kt, 0n, Nil{}) ==
        P0 <> [Nat.add(Y, 32n), _] <>
        Spec.slices(Nat.mul(t, 2n), Nat.add(Nat.add(Y, 32n), 32n)) : List<&2, List<&2, Nat>>}
      %Equal.sym(Nat, Nat.add(Nat.add(Y, 32n), 32n), Nat.add(Y, 64n), Ar.ar_add_assoc(Y, 32n, 32n)) : {P0 <> P1 <> Impl.served_loop(t, 4n, False{}, 1n+kt, 0n, Nil{}) ==
        P0 <> P1 <> Spec.slices(Nat.mul(t, 2n), _) : List<&2, List<&2, Nat>>}
      %Ar.ar_add_comm(64n, Y) : {P0 <> P1 <> Impl.served_loop(t, 4n, False{}, 1n+kt, 0n, Nil{}) ==
        P0 <> P1 <> Spec.slices(Nat.mul(t, 2n), _) : List<&2, List<&2, Nat>>}
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, x => P0 <> P1 <> x,
        Impl.served_loop(t, 4n, False{}, 1n+kt, 0n, Nil{}), Spec.slices(Nat.mul(t, 2n), Nat.add(64n, Y)),
        hw_served_eq(t, 1n+kt))

# (q m) / m == q for m > 0, written for the literal divisors used here.
def hw_div_exact(+q: Nat, +m: Nat, +x: Nat, pos: {Nat.is_lt(0n, m) == True{} : Bool}, e: {Nat.mul(q, m) == x : Nat})
  -> {Nat.div(x, m) == q : Nat}:
  %e : {Nat.div(_, m) == q : Nat}
  %Ar.ar_add_zero_r(Nat.mul(q, m)) : {Nat.div(_, m) == q : Nat}
  Ar.p7_div_q(q, 0n, m, pos)

def Laws.k_order(L):
  +d32 = hw_div_exact(Nat.mul(L, 2n), 32n, Nat.mul(L, 64n), {==}, Ar.ar_mul_assoc(L, 2n, 32n))
  +d64 = hw_div_exact(L, 64n, Nat.mul(L, 64n), {==}, {==})
  (Equal.trans(List<&2, List<&2, Nat>>, Impl.wide_acc(Nat.mul(L, 64n)), Impl.wide_kt(Nat.mul(L, 2n), 0n),
      Spec.slices(Nat.mul(L, 2n), 0n),
      Equal.cong(Nat, List<&2, List<&2, Nat>>, x => Impl.wide_kt(x, 0n), Nat.div(Nat.mul(L, 64n), 32n), Nat.mul(L, 2n), d32),
      hw_wide_eq(Nat.mul(L, 2n), 0n)),
   Equal.trans(List<&2, List<&2, Nat>>, Impl.served_acc(Nat.mul(L, 64n)), Impl.served_loop(L, 4n, False{}, 0n, 0n, Nil{}),
      Spec.slices(Nat.mul(L, 2n), 0n),
      Equal.cong(Nat, List<&2, List<&2, Nat>>, x => Impl.served_loop(x, 4n, False{}, 0n, 0n, Nil{}), Nat.div(Nat.mul(L, 64n), 64n), L, d64),
      hw_served_eq(L, 0n)))

# ==== (1) output ownership ====

# ((((a + b) + c) + d) + e) == a + (((b + c) + d) + e)
def hw_assoc4(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat)
  -> {Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e) == Nat.add(a, Nat.add(Nat.add(Nat.add(b, c), d), e)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e), Nat.add(Nat.add(a, Nat.add(Nat.add(b, c), d)), e),
    Nat.add(a, Nat.add(Nat.add(Nat.add(b, c), d), e)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e), Nat.add(Nat.add(Nat.add(a, Nat.add(b, c)), d), e),
      Nat.add(Nat.add(a, Nat.add(Nat.add(b, c), d)), e),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.add(x, d), e), Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Ar.ar_add_assoc(a, b, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, e), Nat.add(Nat.add(a, Nat.add(b, c)), d), Nat.add(a, Nat.add(Nat.add(b, c), d)),
        Ar.ar_add_assoc(a, Nat.add(b, c), d))),
    Ar.ar_add_assoc(a, Nat.add(Nat.add(b, c), d), e))

def Laws.store_offset(bm, bn, t, i, j, h, e):
  (hw_assoc4(bm, Nat.mul(Impl.wm(t), 64n), Nat.mul(i, 16n), Impl.gq(t), Nat.mul(h, 8n)),
   hw_assoc4(bn, Nat.mul(Impl.wn(t), 64n), Nat.mul(j, 8n), Nat.mul(Impl.tq(t), 2n), e))

def hw_le_ceil_s2(+M: Nat, +q: Nat, +r: Nat, dm: {Nat.add(Nat.mul(q, 128n), r) == Nat.add(M, 127n) : Nat},
    s1: {Nat.is_le(Nat.add(M, r), Nat.add(M, 127n)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(r, M), Nat.add(r, Nat.mul(q, 128n))) == True{} : Bool}:
  %Ar.ar_add_comm(M, r) : {Nat.is_le(_, Nat.add(r, Nat.mul(q, 128n))) == True{} : Bool}
  %Equal.trans(Nat, Nat.add(M, 127n), Nat.add(Nat.mul(q, 128n), r), Nat.add(r, Nat.mul(q, 128n)),
    Equal.sym(Nat, Nat.add(Nat.mul(q, 128n), r), Nat.add(M, 127n), dm), Ar.ar_add_comm(Nat.mul(q, 128n), r))
    : {Nat.is_le(Nat.add(M, r), _) == True{} : Bool}
  s1

# M <= ((M + 127) / 128) * 128
def hw_le_ceil(+M: Nat) -> {Nat.is_le(M, Nat.mul(Nat.div(Nat.add(M, 127n), 128n), 128n)) == True{} : Bool}:
  +x = Nat.add(M, 127n)
  +q = Nat.div(x, 128n)
  +r = Nat.mod(x, 128n)
  +dm = Ar.ard_dm_eq(x, 128n, {==})
  +rl = Ar.ard_dm_lt(x, 128n, {==})
  +rle = Ar.ard_tr(Nat.is_le(r, 127n), Nat.is_lt(r, 128n), Ar.p1_le_lt_succ(r, 127n), rl)
  +s1 = Ar.ard_tr(Nat.is_le(Nat.add(M, r), Nat.add(M, 127n)), Nat.is_le(r, 127n), Ar.ar_le_add_cancel(M, r, 127n), rle)
  +s2 = hw_le_ceil_s2(M, q, r, dm, s1)
  Ar.ard_rt(Nat.is_le(Nat.add(r, M), Nat.add(r, Nat.mul(q, 128n))), Nat.is_le(M, Nat.mul(q, 128n)),
    Ar.ar_le_add_cancel(r, M, Nat.mul(q, 128n)), s2)

def Laws.grid_rows(M):
  +e1 = Equal.trans(Nat, Nat.sub(Nat.add(M, 128n), 1n), Nat.sub(1n+Nat.add(M, 127n), 1n), Nat.add(M, 127n),
    Equal.cong(Nat, Nat, y => Nat.sub(y, 1n), Nat.add(M, 128n), 1n+Nat.add(M, 127n), Ar.ar_add_succ_r(M, 127n)),
    Ar.ar_sub_zero_r(Nat.add(M, 127n)))
  %Equal.sym(Nat, Nat.sub(Nat.add(M, 128n), 1n), Nat.add(M, 127n), e1)
    : {Nat.is_le(M, Nat.mul(Nat.div(_, 128n), 128n)) == True{} : Bool}
  hw_le_ceil(M)

# ==== (3) stage writes ====

# x < 0 is absurd.
def hw_lt0(x: Nat, h: {Nat.is_lt(x, 0n) == True{} : Bool}) -> Empty:
  match x:
    case 0n:
      Ar.ar_false_true(h)
    case 1n+y:
      Ar.ar_false_true(h)

# A swizzle: 2-bit chunk, key (row / 2) % 4 < 4; B swizzle: 4-bit chunk, key row % 8 < 8.
def hw_xa(a: Nat, k: Nat, ha: {Nat.is_lt(a, 4n) == True{} : Bool},
    hk: {Nat.is_lt(k, 4n) == True{} : Bool})
  -> {Nat.is_lt(Spec.xor(2n, a, k), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, a, k), k) == a : Nat}:
  match a:
    case 0n:
      match k:
        case 0n:
          ({==}, {==})
        case 1n+k1:
          match k1:
            case 0n:
              ({==}, {==})
            case 1n+k2:
              match k2:
                case 0n:
                  ({==}, {==})
                case 1n+k3:
                  match k3:
                    case 0n:
                      ({==}, {==})
                    case 1n+k4:
                      Empty.absurd({Nat.is_lt(Spec.xor(2n, 0n, 1n+1n+1n+1n+k4), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, 0n, 1n+1n+1n+1n+k4), 1n+1n+1n+1n+k4) == 0n : Nat}, hw_lt0(k4, hk))
    case 1n+a1:
      match a1:
        case 0n:
          match k:
            case 0n:
              ({==}, {==})
            case 1n+k1:
              match k1:
                case 0n:
                  ({==}, {==})
                case 1n+k2:
                  match k2:
                    case 0n:
                      ({==}, {==})
                    case 1n+k3:
                      match k3:
                        case 0n:
                          ({==}, {==})
                        case 1n+k4:
                          Empty.absurd({Nat.is_lt(Spec.xor(2n, 1n, 1n+1n+1n+1n+k4), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, 1n, 1n+1n+1n+1n+k4), 1n+1n+1n+1n+k4) == 1n : Nat}, hw_lt0(k4, hk))
        case 1n+a2:
          match a2:
            case 0n:
              match k:
                case 0n:
                  ({==}, {==})
                case 1n+k1:
                  match k1:
                    case 0n:
                      ({==}, {==})
                    case 1n+k2:
                      match k2:
                        case 0n:
                          ({==}, {==})
                        case 1n+k3:
                          match k3:
                            case 0n:
                              ({==}, {==})
                            case 1n+k4:
                              Empty.absurd({Nat.is_lt(Spec.xor(2n, 1n+1n, 1n+1n+1n+1n+k4), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, 1n+1n, 1n+1n+1n+1n+k4), 1n+1n+1n+1n+k4) == 1n+1n : Nat}, hw_lt0(k4, hk))
            case 1n+a3:
              match a3:
                case 0n:
                  match k:
                    case 0n:
                      ({==}, {==})
                    case 1n+k1:
                      match k1:
                        case 0n:
                          ({==}, {==})
                        case 1n+k2:
                          match k2:
                            case 0n:
                              ({==}, {==})
                            case 1n+k3:
                              match k3:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k4:
                                  Empty.absurd({Nat.is_lt(Spec.xor(2n, 1n+1n+1n, 1n+1n+1n+1n+k4), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, 1n+1n+1n, 1n+1n+1n+1n+k4), 1n+1n+1n+1n+k4) == 1n+1n+1n : Nat}, hw_lt0(k4, hk))
                case 1n+a4:
                  Empty.absurd({Nat.is_lt(Spec.xor(2n, 1n+1n+1n+1n+a4, k), 4n) == True{} : Bool} & {Spec.xor(2n, Spec.xor(2n, 1n+1n+1n+1n+a4, k), k) == 1n+1n+1n+1n+a4 : Nat}, hw_lt0(a4, ha))

def hw_xb(a: Nat, k: Nat, ha: {Nat.is_lt(a, 16n) == True{} : Bool},
    hk: {Nat.is_lt(k, 8n) == True{} : Bool})
  -> {Nat.is_lt(Spec.xor(4n, a, k), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, a, k), k) == a : Nat}:
  match a:
    case 0n:
      match k:
        case 0n:
          ({==}, {==})
        case 1n+k1:
          match k1:
            case 0n:
              ({==}, {==})
            case 1n+k2:
              match k2:
                case 0n:
                  ({==}, {==})
                case 1n+k3:
                  match k3:
                    case 0n:
                      ({==}, {==})
                    case 1n+k4:
                      match k4:
                        case 0n:
                          ({==}, {==})
                        case 1n+k5:
                          match k5:
                            case 0n:
                              ({==}, {==})
                            case 1n+k6:
                              match k6:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k7:
                                  match k7:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k8:
                                      Empty.absurd({Nat.is_lt(Spec.xor(4n, 0n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 0n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 0n : Nat}, hw_lt0(k8, hk))
    case 1n+a1:
      match a1:
        case 0n:
          match k:
            case 0n:
              ({==}, {==})
            case 1n+k1:
              match k1:
                case 0n:
                  ({==}, {==})
                case 1n+k2:
                  match k2:
                    case 0n:
                      ({==}, {==})
                    case 1n+k3:
                      match k3:
                        case 0n:
                          ({==}, {==})
                        case 1n+k4:
                          match k4:
                            case 0n:
                              ({==}, {==})
                            case 1n+k5:
                              match k5:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k6:
                                  match k6:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k7:
                                      match k7:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k8:
                                          Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n : Nat}, hw_lt0(k8, hk))
        case 1n+a2:
          match a2:
            case 0n:
              match k:
                case 0n:
                  ({==}, {==})
                case 1n+k1:
                  match k1:
                    case 0n:
                      ({==}, {==})
                    case 1n+k2:
                      match k2:
                        case 0n:
                          ({==}, {==})
                        case 1n+k3:
                          match k3:
                            case 0n:
                              ({==}, {==})
                            case 1n+k4:
                              match k4:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k5:
                                  match k5:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k6:
                                      match k6:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k7:
                                          match k7:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k8:
                                              Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n : Nat}, hw_lt0(k8, hk))
            case 1n+a3:
              match a3:
                case 0n:
                  match k:
                    case 0n:
                      ({==}, {==})
                    case 1n+k1:
                      match k1:
                        case 0n:
                          ({==}, {==})
                        case 1n+k2:
                          match k2:
                            case 0n:
                              ({==}, {==})
                            case 1n+k3:
                              match k3:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k4:
                                  match k4:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k5:
                                      match k5:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k6:
                                          match k6:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k7:
                                              match k7:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k8:
                                                  Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n : Nat}, hw_lt0(k8, hk))
                case 1n+a4:
                  match a4:
                    case 0n:
                      match k:
                        case 0n:
                          ({==}, {==})
                        case 1n+k1:
                          match k1:
                            case 0n:
                              ({==}, {==})
                            case 1n+k2:
                              match k2:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k3:
                                  match k3:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k4:
                                      match k4:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k5:
                                          match k5:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k6:
                                              match k6:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k7:
                                                  match k7:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k8:
                                                      Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                    case 1n+a5:
                      match a5:
                        case 0n:
                          match k:
                            case 0n:
                              ({==}, {==})
                            case 1n+k1:
                              match k1:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k2:
                                  match k2:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k3:
                                      match k3:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k4:
                                          match k4:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k5:
                                              match k5:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k6:
                                                  match k6:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k7:
                                                      match k7:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k8:
                                                          Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                        case 1n+a6:
                          match a6:
                            case 0n:
                              match k:
                                case 0n:
                                  ({==}, {==})
                                case 1n+k1:
                                  match k1:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k2:
                                      match k2:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k3:
                                          match k3:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k4:
                                              match k4:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k5:
                                                  match k5:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k6:
                                                      match k6:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k7:
                                                          match k7:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k8:
                                                              Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                            case 1n+a7:
                              match a7:
                                case 0n:
                                  match k:
                                    case 0n:
                                      ({==}, {==})
                                    case 1n+k1:
                                      match k1:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k2:
                                          match k2:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k3:
                                              match k3:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k4:
                                                  match k4:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k5:
                                                      match k5:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k6:
                                                          match k6:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k7:
                                                              match k7:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k8:
                                                                  Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                case 1n+a8:
                                  match a8:
                                    case 0n:
                                      match k:
                                        case 0n:
                                          ({==}, {==})
                                        case 1n+k1:
                                          match k1:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k2:
                                              match k2:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k3:
                                                  match k3:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k4:
                                                      match k4:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k5:
                                                          match k5:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k6:
                                                              match k6:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k7:
                                                                  match k7:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k8:
                                                                      Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                    case 1n+a9:
                                      match a9:
                                        case 0n:
                                          match k:
                                            case 0n:
                                              ({==}, {==})
                                            case 1n+k1:
                                              match k1:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k2:
                                                  match k2:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k3:
                                                      match k3:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k4:
                                                          match k4:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k5:
                                                              match k5:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k6:
                                                                  match k6:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k7:
                                                                      match k7:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k8:
                                                                          Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                        case 1n+a10:
                                          match a10:
                                            case 0n:
                                              match k:
                                                case 0n:
                                                  ({==}, {==})
                                                case 1n+k1:
                                                  match k1:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k2:
                                                      match k2:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k3:
                                                          match k3:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k4:
                                                              match k4:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k5:
                                                                  match k5:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k6:
                                                                      match k6:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k7:
                                                                          match k7:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k8:
                                                                              Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                            case 1n+a11:
                                              match a11:
                                                case 0n:
                                                  match k:
                                                    case 0n:
                                                      ({==}, {==})
                                                    case 1n+k1:
                                                      match k1:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k2:
                                                          match k2:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k3:
                                                              match k3:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k4:
                                                                  match k4:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k5:
                                                                      match k5:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k6:
                                                                          match k6:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k7:
                                                                              match k7:
                                                                                case 0n:
                                                                                  ({==}, {==})
                                                                                case 1n+k8:
                                                                                  Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                                case 1n+a12:
                                                  match a12:
                                                    case 0n:
                                                      match k:
                                                        case 0n:
                                                          ({==}, {==})
                                                        case 1n+k1:
                                                          match k1:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k2:
                                                              match k2:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k3:
                                                                  match k3:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k4:
                                                                      match k4:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k5:
                                                                          match k5:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k6:
                                                                              match k6:
                                                                                case 0n:
                                                                                  ({==}, {==})
                                                                                case 1n+k7:
                                                                                  match k7:
                                                                                    case 0n:
                                                                                      ({==}, {==})
                                                                                    case 1n+k8:
                                                                                      Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                                    case 1n+a13:
                                                      match a13:
                                                        case 0n:
                                                          match k:
                                                            case 0n:
                                                              ({==}, {==})
                                                            case 1n+k1:
                                                              match k1:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k2:
                                                                  match k2:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k3:
                                                                      match k3:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k4:
                                                                          match k4:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k5:
                                                                              match k5:
                                                                                case 0n:
                                                                                  ({==}, {==})
                                                                                case 1n+k6:
                                                                                  match k6:
                                                                                    case 0n:
                                                                                      ({==}, {==})
                                                                                    case 1n+k7:
                                                                                      match k7:
                                                                                        case 0n:
                                                                                          ({==}, {==})
                                                                                        case 1n+k8:
                                                                                          Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                                        case 1n+a14:
                                                          match a14:
                                                            case 0n:
                                                              match k:
                                                                case 0n:
                                                                  ({==}, {==})
                                                                case 1n+k1:
                                                                  match k1:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k2:
                                                                      match k2:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k3:
                                                                          match k3:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k4:
                                                                              match k4:
                                                                                case 0n:
                                                                                  ({==}, {==})
                                                                                case 1n+k5:
                                                                                  match k5:
                                                                                    case 0n:
                                                                                      ({==}, {==})
                                                                                    case 1n+k6:
                                                                                      match k6:
                                                                                        case 0n:
                                                                                          ({==}, {==})
                                                                                        case 1n+k7:
                                                                                          match k7:
                                                                                            case 0n:
                                                                                              ({==}, {==})
                                                                                            case 1n+k8:
                                                                                              Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                                            case 1n+a15:
                                                              match a15:
                                                                case 0n:
                                                                  match k:
                                                                    case 0n:
                                                                      ({==}, {==})
                                                                    case 1n+k1:
                                                                      match k1:
                                                                        case 0n:
                                                                          ({==}, {==})
                                                                        case 1n+k2:
                                                                          match k2:
                                                                            case 0n:
                                                                              ({==}, {==})
                                                                            case 1n+k3:
                                                                              match k3:
                                                                                case 0n:
                                                                                  ({==}, {==})
                                                                                case 1n+k4:
                                                                                  match k4:
                                                                                    case 0n:
                                                                                      ({==}, {==})
                                                                                    case 1n+k5:
                                                                                      match k5:
                                                                                        case 0n:
                                                                                          ({==}, {==})
                                                                                        case 1n+k6:
                                                                                          match k6:
                                                                                            case 0n:
                                                                                              ({==}, {==})
                                                                                            case 1n+k7:
                                                                                              match k7:
                                                                                                case 0n:
                                                                                                  ({==}, {==})
                                                                                                case 1n+k8:
                                                                                                  Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n, 1n+1n+1n+1n+1n+1n+1n+1n+k8), 1n+1n+1n+1n+1n+1n+1n+1n+k8) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n : Nat}, hw_lt0(k8, hk))
                                                                case 1n+a16:
                                                                  Empty.absurd({Nat.is_lt(Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+a16, k), 16n) == True{} : Bool} & {Spec.xor(4n, Spec.xor(4n, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+a16, k), k) == 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+a16 : Nat}, hw_lt0(a16, ha))


# row RS + pc 8 == (row CPR + pc) 8 when CPR 8 == RS.
def hw_slot(+row: Nat, +pc: Nat, +CPR: Nat, +RS: Nat, e: {Nat.mul(CPR, 8n) == RS : Nat})
  -> {Nat.add(Nat.mul(row, RS), Nat.mul(pc, 8n)) == Nat.mul(Nat.add(Nat.mul(row, CPR), pc), 8n) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(row, CPR), pc), 8n), Nat.add(Nat.mul(Nat.mul(row, CPR), 8n), Nat.mul(pc, 8n)),
    Ar.ar_mul_add_l(Nat.mul(row, CPR), pc, 8n)) : {Nat.add(Nat.mul(row, RS), Nat.mul(pc, 8n)) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(row, CPR), 8n), Nat.mul(row, RS),
    Equal.trans(Nat, Nat.mul(Nat.mul(row, CPR), 8n), Nat.mul(row, Nat.mul(CPR, 8n)), Nat.mul(row, RS),
      Ar.ar_mul_assoc(row, CPR, 8n), Equal.cong(Nat, Nat, y => Nat.mul(row, y), Nat.mul(CPR, 8n), RS, e)))
    : {Nat.add(Nat.mul(row, RS), Nat.mul(pc, 8n)) == Nat.add(_, Nat.mul(pc, 8n)) : Nat}
  {==}

# x 8 == y 8 gives x == y.
def hw_mul8_inj(+x: Nat, +y: Nat, e: {Nat.mul(x, 8n) == Nat.mul(y, 8n) : Nat}) -> {x == y : Nat}:
  Ar.ard_fst({x == y : Nat}, {0n == 0n : Nat}, Ar.ar_divmod_inj(x, 0n, y, 0n, 8n, {==}, {==},
    Equal.cong(Nat, Nat, u => Nat.add(u, 0n), Nat.mul(x, 8n), Nat.mul(y, 8n), e)))

# (x 8) / 8 == x and (x 8) % 8 == 0.
def hw_div8(+x: Nat) -> {Nat.div(Nat.mul(x, 8n), 8n) == x : Nat}:
  %Ar.ar_add_zero_r(Nat.mul(x, 8n)) : {Nat.div(_, 8n) == x : Nat}
  Ar.p7_div_q(x, 0n, 8n, {==})

def hw_mod8(+x: Nat) -> {Nat.mod(Nat.mul(x, 8n), 8n) == 0n : Nat}:
  %Ar.ar_add_zero_r(Nat.mul(x, 8n)) : {Nat.mod(_, 8n) == 0n : Nat}
  Ar.p7_mod_r(x, 0n, 8n, {==})

def hw_xor2_cong(+bits: Nat, +a1: Nat, +a2: Nat, +k1: Nat, +k2: Nat, ea: {a1 == a2 : Nat}, ek: {k1 == k2 : Nat})
  -> {Spec.xor(bits, a1, k1) == Spec.xor(bits, a2, k2) : Nat}:
  Equal.trans(Nat, Spec.xor(bits, a1, k1), Spec.xor(bits, a2, k1), Spec.xor(bits, a2, k2),
    Equal.cong(Nat, Nat, x => Spec.xor(bits, x, k1), a1, a2, ea),
    Equal.cong(Nat, Nat, y => Spec.xor(bits, a2, y), k1, k2, ek))

def hw_qr_cong(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, eq: {q1 == q2 : Nat}, er: {r1 == r2 : Nat})
  -> {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(q1, m), r1), Nat.add(Nat.mul(q2, m), r1), Nat.add(Nat.mul(q2, m), r2),
    Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, m), r1), q1, q2, eq),
    Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(q2, m), y), r1, r2, er))

# d == s 8 and s < n give d / 8 < n and d % 8 == 0.
def hw_dest_in(+d: Nat, +s: Nat, +n: Nat, +ed: {d == Nat.mul(s, 8n) : Nat}, sl: {Nat.is_lt(s, n) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(d, 8n), n) == True{} : Bool} & {Nat.mod(d, 8n) == 0n : Nat}:
  (Equal.trans(Bool, Nat.is_lt(Nat.div(d, 8n), n), Nat.is_lt(s, n), True{},
     Equal.trans(Bool, Nat.is_lt(Nat.div(d, 8n), n), Nat.is_lt(Nat.div(Nat.mul(s, 8n), 8n), n), Nat.is_lt(s, n),
       Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.div(x, 8n), n), d, Nat.mul(s, 8n), ed),
       Equal.cong(Nat, Bool, x => Nat.is_lt(x, n), Nat.div(Nat.mul(s, 8n), 8n), s, hw_div8(s))), sl),
   Equal.trans(Nat, Nat.mod(d, 8n), Nat.mod(Nat.mul(s, 8n), 8n), 0n,
     Equal.cong(Nat, Nat, x => Nat.mod(x, 8n), d, Nat.mul(s, 8n), ed), hw_mod8(s)))

def hw_swap(-A: Type, -B: Type, p: A & B) -> B & A:
  match p:
    case (a, b):
      (b, a)

# The linear chunk index of (t, i): c = t + 128 i < 512, and it determines (t, i).
def hw_c_comm(+t: Nat, +i: Nat) -> {Impl.ld_c(t, i) == Nat.add(Nat.mul(i, 128n), t) : Nat}:
  Ar.ar_add_comm(t, Nat.mul(i, 128n))

def hw_c_lt(+t: Nat, +i: Nat, tt: {Nat.is_lt(t, 128n) == True{} : Bool}, ii: {Nat.is_lt(i, 4n) == True{} : Bool})
  -> {Nat.is_lt(Impl.ld_c(t, i), 512n) == True{} : Bool}:
  %Equal.sym(Nat, Impl.ld_c(t, i), Nat.add(Nat.mul(i, 128n), t), hw_c_comm(t, i)) : {Nat.is_lt(_, 512n) == True{} : Bool}
  Ar.p7_mr_lt(i, t, 4n, 128n, ii, tt)

def hw_c_inj(+t1: Nat, +i1: Nat, +t2: Nat, +i2: Nat, tt1: {Nat.is_lt(t1, 128n) == True{} : Bool},
    tt2: {Nat.is_lt(t2, 128n) == True{} : Bool}, e: {Impl.ld_c(t1, i1) == Impl.ld_c(t2, i2) : Nat})
  -> {t1 == t2 : Nat} & {i1 == i2 : Nat}:
  +same = Equal.trans(Nat, Nat.add(Nat.mul(i1, 128n), t1), Impl.ld_c(t1, i1), Nat.add(Nat.mul(i2, 128n), t2),
    Equal.sym(Nat, Impl.ld_c(t1, i1), Nat.add(Nat.mul(i1, 128n), t1), hw_c_comm(t1, i1)),
    Equal.trans(Nat, Impl.ld_c(t1, i1), Impl.ld_c(t2, i2), Nat.add(Nat.mul(i2, 128n), t2), e, hw_c_comm(t2, i2)))
  hw_swap({i1 == i2 : Nat}, {t1 == t2 : Nat}, Ar.ar_divmod_inj(i1, t1, i2, t2, 128n, tt1, tt2, same))

# ---- A stage ----

def hw_a_key(+row: Nat) -> Nat:
  Nat.mod(Nat.div(row, 2n), 4n)

def hw_adc(+c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(c, 4n), 32n), Nat.mul(Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), 8n))

def hw_a_slot(+c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(c, 4n), 4n), Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)))

def hw_a_unfold(+t: Nat, +i: Nat) -> {Impl.a_dest(t, i) == hw_adc(Impl.ld_c(t, i)) : Nat}:
  {==}

def hw_a_x(+c: Nat) -> {Nat.is_lt(Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), 4n) == True{} : Bool} &
    {Spec.xor(2n, Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), hw_a_key(Nat.div(c, 4n))) == Nat.mod(c, 4n) : Nat}:
  hw_xa(Nat.mod(c, 4n), hw_a_key(Nat.div(c, 4n)), Ar.ard_dm_lt(c, 4n, {==}), Ar.ard_dm_lt(Nat.div(Nat.div(c, 4n), 2n), 4n, {==}))

def hw_a_dest_slot(+c: Nat) -> {hw_adc(c) == Nat.mul(hw_a_slot(c), 8n) : Nat}:
  hw_slot(Nat.div(c, 4n), Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), 4n, 32n, {==})

def hw_a_slot_lt(+c: Nat, cl: {Nat.is_lt(c, 512n) == True{} : Bool}) -> {Nat.is_lt(hw_a_slot(c), 512n) == True{} : Bool}:
  +rl = Ar.ard_rt(Nat.is_lt(c, Nat.mul(128n, 4n)), Nat.is_lt(Nat.div(c, 4n), 128n),
    Equal.sym(Bool, Nat.is_lt(Nat.div(c, 4n), 128n), Nat.is_lt(c, Nat.mul(128n, 4n)), Ar.ar_div_lt(128n, c, 4n, {==})), cl)
  Ar.p7_mr_lt(Nat.div(c, 4n), Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), 128n, 4n, rl,
    Ar.ard_fst({Nat.is_lt(Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), 4n) == True{} : Bool},
      {Spec.xor(2n, Impl.a_pc(Nat.div(c, 4n), Nat.mod(c, 4n)), hw_a_key(Nat.div(c, 4n))) == Nat.mod(c, 4n) : Nat}, hw_a_x(c)))

# Two chunk indices with the same destination slot are equal.
def hw_a_slot_inj(+c1: Nat, +c2: Nat, +e: {hw_a_slot(c1) == hw_a_slot(c2) : Nat}) -> {c1 == c2 : Nat}:
  +pc1 = Impl.a_pc(Nat.div(c1, 4n), Nat.mod(c1, 4n))
  +pc2 = Impl.a_pc(Nat.div(c2, 4n), Nat.mod(c2, 4n))
  +k1 = hw_a_key(Nat.div(c1, 4n))
  +k2 = hw_a_key(Nat.div(c2, 4n))
  +pl1 = Ar.ard_fst({Nat.is_lt(pc1, 4n) == True{} : Bool}, {Spec.xor(2n, pc1, k1) == Nat.mod(c1, 4n) : Nat}, hw_a_x(c1))
  +pl2 = Ar.ard_fst({Nat.is_lt(pc2, 4n) == True{} : Bool}, {Spec.xor(2n, pc2, k2) == Nat.mod(c2, 4n) : Nat}, hw_a_x(c2))
  +iv1 = Ar.ard_snd({Nat.is_lt(pc1, 4n) == True{} : Bool}, {Spec.xor(2n, pc1, k1) == Nat.mod(c1, 4n) : Nat}, hw_a_x(c1))
  +iv2 = Ar.ard_snd({Nat.is_lt(pc2, 4n) == True{} : Bool}, {Spec.xor(2n, pc2, k2) == Nat.mod(c2, 4n) : Nat}, hw_a_x(c2))
  +er = Ar.ard_fst({Nat.div(c1, 4n) == Nat.div(c2, 4n) : Nat}, {pc1 == pc2 : Nat},
    Ar.ar_divmod_inj(Nat.div(c1, 4n), pc1, Nat.div(c2, 4n), pc2, 4n, pl1, pl2, e))
  +ep = Ar.ard_snd({Nat.div(c1, 4n) == Nat.div(c2, 4n) : Nat}, {pc1 == pc2 : Nat},
    Ar.ar_divmod_inj(Nat.div(c1, 4n), pc1, Nat.div(c2, 4n), pc2, 4n, pl1, pl2, e))
  +ek = Equal.cong(Nat, Nat, r => hw_a_key(r), Nat.div(c1, 4n), Nat.div(c2, 4n), er)
  +ech = Equal.trans(Nat, Nat.mod(c1, 4n), Spec.xor(2n, pc1, k1), Nat.mod(c2, 4n),
    Equal.sym(Nat, Spec.xor(2n, pc1, k1), Nat.mod(c1, 4n), iv1),
    Equal.trans(Nat, Spec.xor(2n, pc1, k1), Spec.xor(2n, pc2, k2), Nat.mod(c2, 4n),
      hw_xor2_cong(2n, pc1, pc2, k1, k2, ep, ek), iv2))
  Equal.trans(Nat, c1, Nat.add(Nat.mul(Nat.div(c1, 4n), 4n), Nat.mod(c1, 4n)), c2,
    Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(c1, 4n), 4n), Nat.mod(c1, 4n)), c1, Ar.ard_dm_eq(c1, 4n, {==})),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(c1, 4n), 4n), Nat.mod(c1, 4n)), Nat.add(Nat.mul(Nat.div(c2, 4n), 4n), Nat.mod(c2, 4n)), c2,
      hw_qr_cong(Nat.div(c1, 4n), Nat.mod(c1, 4n), Nat.div(c2, 4n), Nat.mod(c2, 4n), 4n, er, ech),
      Ar.ard_dm_eq(c2, 4n, {==})))

# a_dest(t, i) == slot(ld_c(t, i)) 8
def hw_a_dest_eq(+t: Nat, +i: Nat) -> {Impl.a_dest(t, i) == Nat.mul(hw_a_slot(Impl.ld_c(t, i)), 8n) : Nat}:
  Equal.trans(Nat, Impl.a_dest(t, i), hw_adc(Impl.ld_c(t, i)), Nat.mul(hw_a_slot(Impl.ld_c(t, i)), 8n),
    hw_a_unfold(t, i), hw_a_dest_slot(Impl.ld_c(t, i)))

def Laws.a_stage_inj(t1, i1, t2, i2, tt1, ii1, tt2, ii2, same):
  +c1 = Impl.ld_c(t1, i1)
  +c2 = Impl.ld_c(t2, i2)
  +d = Equal.trans(Nat, Nat.mul(hw_a_slot(c1), 8n), Impl.a_dest(t1, i1), Nat.mul(hw_a_slot(c2), 8n),
    Equal.sym(Nat, Impl.a_dest(t1, i1), Nat.mul(hw_a_slot(c1), 8n), hw_a_dest_eq(t1, i1)),
    Equal.trans(Nat, Impl.a_dest(t1, i1), Impl.a_dest(t2, i2), Nat.mul(hw_a_slot(c2), 8n), same, hw_a_dest_eq(t2, i2)))
  hw_c_inj(t1, i1, t2, i2, tt1, tt2, hw_a_slot_inj(c1, c2, hw_mul8_inj(hw_a_slot(c1), hw_a_slot(c2), d)))

def Laws.a_stage_in(t, i, tt, ii):
  +c = Impl.ld_c(t, i)
  hw_dest_in(Impl.a_dest(t, i), hw_a_slot(c), 512n,
    Equal.trans(Nat, Impl.a_dest(t, i), hw_adc(c), Nat.mul(hw_a_slot(c), 8n), hw_a_unfold(t, i), hw_a_dest_slot(c)),
    hw_a_slot_lt(c, hw_c_lt(t, i, tt, ii)))

def hw_a_slot_of(+q: Nat, +r: Nat) -> Nat:
  Nat.add(Nat.mul(q, 4n), Impl.a_pc(q, r))

def hw_a_cong2(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, eq: {q1 == q2 : Nat}, er: {r1 == r2 : Nat})
  -> {hw_a_slot_of(q1, r1) == hw_a_slot_of(q2, r2) : Nat}:
  Equal.trans(Nat, hw_a_slot_of(q1, r1), hw_a_slot_of(q2, r1), hw_a_slot_of(q2, r2),
    Equal.cong(Nat, Nat, x => hw_a_slot_of(x, r1), q1, q2, eq),
    Equal.cong(Nat, Nat, y => hw_a_slot_of(q2, y), r1, r2, er))

# t = c % 128, i = c / 128 give ld_c(t, i) == c.
def hw_c_back(+c: Nat) -> {Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n)) == c : Nat}:
  Equal.trans(Nat, Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n)), Nat.add(Nat.mul(Nat.div(c, 128n), 128n), Nat.mod(c, 128n)), c,
    hw_c_comm(Nat.mod(c, 128n), Nat.div(c, 128n)), Ar.ard_dm_eq(c, 128n, {==}))

# c < 512 gives c / 128 < 4.
def hw_c_div(+c: Nat, cl: {Nat.is_lt(c, 512n) == True{} : Bool}) -> {Nat.is_lt(Nat.div(c, 128n), 4n) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.div(c, 128n), 4n), Nat.is_lt(c, Nat.mul(4n, 128n)), Ar.ar_div_lt(4n, c, 128n, {==}), cl)

# s < 512 (4 chunks per row) gives s / 4 < 128.
def hw_row_lt(+s: Nat, +R: Nat, +C: Nat, +cpos: {Nat.is_lt(0n, C) == True{} : Bool},
    sl: {Nat.is_lt(s, Nat.mul(R, C)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(s, C), R) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.div(s, C), R), Nat.is_lt(s, Nat.mul(R, C)), Ar.ar_div_lt(R, s, C, cpos), sl)

def hw_a_xs(+s: Nat) -> {Nat.is_lt(Spec.a_chunk(s), 4n) == True{} : Bool} &
    {Spec.xor(2n, Spec.a_chunk(s), hw_a_key(Nat.div(s, 4n))) == Nat.mod(s, 4n) : Nat}:
  hw_xa(Nat.mod(s, 4n), hw_a_key(Nat.div(s, 4n)), Ar.ard_dm_lt(s, 4n, {==}), Ar.ard_dm_lt(Nat.div(Nat.div(s, 4n), 2n), 4n, {==}))

def Laws.a_stage_cover(s, ss):
  +sl = ss
  +row = Nat.div(s, 4n)
  +ch = Spec.a_chunk(s)
  +c = Spec.a_own_c(s)
  +chl = Ar.ard_fst({Nat.is_lt(ch, 4n) == True{} : Bool}, {Spec.xor(2n, ch, hw_a_key(row)) == Nat.mod(s, 4n) : Nat}, hw_a_xs(s))
  +inv = Ar.ard_snd({Nat.is_lt(ch, 4n) == True{} : Bool}, {Spec.xor(2n, ch, hw_a_key(row)) == Nat.mod(s, 4n) : Nat}, hw_a_xs(s))
  +cl = Ar.p7_mr_lt(row, ch, 128n, 4n, hw_row_lt(s, 128n, 4n, {==}, sl), chl)
  # slot(c) == s
  +sq = Equal.trans(Nat, hw_a_slot(c), hw_a_slot_of(row, ch), s,
    hw_a_cong2(Nat.div(c, 4n), Nat.mod(c, 4n), row, ch, Ar.p7_div_q(row, ch, 4n, chl), Ar.p7_mod_r(row, ch, 4n, chl)),
    Equal.trans(Nat, hw_a_slot_of(row, ch), Nat.add(Nat.mul(row, 4n), Nat.mod(s, 4n)), s,
      Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(row, 4n), x), Impl.a_pc(row, ch), Nat.mod(s, 4n), inv),
      Ar.ard_dm_eq(s, 4n, {==})))
  (Ar.ard_dm_lt(c, 128n, {==}), hw_c_div(c, cl),
   Equal.trans(Nat, Impl.a_dest(Nat.mod(c, 128n), Nat.div(c, 128n)), Nat.mul(hw_a_slot(Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n))), 8n),
     Nat.mul(s, 8n), hw_a_dest_eq(Nat.mod(c, 128n), Nat.div(c, 128n)),
     Equal.trans(Nat, Nat.mul(hw_a_slot(Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n))), 8n), Nat.mul(hw_a_slot(c), 8n), Nat.mul(s, 8n),
       Equal.cong(Nat, Nat, x => Nat.mul(hw_a_slot(x), 8n), Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n)), c, hw_c_back(c)),
       Equal.cong(Nat, Nat, x => Nat.mul(x, 8n), hw_a_slot(c), s, sq))))

# ---- B stage ----

def hw_b_key(+row: Nat) -> Nat:
  Nat.mod(row, 8n)

def hw_bdc(+c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(c, 16n), 128n), Nat.mul(Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), 8n))

def hw_b_slot(+c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(c, 16n), 16n), Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)))

def hw_b_unfold(+t: Nat, +i: Nat) -> {Impl.b_dest(t, i) == hw_bdc(Impl.ld_c(t, i)) : Nat}:
  {==}

def hw_b_x(+c: Nat) -> {Nat.is_lt(Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), 16n) == True{} : Bool} &
    {Spec.xor(4n, Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), hw_b_key(Nat.div(c, 16n))) == Nat.mod(c, 16n) : Nat}:
  hw_xb(Nat.mod(c, 16n), hw_b_key(Nat.div(c, 16n)), Ar.ard_dm_lt(c, 16n, {==}), Ar.ard_dm_lt(Nat.div(c, 16n), 8n, {==}))

def hw_b_dest_slot(+c: Nat) -> {hw_bdc(c) == Nat.mul(hw_b_slot(c), 8n) : Nat}:
  hw_slot(Nat.div(c, 16n), Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), 16n, 128n, {==})

def hw_b_slot_lt(+c: Nat, cl: {Nat.is_lt(c, 512n) == True{} : Bool}) -> {Nat.is_lt(hw_b_slot(c), 512n) == True{} : Bool}:
  +rl = Ar.ard_rt(Nat.is_lt(c, Nat.mul(32n, 16n)), Nat.is_lt(Nat.div(c, 16n), 32n),
    Equal.sym(Bool, Nat.is_lt(Nat.div(c, 16n), 32n), Nat.is_lt(c, Nat.mul(32n, 16n)), Ar.ar_div_lt(32n, c, 16n, {==})), cl)
  Ar.p7_mr_lt(Nat.div(c, 16n), Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), 32n, 16n, rl,
    Ar.ard_fst({Nat.is_lt(Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), 16n) == True{} : Bool},
      {Spec.xor(4n, Impl.b_pc(Nat.div(c, 16n), Nat.mod(c, 16n)), hw_b_key(Nat.div(c, 16n))) == Nat.mod(c, 16n) : Nat}, hw_b_x(c)))

# Two chunk indices with the same destination slot are equal.
def hw_b_slot_inj(+c1: Nat, +c2: Nat, +e: {hw_b_slot(c1) == hw_b_slot(c2) : Nat}) -> {c1 == c2 : Nat}:
  +pc1 = Impl.b_pc(Nat.div(c1, 16n), Nat.mod(c1, 16n))
  +pc2 = Impl.b_pc(Nat.div(c2, 16n), Nat.mod(c2, 16n))
  +k1 = hw_b_key(Nat.div(c1, 16n))
  +k2 = hw_b_key(Nat.div(c2, 16n))
  +pl1 = Ar.ard_fst({Nat.is_lt(pc1, 16n) == True{} : Bool}, {Spec.xor(4n, pc1, k1) == Nat.mod(c1, 16n) : Nat}, hw_b_x(c1))
  +pl2 = Ar.ard_fst({Nat.is_lt(pc2, 16n) == True{} : Bool}, {Spec.xor(4n, pc2, k2) == Nat.mod(c2, 16n) : Nat}, hw_b_x(c2))
  +iv1 = Ar.ard_snd({Nat.is_lt(pc1, 16n) == True{} : Bool}, {Spec.xor(4n, pc1, k1) == Nat.mod(c1, 16n) : Nat}, hw_b_x(c1))
  +iv2 = Ar.ard_snd({Nat.is_lt(pc2, 16n) == True{} : Bool}, {Spec.xor(4n, pc2, k2) == Nat.mod(c2, 16n) : Nat}, hw_b_x(c2))
  +er = Ar.ard_fst({Nat.div(c1, 16n) == Nat.div(c2, 16n) : Nat}, {pc1 == pc2 : Nat},
    Ar.ar_divmod_inj(Nat.div(c1, 16n), pc1, Nat.div(c2, 16n), pc2, 16n, pl1, pl2, e))
  +ep = Ar.ard_snd({Nat.div(c1, 16n) == Nat.div(c2, 16n) : Nat}, {pc1 == pc2 : Nat},
    Ar.ar_divmod_inj(Nat.div(c1, 16n), pc1, Nat.div(c2, 16n), pc2, 16n, pl1, pl2, e))
  +ek = Equal.cong(Nat, Nat, r => hw_b_key(r), Nat.div(c1, 16n), Nat.div(c2, 16n), er)
  +ech = Equal.trans(Nat, Nat.mod(c1, 16n), Spec.xor(4n, pc1, k1), Nat.mod(c2, 16n),
    Equal.sym(Nat, Spec.xor(4n, pc1, k1), Nat.mod(c1, 16n), iv1),
    Equal.trans(Nat, Spec.xor(4n, pc1, k1), Spec.xor(4n, pc2, k2), Nat.mod(c2, 16n),
      hw_xor2_cong(4n, pc1, pc2, k1, k2, ep, ek), iv2))
  Equal.trans(Nat, c1, Nat.add(Nat.mul(Nat.div(c1, 16n), 16n), Nat.mod(c1, 16n)), c2,
    Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(c1, 16n), 16n), Nat.mod(c1, 16n)), c1, Ar.ard_dm_eq(c1, 16n, {==})),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(c1, 16n), 16n), Nat.mod(c1, 16n)), Nat.add(Nat.mul(Nat.div(c2, 16n), 16n), Nat.mod(c2, 16n)), c2,
      hw_qr_cong(Nat.div(c1, 16n), Nat.mod(c1, 16n), Nat.div(c2, 16n), Nat.mod(c2, 16n), 16n, er, ech),
      Ar.ard_dm_eq(c2, 16n, {==})))

# a_dest(t, i) == slot(ld_c(t, i)) 8
def hw_b_dest_eq(+t: Nat, +i: Nat) -> {Impl.b_dest(t, i) == Nat.mul(hw_b_slot(Impl.ld_c(t, i)), 8n) : Nat}:
  Equal.trans(Nat, Impl.b_dest(t, i), hw_bdc(Impl.ld_c(t, i)), Nat.mul(hw_b_slot(Impl.ld_c(t, i)), 8n),
    hw_b_unfold(t, i), hw_b_dest_slot(Impl.ld_c(t, i)))

def Laws.b_stage_inj(t1, i1, t2, i2, tt1, ii1, tt2, ii2, same):
  +c1 = Impl.ld_c(t1, i1)
  +c2 = Impl.ld_c(t2, i2)
  +d = Equal.trans(Nat, Nat.mul(hw_b_slot(c1), 8n), Impl.b_dest(t1, i1), Nat.mul(hw_b_slot(c2), 8n),
    Equal.sym(Nat, Impl.b_dest(t1, i1), Nat.mul(hw_b_slot(c1), 8n), hw_b_dest_eq(t1, i1)),
    Equal.trans(Nat, Impl.b_dest(t1, i1), Impl.b_dest(t2, i2), Nat.mul(hw_b_slot(c2), 8n), same, hw_b_dest_eq(t2, i2)))
  hw_c_inj(t1, i1, t2, i2, tt1, tt2, hw_b_slot_inj(c1, c2, hw_mul8_inj(hw_b_slot(c1), hw_b_slot(c2), d)))

def Laws.b_stage_in(t, i, tt, ii):
  +c = Impl.ld_c(t, i)
  hw_dest_in(Impl.b_dest(t, i), hw_b_slot(c), 512n,
    Equal.trans(Nat, Impl.b_dest(t, i), hw_bdc(c), Nat.mul(hw_b_slot(c), 8n), hw_b_unfold(t, i), hw_b_dest_slot(c)),
    hw_b_slot_lt(c, hw_c_lt(t, i, tt, ii)))


def hw_b_slot_of(+q: Nat, +r: Nat) -> Nat:
  Nat.add(Nat.mul(q, 16n), Impl.b_pc(q, r))

def hw_b_cong2(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, eq: {q1 == q2 : Nat}, er: {r1 == r2 : Nat})
  -> {hw_b_slot_of(q1, r1) == hw_b_slot_of(q2, r2) : Nat}:
  Equal.trans(Nat, hw_b_slot_of(q1, r1), hw_b_slot_of(q2, r1), hw_b_slot_of(q2, r2),
    Equal.cong(Nat, Nat, x => hw_b_slot_of(x, r1), q1, q2, eq),
    Equal.cong(Nat, Nat, y => hw_b_slot_of(q2, y), r1, r2, er))

def hw_b_xs(+s: Nat) -> {Nat.is_lt(Spec.b_chunk(s), 16n) == True{} : Bool} &
    {Spec.xor(4n, Spec.b_chunk(s), hw_b_key(Nat.div(s, 16n))) == Nat.mod(s, 16n) : Nat}:
  hw_xb(Nat.mod(s, 16n), hw_b_key(Nat.div(s, 16n)), Ar.ard_dm_lt(s, 16n, {==}), Ar.ard_dm_lt(Nat.div(s, 16n), 8n, {==}))

def Laws.b_stage_cover(s, ss):
  +sl = ss
  +row = Nat.div(s, 16n)
  +ch = Spec.b_chunk(s)
  +c = Spec.b_own_c(s)
  +chl = Ar.ard_fst({Nat.is_lt(ch, 16n) == True{} : Bool}, {Spec.xor(4n, ch, hw_b_key(row)) == Nat.mod(s, 16n) : Nat}, hw_b_xs(s))
  +inv = Ar.ard_snd({Nat.is_lt(ch, 16n) == True{} : Bool}, {Spec.xor(4n, ch, hw_b_key(row)) == Nat.mod(s, 16n) : Nat}, hw_b_xs(s))
  +cl = Ar.p7_mr_lt(row, ch, 32n, 16n, hw_row_lt(s, 32n, 16n, {==}, sl), chl)
  # slot(c) == s
  +sq = Equal.trans(Nat, hw_b_slot(c), hw_b_slot_of(row, ch), s,
    hw_b_cong2(Nat.div(c, 16n), Nat.mod(c, 16n), row, ch, Ar.p7_div_q(row, ch, 16n, chl), Ar.p7_mod_r(row, ch, 16n, chl)),
    Equal.trans(Nat, hw_b_slot_of(row, ch), Nat.add(Nat.mul(row, 16n), Nat.mod(s, 16n)), s,
      Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(row, 16n), x), Impl.b_pc(row, ch), Nat.mod(s, 16n), inv),
      Ar.ard_dm_eq(s, 16n, {==})))
  (Ar.ard_dm_lt(c, 128n, {==}), hw_c_div(c, cl),
   Equal.trans(Nat, Impl.b_dest(Nat.mod(c, 128n), Nat.div(c, 128n)), Nat.mul(hw_b_slot(Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n))), 8n),
     Nat.mul(s, 8n), hw_b_dest_eq(Nat.mod(c, 128n), Nat.div(c, 128n)),
     Equal.trans(Nat, Nat.mul(hw_b_slot(Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n))), 8n), Nat.mul(hw_b_slot(c), 8n), Nat.mul(s, 8n),
       Equal.cong(Nat, Nat, x => Nat.mul(hw_b_slot(x), 8n), Impl.ld_c(Nat.mod(c, 128n), Nat.div(c, 128n)), c, hw_c_back(c)),
       Equal.cong(Nat, Nat, x => Nat.mul(x, 8n), hw_b_slot(c), s, sq))))


# ---- in-tile store map ----

# The in-tile row / column of a store, over its digits.
def hw_Lr(+a: Nat, +i: Nat, +g: Nat, +h: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), g), Nat.mul(h, 8n))

def hw_Lc(+b: Nat, +j: Nat, +q: Nat, +e: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.mul(b, 64n), Nat.mul(j, 8n)), Nat.mul(q, 2n)), e)

def hw_row_unfold(+t: Nat, +i: Nat, +h: Nat) -> {Impl.row_of(0n, t, i, h) == hw_Lr(Impl.wm(t), i, Impl.gq(t), h) : Nat}:
  {==}

def hw_col_unfold(+t: Nat, +j: Nat, +e: Nat) -> {Impl.col_of(0n, t, j, e) == hw_Lc(Impl.wn(t), j, Impl.tq(t), e) : Nat}:
  {==}

# (x k + y) m == x KM + y m when k m == KM.
def hw_nest(+x: Nat, +y: Nat, +k: Nat, +m: Nat, +KM: Nat, e: {Nat.mul(k, m) == KM : Nat})
  -> {Nat.mul(Nat.add(Nat.mul(x, k), y), m) == Nat.add(Nat.mul(x, KM), Nat.mul(y, m)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(x, k), y), m), Nat.add(Nat.mul(Nat.mul(x, k), m), Nat.mul(y, m)),
    Nat.add(Nat.mul(x, KM), Nat.mul(y, m)),
    Ar.ar_mul_add_l(Nat.mul(x, k), y, m),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(y, m)), Nat.mul(Nat.mul(x, k), m), Nat.mul(x, KM),
      Equal.trans(Nat, Nat.mul(Nat.mul(x, k), m), Nat.mul(x, Nat.mul(k, m)), Nat.mul(x, KM),
        Ar.ar_mul_assoc(x, k, m), Equal.cong(Nat, Nat, w => Nat.mul(x, w), Nat.mul(k, m), KM, e))))

# ((p + g) + H) == ((p + H) + g)
def hw_swap_last(+p: Nat, +g: Nat, +H: Nat) -> {Nat.add(Nat.add(p, g), H) == Nat.add(Nat.add(p, H), g) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(p, g), H), Nat.add(p, Nat.add(g, H)), Nat.add(Nat.add(p, H), g),
    Ar.ar_add_assoc(p, g, H),
    Equal.trans(Nat, Nat.add(p, Nat.add(g, H)), Nat.add(p, Nat.add(H, g)), Nat.add(Nat.add(p, H), g),
      Equal.cong(Nat, Nat, z => Nat.add(p, z), Nat.add(g, H), Nat.add(H, g), Ar.ar_add_comm(g, H)),
      Equal.sym(Nat, Nat.add(Nat.add(p, H), g), Nat.add(p, Nat.add(H, g)), Ar.ar_add_assoc(p, H, g))))

# Nested (mixed radix) forms: row = ((a 4 + i) 2 + h) 8 + g, col = ((b 8 + j) 4 + q) 2 + e.
def hw_Nr(+a: Nat, +i: Nat, +g: Nat, +h: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(a, 4n), i), 2n), h), 8n), g)

def hw_Nc(+b: Nat, +j: Nat, +q: Nat, +e: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, 8n), j), 4n), q), 2n), e)

def hw_row_nest(+a: Nat, +i: Nat, +g: Nat, +h: Nat) -> {hw_Lr(a, i, g, h) == hw_Nr(a, i, g, h) : Nat}:
  +i1 = Nat.add(Nat.mul(a, 4n), i)
  +e1 = Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(i1, 2n), h), 8n), Nat.add(Nat.mul(i1, 16n), Nat.mul(h, 8n)),
    Nat.add(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), Nat.mul(h, 8n)),
    hw_nest(i1, h, 2n, 8n, 16n, {==}),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(h, 8n)), Nat.mul(i1, 16n), Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)),
      hw_nest(a, i, 4n, 16n, 64n, {==})))
  Equal.trans(Nat, hw_Lr(a, i, g, h), Nat.add(Nat.add(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), Nat.mul(h, 8n)), g), hw_Nr(a, i, g, h),
    hw_swap_last(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), g, Nat.mul(h, 8n)),
    Equal.cong(Nat, Nat, z => Nat.add(z, g), Nat.add(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), Nat.mul(h, 8n)),
      Nat.mul(Nat.add(Nat.mul(i1, 2n), h), 8n), Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(i1, 2n), h), 8n),
        Nat.add(Nat.add(Nat.mul(a, 64n), Nat.mul(i, 16n)), Nat.mul(h, 8n)), e1)))

def hw_col_nest(+b: Nat, +j: Nat, +q: Nat, +e: Nat) -> {hw_Lc(b, j, q, e) == hw_Nc(b, j, q, e) : Nat}:
  +j1 = Nat.add(Nat.mul(b, 8n), j)
  +e1 = Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(j1, 4n), q), 2n), Nat.add(Nat.mul(j1, 8n), Nat.mul(q, 2n)),
    Nat.add(Nat.add(Nat.mul(b, 64n), Nat.mul(j, 8n)), Nat.mul(q, 2n)),
    hw_nest(j1, q, 4n, 2n, 8n, {==}),
    Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(q, 2n)), Nat.mul(j1, 8n), Nat.add(Nat.mul(b, 64n), Nat.mul(j, 8n)),
      hw_nest(b, j, 8n, 8n, 64n, {==})))
  Equal.cong(Nat, Nat, z => Nat.add(z, e), Nat.add(Nat.add(Nat.mul(b, 64n), Nat.mul(j, 8n)), Nat.mul(q, 2n)),
    Nat.mul(Nat.add(Nat.mul(j1, 4n), q), 2n), Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(j1, 4n), q), 2n),
      Nat.add(Nat.add(Nat.mul(b, 64n), Nat.mul(j, 8n)), Nat.mul(q, 2n)), e1))

# Peel one digit: (q1 m + r1 == q2 m + r2, r < m) gives both equalities.
def hw_peel_q(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {q1 == q2 : Nat}:
  Ar.ard_fst({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

def hw_peel_r(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {r1 == r2 : Nat}:
  Ar.ard_snd({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

# Thread digits: g = (t % 32) / 4 < 8, q = (t % 32) % 4 < 4, and t == ((wm 2 + wn) 32 + (g 4 + q)).
def hw_g_lt(+t: Nat) -> {Nat.is_lt(Impl.gq(t), 8n) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Impl.gq(t), 8n), Nat.is_lt(Nat.mod(t, 32n), Nat.mul(8n, 4n)), Ar.ar_div_lt(8n, Nat.mod(t, 32n), 4n, {==}),
    Ar.ard_dm_lt(t, 32n, {==}))

def hw_q_lt(+t: Nat) -> {Nat.is_lt(Impl.tq(t), 4n) == True{} : Bool}:
  Ar.ard_dm_lt(Nat.mod(t, 32n), 4n, {==})

def hw_wn_lt(+t: Nat) -> {Nat.is_lt(Impl.wn(t), 2n) == True{} : Bool}:
  Ar.ard_dm_lt(Nat.div(t, 32n), 2n, {==})

def hw_wm_lt(+t: Nat, tt: {Nat.is_lt(t, 128n) == True{} : Bool}) -> {Nat.is_lt(Impl.wm(t), 2n) == True{} : Bool}:
  +w4 = Ar.ard_tr(Nat.is_lt(Nat.div(t, 32n), 4n), Nat.is_lt(t, Nat.mul(4n, 32n)), Ar.ar_div_lt(4n, t, 32n, {==}), tt)
  Ar.ard_tr(Nat.is_lt(Impl.wm(t), 2n), Nat.is_lt(Nat.div(t, 32n), Nat.mul(2n, 2n)), Ar.ar_div_lt(2n, Nat.div(t, 32n), 2n, {==}), w4)

def hw_t_digits(+t: Nat)
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(Impl.wm(t), 2n), Impl.wn(t)), 32n), Nat.add(Nat.mul(Impl.gq(t), 4n), Impl.tq(t))) == t : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.mul(Impl.wm(t), 2n), Impl.wn(t)), Nat.div(t, 32n), Ar.ard_dm_eq(Nat.div(t, 32n), 2n, {==})) : {Nat.add(Nat.mul(_, 32n), Nat.add(Nat.mul(Impl.gq(t), 4n), Impl.tq(t))) == t : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(Impl.gq(t), 4n), Impl.tq(t)), Nat.mod(t, 32n), Ar.ard_dm_eq(Nat.mod(t, 32n), 4n, {==})) : {Nat.add(Nat.mul(Nat.div(t, 32n), 32n), _) == t : Nat}
  Ar.ard_dm_eq(t, 32n, {==})

def hw_row_N(+t: Nat, +i: Nat, +h: Nat) -> {Impl.row_of(0n, t, i, h) == hw_Nr(Impl.wm(t), i, Impl.gq(t), h) : Nat}:
  Equal.trans(Nat, Impl.row_of(0n, t, i, h), hw_Lr(Impl.wm(t), i, Impl.gq(t), h), hw_Nr(Impl.wm(t), i, Impl.gq(t), h),
    hw_row_unfold(t, i, h), hw_row_nest(Impl.wm(t), i, Impl.gq(t), h))

def hw_col_N(+t: Nat, +j: Nat, +e: Nat) -> {Impl.col_of(0n, t, j, e) == hw_Nc(Impl.wn(t), j, Impl.tq(t), e) : Nat}:
  Equal.trans(Nat, Impl.col_of(0n, t, j, e), hw_Lc(Impl.wn(t), j, Impl.tq(t), e), hw_Nc(Impl.wn(t), j, Impl.tq(t), e),
    hw_col_unfold(t, j, e), hw_col_nest(Impl.wn(t), j, Impl.tq(t), e))

def hw_tf(+a: Nat, +b: Nat, +g: Nat, +q: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(a, 2n), b), 32n), Nat.add(Nat.mul(g, 4n), q))

def hw_tf_cong(+a1: Nat, +b1: Nat, +g1: Nat, +q1: Nat, +a2: Nat, +b2: Nat, +g2: Nat, +q2: Nat,
    ea: {a1 == a2 : Nat}, eb: {b1 == b2 : Nat}, eg: {g1 == g2 : Nat}, eq: {q1 == q2 : Nat})
  -> {hw_tf(a1, b1, g1, q1) == hw_tf(a2, b2, g2, q2) : Nat}:
  Equal.trans(Nat, hw_tf(a1, b1, g1, q1), hw_tf(a2, b1, g1, q1), hw_tf(a2, b2, g2, q2),
    Equal.cong(Nat, Nat, x => hw_tf(x, b1, g1, q1), a1, a2, ea),
    Equal.trans(Nat, hw_tf(a2, b1, g1, q1), hw_tf(a2, b2, g1, q1), hw_tf(a2, b2, g2, q2),
      Equal.cong(Nat, Nat, x => hw_tf(a2, x, g1, q1), b1, b2, eb),
      Equal.trans(Nat, hw_tf(a2, b2, g1, q1), hw_tf(a2, b2, g2, q1), hw_tf(a2, b2, g2, q2),
        Equal.cong(Nat, Nat, x => hw_tf(a2, b2, x, q1), g1, g2, eg),
        Equal.cong(Nat, Nat, x => hw_tf(a2, b2, g2, x), q1, q2, eq))))

def Laws.tile_store_inj(t1, i1, j1, h1, e1, t2, i2, j2, h2, e2, tt1, ii1, jj1, hh1, ee1, tt2, ii2, jj2, hh2, ee2, same_r, same_c):
  +i1b = ii1
  +i2b = ii2
  +h1b = hh1
  +h2b = hh2
  +j1b = jj1
  +j2b = jj2
  +e1b = ee1
  +e2b = ee2
  +a1 = Impl.wm(t1)
  +a2 = Impl.wm(t2)
  +g1 = Impl.gq(t1)
  +g2 = Impl.gq(t2)
  +b1 = Impl.wn(t1)
  +b2 = Impl.wn(t2)
  +q1 = Impl.tq(t1)
  +q2 = Impl.tq(t2)
  +X1a = Nat.add(Nat.mul(a1, 4n), i1)
  +X1b = Nat.add(Nat.mul(a2, 4n), i2)
  +X2a = Nat.add(Nat.mul(X1a, 2n), h1)
  +X2b = Nat.add(Nat.mul(X1b, 2n), h2)
  +Y1a = Nat.add(Nat.mul(b1, 8n), j1)
  +Y1b = Nat.add(Nat.mul(b2, 8n), j2)
  +Y2a = Nat.add(Nat.mul(Y1a, 4n), q1)
  +Y2b = Nat.add(Nat.mul(Y1b, 4n), q2)
  +er = Equal.trans(Nat, hw_Nr(a1, i1, g1, h1), Impl.row_of(0n, t1, i1, h1), hw_Nr(a2, i2, g2, h2),
    Equal.sym(Nat, Impl.row_of(0n, t1, i1, h1), hw_Nr(a1, i1, g1, h1), hw_row_N(t1, i1, h1)),
    Equal.trans(Nat, Impl.row_of(0n, t1, i1, h1), Impl.row_of(0n, t2, i2, h2), hw_Nr(a2, i2, g2, h2), same_r, hw_row_N(t2, i2, h2)))
  +ec = Equal.trans(Nat, hw_Nc(b1, j1, q1, e1), Impl.col_of(0n, t1, j1, e1), hw_Nc(b2, j2, q2, e2),
    Equal.sym(Nat, Impl.col_of(0n, t1, j1, e1), hw_Nc(b1, j1, q1, e1), hw_col_N(t1, j1, e1)),
    Equal.trans(Nat, Impl.col_of(0n, t1, j1, e1), Impl.col_of(0n, t2, j2, e2), hw_Nc(b2, j2, q2, e2), same_c, hw_col_N(t2, j2, e2)))
  +eX2 = hw_peel_q(X2a, g1, X2b, g2, 8n, hw_g_lt(t1), hw_g_lt(t2), er)
  +eg = hw_peel_r(X2a, g1, X2b, g2, 8n, hw_g_lt(t1), hw_g_lt(t2), er)
  +eX1 = hw_peel_q(X1a, h1, X1b, h2, 2n, h1b, h2b, eX2)
  +eh = hw_peel_r(X1a, h1, X1b, h2, 2n, h1b, h2b, eX2)
  +ea = hw_peel_q(a1, i1, a2, i2, 4n, i1b, i2b, eX1)
  +ei = hw_peel_r(a1, i1, a2, i2, 4n, i1b, i2b, eX1)
  +eY2 = hw_peel_q(Y2a, e1, Y2b, e2, 2n, e1b, e2b, ec)
  +ee = hw_peel_r(Y2a, e1, Y2b, e2, 2n, e1b, e2b, ec)
  +eY1 = hw_peel_q(Y1a, q1, Y1b, q2, 4n, hw_q_lt(t1), hw_q_lt(t2), eY2)
  +eq = hw_peel_r(Y1a, q1, Y1b, q2, 4n, hw_q_lt(t1), hw_q_lt(t2), eY2)
  +eb = hw_peel_q(b1, j1, b2, j2, 8n, j1b, j2b, eY1)
  +ej = hw_peel_r(b1, j1, b2, j2, 8n, j1b, j2b, eY1)
  +et = Equal.trans(Nat, t1, hw_tf(a1, b1, g1, q1), t2,
    Equal.sym(Nat, hw_tf(a1, b1, g1, q1), t1, hw_t_digits(t1)),
    Equal.trans(Nat, hw_tf(a1, b1, g1, q1), hw_tf(a2, b2, g2, q2), t2,
      hw_tf_cong(a1, b1, g1, q1, a2, b2, g2, q2, ea, eb, eg, eq), hw_t_digits(t2)))
  (et, ei, ej, eh, ee)

def Laws.tile_store_in(t, i, j, h, e, tt, ii, jj, hh, ee):
  +a = Impl.wm(t)
  +g = Impl.gq(t)
  +b = Impl.wn(t)
  +q = Impl.tq(t)
  +r1 = Ar.p7_mr_lt(a, i, 2n, 4n, hw_wm_lt(t, tt), ii)
  +r2 = Ar.p7_mr_lt(Nat.add(Nat.mul(a, 4n), i), h, 8n, 2n, r1, hh)
  +r3 = Ar.p7_mr_lt(Nat.add(Nat.mul(Nat.add(Nat.mul(a, 4n), i), 2n), h), g, 16n, 8n, r2, hw_g_lt(t))
  +c1 = Ar.p7_mr_lt(b, j, 2n, 8n, hw_wn_lt(t), jj)
  +c2 = Ar.p7_mr_lt(Nat.add(Nat.mul(b, 8n), j), q, 16n, 4n, c1, hw_q_lt(t))
  +c3 = Ar.p7_mr_lt(Nat.add(Nat.mul(Nat.add(Nat.mul(b, 8n), j), 4n), q), e, 64n, 2n, c2, ee)
  (Equal.trans(Bool, Nat.is_lt(Impl.row_of(0n, t, i, h), 128n), Nat.is_lt(hw_Nr(a, i, g, h), 128n), True{},
     Equal.cong(Nat, Bool, x => Nat.is_lt(x, 128n), Impl.row_of(0n, t, i, h), hw_Nr(a, i, g, h), hw_row_N(t, i, h)), r3),
   Equal.trans(Bool, Nat.is_lt(Impl.col_of(0n, t, j, e), 128n), Nat.is_lt(hw_Nc(b, j, q, e), 128n), True{},
     Equal.cong(Nat, Bool, x => Nat.is_lt(x, 128n), Impl.col_of(0n, t, j, e), hw_Nc(b, j, q, e), hw_col_N(t, j, e)), c3))

def hw_Lr_cong(+a1: Nat, +g1: Nat, +a2: Nat, +g2: Nat, +i: Nat, +h: Nat, ea: {a1 == a2 : Nat}, eg: {g1 == g2 : Nat})
  -> {hw_Lr(a1, i, g1, h) == hw_Lr(a2, i, g2, h) : Nat}:
  Equal.trans(Nat, hw_Lr(a1, i, g1, h), hw_Lr(a2, i, g1, h), hw_Lr(a2, i, g2, h),
    Equal.cong(Nat, Nat, x => hw_Lr(x, i, g1, h), a1, a2, ea),
    Equal.cong(Nat, Nat, x => hw_Lr(a2, i, x, h), g1, g2, eg))

def hw_Lc_cong(+b1: Nat, +q1: Nat, +b2: Nat, +q2: Nat, +j: Nat, +e: Nat, eb: {b1 == b2 : Nat}, eq: {q1 == q2 : Nat})
  -> {hw_Lc(b1, j, q1, e) == hw_Lc(b2, j, q2, e) : Nat}:
  Equal.trans(Nat, hw_Lc(b1, j, q1, e), hw_Lc(b2, j, q1, e), hw_Lc(b2, j, q2, e),
    Equal.cong(Nat, Nat, x => hw_Lc(x, j, q1, e), b1, b2, eb),
    Equal.cong(Nat, Nat, x => hw_Lc(b2, j, x, e), q1, q2, eq))

# ((A + I) + H) + g == A + (I + (H + g))
def hw_assoc3(+A: Nat, +I: Nat, +H: Nat, +g: Nat)
  -> {Nat.add(Nat.add(Nat.add(A, I), H), g) == Nat.add(A, Nat.add(I, Nat.add(H, g))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(A, I), H), g), Nat.add(Nat.add(A, I), Nat.add(H, g)), Nat.add(A, Nat.add(I, Nat.add(H, g))),
    Ar.ar_add_assoc(Nat.add(A, I), H, g), Ar.ar_add_assoc(A, I, Nat.add(H, g)))

# The canonical digits of r < 128 rebuild r: hw_Lr(r / 64, (r % 64) / 16, r % 8, (r % 16) / 8) == r.
def hw_row_rebuild(+r: Nat)
  -> {hw_Lr(Nat.div(r, 64n), Spec.own_i(r), Nat.mod(r, 8n), Spec.own_h(r)) == r : Nat}:
  +A = Nat.mul(Nat.div(r, 64n), 64n)
  +I = Nat.mul(Spec.own_i(r), 16n)
  +H = Nat.mul(Spec.own_h(r), 8n)
  +g = Nat.mod(r, 8n)
  +d1 = Ar.p7_digit(r, 2n, 8n, {==}, {==})
  +d2 = Ar.p7_digit(r, 4n, 16n, {==}, {==})
  Equal.trans(Nat, hw_Lr(Nat.div(r, 64n), Spec.own_i(r), g, Spec.own_h(r)), Nat.add(Nat.add(Nat.add(A, I), H), g), r,
    hw_swap_last(Nat.add(A, I), g, H),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(A, I), H), g), Nat.add(A, Nat.add(I, Nat.add(H, g))), r,
      hw_assoc3(A, I, H, g),
      Equal.trans(Nat, Nat.add(A, Nat.add(I, Nat.add(H, g))), Nat.add(A, Nat.add(I, Nat.mod(r, 16n))), r,
        Equal.cong(Nat, Nat, x => Nat.add(A, Nat.add(I, x)), Nat.add(H, g), Nat.mod(r, 16n), d1),
        Equal.trans(Nat, Nat.add(A, Nat.add(I, Nat.mod(r, 16n))), Nat.add(A, Nat.mod(r, 64n)), r,
          Equal.cong(Nat, Nat, x => Nat.add(A, x), Nat.add(I, Nat.mod(r, 16n)), Nat.mod(r, 64n), d2),
          Ar.ard_dm_eq(r, 64n, {==})))))

def hw_col_rebuild(+c: Nat)
  -> {hw_Lc(Nat.div(c, 64n), Spec.own_j(c), Nat.div(Nat.mod(c, 8n), 2n), Spec.own_e(c)) == c : Nat}:
  +B = Nat.mul(Nat.div(c, 64n), 64n)
  +J = Nat.mul(Spec.own_j(c), 8n)
  +Q = Nat.mul(Nat.div(Nat.mod(c, 8n), 2n), 2n)
  +e = Spec.own_e(c)
  +d1 = Ar.p7_digit(c, 4n, 2n, {==}, {==})
  +d2 = Ar.p7_digit(c, 8n, 8n, {==}, {==})
  Equal.trans(Nat, hw_Lc(Nat.div(c, 64n), Spec.own_j(c), Nat.div(Nat.mod(c, 8n), 2n), e), Nat.add(B, Nat.add(J, Nat.add(Q, e))), c,
    hw_assoc3(B, J, Q, e),
    Equal.trans(Nat, Nat.add(B, Nat.add(J, Nat.add(Q, e))), Nat.add(B, Nat.add(J, Nat.mod(c, 8n))), c,
      Equal.cong(Nat, Nat, x => Nat.add(B, Nat.add(J, x)), Nat.add(Q, e), Nat.mod(c, 8n), d1),
      Equal.trans(Nat, Nat.add(B, Nat.add(J, Nat.mod(c, 8n))), Nat.add(B, Nat.mod(c, 64n)), c,
        Equal.cong(Nat, Nat, x => Nat.add(B, x), Nat.add(J, Nat.mod(c, 8n)), Nat.mod(c, 64n), d2),
        Ar.ard_dm_eq(c, 64n, {==}))))

# x < R * m gives x / m < R (m > 0).
def hw_div_lt(+x: Nat, +R: Nat, +m: Nat, +mpos: {Nat.is_lt(0n, m) == True{} : Bool},
    xl: {Nat.is_lt(x, Nat.mul(R, m)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(x, m), R) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.div(x, m), R), Nat.is_lt(x, Nat.mul(R, m)), Ar.ar_div_lt(R, x, m, mpos), xl)

def hw_tsc_row(+r: Nat, +c: Nat, +rr: {Nat.is_lt(r, 128n) == True{} : Bool}, +cc: {Nat.is_lt(c, 128n) == True{} : Bool})
  -> {Impl.row_of(0n, Spec.own_tid(r, c), Spec.own_i(r), Spec.own_h(r)) == r : Nat}:
  +a = Nat.div(r, 64n)
  +b = Nat.div(c, 64n)
  +g = Nat.mod(r, 8n)
  +q = Nat.div(Nat.mod(c, 8n), 2n)
  +W = Nat.add(Nat.mul(a, 2n), b)
  +Ln = Nat.add(Nat.mul(g, 4n), q)
  +t = Spec.own_tid(r, c)
  +al = hw_div_lt(r, 2n, 64n, {==}, rr)
  +bl = hw_div_lt(c, 2n, 64n, {==}, cc)
  +gl = Ar.ard_dm_lt(r, 8n, {==})
  +ql = hw_div_lt(Nat.mod(c, 8n), 4n, 2n, {==}, Ar.ard_dm_lt(c, 8n, {==}))
  +Wl = Ar.p7_mr_lt(a, b, 2n, 2n, al, bl)
  +Ll = Ar.p7_mr_lt(g, q, 8n, 4n, gl, ql)
  # thread digits of t
  +ew = Ar.p7_div_q(W, Ln, 32n, Ll)
  +el = Ar.p7_mod_r(W, Ln, 32n, Ll)
  +ea = Equal.trans(Nat, Impl.wm(t), Nat.div(W, 2n), a, Equal.cong(Nat, Nat, x => Nat.div(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_div_q(a, b, 2n, bl))
  +eb = Equal.trans(Nat, Impl.wn(t), Nat.mod(W, 2n), b, Equal.cong(Nat, Nat, x => Nat.mod(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_mod_r(a, b, 2n, bl))
  +eg = Equal.trans(Nat, Impl.gq(t), Nat.div(Ln, 4n), g, Equal.cong(Nat, Nat, x => Nat.div(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_div_q(g, q, 4n, ql))
  +eq = Equal.trans(Nat, Impl.tq(t), Nat.mod(Ln, 4n), q, Equal.cong(Nat, Nat, x => Nat.mod(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_mod_r(g, q, 4n, ql))
  Equal.trans(Nat, Impl.row_of(0n, t, Spec.own_i(r), Spec.own_h(r)), hw_Lr(Impl.wm(t), Spec.own_i(r), Impl.gq(t), Spec.own_h(r)), r,
     hw_row_unfold(t, Spec.own_i(r), Spec.own_h(r)),
     Equal.trans(Nat, hw_Lr(Impl.wm(t), Spec.own_i(r), Impl.gq(t), Spec.own_h(r)), hw_Lr(a, Spec.own_i(r), g, Spec.own_h(r)), r,
       hw_Lr_cong(Impl.wm(t), Impl.gq(t), a, g, Spec.own_i(r), Spec.own_h(r), ea, eg), hw_row_rebuild(r)))

def hw_tsc_col(+r: Nat, +c: Nat, +rr: {Nat.is_lt(r, 128n) == True{} : Bool}, +cc: {Nat.is_lt(c, 128n) == True{} : Bool})
  -> {Impl.col_of(0n, Spec.own_tid(r, c), Spec.own_j(c), Spec.own_e(c)) == c : Nat}:
  +a = Nat.div(r, 64n)
  +b = Nat.div(c, 64n)
  +g = Nat.mod(r, 8n)
  +q = Nat.div(Nat.mod(c, 8n), 2n)
  +W = Nat.add(Nat.mul(a, 2n), b)
  +Ln = Nat.add(Nat.mul(g, 4n), q)
  +t = Spec.own_tid(r, c)
  +al = hw_div_lt(r, 2n, 64n, {==}, rr)
  +bl = hw_div_lt(c, 2n, 64n, {==}, cc)
  +gl = Ar.ard_dm_lt(r, 8n, {==})
  +ql = hw_div_lt(Nat.mod(c, 8n), 4n, 2n, {==}, Ar.ard_dm_lt(c, 8n, {==}))
  +Wl = Ar.p7_mr_lt(a, b, 2n, 2n, al, bl)
  +Ll = Ar.p7_mr_lt(g, q, 8n, 4n, gl, ql)
  # thread digits of t
  +ew = Ar.p7_div_q(W, Ln, 32n, Ll)
  +el = Ar.p7_mod_r(W, Ln, 32n, Ll)
  +ea = Equal.trans(Nat, Impl.wm(t), Nat.div(W, 2n), a, Equal.cong(Nat, Nat, x => Nat.div(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_div_q(a, b, 2n, bl))
  +eb = Equal.trans(Nat, Impl.wn(t), Nat.mod(W, 2n), b, Equal.cong(Nat, Nat, x => Nat.mod(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_mod_r(a, b, 2n, bl))
  +eg = Equal.trans(Nat, Impl.gq(t), Nat.div(Ln, 4n), g, Equal.cong(Nat, Nat, x => Nat.div(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_div_q(g, q, 4n, ql))
  +eq = Equal.trans(Nat, Impl.tq(t), Nat.mod(Ln, 4n), q, Equal.cong(Nat, Nat, x => Nat.mod(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_mod_r(g, q, 4n, ql))
  Equal.trans(Nat, Impl.col_of(0n, t, Spec.own_j(c), Spec.own_e(c)), hw_Lc(Impl.wn(t), Spec.own_j(c), Impl.tq(t), Spec.own_e(c)), c,
     hw_col_unfold(t, Spec.own_j(c), Spec.own_e(c)),
     Equal.trans(Nat, hw_Lc(Impl.wn(t), Spec.own_j(c), Impl.tq(t), Spec.own_e(c)), hw_Lc(b, Spec.own_j(c), q, Spec.own_e(c)), c,
       hw_Lc_cong(Impl.wn(t), Impl.tq(t), b, q, Spec.own_j(c), Spec.own_e(c), eb, eq), hw_col_rebuild(c)))

def hw_tsc_tid(+r: Nat, +c: Nat, +rr: {Nat.is_lt(r, 128n) == True{} : Bool}, +cc: {Nat.is_lt(c, 128n) == True{} : Bool})
  -> {Nat.is_lt(Spec.own_tid(r, c), 128n) == True{} : Bool}:
  +a = Nat.div(r, 64n)
  +b = Nat.div(c, 64n)
  +g = Nat.mod(r, 8n)
  +q = Nat.div(Nat.mod(c, 8n), 2n)
  +W = Nat.add(Nat.mul(a, 2n), b)
  +Ln = Nat.add(Nat.mul(g, 4n), q)
  +t = Spec.own_tid(r, c)
  +al = hw_div_lt(r, 2n, 64n, {==}, rr)
  +bl = hw_div_lt(c, 2n, 64n, {==}, cc)
  +gl = Ar.ard_dm_lt(r, 8n, {==})
  +ql = hw_div_lt(Nat.mod(c, 8n), 4n, 2n, {==}, Ar.ard_dm_lt(c, 8n, {==}))
  +Wl = Ar.p7_mr_lt(a, b, 2n, 2n, al, bl)
  +Ll = Ar.p7_mr_lt(g, q, 8n, 4n, gl, ql)
  # thread digits of t
  +ew = Ar.p7_div_q(W, Ln, 32n, Ll)
  +el = Ar.p7_mod_r(W, Ln, 32n, Ll)
  +ea = Equal.trans(Nat, Impl.wm(t), Nat.div(W, 2n), a, Equal.cong(Nat, Nat, x => Nat.div(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_div_q(a, b, 2n, bl))
  +eb = Equal.trans(Nat, Impl.wn(t), Nat.mod(W, 2n), b, Equal.cong(Nat, Nat, x => Nat.mod(x, 2n), Nat.div(t, 32n), W, ew),
    Ar.p7_mod_r(a, b, 2n, bl))
  +eg = Equal.trans(Nat, Impl.gq(t), Nat.div(Ln, 4n), g, Equal.cong(Nat, Nat, x => Nat.div(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_div_q(g, q, 4n, ql))
  +eq = Equal.trans(Nat, Impl.tq(t), Nat.mod(Ln, 4n), q, Equal.cong(Nat, Nat, x => Nat.mod(x, 4n), Nat.mod(t, 32n), Ln, el),
    Ar.p7_mod_r(g, q, 4n, ql))
  Ar.p7_mr_lt(W, Ln, 4n, 32n, Wl, Ll)

def Laws.tile_store_cover(r, c, rr, cc):
  +rl = rr
  +cl = cc
  (hw_tsc_tid(r, c, rl, cl),
   hw_div_lt(Nat.mod(r, 64n), 4n, 16n, {==}, Ar.ard_dm_lt(r, 64n, {==})),
   hw_div_lt(Nat.mod(c, 64n), 8n, 8n, {==}, Ar.ard_dm_lt(c, 64n, {==})),
   hw_div_lt(Nat.mod(r, 16n), 2n, 8n, {==}, Ar.ard_dm_lt(r, 16n, {==})),
   Ar.ard_dm_lt(c, 2n, {==}),
   hw_tsc_row(r, c, rl, cl), hw_tsc_col(r, c, rl, cl))

# ---- grouped raster ----

# min(a, b) == b when not a <= b.
def hw_min_right(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.min(0n, b) == b : Nat}, Ar.ar_true_false(Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{},
        Equal.sym(Bool, Nat.is_le(0n, b), True{}, Ar.ar_h_le_zero(b)), h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), q, hw_min_right(p, q, h))

def hw_lt_min_go(v: Bool, +x: Nat, +n: Nat, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == v : Bool},
    ha: {Nat.is_lt(x, Nat.mul(n, a)) == True{} : Bool}, hb: {Nat.is_lt(x, Nat.mul(n, b)) == True{} : Bool})
  -> {Nat.is_lt(x, Nat.mul(n, Nat.min(a, b))) == True{} : Bool}:
  match v:
    case True{}:
      %Equal.sym(Nat, Nat.min(a, b), a, Ar.ar_min_left(a, b, e)) : {Nat.is_lt(x, Nat.mul(n, _)) == True{} : Bool}
      ha
    case False{}:
      %Equal.sym(Nat, Nat.min(a, b), b, hw_min_right(a, b, e)) : {Nat.is_lt(x, Nat.mul(n, _)) == True{} : Bool}
      hb

# x < n a and x < n b give x < n min(a, b).
def hw_lt_min(+x: Nat, +n: Nat, +a: Nat, +b: Nat, ha: {Nat.is_lt(x, Nat.mul(n, a)) == True{} : Bool},
    hb: {Nat.is_lt(x, Nat.mul(n, b)) == True{} : Bool}) -> {Nat.is_lt(x, Nat.mul(n, Nat.min(a, b))) == True{} : Bool}:
  hw_lt_min_go(Nat.is_le(a, b), x, n, a, b, {==}, ha, hb)

# x < min(a, b) gives x < a and x < b.
def hw_min_l(+x: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(x, Nat.min(a, b)) == True{} : Bool}) -> {Nat.is_lt(x, a) == True{} : Bool}:
  Ar.ar_and_l(Nat.is_lt(x, a), Nat.is_lt(x, b), Ar.ard_rt(Nat.is_lt(x, Nat.min(a, b)), Bool.and(Nat.is_lt(x, a), Nat.is_lt(x, b)),
    Ar.ar_min_lt(x, a, b), h))

def hw_min_r(+x: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(x, Nat.min(a, b)) == True{} : Bool}) -> {Nat.is_lt(x, b) == True{} : Bool}:
  Ar.ar_and_r(Nat.is_lt(x, a), Nat.is_lt(x, b), Ar.ard_rt(Nat.is_lt(x, Nat.min(a, b)), Bool.and(Nat.is_lt(x, a), Nat.is_lt(x, b)),
    Ar.ar_min_lt(x, a, b), h))

def hw_min_intro(+x: Nat, +a: Nat, +b: Nat, ha: {Nat.is_lt(x, a) == True{} : Bool}, hb: {Nat.is_lt(x, b) == True{} : Bool})
  -> {Nat.is_lt(x, Nat.min(a, b)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(x, Nat.min(a, b)), Bool.and(Nat.is_lt(x, a), Nat.is_lt(x, b)), Ar.ar_min_lt(x, a, b),
    Ar.ar_and_intro(Nat.is_lt(x, a), Nat.is_lt(x, b), ha, hb))

# 0 < G gn.
def hw_gs_pos(+G: Nat, +gn: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool}, npos: {Nat.is_lt(0n, gn) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(G, gn)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(0n, Nat.mul(G, gn)), Nat.is_lt(0n, G), Ar.ar_mul_lt_cancel(0n, G, gn, npos), gpos)

# in_group(b) == b % (G gn) and b == group(b) (G gn) + in_group(b).
def hw_ig_mod(+b: Nat, +G: Nat, +gn: Nat, gsp: {Nat.is_lt(0n, Nat.mul(G, gn)) == True{} : Bool})
  -> {Impl.in_group(b, G, gn) == Nat.mod(b, Nat.mul(G, gn)) : Nat}:
  +gs = Nat.mul(G, gn)
  +q = Nat.div(b, gs)
  Equal.trans(Nat, Nat.sub(b, Nat.mul(q, gs)), Nat.sub(Nat.add(Nat.mul(q, gs), Nat.mod(b, gs)), Nat.mul(q, gs)), Nat.mod(b, gs),
    Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.mul(q, gs)), b, Nat.add(Nat.mul(q, gs), Nat.mod(b, gs)),
      Equal.sym(Nat, Nat.add(Nat.mul(q, gs), Nat.mod(b, gs)), b, Ar.ard_dm_eq(b, gs, gsp))),
    Ar.ar_add_sub(Nat.mul(q, gs), Nat.mod(b, gs)))

def hw_b_split(+b: Nat, +G: Nat, +gn: Nat, +gsp: {Nat.is_lt(0n, Nat.mul(G, gn)) == True{} : Bool})
  -> {Nat.add(Nat.mul(Impl.group(b, G, gn), Nat.mul(G, gn)), Impl.in_group(b, G, gn)) == b : Nat}:
  %Equal.sym(Nat, Impl.in_group(b, G, gn), Nat.mod(b, Nat.mul(G, gn)), hw_ig_mod(b, G, gn, gsp))
    : {Nat.add(Nat.mul(Impl.group(b, G, gn), Nat.mul(G, gn)), _) == b : Nat}
  Ar.ard_dm_eq(b, Nat.mul(G, gn), gsp)

# q (G gn) == (q G) gn
def hw_fm_gn(+q: Nat, +G: Nat, +gn: Nat) -> {Nat.mul(q, Nat.mul(G, gn)) == Nat.mul(Nat.mul(q, G), gn) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.mul(q, G), gn), Nat.mul(q, Nat.mul(G, gn)), Ar.ar_mul_assoc(q, G, gn))

# b < gm gn gives first_m(b) < gm.
def hw_fm_lt(+b: Nat, +G: Nat, +gn: Nat, +gm: Nat, +gpos: {Nat.is_lt(0n, G) == True{} : Bool}, +npos: {Nat.is_lt(0n, gn) == True{} : Bool},
    inside: {Nat.is_lt(b, Nat.mul(gm, gn)) == True{} : Bool}) -> {Nat.is_lt(Impl.first_m(b, G, gn), gm) == True{} : Bool}:
  +gsp = hw_gs_pos(G, gn, gpos, npos)
  +q = Impl.group(b, G, gn)
  +le1 = Ar.ard_le_of_add(Nat.mul(q, Nat.mul(G, gn)), Impl.in_group(b, G, gn), b, hw_b_split(b, G, gn, gsp))
  +le2 = Equal.trans(Bool, Nat.is_le(Nat.mul(Nat.mul(q, G), gn), b), Nat.is_le(Nat.mul(q, Nat.mul(G, gn)), b), True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(x, b), Nat.mul(Nat.mul(q, G), gn), Nat.mul(q, Nat.mul(G, gn)), Ar.ar_mul_assoc(q, G, gn)), le1)
  +lt = Ar.ar_le_lt_trans(Nat.mul(Nat.mul(q, G), gn), b, Nat.mul(gm, gn), le2, inside)
  Ar.ard_rt(Nat.is_lt(Nat.mul(Nat.mul(q, G), gn), Nat.mul(gm, gn)), Nat.is_lt(Nat.mul(q, G), gm), Ar.ar_mul_lt_cancel(Nat.mul(q, G), gm, gn, npos), lt)

# f < gm gives 0 < gm - f.
def hw_sub_pos(+f: Nat, +gm: Nat, h: {Nat.is_lt(f, gm) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(gm, f)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(0n, Nat.sub(gm, f)), Nat.is_lt(Nat.add(f, 0n), gm), Ar.ar_lt_sub_iff(gm, f, 0n),
    Equal.trans(Bool, Nat.is_lt(Nat.add(f, 0n), gm), Nat.is_lt(f, gm), True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, gm), Nat.add(f, 0n), f, Ar.ar_add_zero_r(f)), h))

# 0 < min(G, gm - f) when G > 0 and f < gm.
def hw_eff_pos(+G: Nat, +f: Nat, +gm: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool}, h: {Nat.is_lt(f, gm) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.min(G, Nat.sub(gm, f))) == True{} : Bool}:
  hw_min_intro(0n, G, Nat.sub(gm, f), gpos, hw_sub_pos(f, gm, h))

# b < gm gn and first_m(b) < gm give in_group(b) < gn (gm - first_m(b)).
def hw_ig_lt_rest(+b: Nat, +G: Nat, +gn: Nat, +gm: Nat, +gsp: {Nat.is_lt(0n, Nat.mul(G, gn)) == True{} : Bool},
    fl: {Nat.is_lt(Impl.first_m(b, G, gn), gm) == True{} : Bool}, inside: {Nat.is_lt(b, Nat.mul(gm, gn)) == True{} : Bool})
  -> {Nat.is_lt(Impl.in_group(b, G, gn), Nat.mul(gn, Nat.sub(gm, Impl.first_m(b, G, gn)))) == True{} : Bool}:
  +q = Impl.group(b, G, gn)
  +F = Impl.first_m(b, G, gn)
  +S = Nat.sub(gm, F)
  +ig = Impl.in_group(b, G, gn)
  +mF = Nat.mul(F, gn)
  +mS = Nat.mul(S, gn)
  +eb = Equal.trans(Nat, Nat.add(mF, ig), Nat.add(Nat.mul(q, Nat.mul(G, gn)), ig), b,
    Equal.cong(Nat, Nat, x => Nat.add(x, ig), mF, Nat.mul(q, Nat.mul(G, gn)),
      Equal.sym(Nat, Nat.mul(q, Nat.mul(G, gn)), mF, hw_fm_gn(q, G, gn))),
    hw_b_split(b, G, gn, gsp))
  +egm = Equal.trans(Nat, Nat.mul(gm, gn), Nat.mul(Nat.add(F, S), gn), Nat.add(mF, mS),
    Equal.cong(Nat, Nat, x => Nat.mul(x, gn), gm, Nat.add(F, S), Equal.sym(Nat, Nat.add(F, S), gm, Ar.ar_sub_add(gm, F, Ar.ar_lt_le(F, gm, fl)))),
    Ar.ar_mul_add_l(F, S, gn))
  +lt1 = Equal.trans(Bool, Nat.is_lt(Nat.add(mF, ig), Nat.add(mF, mS)), Nat.is_lt(b, Nat.mul(gm, gn)), True{},
    Equal.trans(Bool, Nat.is_lt(Nat.add(mF, ig), Nat.add(mF, mS)), Nat.is_lt(b, Nat.add(mF, mS)), Nat.is_lt(b, Nat.mul(gm, gn)),
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.add(mF, mS)), Nat.add(mF, ig), b, eb),
      Equal.cong(Nat, Bool, x => Nat.is_lt(b, x), Nat.add(mF, mS), Nat.mul(gm, gn), Equal.sym(Nat, Nat.mul(gm, gn), Nat.add(mF, mS), egm))),
    inside)
  +lt2 = Ar.ard_rt(Nat.is_lt(Nat.add(mF, ig), Nat.add(mF, mS)), Nat.is_lt(ig, mS), Ar.ar_lt_add_cancel(mF, ig, mS), lt1)
  Equal.trans(Bool, Nat.is_lt(ig, Nat.mul(gn, S)), Nat.is_lt(ig, mS), True{},
    Equal.cong(Nat, Bool, x => Nat.is_lt(ig, x), Nat.mul(gn, S), mS, Ar.ar_mul_comm(gn, S)), lt2)

def Laws.raster_in_range(b, G, gn, gm, gpos, npos, inside):
  +gp = gpos
  +np = npos
  +ins = inside
  +gsp = hw_gs_pos(G, gn, gp, np)
  +q = Impl.group(b, G, gn)
  +F = Impl.first_m(b, G, gn)
  +S = Nat.sub(gm, F)
  +E = Impl.gm_eff(b, G, gn, gm)
  +ig = Impl.in_group(b, G, gn)
  +fl = hw_fm_lt(b, G, gn, gm, gp, np, ins)
  +ep = hw_eff_pos(G, F, gm, gp, fl)
  +rl = Ar.ard_dm_lt(ig, E, ep)
  # tile_m = F + ig % E < F + (gm - F) = gm
  +tm = Ar.ard_rt(Nat.is_lt(Nat.mod(ig, E), S), Nat.is_lt(Nat.add(F, Nat.mod(ig, E)), gm), Ar.ar_lt_sub_iff(gm, F, Nat.mod(ig, E)),
    hw_min_r(Nat.mod(ig, E), G, S, rl))
  # in_group < gn G (it is b % (G gn)) and < gn (gm - F) (b < gm gn)
  +i1 = Equal.trans(Bool, Nat.is_lt(ig, Nat.mul(gn, G)), Nat.is_lt(Nat.mod(b, Nat.mul(G, gn)), Nat.mul(G, gn)), True{},
    Equal.trans(Bool, Nat.is_lt(ig, Nat.mul(gn, G)), Nat.is_lt(Nat.mod(b, Nat.mul(G, gn)), Nat.mul(gn, G)),
      Nat.is_lt(Nat.mod(b, Nat.mul(G, gn)), Nat.mul(G, gn)),
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.mul(gn, G)), ig, Nat.mod(b, Nat.mul(G, gn)), hw_ig_mod(b, G, gn, gsp)),
      Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.mod(b, Nat.mul(G, gn)), x), Nat.mul(gn, G), Nat.mul(G, gn), Ar.ar_mul_comm(gn, G))),
    Ar.ard_dm_lt(b, Nat.mul(G, gn), gsp))
  +i2 = hw_ig_lt_rest(b, G, gn, gm, gsp, fl, ins)
  +il = hw_lt_min(ig, gn, G, S, i1, i2)
  (tm,
   Ar.ard_tr(Nat.is_lt(Impl.tile_n(b, G, gn, gm), gn), Nat.is_lt(ig, Nat.mul(gn, E)), Ar.ar_div_lt(gn, ig, E, ep), il))

def hw_dmr_cong(+d1: Nat, +E1: Nat, +r1: Nat, +d2: Nat, +E2: Nat, +r2: Nat,
    ed: {d1 == d2 : Nat}, eE: {E1 == E2 : Nat}, er: {r1 == r2 : Nat})
  -> {Nat.add(Nat.mul(d1, E1), r1) == Nat.add(Nat.mul(d2, E2), r2) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(d1, E1), r1), Nat.add(Nat.mul(d2, E1), r1), Nat.add(Nat.mul(d2, E2), r2),
    Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, E1), r1), d1, d2, ed),
    Equal.trans(Nat, Nat.add(Nat.mul(d2, E1), r1), Nat.add(Nat.mul(d2, E2), r1), Nat.add(Nat.mul(d2, E2), r2),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(d2, x), r1), E1, E2, eE),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(d2, E2), x), r1, r2, er)))

def hw_eff_of(+q: Nat, +G: Nat, +gm: Nat) -> Nat:
  Nat.min(G, Nat.sub(gm, Nat.mul(q, G)))

def Laws.raster_inj(b1, b2, G, gn, gm, gpos, npos, in1, in2, same_m, same_n):
  +gp = gpos
  +np = npos
  +sm = same_m
  +i1 = in1
  +i2 = in2
  +gsp = hw_gs_pos(G, gn, gp, np)
  +gs = Nat.mul(G, gn)
  +q1 = Impl.group(b1, G, gn)
  +q2 = Impl.group(b2, G, gn)
  +E1 = Impl.gm_eff(b1, G, gn, gm)
  +E2 = Impl.gm_eff(b2, G, gn, gm)
  +ig1 = Impl.in_group(b1, G, gn)
  +ig2 = Impl.in_group(b2, G, gn)
  +ep1 = hw_eff_pos(G, Impl.first_m(b1, G, gn), gm, gp, hw_fm_lt(b1, G, gn, gm, gp, np, i1))
  +ep2 = hw_eff_pos(G, Impl.first_m(b2, G, gn), gm, gp, hw_fm_lt(b2, G, gn, gm, gp, np, i2))
  +r1 = Nat.mod(ig1, E1)
  +r2 = Nat.mod(ig2, E2)
  +rl1 = hw_min_l(r1, G, Nat.sub(gm, Impl.first_m(b1, G, gn)), Ar.ard_dm_lt(ig1, E1, ep1))
  +rl2 = hw_min_l(r2, G, Nat.sub(gm, Impl.first_m(b2, G, gn)), Ar.ard_dm_lt(ig2, E2, ep2))
  +eq = Ar.ard_fst({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, G, rl1, rl2, sm))
  +er = Ar.ard_snd({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, G, rl1, rl2, sm))
  +eE = Equal.cong(Nat, Nat, x => hw_eff_of(x, G, gm), q1, q2, eq)
  +eig = Equal.trans(Nat, ig1, Nat.add(Nat.mul(Nat.div(ig1, E1), E1), r1), ig2,
    Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(ig1, E1), E1), r1), ig1, Ar.ard_dm_eq(ig1, E1, ep1)),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(ig1, E1), E1), r1), Nat.add(Nat.mul(Nat.div(ig2, E2), E2), r2), ig2,
      hw_dmr_cong(Nat.div(ig1, E1), E1, r1, Nat.div(ig2, E2), E2, r2, same_n, eE, er),
      Ar.ard_dm_eq(ig2, E2, ep2)))
  Equal.trans(Nat, b1, Nat.add(Nat.mul(q1, gs), ig1), b2,
    Equal.sym(Nat, Nat.add(Nat.mul(q1, gs), ig1), b1, hw_b_split(b1, G, gn, gsp)),
    Equal.trans(Nat, Nat.add(Nat.mul(q1, gs), ig1), Nat.add(Nat.mul(q2, gs), ig2), b2,
      hw_qr_cong(q1, ig1, q2, ig2, gs, eq, eig), hw_b_split(b2, G, gn, gsp)))

def hw_min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      hw_min_le_l(p, q)

def hw_min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      hw_min_le_r(p, q)

def hw_tm_of(+q: Nat, +ig: Nat, +E: Nat, +G: Nat) -> Nat:
  Nat.add(Nat.mul(q, G), Nat.mod(ig, E))

def hw_tm_cong(+q1: Nat, +i1: Nat, +E1: Nat, +q2: Nat, +i2: Nat, +E2: Nat, +G: Nat,
    eq: {q1 == q2 : Nat}, ei: {i1 == i2 : Nat}, eE: {E1 == E2 : Nat})
  -> {hw_tm_of(q1, i1, E1, G) == hw_tm_of(q2, i2, E2, G) : Nat}:
  Equal.trans(Nat, hw_tm_of(q1, i1, E1, G), hw_tm_of(q2, i1, E1, G), hw_tm_of(q2, i2, E2, G),
    Equal.cong(Nat, Nat, x => hw_tm_of(x, i1, E1, G), q1, q2, eq),
    Equal.trans(Nat, hw_tm_of(q2, i1, E1, G), hw_tm_of(q2, i2, E1, G), hw_tm_of(q2, i2, E2, G),
      Equal.cong(Nat, Nat, x => hw_tm_of(q2, x, E1, G), i1, i2, ei),
      Equal.cong(Nat, Nat, x => hw_tm_of(q2, i2, x, G), E1, E2, eE)))

def hw_div_cong(+i1: Nat, +E1: Nat, +i2: Nat, +E2: Nat, ei: {i1 == i2 : Nat}, eE: {E1 == E2 : Nat})
  -> {Nat.div(i1, E1) == Nat.div(i2, E2) : Nat}:
  Equal.trans(Nat, Nat.div(i1, E1), Nat.div(i2, E1), Nat.div(i2, E2),
    Equal.cong(Nat, Nat, x => Nat.div(x, E1), i1, i2, ei), Equal.cong(Nat, Nat, x => Nat.div(i2, x), E1, E2, eE))

def Laws.raster_cover(tm, tn, G, gn, gm, gpos, tmin, tnin):
  +gp = gpos
  +tml = tmin
  +tnl = tnin
  +np = Ar.ard_pos(tn, gn, tnl)
  +gs = Nat.mul(G, gn)
  +g = Nat.div(tm, G)
  +r = Nat.mod(tm, G)
  +F = Nat.mul(g, G)
  +S = Nat.sub(gm, F)
  +st = Nat.min(G, S)
  +igs = Nat.add(Nat.mul(tn, st), r)
  +B = Nat.add(Nat.mul(g, gs), igs)
  +dmt = Ar.ard_dm_eq(tm, G, gp)
  +rG = Ar.ard_dm_lt(tm, G, gp)
  +Fl = Ar.ar_le_lt_trans(F, tm, gm, Ar.ard_le_of_add(F, r, tm, dmt), tml)
  +rS = Ar.ard_tr(Nat.is_lt(r, S), Nat.is_lt(Nat.add(F, r), gm), Ar.ar_lt_sub_iff(gm, F, r),
    Equal.trans(Bool, Nat.is_lt(Nat.add(F, r), gm), Nat.is_lt(tm, gm), True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, gm), Nat.add(F, r), tm, dmt), tml))
  +rst = hw_min_intro(r, G, S, rG, rS)
  +igl = Ar.p7_mr_lt(tn, r, gn, st, tnl, rst)
  +igl2 = Equal.trans(Bool, Nat.is_lt(igs, Nat.mul(st, gn)), Nat.is_lt(igs, Nat.mul(gn, st)), True{},
    Equal.cong(Nat, Bool, x => Nat.is_lt(igs, x), Nat.mul(st, gn), Nat.mul(gn, st), Ar.ar_mul_comm(st, gn)), igl)
  +igg = Ar.ar_lt_le_trans(igs, Nat.mul(st, gn), gs, igl2, Ar.ar_le_mul_mono(st, G, gn, hw_min_le_l(G, S)))
  # block B's raster variables
  +eg = Ar.p7_div_q(g, igs, gs, igg)
  +eig = Equal.trans(Nat, Impl.in_group(B, G, gn), Nat.sub(B, Nat.mul(g, gs)), igs,
    Equal.cong(Nat, Nat, x => Nat.sub(B, Nat.mul(x, gs)), Impl.group(B, G, gn), g, eg),
    Ar.ar_add_sub(Nat.mul(g, gs), igs))
  +eE = Equal.cong(Nat, Nat, x => hw_eff_of(x, G, gm), Impl.group(B, G, gn), g, eg)
  +etm = Equal.trans(Nat, Impl.tile_m(B, G, gn, gm), hw_tm_of(g, igs, st, G), tm,
    hw_tm_cong(Impl.group(B, G, gn), Impl.in_group(B, G, gn), Impl.gm_eff(B, G, gn, gm), g, igs, st, G, eg, eig, eE),
    Equal.trans(Nat, hw_tm_of(g, igs, st, G), Nat.add(F, r), tm,
      Equal.cong(Nat, Nat, x => Nat.add(F, x), Nat.mod(igs, st), r, Ar.p7_mod_r(tn, r, st, rst)), dmt))
  +etn = Equal.trans(Nat, Impl.tile_n(B, G, gn, gm), Nat.div(igs, st), tn,
    hw_div_cong(Impl.in_group(B, G, gn), Impl.gm_eff(B, G, gn, gm), igs, st, eig, eE), Ar.p7_div_q(tn, r, st, rst))
  # B < gm gn
  +mF = Nat.mul(F, gn)
  +eB = Equal.cong(Nat, Nat, x => Nat.add(x, igs), Nat.mul(g, gs), mF, hw_fm_gn(g, G, gn))
  +lt1 = Ar.ard_tr(Nat.is_lt(Nat.add(mF, igs), Nat.add(mF, Nat.mul(st, gn))), Nat.is_lt(igs, Nat.mul(st, gn)),
    Ar.ar_lt_add_cancel(mF, igs, Nat.mul(st, gn)), igl2)
  +lt2 = Equal.trans(Bool, Nat.is_lt(Nat.add(mF, igs), Nat.mul(Nat.add(F, st), gn)),
    Nat.is_lt(Nat.add(mF, igs), Nat.add(mF, Nat.mul(st, gn))), True{},
    Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.add(mF, igs), x), Nat.mul(Nat.add(F, st), gn), Nat.add(mF, Nat.mul(st, gn)),
      Ar.ar_mul_add_l(F, st, gn)), lt1)
  +sle = Ar.ard_tr(Nat.is_le(Nat.add(F, st), Nat.add(F, S)), Nat.is_le(st, S), Ar.ar_le_add_cancel(F, st, S), hw_min_le_r(G, S))
  +gle = Equal.trans(Bool, Nat.is_le(Nat.add(F, st), gm), Nat.is_le(Nat.add(F, st), Nat.add(F, S)), True{},
    Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(F, st), x), gm, Nat.add(F, S),
      Equal.sym(Nat, Nat.add(F, S), gm, Ar.ar_sub_add(gm, F, Ar.ar_lt_le(F, gm, Fl)))), sle)
  +lt3 = Ar.ar_lt_le_trans(Nat.add(mF, igs), Nat.mul(Nat.add(F, st), gn), Nat.mul(gm, gn), lt2, Ar.ar_le_mul_mono(Nat.add(F, st), gm, gn, gle))
  (Equal.trans(Bool, Nat.is_lt(B, Nat.mul(gm, gn)), Nat.is_lt(Nat.add(mF, igs), Nat.mul(gm, gn)), True{},
     Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.mul(gm, gn)), B, Nat.add(mF, igs), eB), lt3),
   etm, etn)

# ---- composed over the launch ----

def hw_p3a(-A: Type, -B: Type, -C: Type, p: A & B & C) -> A:
  match p:
    case (a, rest):
      a

def hw_p3b(-A: Type, -B: Type, -C: Type, p: A & B & C) -> B:
  match p:
    case (a, rest):
      Ar.ard_fst(B, C, rest)

def hw_p3c(-A: Type, -B: Type, -C: Type, p: A & B & C) -> C:
  match p:
    case (a, rest):
      Ar.ard_snd(B, C, rest)

# bid(B / gn, B % gn) == B
def hw_bid_back(+B: Nat, +gn: Nat, npos: {Nat.is_lt(0n, gn) == True{} : Bool})
  -> {Impl.bid(Nat.div(B, gn), Nat.mod(B, gn), gn) == B : Nat}:
  Ar.ard_dm_eq(B, gn, npos)

def Laws.global_cover(R, C, M, G, gn, gpos, rr, cc):
  +gp = gpos
  +rl = rr
  +cl = cc
  +gm = Impl.grid_m(M)
  +tm = Nat.div(R, 128n)
  +tn = Nat.div(C, 128n)
  +r = Nat.mod(R, 128n)
  +c = Nat.mod(C, 128n)
  +np = Ar.ard_rt(Nat.is_lt(Nat.mul(0n, 128n), Nat.mul(gn, 128n)), Nat.is_lt(0n, gn), Ar.ar_mul_lt_cancel(0n, gn, 128n, {==}),
    Ar.ard_pos(C, Nat.mul(gn, 128n), cl))
  +Rl = Ar.ar_lt_le_trans(R, M, Nat.mul(gm, 128n), rl, Laws.grid_rows(M))
  +tml = hw_div_lt(R, gm, 128n, {==}, Rl)
  +tnl = hw_div_lt(C, gn, 128n, {==}, cl)
  +B = Spec.bid_of(tm, tn, G, gn, gm)
  -TA = {Nat.is_lt(B, Nat.mul(gm, gn)) == True{} : Bool}
  -TB = {Impl.tile_m(B, G, gn, gm) == tm : Nat}
  -TC = {Impl.tile_n(B, G, gn, gm) == tn : Nat}
  +Bl = hw_p3a(TA, TB, TC, Laws.raster_cover(tm, tn, G, gn, gm, gp, tml, tnl))
  +etm = hw_p3b(TA, TB, TC, Laws.raster_cover(tm, tn, G, gn, gm, gp, tml, tnl))
  +etn = hw_p3c(TA, TB, TC, Laws.raster_cover(tm, tn, G, gn, gm, gp, tml, tnl))
  +by = Nat.div(B, gn)
  +bx = Nat.mod(B, gn)
  +rl2 = Ar.ard_dm_lt(R, 128n, {==})
  +cl2 = Ar.ard_dm_lt(C, 128n, {==})
  +t = Spec.own_tid(r, c)
  +i = Spec.own_i(r)
  +h = Spec.own_h(r)
  +j = Spec.own_j(c)
  +e = Spec.own_e(c)
  +eb = hw_bid_back(B, gn, np)
  +em = Equal.trans(Nat, Impl.tile_m(Impl.bid(by, bx, gn), G, gn, gm), Impl.tile_m(B, G, gn, gm), tm,
    Equal.cong(Nat, Nat, x => Impl.tile_m(x, G, gn, gm), Impl.bid(by, bx, gn), B, eb), etm)
  +en = Equal.trans(Nat, Impl.tile_n(Impl.bid(by, bx, gn), G, gn, gm), Impl.tile_n(B, G, gn, gm), tn,
    Equal.cong(Nat, Nat, x => Impl.tile_n(x, G, gn, gm), Impl.bid(by, bx, gn), B, eb), etn)
  +erow = Equal.trans(Nat, Impl.grow(by, bx, t, i, h, G, gn, gm), Impl.row_of(Nat.mul(tm, 128n), t, i, h), R,
    Equal.cong(Nat, Nat, x => Impl.row_of(Nat.mul(x, 128n), t, i, h), Impl.tile_m(Impl.bid(by, bx, gn), G, gn, gm), tm, em),
    Equal.trans(Nat, Impl.row_of(Nat.mul(tm, 128n), t, i, h), Nat.add(Nat.mul(tm, 128n), Impl.row_of(0n, t, i, h)), R,
      hw_assoc4(Nat.mul(tm, 128n), Nat.mul(Impl.wm(t), 64n), Nat.mul(i, 16n), Impl.gq(t), Nat.mul(h, 8n)),
      Equal.trans(Nat, Nat.add(Nat.mul(tm, 128n), Impl.row_of(0n, t, i, h)), Nat.add(Nat.mul(tm, 128n), r), R,
        Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(tm, 128n), x), Impl.row_of(0n, t, i, h), r, hw_tsc_row(r, c, rl2, cl2)),
        Ar.ard_dm_eq(R, 128n, {==}))))
  +ecol = Equal.trans(Nat, Impl.gcol(by, bx, t, j, e, G, gn, gm), Impl.col_of(Nat.mul(tn, 128n), t, j, e), C,
    Equal.cong(Nat, Nat, x => Impl.col_of(Nat.mul(x, 128n), t, j, e), Impl.tile_n(Impl.bid(by, bx, gn), G, gn, gm), tn, en),
    Equal.trans(Nat, Impl.col_of(Nat.mul(tn, 128n), t, j, e), Nat.add(Nat.mul(tn, 128n), Impl.col_of(0n, t, j, e)), C,
      hw_assoc4(Nat.mul(tn, 128n), Nat.mul(Impl.wn(t), 64n), Nat.mul(j, 8n), Nat.mul(Impl.tq(t), 2n), e),
      Equal.trans(Nat, Nat.add(Nat.mul(tn, 128n), Impl.col_of(0n, t, j, e)), Nat.add(Nat.mul(tn, 128n), c), C,
        Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(tn, 128n), x), Impl.col_of(0n, t, j, e), c, hw_tsc_col(r, c, rl2, cl2)),
        Ar.ard_dm_eq(C, 128n, {==}))))
  (hw_div_lt(B, gm, gn, np, Bl), Ar.ard_dm_lt(B, gn, np), erow, ecol,
   Equal.trans(Bool, Impl.stored(by, bx, t, i, h, G, gn, gm, M), Nat.is_lt(R, M), True{},
     Equal.cong(Nat, Bool, x => Nat.is_lt(x, M), Impl.grow(by, bx, t, i, h, G, gn, gm), R, erow), rl))

def Laws.global_inj(by1, bx1, t1, i1, j1, h1, e1, by2, bx2, t2, i2, j2, h2, e2, G, gn, gm, gpos,
    yy1, xx1, tt1, ii1, jj1, hh1, ee1, yy2, xx2, tt2, ii2, jj2, hh2, ee2, same_r, same_c):
  +ii1b = ii1
  +jj1b = jj1
  +hh1b = hh1
  +ee1b = ee1
  +ii2b = ii2
  +jj2b = jj2
  +hh2b = hh2
  +ee2b = ee2
  +yy1b = yy1
  +yy2b = yy2
  +x1 = xx1
  +x2 = xx2
  +a1 = tt1
  +a2 = tt2
  +np = Ar.ard_pos(bx1, gn, x1)
  +B1 = Impl.bid(by1, bx1, gn)
  +B2 = Impl.bid(by2, bx2, gn)
  +T1 = Impl.tile_m(B1, G, gn, gm)
  +T2 = Impl.tile_m(B2, G, gn, gm)
  +U1 = Impl.tile_n(B1, G, gn, gm)
  +U2 = Impl.tile_n(B2, G, gn, gm)
  +lr1 = Impl.row_of(0n, t1, i1, h1)
  +lr2 = Impl.row_of(0n, t2, i2, h2)
  +lc1 = Impl.col_of(0n, t1, j1, e1)
  +lc2 = Impl.col_of(0n, t2, j2, e2)
  -PR1 = {Nat.is_lt(lr1, 128n) == True{} : Bool}
  -PC1 = {Nat.is_lt(lc1, 128n) == True{} : Bool}
  -PR2 = {Nat.is_lt(lr2, 128n) == True{} : Bool}
  -PC2 = {Nat.is_lt(lc2, 128n) == True{} : Bool}
  +r1l = Ar.ard_fst(PR1, PC1, Laws.tile_store_in(t1, i1, j1, h1, e1, a1, ii1b, jj1b, hh1b, ee1b))
  +c1l = Ar.ard_snd(PR1, PC1, Laws.tile_store_in(t1, i1, j1, h1, e1, a1, ii1b, jj1b, hh1b, ee1b))
  +r2l = Ar.ard_fst(PR2, PC2, Laws.tile_store_in(t2, i2, j2, h2, e2, a2, ii2b, jj2b, hh2b, ee2b))
  +c2l = Ar.ard_snd(PR2, PC2, Laws.tile_store_in(t2, i2, j2, h2, e2, a2, ii2b, jj2b, hh2b, ee2b))
  +sr = Equal.trans(Nat, Nat.add(Nat.mul(T1, 128n), lr1), Impl.grow(by1, bx1, t1, i1, h1, G, gn, gm), Nat.add(Nat.mul(T2, 128n), lr2),
    Equal.sym(Nat, Impl.grow(by1, bx1, t1, i1, h1, G, gn, gm), Nat.add(Nat.mul(T1, 128n), lr1),
      hw_assoc4(Nat.mul(T1, 128n), Nat.mul(Impl.wm(t1), 64n), Nat.mul(i1, 16n), Impl.gq(t1), Nat.mul(h1, 8n))),
    Equal.trans(Nat, Impl.grow(by1, bx1, t1, i1, h1, G, gn, gm), Impl.grow(by2, bx2, t2, i2, h2, G, gn, gm), Nat.add(Nat.mul(T2, 128n), lr2),
      same_r, hw_assoc4(Nat.mul(T2, 128n), Nat.mul(Impl.wm(t2), 64n), Nat.mul(i2, 16n), Impl.gq(t2), Nat.mul(h2, 8n))))
  +sc = Equal.trans(Nat, Nat.add(Nat.mul(U1, 128n), lc1), Impl.gcol(by1, bx1, t1, j1, e1, G, gn, gm), Nat.add(Nat.mul(U2, 128n), lc2),
    Equal.sym(Nat, Impl.gcol(by1, bx1, t1, j1, e1, G, gn, gm), Nat.add(Nat.mul(U1, 128n), lc1),
      hw_assoc4(Nat.mul(U1, 128n), Nat.mul(Impl.wn(t1), 64n), Nat.mul(j1, 8n), Nat.mul(Impl.tq(t1), 2n), e1)),
    Equal.trans(Nat, Impl.gcol(by1, bx1, t1, j1, e1, G, gn, gm), Impl.gcol(by2, bx2, t2, j2, e2, G, gn, gm), Nat.add(Nat.mul(U2, 128n), lc2),
      same_c, hw_assoc4(Nat.mul(U2, 128n), Nat.mul(Impl.wn(t2), 64n), Nat.mul(j2, 8n), Nat.mul(Impl.tq(t2), 2n), e2)))
  +eT = hw_peel_q(T1, lr1, T2, lr2, 128n, r1l, r2l, sr)
  +elr = hw_peel_r(T1, lr1, T2, lr2, 128n, r1l, r2l, sr)
  +eU = hw_peel_q(U1, lc1, U2, lc2, 128n, c1l, c2l, sc)
  +elc = hw_peel_r(U1, lc1, U2, lc2, 128n, c1l, c2l, sc)
  +eB = Laws.raster_inj(B1, B2, G, gn, gm, gpos, np, Ar.p7_mr_lt(by1, bx1, gm, gn, yy1b, x1), Ar.p7_mr_lt(by2, bx2, gm, gn, yy2b, x2), eT, eU)
  (hw_peel_q(by1, bx1, by2, bx2, gn, x1, x2, eB), hw_peel_r(by1, bx1, by2, bx2, gn, x1, x2, eB),
   Laws.tile_store_inj(t1, i1, j1, h1, e1, t2, i2, j2, h2, e2, a1, ii1b, jj1b, hh1b, ee1b, a2, ii2b, jj2b, hh2b, ee2b, elr, elc))
