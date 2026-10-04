# Proofs of err_gdn_laws.bend. Nat lemmas from gemm_m16_partition_proof.bend (Ar).
import Base
import ./err_bound.bend as Eb
import ./err_gdn.bend as G
import ./err_gdn_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

# ==== Nat helpers ====
# a - b <= a
def eg_sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Ar.ar_le_refl(1n+p)
    case 1n+p 1n+q:
      Ar.ar_le_trans(Nat.sub(p, q), p, 1n+p, eg_sub_le(p, q), Ar.ar_h_le_succ(p))

# a <= b and c <= d give a + c <= b + d
def eg_le_add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool},
    cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  +s1 = Ar.ard_tr(Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), Ar.ar_le_add_cancel(c, a, b), ab)
  +s1r = Equal.trans(Bool, Nat.is_le(Nat.add(a, c), Nat.add(b, c)), Nat.is_le(Nat.add(c, a), Nat.add(c, b)), True{},
    Equal.trans(Bool, Nat.is_le(Nat.add(a, c), Nat.add(b, c)), Nat.is_le(Nat.add(c, a), Nat.add(b, c)), Nat.is_le(Nat.add(c, a), Nat.add(c, b)),
      Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(b, c)), Nat.add(a, c), Nat.add(c, a), Ar.ar_add_comm(a, c)),
      Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(c, a), z), Nat.add(b, c), Nat.add(c, b), Ar.ar_add_comm(b, c))),
    s1)
  +s2 = Ar.ard_tr(Nat.is_le(Nat.add(b, c), Nat.add(b, d)), Nat.is_le(c, d), Ar.ar_le_add_cancel(b, c, d), cd)
  Ar.ar_le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), s1r, s2)

# (a + b) + (c + d) == (a + c) + (b + d)
def eg_swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat)
  -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
    Ar.ar_add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), Ar.ar_h_add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), Ar.ar_add_assoc(a, c, Nat.add(b, d)))))

# a < b and b <= c give a < c
def eg_lt_le(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  Ar.ar_lt_le_trans(a, b, c, ab, bc)

# ==== Path helpers ====
# A Path dominates itself plus any number of extra r32 steps on the dominating side.
def eg_dom_ext(+x: Nat, P: Eb.Path, +D: Nat) -> {Eb.dom(x, P, Eb.add(G.r32p(D), P)) == True{} : Bool}:
  match P:
    case Eb.Path{+a, +b, +c, +d, +h, +e, +f, +g}:
      +capc = Nat.mul(x, Nat.sub(h, h))
      +spare = Nat.sub(Nat.add(Nat.add(d, c), capc), Nat.add(d, c))
      +Y = Nat.mul(x, spare)
      +c5a = Ar.ard_tr(Nat.is_le(Nat.add(b, a), Nat.add(b, Nat.add(D, a))), Nat.is_le(a, Nat.add(D, a)),
        Ar.ar_le_add_cancel(b, a, Nat.add(D, a)), Ar.ar_le_add_l(D, a))
      +c5 = Ar.ar_le_trans(Nat.add(b, a), Nat.add(b, Nat.add(D, a)), Nat.add(Nat.add(b, Nat.add(D, a)), Y), c5a,
        Ar.ar_le_add_r(Nat.add(b, Nat.add(D, a)), Y))
      Ar.ar_and_intro(Nat.is_le(h, h), Bool.and(Nat.is_le(d, Nat.add(d, capc)),
          Bool.and(Nat.is_le(Nat.add(d, c), Nat.add(Nat.add(d, c), capc)),
            Bool.and(Nat.is_le(b, Nat.add(b, Y)),
              Bool.and(Nat.is_le(Nat.add(b, a), Nat.add(Nat.add(b, Nat.add(D, a)), Y)),
                Bool.and(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g))))))),
        Ar.ar_le_refl(h),
      Ar.ar_and_intro(Nat.is_le(d, Nat.add(d, capc)), Bool.and(Nat.is_le(Nat.add(d, c), Nat.add(Nat.add(d, c), capc)),
            Bool.and(Nat.is_le(b, Nat.add(b, Y)),
              Bool.and(Nat.is_le(Nat.add(b, a), Nat.add(Nat.add(b, Nat.add(D, a)), Y)),
                Bool.and(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g)))))),
        Ar.ar_le_add_r(d, capc),
      Ar.ar_and_intro(Nat.is_le(Nat.add(d, c), Nat.add(Nat.add(d, c), capc)),
            Bool.and(Nat.is_le(b, Nat.add(b, Y)),
              Bool.and(Nat.is_le(Nat.add(b, a), Nat.add(Nat.add(b, Nat.add(D, a)), Y)),
                Bool.and(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g))))),
        Ar.ar_le_add_r(Nat.add(d, c), capc),
      Ar.ar_and_intro(Nat.is_le(b, Nat.add(b, Y)),
              Bool.and(Nat.is_le(Nat.add(b, a), Nat.add(Nat.add(b, Nat.add(D, a)), Y)),
                Bool.and(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g)))),
        Ar.ar_le_add_r(b, Y),
      Ar.ar_and_intro(Nat.is_le(Nat.add(b, a), Nat.add(Nat.add(b, Nat.add(D, a)), Y)),
                Bool.and(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g))),
        c5,
      Ar.ar_and_intro(Nat.is_le(e, e), Bool.and(Nat.is_le(f, f), Nat.is_le(g, g)), Ar.ar_le_refl(e),
      Ar.ar_and_intro(Nat.is_le(f, f), Nat.is_le(g, g), Ar.ar_le_refl(f), Ar.ar_le_refl(g))))))))

# Extra r32 steps commute out of a concatenation.
def eg_shift(+g: Nat, +h: Nat, P: Eb.Path, Q: Eb.Path)
  -> {Eb.add(Eb.add(G.r32p(g), P), Eb.add(G.r32p(h), Q)) == Eb.add(G.r32p(Nat.add(g, h)), Eb.add(P, Q)) : Eb.Path}:
  match P Q:
    case Eb.Path{+a1, b1, c1, d1, h1, e1, f1, g1} Eb.Path{+a2, b2, c2, d2, h2, e2, f2, g2}:
      Equal.cong(Nat, Eb.Path, z => Eb.Path{z, Nat.add(b1, b2), Nat.add(c1, c2), Nat.add(d1, d2), Nat.add(h1, h2),
          Nat.add(e1, e2), Nat.add(f1, f2), Nat.add(g1, g2)},
        Nat.add(Nat.add(g, a1), Nat.add(h, a2)), Nat.add(Nat.add(g, h), Nat.add(a1, a2)), eg_swap4(g, a1, h, a2))

# ==== b/a bounds ====
def eg_ws_le(+w: Nat) -> {Nat.is_le(G.e_wsum(w), 15n) == True{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+q:
      eg_sub_le(15n, q)

def Laws.ba_bound(w, i, c, hb):
  +h = G.bit(hb)
  +X = Nat.sub(10n, Nat.add(Nat.mul(i, 2n), c))
  eg_le_add_mono(X, 10n, Nat.add(5n, Nat.add(G.e_wsum(w), h)), Nat.add(5n, Nat.add(15n, h)),
    eg_sub_le(10n, Nat.add(Nat.mul(i, 2n), c)),
    eg_le_add_mono(5n, 5n, Nat.add(G.e_wsum(w), h), Nat.add(15n, h), {==},
      eg_le_add_mono(G.e_wsum(w), 15n, h, h, eg_ws_le(w), Ar.ar_le_refl(h))))

def Laws.ba_stock_worst(m, c, hb):
  +h = G.bit(hb)
  (eg_le_add_mono(Nat.sub(160n, Nat.add(Nat.mul(m, 2n), c)), 160n, Nat.add(5n, h), Nat.add(5n, h),
    eg_sub_le(160n, Nat.add(Nat.mul(m, 2n), c)), Ar.ar_le_refl(Nat.add(5n, h))), {==})

# the elpis b/a term is below stock's witness
def eg_ba_le(+w: Nat, +i: Nat, +c: Nat, +hb: Bool)
  -> {Nat.is_le(G.e_ba(w, i, c, hb), G.s_ba(0n, 0n, hb)) == True{} : Bool}:
  +h = G.bit(hb)
  Ar.ar_le_trans(G.e_ba(w, i, c, hb), Nat.add(30n, h), G.s_ba(0n, 0n, hb), Laws.ba_bound(w, i, c, hb),
    Ar.ard_tr(Nat.is_le(Nat.add(30n, h), Nat.add(30n, Nat.add(135n, h))), Nat.is_le(h, Nat.add(135n, h)),
      Ar.ar_le_add_cancel(30n, h, Nat.add(135n, h)), Ar.ar_le_add_l(135n, h)))

def Laws.edge_nodes(s):
  match s:
    case G.Cast{}:
      ({==}, {==})
    case G.ConvX{kk}:
      ({==}, {==})
    case G.ConvW{kk}:
      ({==}, {==})
    case G.ConvB{}:
      ({==}, {==})
    case G.SiluD{}:
      ({==}, {==})
    case G.SiluG{}:
      ({==}, {==})
    case G.ConvO{}:
      ({==}, {==})
    case G.L2D{qk}:
      ({==}, {==})
    case G.L2S{qk}:
      ({==}, {==})
    case G.D1K{p}:
      ({==}, {==})
    case G.D1S{p}:
      ({==}, {==})
    case G.D1Sl{w}:
      ({==}, {==})
    case G.VD{}:
      ({==}, {==})
    case G.VI{}:
      ({==}, {==})
    case G.VG{}:
      ({==}, {==})
    case G.GX{}:
      ({==}, {==})
    case G.UpS{}:
      ({==}, {==})
    case G.UpG{}:
      ({==}, {==})
    case G.UpK{}:
      ({==}, {==})
    case G.UpV{}:
      ({==}, {==})
    case G.UpB{}:
      ({==}, {==})
    case G.Carry{}:
      ({==}, {==})
    case G.VoN{p}:
      ({==}, {==})
    case G.VoQ{p}:
      ({==}, {==})
    case G.VoSl{w}:
      ({==}, {==})
    case G.Sc{}:
      ({==}, {==})
    case G.NoD{}:
      ({==}, {==})
    case G.NoW{cb}:
      ({==}, {==})
    case G.NoS{q}:
      ({==}, {==})
    case G.NoGD{}:
      ({==}, {==})
    case G.NoGS{}:
      ({==}, {==})
    case G.BaE{ab, w, l, i, c, hb}:
      ({==}, {==})
    case G.BaS{ab, l, m, c, hb}:
      ({==}, {==})
    case G.BaB{ab}:
      ({==}, {==})
    case G.Beta{}:
      ({==}, {==})
    case G.GA{lin}:
      ({==}, {==})
    case G.GD{lin}:
      ({==}, {==})
    case G.GL{}:
      ({==}, {==})

def Laws.com_same(s):
  match s:
    case G.Cast{}:
      {==}
    case G.ConvX{kk}:
      {==}
    case G.ConvW{kk}:
      {==}
    case G.ConvB{}:
      {==}
    case G.SiluD{}:
      {==}
    case G.SiluG{}:
      {==}
    case G.ConvO{}:
      {==}
    case G.L2D{qk}:
      {==}
    case G.L2S{qk}:
      {==}
    case G.D1K{p}:
      {==}
    case G.D1S{p}:
      {==}
    case G.D1Sl{w}:
      {==}
    case G.VD{}:
      {==}
    case G.VI{}:
      {==}
    case G.VG{}:
      {==}
    case G.GX{}:
      {==}
    case G.UpS{}:
      {==}
    case G.UpG{}:
      {==}
    case G.UpK{}:
      {==}
    case G.UpV{}:
      {==}
    case G.UpB{}:
      {==}
    case G.Carry{}:
      {==}
    case G.VoN{p}:
      {==}
    case G.VoQ{p}:
      {==}
    case G.VoSl{w}:
      {==}
    case G.Sc{}:
      {==}
    case G.NoD{}:
      {==}
    case G.NoW{cb}:
      {==}
    case G.NoS{q}:
      {==}
    case G.NoGD{}:
      {==}
    case G.NoGS{}:
      {==}
    case G.BaE{ab, w, l, i, c, hb}:
      {==}
    case G.BaS{ab, l, m, c, hb}:
      {==}
    case G.BaB{ab}:
      {==}
    case G.Beta{}:
      {==}
    case G.GA{lin}:
      {==}
    case G.GD{lin}:
      {==}
    case G.GL{}:
      {==}

# The witness of a valid elpis edge is a valid stock edge.
def eg_edge_valid(s: G.Seg, v: {G.valid_e(s) == True{} : Bool}) -> {G.valid_s(G.wit(s)) == True{} : Bool}:
  match s:
    case G.Cast{}:
      v
    case G.ConvX{kk}:
      v
    case G.ConvW{kk}:
      v
    case G.ConvB{}:
      v
    case G.SiluD{}:
      v
    case G.SiluG{}:
      v
    case G.ConvO{}:
      v
    case G.L2D{qk}:
      v
    case G.L2S{qk}:
      v
    case G.D1K{p}:
      v
    case G.D1S{p}:
      v
    case G.D1Sl{w}:
      v
    case G.VD{}:
      v
    case G.VI{}:
      v
    case G.VG{}:
      v
    case G.GX{}:
      v
    case G.UpS{}:
      v
    case G.UpG{}:
      v
    case G.UpK{}:
      v
    case G.UpV{}:
      v
    case G.UpB{}:
      v
    case G.Carry{}:
      v
    case G.VoN{p}:
      v
    case G.VoQ{p}:
      v
    case G.VoSl{w}:
      v
    case G.Sc{}:
      v
    case G.NoD{}:
      v
    case G.NoW{cb}:
      v
    case G.NoS{q}:
      v
    case G.NoGD{}:
      v
    case G.NoGS{}:
      v
    case G.BaE{+ab, +w, +l, +i, +c, +hb}:
      Ar.ar_and_intro(Nat.is_lt(ab, 2n), Bool.and(Nat.is_lt(0n, 32n), Bool.and(Nat.is_lt(0n, 80n), Nat.is_lt(0n, 2n))),
        Ar.ar_and_l(Nat.is_lt(ab, 2n), Bool.and(Nat.is_lt(w, 16n), Bool.and(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(i, 5n), Nat.is_lt(c, 2n)))), v),
        {==})
    case G.BaS{ab, l, m, c, hb}:
      Empty.absurd({G.valid_s(G.wit(G.BaS{ab, l, m, c, hb})) == True{} : Bool}, Ar.ar_false_true(v))
    case G.BaB{ab}:
      v
    case G.Beta{}:
      v
    case G.GA{lin}:
      v
    case G.GD{lin}:
      v
    case G.GL{}:
      v

# The witness Path is the elpis Path plus `gap` extra r32 steps.
def eg_edge_gap(s: G.Seg, v: {G.valid_e(s) == True{} : Bool})
  -> {G.s_path(G.wit(s)) == Eb.add(G.r32p(G.gap(s)), G.e_path(s)) : Eb.Path}:
  match s:
    case G.Cast{}:
      {==}
    case G.ConvX{kk}:
      {==}
    case G.ConvW{kk}:
      {==}
    case G.ConvB{}:
      {==}
    case G.SiluD{}:
      {==}
    case G.SiluG{}:
      {==}
    case G.ConvO{}:
      {==}
    case G.L2D{qk}:
      {==}
    case G.L2S{qk}:
      {==}
    case G.D1K{p}:
      {==}
    case G.D1S{p}:
      {==}
    case G.D1Sl{w}:
      {==}
    case G.VD{}:
      {==}
    case G.VI{}:
      {==}
    case G.VG{}:
      {==}
    case G.GX{}:
      {==}
    case G.UpS{}:
      {==}
    case G.UpG{}:
      {==}
    case G.UpK{}:
      {==}
    case G.UpV{}:
      {==}
    case G.UpB{}:
      {==}
    case G.Carry{}:
      {==}
    case G.VoN{p}:
      {==}
    case G.VoQ{p}:
      {==}
    case G.VoSl{w}:
      {==}
    case G.Sc{}:
      {==}
    case G.NoD{}:
      {==}
    case G.NoW{cb}:
      {==}
    case G.NoS{q}:
      {==}
    case G.NoGD{}:
      {==}
    case G.NoGS{}:
      {==}
    case G.BaE{+ab, +w, +l, +i, +c, +hb}:
      +S = G.s_ba(0n, 0n, hb)
      +E = G.e_ba(w, i, c, hb)
      +eqS = Equal.trans(Nat, Nat.add(Nat.sub(S, E), E), Nat.add(E, Nat.sub(S, E)), S,
        Ar.ar_add_comm(Nat.sub(S, E), E), Ar.ar_sub_add(S, E, eg_ba_le(w, i, c, hb)))
      Equal.sym(Eb.Path, G.r32p(Nat.add(Nat.sub(S, E), E)), G.r32p(S),
        Equal.cong(Nat, Eb.Path, z => G.r32p(z), Nat.add(Nat.sub(S, E), E), S, eqS))
    case G.BaS{ab, l, m, c, hb}:
      Empty.absurd({G.s_path(G.wit(G.BaS{ab, l, m, c, hb})) == Eb.add(G.r32p(G.gap(G.BaS{ab, l, m, c, hb})), G.e_path(G.BaS{ab, l, m, c, hb})) : Eb.Path},
        Ar.ar_false_true(v))
    case G.BaB{ab}:
      {==}
    case G.Beta{}:
      {==}
    case G.GA{lin}:
      match lin:
        case True{}:
          {==}
        case False{}:
          {==}
    case G.GD{lin}:
      match lin:
        case True{}:
          {==}
        case False{}:
          {==}
    case G.GL{}:
      {==}

def eg_edge_dom(+s: G.Seg, +v: {G.valid_e(s) == True{} : Bool})
  -> {Eb.dom(128n, G.e_path(s), G.s_path(G.wit(s))) == True{} : Bool}:
  %Equal.sym(Eb.Path, G.s_path(G.wit(s)), Eb.add(G.r32p(G.gap(s)), G.e_path(s)), eg_edge_gap(s, v))
    : {Eb.dom(128n, G.e_path(s), _) == True{} : Bool}
  eg_dom_ext(128n, G.e_path(s), G.gap(s))

def Laws.edge_dom(s, v):
  +vv = v
  (eg_edge_valid(s, vv), eg_edge_gap(s, vv), eg_edge_dom(s, vv))

# ==== b/a term correspondence ====
# 16 i + w < 80 for i < 5, w < 16
def eg_m_lt(+i: Nat, +w: Nat, vi: {Nat.is_lt(i, 5n) == True{} : Bool}, vw: {Nat.is_lt(w, 16n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(i, 16n), w), 80n) == True{} : Bool}:
  match i:
    case 0n:
      eg_lt_le(w, 16n, 80n, vw, {==})
    case 1n+i1:
      match i1:
        case 0n:
          eg_lt_le(w, 16n, 64n, vw, {==})
        case 1n+i2:
          match i2:
            case 0n:
              eg_lt_le(w, 16n, 48n, vw, {==})
            case 1n+i3:
              match i3:
                case 0n:
                  eg_lt_le(w, 16n, 32n, vw, {==})
                case 1n+i4:
                  match i4:
                    case 0n:
                      vw
                    case 1n+p:
                      Empty.absurd({Nat.is_lt(Nat.add(Nat.mul(5n+p, 16n), w), 80n) == True{} : Bool},
                        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{},
                          Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, Ar.ar_h_lt_zero(p)), vi)))

# l + (16 i + w) 32 == (32 w + l) + 512 i
def eg_elem(+w: Nat, +l: Nat, +i: Nat)
  -> {Nat.add(l, Nat.mul(Nat.add(Nat.mul(i, 16n), w), 32n)) == Nat.add(Nat.add(Nat.mul(w, 32n), l), Nat.mul(i, 512n)) : Nat}:
  +I = Nat.mul(i, 512n)
  +Wt = Nat.mul(w, 32n)
  +M32 = Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(i, 16n), w), 32n), Nat.add(Nat.mul(Nat.mul(i, 16n), 32n), Wt), Nat.add(I, Wt),
    Ar.ar_mul_add_l(Nat.mul(i, 16n), w, 32n),
    Equal.cong(Nat, Nat, z => Nat.add(z, Wt), Nat.mul(Nat.mul(i, 16n), 32n), I, Ar.ar_mul_assoc(i, 16n, 32n)))
  +lhs = Equal.trans(Nat, Nat.add(l, Nat.mul(Nat.add(Nat.mul(i, 16n), w), 32n)), Nat.add(l, Nat.add(I, Wt)), Nat.add(I, Nat.add(l, Wt)),
    Equal.cong(Nat, Nat, z => Nat.add(l, z), Nat.mul(Nat.add(Nat.mul(i, 16n), w), 32n), Nat.add(I, Wt), M32),
    Ar.ar_h_add_swap(l, I, Wt))
  +rhs = Equal.trans(Nat, Nat.add(Nat.add(Wt, l), I), Nat.add(I, Nat.add(Wt, l)), Nat.add(I, Nat.add(l, Wt)),
    Ar.ar_add_comm(Nat.add(Wt, l), I),
    Equal.cong(Nat, Nat, z => Nat.add(I, z), Nat.add(Wt, l), Nat.add(l, Wt), Ar.ar_add_comm(Wt, l)))
  Equal.trans(Nat, Nat.add(l, Nat.mul(Nat.add(Nat.mul(i, 16n), w), 32n)), Nat.add(I, Nat.add(l, Wt)), Nat.add(Nat.add(Wt, l), I),
    lhs, Equal.sym(Nat, Nat.add(Nat.add(Wt, l), I), Nat.add(I, Nat.add(l, Wt)), rhs))

def Laws.ba_into(ab, w, l, i, c, hb, v):
  +R3 = Bool.and(Nat.is_lt(i, 5n), Nat.is_lt(c, 2n))
  +R2 = Bool.and(Nat.is_lt(l, 32n), R3)
  +R1 = Bool.and(Nat.is_lt(w, 16n), R2)
  +vv = v
  +vab = Ar.ar_and_l(Nat.is_lt(ab, 2n), R1, vv)
  +v1 = Ar.ar_and_r(Nat.is_lt(ab, 2n), R1, vv)
  +vw = Ar.ar_and_l(Nat.is_lt(w, 16n), R2, v1)
  +v2 = Ar.ar_and_r(Nat.is_lt(w, 16n), R2, v1)
  +vl = Ar.ar_and_l(Nat.is_lt(l, 32n), R3, v2)
  +v3 = Ar.ar_and_r(Nat.is_lt(l, 32n), R3, v2)
  +vi = Ar.ar_and_l(Nat.is_lt(i, 5n), Nat.is_lt(c, 2n), v3)
  +vc = Ar.ar_and_r(Nat.is_lt(i, 5n), Nat.is_lt(c, 2n), v3)
  +M = Nat.add(Nat.mul(i, 16n), w)
  +vM = eg_m_lt(i, w, vi, vw)
  +p1 = Ar.ar_and_intro(Nat.is_lt(ab, 2n), Bool.and(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(M, 80n), Nat.is_lt(c, 2n))), vab,
    Ar.ar_and_intro(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(M, 80n), Nat.is_lt(c, 2n)), vl,
      Ar.ar_and_intro(Nat.is_lt(M, 80n), Nat.is_lt(c, 2n), vM, vc)))
  +p2 = Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(z, 2n), c),
    Nat.add(l, Nat.mul(M, 32n)), Nat.add(Nat.add(Nat.mul(w, 32n), l), Nat.mul(i, 512n)), eg_elem(w, l, i))
  +dq = Ar.ard_fst({Nat.div(M, 16n) == i : Nat}, {Nat.mod(M, 16n) == w : Nat}, Ar.ar_div_unique(i, w, 16n, vw))
  +dr = Ar.ard_snd({Nat.div(M, 16n) == i : Nat}, {Nat.mod(M, 16n) == w : Nat}, Ar.ar_div_unique(i, w, 16n, vw))
  +p3 = Equal.trans(G.Seg, G.BaE{ab, Nat.mod(M, 16n), l, Nat.div(M, 16n), c, hb}, G.BaE{ab, w, l, Nat.div(M, 16n), c, hb},
    G.BaE{ab, w, l, i, c, hb},
    Equal.cong(Nat, G.Seg, z => G.BaE{ab, z, l, Nat.div(M, 16n), c, hb}, Nat.mod(M, 16n), w, dr),
    Equal.cong(Nat, G.Seg, z => G.BaE{ab, w, l, z, c, hb}, Nat.div(M, 16n), i, dq))
  (p1, p2, p3)

def Laws.ba_onto(ab, l, m, c, hb, v):
  +R2 = Bool.and(Nat.is_lt(m, 80n), Nat.is_lt(c, 2n))
  +R1 = Bool.and(Nat.is_lt(l, 32n), R2)
  +vv = v
  +vab = Ar.ar_and_l(Nat.is_lt(ab, 2n), R1, vv)
  +v1 = Ar.ar_and_r(Nat.is_lt(ab, 2n), R1, vv)
  +vl = Ar.ar_and_l(Nat.is_lt(l, 32n), R2, v1)
  +v2 = Ar.ar_and_r(Nat.is_lt(l, 32n), R2, v1)
  +vm = Ar.ar_and_l(Nat.is_lt(m, 80n), Nat.is_lt(c, 2n), v2)
  +vc = Ar.ar_and_r(Nat.is_lt(m, 80n), Nat.is_lt(c, 2n), v2)
  +D = Nat.div(m, 16n)
  +Md = Nat.mod(m, 16n)
  +vmd = Ar.ard_dm_lt(m, 16n, {==})
  +vd = Ar.ard_tr(Nat.is_lt(D, 5n), Nat.is_lt(m, Nat.mul(5n, 16n)), Ar.ar_div_lt(5n, m, 16n, {==}), vm)
  +p1 = Ar.ar_and_intro(Nat.is_lt(ab, 2n), Bool.and(Nat.is_lt(Md, 16n), Bool.and(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(D, 5n), Nat.is_lt(c, 2n)))), vab,
    Ar.ar_and_intro(Nat.is_lt(Md, 16n), Bool.and(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(D, 5n), Nat.is_lt(c, 2n))), vmd,
      Ar.ar_and_intro(Nat.is_lt(l, 32n), Bool.and(Nat.is_lt(D, 5n), Nat.is_lt(c, 2n)), vl,
        Ar.ar_and_intro(Nat.is_lt(D, 5n), Nat.is_lt(c, 2n), vd, vc))))
  +p2 = Equal.cong(Nat, G.Seg, z => G.BaS{ab, l, z, c, hb}, Nat.add(Nat.mul(D, 16n), Md), m, Ar.ard_dm_eq(m, 16n, {==}))
  (p1, p2)

# ==== routes ====
def eg_route_valid(r: List<&2, G.Seg>, v: {G.all_e(r) == True{} : Bool}) -> {G.all_s(G.wits(r)) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +vv = v
      Ar.ar_and_intro(G.valid_s(G.wit(s)), G.all_s(G.wits(t)),
        eg_edge_valid(s, Ar.ar_and_l(G.valid_e(s), G.all_e(t), vv)),
        eg_route_valid(t, Ar.ar_and_r(G.valid_e(s), G.all_e(t), vv)))

def eg_chain_go(t: List<&2, G.Seg>, +a: G.Seg) -> {G.chain_go(G.wits(t), G.wit(a)) == G.chain_go(t, a) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+b, +t2}:
      +ead = Ar.ard_snd({G.src(G.wit(a)) == G.src(a) : Nat}, {G.dst(G.wit(a)) == G.dst(a) : Nat}, Laws.edge_nodes(a))
      +ebs = Ar.ard_fst({G.src(G.wit(b)) == G.src(b) : Nat}, {G.dst(G.wit(b)) == G.dst(b) : Nat}, Laws.edge_nodes(b))
      +X1 = Nat.is_eq(G.dst(G.wit(a)), G.src(G.wit(b)))
      +X2 = Nat.is_eq(G.dst(a), G.src(b))
      +e1 = Equal.trans(Bool, X1, Nat.is_eq(G.dst(a), G.src(G.wit(b))), X2,
        Equal.cong(Nat, Bool, z => Nat.is_eq(z, G.src(G.wit(b))), G.dst(G.wit(a)), G.dst(a), ead),
        Equal.cong(Nat, Bool, z => Nat.is_eq(G.dst(a), z), G.src(G.wit(b)), G.src(b), ebs))
      +Y1 = G.chain_go(G.wits(t2), G.wit(b))
      +Y2 = G.chain_go(t2, b)
      Equal.trans(Bool, Bool.and(X1, Y1), Bool.and(X2, Y1), Bool.and(X2, Y2),
        Equal.cong(Bool, Bool, z => Bool.and(z, Y1), X1, X2, e1),
        Equal.cong(Bool, Bool, z => Bool.and(X2, z), Y1, Y2, eg_chain_go(t2, b)))

def eg_chain(r: List<&2, G.Seg>) -> {G.chain(G.wits(r)) == G.chain(r) : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      eg_chain_go(t, a)

def eg_com(r: List<&2, G.Seg>) -> {G.com_s(G.wits(r)) == G.com_e(r) : G.Com}:
  match r:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      Equal.trans(G.Com, G.com_add(G.s_com(G.wit(s)), G.com_s(G.wits(t))), G.com_add(G.e_com(s), G.com_s(G.wits(t))),
        G.com_add(G.e_com(s), G.com_e(t)),
        Equal.cong(G.Com, G.Com, z => G.com_add(z, G.com_s(G.wits(t))), G.s_com(G.wit(s)), G.e_com(s), Laws.com_same(s)),
        Equal.cong(G.Com, G.Com, z => G.com_add(G.e_com(s), z), G.com_s(G.wits(t)), G.com_e(t), eg_com(t)))

def eg_route_gap(r: List<&2, G.Seg>, v: {G.all_e(r) == True{} : Bool})
  -> {G.sum_s(G.wits(r)) == Eb.add(G.r32p(G.gaps(r)), G.sum_e(r)) : Eb.Path}:
  match r:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      +vv = v
      +A = G.s_path(G.wit(s))
      +Bs = G.sum_s(G.wits(t))
      +A2 = Eb.add(G.r32p(G.gap(s)), G.e_path(s))
      +B2 = Eb.add(G.r32p(G.gaps(t)), G.sum_e(t))
      +e1 = eg_edge_gap(s, Ar.ar_and_l(G.valid_e(s), G.all_e(t), vv))
      +e2 = eg_route_gap(t, Ar.ar_and_r(G.valid_e(s), G.all_e(t), vv))
      Equal.trans(Eb.Path, Eb.add(A, Bs), Eb.add(A2, B2), Eb.add(G.r32p(Nat.add(G.gap(s), G.gaps(t))), Eb.add(G.e_path(s), G.sum_e(t))),
        Equal.trans(Eb.Path, Eb.add(A, Bs), Eb.add(A2, Bs), Eb.add(A2, B2),
          Equal.cong(Eb.Path, Eb.Path, z => Eb.add(z, Bs), A, A2, e1),
          Equal.cong(Eb.Path, Eb.Path, z => Eb.add(A2, z), Bs, B2, e2)),
        eg_shift(G.gap(s), G.gaps(t), G.e_path(s), G.sum_e(t)))

def eg_route_dom(+r: List<&2, G.Seg>, +v: {G.all_e(r) == True{} : Bool})
  -> {Eb.dom(128n, G.sum_e(r), G.sum_s(G.wits(r))) == True{} : Bool}:
  %Equal.sym(Eb.Path, G.sum_s(G.wits(r)), Eb.add(G.r32p(G.gaps(r)), G.sum_e(r)), eg_route_gap(r, v))
    : {Eb.dom(128n, G.sum_e(r), _) == True{} : Bool}
  eg_dom_ext(128n, G.sum_e(r), G.gaps(r))

def Laws.route_dom(r, v):
  +vv = v
  (eg_route_valid(r, vv), eg_chain(r), eg_com(r), eg_route_dom(r, vv))
