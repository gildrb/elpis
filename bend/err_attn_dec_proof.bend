# Proofs of bend/err_attn_dec_laws.bend (decode / verify attention after ext 3030 against stock 355c6ee,
# model bend/err_attn_dec.bend). Structure: path rearrangement (both routes regroup into (numerator
# steps beyond P V + denominator part) + shared segments), the per-key bounds (bend/err_attn_dec_keys.bend),
# the totals for every L (bend/err_attn_dec_p2.bend), then Eb.dom by bend/err_bound_proof.bend's
# eb_dom_mk and the core laws dom_add / dom_refl. No @unsafe definitions, axioms, holes or foreign code;
# every def precedes its uses.
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as EbL
import ./err_bound_proof.bend as EbP
import ./err_attn.bend as Ea
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./err_attn_dec_laws.bend as Laws
import ./err_attn_dec_tree.bend as Tr
import ./err_attn_dec_keys.bend as K
import ./err_attn_dec_p2.bend as P2
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP

# ==== Nat rearrangements ====

# a + (b + (c + (d + x))) == (a + (b + (c + d))) + x
def pn_h1(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +x: Nat)
  -> {Nat.add(a, Nat.add(b, Nat.add(c, Nat.add(d, x)))) == Nat.add(Nat.add(a, Nat.add(b, Nat.add(c, d))), x) : Nat}:
  +cd = Nat.add(c, d)
  +bcd = Nat.add(b, cd)
  Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, Nat.add(d, x)))), Nat.add(a, Nat.add(b, Nat.add(cd, x))),
    Nat.add(Nat.add(a, bcd), x),
    Equal.cong(Nat, Nat, t => Nat.add(a, Nat.add(b, t)), Nat.add(c, Nat.add(d, x)), Nat.add(cd, x),
      Equal.sym(Nat, Nat.add(cd, x), Nat.add(c, Nat.add(d, x)), Ar.ar_add_assoc(c, d, x))),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(cd, x))), Nat.add(a, Nat.add(bcd, x)), Nat.add(Nat.add(a, bcd), x),
      Equal.cong(Nat, Nat, t => Nat.add(a, t), Nat.add(b, Nat.add(cd, x)), Nat.add(bcd, x),
        Equal.sym(Nat, Nat.add(bcd, x), Nat.add(b, Nat.add(cd, x)), Ar.ar_add_assoc(b, cd, x))),
      Equal.sym(Nat, Nat.add(Nat.add(a, bcd), x), Nat.add(a, Nat.add(bcd, x)), Ar.ar_add_assoc(a, bcd, x))))

# (q + y) + v == (q + v) + y
def pn_h2(+q: Nat, +y: Nat, +v: Nat) -> {Nat.add(Nat.add(q, y), v) == Nat.add(Nat.add(q, v), y) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(q, y), v), Nat.add(q, Nat.add(y, v)), Nat.add(Nat.add(q, v), y),
    Ar.ar_add_assoc(q, y, v),
    Equal.trans(Nat, Nat.add(q, Nat.add(y, v)), Nat.add(q, Nat.add(v, y)), Nat.add(Nat.add(q, v), y),
      Equal.cong(Nat, Nat, t => Nat.add(q, t), Nat.add(y, v), Nat.add(v, y), Ar.ar_add_comm(y, v)),
      Equal.sym(Nat, Nat.add(Nat.add(q, v), y), Nat.add(q, Nat.add(v, y)), Ar.ar_add_assoc(q, v, y))))

# ((N + x) + ((q + y) + v)) + p == (x + y) + ((N + (q + v)) + p)
def pn_core(+N: Nat, +x: Nat, +q: Nat, +y: Nat, +v: Nat, +p: Nat)
  -> {Nat.add(Nat.add(Nat.add(N, x), Nat.add(Nat.add(q, y), v)), p) == Nat.add(Nat.add(x, y), Nat.add(Nat.add(N, Nat.add(q, v)), p)) : Nat}:
  +qv = Nat.add(q, v)
  +xy = Nat.add(x, y)
  +Nqv = Nat.add(N, qv)
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(N, x), Nat.add(Nat.add(q, y), v)), p), Nat.add(Nat.add(Nat.add(N, x), Nat.add(qv, y)), p),
    Nat.add(xy, Nat.add(Nqv, p)),
    Equal.cong(Nat, Nat, t => Nat.add(Nat.add(Nat.add(N, x), t), p), Nat.add(Nat.add(q, y), v), Nat.add(qv, y), pn_h2(q, y, v)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.add(N, x), Nat.add(qv, y)), p), Nat.add(Nat.add(Nqv, xy), p), Nat.add(xy, Nat.add(Nqv, p)),
      Equal.cong(Nat, Nat, t => Nat.add(t, p), Nat.add(Nat.add(N, x), Nat.add(qv, y)), Nat.add(Nqv, xy), NO.add_swap4(N, x, qv, y)),
      Equal.trans(Nat, Nat.add(Nat.add(Nqv, xy), p), Nat.add(Nqv, Nat.add(xy, p)), Nat.add(xy, Nat.add(Nqv, p)),
        Ar.ar_add_assoc(Nqv, xy, p), NO.add_swap(Nqv, xy, p))))

# (a + 0) + 0 == a
def pn_z2(+a: Nat) -> {Nat.add(Nat.add(a, 0n), 0n) == a : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, 0n), 0n), Nat.add(a, 0n), a, Ar.ar_add_zero_r(Nat.add(a, 0n)), Ar.ar_add_zero_r(a))

# ==== path rearrangements ====

# Paths with equal components are equal
def pf_ext(-a1: Nat, -a2: Nat, -a3: Nat, -a4: Nat, -a5: Nat, -a6: Nat, -a7: Nat, -a8: Nat, -b1: Nat, -b2: Nat, -b3: Nat, -b4: Nat, -b5: Nat, -b6: Nat, -b7: Nat, -b8: Nat,
    e1: {a1 == b1 : Nat}, e2: {a2 == b2 : Nat}, e3: {a3 == b3 : Nat}, e4: {a4 == b4 : Nat}, e5: {a5 == b5 : Nat}, e6: {a6 == b6 : Nat}, e7: {a7 == b7 : Nat}, e8: {a8 == b8 : Nat})
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

# a + (b + (c + (d + X))) == (a + (b + (c + d))) + X, for paths
def pf_h1(a: Eb.Path, b: Eb.Path, c: Eb.Path, d: Eb.Path, X: Eb.Path)
  -> {Ea.cat(a, Ea.cat(b, Ea.cat(c, Ea.cat(d, X)))) == Ea.cat(Ea.cat(a, Ea.cat(b, Ea.cat(c, d))), X) : Eb.Path}:
  match a:
    case Eb.Path{+a1, +a2, +a3, +a4, +a5, +a6, +a7, +a8}:
      match b:
        case Eb.Path{+b1, +b2, +b3, +b4, +b5, +b6, +b7, +b8}:
          match c:
            case Eb.Path{+c1, +c2, +c3, +c4, +c5, +c6, +c7, +c8}:
              match d:
                case Eb.Path{+d1, +d2, +d3, +d4, +d5, +d6, +d7, +d8}:
                  match X:
                    case Eb.Path{+X1, +X2, +X3, +X4, +X5, +X6, +X7, +X8}:
                      pf_ext(Nat.add(a1, Nat.add(b1, Nat.add(c1, Nat.add(d1, X1)))),
                        Nat.add(a2, Nat.add(b2, Nat.add(c2, Nat.add(d2, X2)))),
                        Nat.add(a3, Nat.add(b3, Nat.add(c3, Nat.add(d3, X3)))),
                        Nat.add(a4, Nat.add(b4, Nat.add(c4, Nat.add(d4, X4)))),
                        Nat.add(a5, Nat.add(b5, Nat.add(c5, Nat.add(d5, X5)))),
                        Nat.add(a6, Nat.add(b6, Nat.add(c6, Nat.add(d6, X6)))),
                        Nat.add(a7, Nat.add(b7, Nat.add(c7, Nat.add(d7, X7)))),
                        Nat.add(a8, Nat.add(b8, Nat.add(c8, Nat.add(d8, X8)))),
                        Nat.add(Nat.add(a1, Nat.add(b1, Nat.add(c1, d1))), X1),
                        Nat.add(Nat.add(a2, Nat.add(b2, Nat.add(c2, d2))), X2),
                        Nat.add(Nat.add(a3, Nat.add(b3, Nat.add(c3, d3))), X3),
                        Nat.add(Nat.add(a4, Nat.add(b4, Nat.add(c4, d4))), X4),
                        Nat.add(Nat.add(a5, Nat.add(b5, Nat.add(c5, d5))), X5),
                        Nat.add(Nat.add(a6, Nat.add(b6, Nat.add(c6, d6))), X6),
                        Nat.add(Nat.add(a7, Nat.add(b7, Nat.add(c7, d7))), X7),
                        Nat.add(Nat.add(a8, Nat.add(b8, Nat.add(c8, d8))), X8),
                        pn_h1(a1, b1, c1, d1, X1),
                        pn_h1(a2, b2, c2, d2, X2),
                        pn_h1(a3, b3, c3, d3, X3),
                        pn_h1(a4, b4, c4, d4, X4),
                        pn_h1(a5, b5, c5, d5, X5),
                        pn_h1(a6, b6, c6, d6, X6),
                        pn_h1(a7, b7, c7, d7, X7),
                        pn_h1(a8, b8, c8, d8, X8))

# ((N + X) + ((qrot(0) + Y) + div)) + po == (X + Y) + ((N + (qrot(0) + div)) + po), for paths
def pf_core(N: Eb.Path, X: Eb.Path, Y: Eb.Path, po: Eb.Path)
  -> {Ea.cat(Ea.cat(Ea.cat(N, X), Ea.cat(Ea.cat(Ea.qrot(0n), Y), Ea.div())), po) ==
      Ea.cat(Ea.cat(X, Y), Ea.cat(Ea.cat(N, Ea.cat(Ea.qrot(0n), Ea.div())), po)) : Eb.Path}:
  match N:
    case Eb.Path{+N1, +N2, +N3, +N4, +N5, +N6, +N7, +N8}:
      match X:
        case Eb.Path{+X1, +X2, +X3, +X4, +X5, +X6, +X7, +X8}:
          match Y:
            case Eb.Path{+Y1, +Y2, +Y3, +Y4, +Y5, +Y6, +Y7, +Y8}:
              match po:
                case Eb.Path{+po1, +po2, +po3, +po4, +po5, +po6, +po7, +po8}:
                  pf_ext(Nat.add(Nat.add(Nat.add(N1, X1), Nat.add(Nat.add(0n, Y1), 1n)), po1),
                    Nat.add(Nat.add(Nat.add(N2, X2), Nat.add(Nat.add(2n, Y2), 0n)), po2),
                    Nat.add(Nat.add(Nat.add(N3, X3), Nat.add(Nat.add(1n, Y3), 0n)), po3),
                    Nat.add(Nat.add(Nat.add(N4, X4), Nat.add(Nat.add(0n, Y4), 0n)), po4),
                    Nat.add(Nat.add(Nat.add(N5, X5), Nat.add(Nat.add(0n, Y5), 0n)), po5),
                    Nat.add(Nat.add(Nat.add(N6, X6), Nat.add(Nat.add(0n, Y6), 0n)), po6),
                    Nat.add(Nat.add(Nat.add(N7, X7), Nat.add(Nat.add(0n, Y7), 1n)), po7),
                    Nat.add(Nat.add(Nat.add(N8, X8), Nat.add(Nat.add(0n, Y8), 0n)), po8),
                    Nat.add(Nat.add(X1, Y1), Nat.add(Nat.add(N1, Nat.add(0n, 1n)), po1)),
                    Nat.add(Nat.add(X2, Y2), Nat.add(Nat.add(N2, Nat.add(2n, 0n)), po2)),
                    Nat.add(Nat.add(X3, Y3), Nat.add(Nat.add(N3, Nat.add(1n, 0n)), po3)),
                    Nat.add(Nat.add(X4, Y4), Nat.add(Nat.add(N4, Nat.add(0n, 0n)), po4)),
                    Nat.add(Nat.add(X5, Y5), Nat.add(Nat.add(N5, Nat.add(0n, 0n)), po5)),
                    Nat.add(Nat.add(X6, Y6), Nat.add(Nat.add(N6, Nat.add(0n, 0n)), po6)),
                    Nat.add(Nat.add(X7, Y7), Nat.add(Nat.add(N7, Nat.add(0n, 1n)), po7)),
                    Nat.add(Nat.add(X8, Y8), Nat.add(Nat.add(N8, Nat.add(0n, 0n)), po8)),
                    pn_core(N1, X1, 0n, Y1, 1n, po1),
                    pn_core(N2, X2, 2n, Y2, 0n, po2),
                    pn_core(N3, X3, 1n, Y3, 0n, po3),
                    pn_core(N4, X4, 0n, Y4, 0n, po4),
                    pn_core(N5, X5, 0n, Y5, 0n, po5),
                    pn_core(N6, X6, 0n, Y6, 0n, po6),
                    pn_core(N7, X7, 0n, Y7, 1n, po7),
                    pn_core(N8, X8, 0n, Y8, 0n, po8))

# sk4 regrouped: (X + Y) + ((N + (qrot(0) + div)) + po), N = a + (b + (c + d))
def pf_sk4(+a: Eb.Path, +b: Eb.Path, +c: Eb.Path, +d: Eb.Path, +X: Eb.Path, +Y: Eb.Path, +po: Eb.Path)
  -> {Dec.sk4(a, b, c, d, X, Y, po) ==
      Ea.cat(Ea.cat(X, Y), Ea.cat(Ea.cat(Ea.cat(a, Ea.cat(b, Ea.cat(c, d))), Ea.cat(Ea.qrot(0n), Ea.div())), po)) : Eb.Path}:
  +N = Ea.cat(a, Ea.cat(b, Ea.cat(c, d)))
  Equal.trans(Eb.Path, Dec.sk4(a, b, c, d, X, Y, po), Dec.sk1(N, X, Y, po),
    Ea.cat(Ea.cat(X, Y), Ea.cat(Ea.cat(N, Ea.cat(Ea.qrot(0n), Ea.div())), po)),
    Equal.cong(Eb.Path, Eb.Path, t => Ea.cat(Ea.cat(t, Ea.cat(Ea.cat(Ea.qrot(0n), Y), Ea.div())), po),
      Ea.cat(a, Ea.cat(b, Ea.cat(c, Ea.cat(d, X)))), Ea.cat(N, X), pf_h1(a, b, c, d, X)),
    pf_core(N, X, Y, po))

# ==== domination of regrouped routes ====

# sk1-shaped routes: the regrouped parts dominated piecewise
def pd_sk1(+Ne: Eb.Path, +Xe: Eb.Path, +Ye: Eb.Path, +poe: Eb.Path, +Ns: Eb.Path, +Xs: Eb.Path, +Ys: Eb.Path, +pos: Eb.Path,
    hc: {Eb.dom(128n, Ea.cat(Xe, Ye), Ea.cat(Xs, Ys)) == True{} : Bool},
    hs: {Eb.dom(128n, Ea.cat(Ea.cat(Ne, Ea.cat(Ea.qrot(0n), Ea.div())), poe), Ea.cat(Ea.cat(Ns, Ea.cat(Ea.qrot(0n), Ea.div())), pos)) == True{} : Bool})
  -> {Eb.dom(128n, Dec.sk1(Ne, Xe, Ye, poe), Dec.sk1(Ns, Xs, Ys, pos)) == True{} : Bool}:
  +Ce = Ea.cat(Ea.cat(Ne, Ea.cat(Ea.qrot(0n), Ea.div())), poe)
  +Cs = Ea.cat(Ea.cat(Ns, Ea.cat(Ea.qrot(0n), Ea.div())), pos)
  %Equal.sym(Eb.Path, Dec.sk1(Ne, Xe, Ye, poe), Ea.cat(Ea.cat(Xe, Ye), Ce), pf_core(Ne, Xe, Ye, poe)) :
    {Eb.dom(128n, _, Dec.sk1(Ns, Xs, Ys, pos)) == True{} : Bool}
  %Equal.sym(Eb.Path, Dec.sk1(Ns, Xs, Ys, pos), Ea.cat(Ea.cat(Xs, Ys), Cs), pf_core(Ns, Xs, Ys, pos)) :
    {Eb.dom(128n, Ea.cat(Ea.cat(Xe, Ye), Ce), _) == True{} : Bool}
  EbL.dom_add(128n, Ea.cat(Xe, Ye), Ea.cat(Xs, Ys), Ce, Cs, hc, hs)

# sk4-shaped routes
def pd_sk4(+ae: Eb.Path, +be: Eb.Path, +ce: Eb.Path, +de: Eb.Path, +Xe: Eb.Path, +Ye: Eb.Path, +poe: Eb.Path,
    +as: Eb.Path, +bs: Eb.Path, +cs: Eb.Path, +ds: Eb.Path, +Xs: Eb.Path, +Ys: Eb.Path, +pos: Eb.Path,
    hc: {Eb.dom(128n, Ea.cat(Xe, Ye), Ea.cat(Xs, Ys)) == True{} : Bool},
    hs: {Eb.dom(128n, Ea.cat(Ea.cat(Ea.cat(ae, Ea.cat(be, Ea.cat(ce, de))), Ea.cat(Ea.qrot(0n), Ea.div())), poe),
                      Ea.cat(Ea.cat(Ea.cat(as, Ea.cat(bs, Ea.cat(cs, ds))), Ea.cat(Ea.qrot(0n), Ea.div())), pos)) == True{} : Bool})
  -> {Eb.dom(128n, Dec.sk4(ae, be, ce, de, Xe, Ye, poe), Dec.sk4(as, bs, cs, ds, Xs, Ys, pos)) == True{} : Bool}:
  +Ce = Ea.cat(Ea.cat(Ea.cat(ae, Ea.cat(be, Ea.cat(ce, de))), Ea.cat(Ea.qrot(0n), Ea.div())), poe)
  +Cs = Ea.cat(Ea.cat(Ea.cat(as, Ea.cat(bs, Ea.cat(cs, ds))), Ea.cat(Ea.qrot(0n), Ea.div())), pos)
  %Equal.sym(Eb.Path, Dec.sk4(ae, be, ce, de, Xe, Ye, poe), Ea.cat(Ea.cat(Xe, Ye), Ce), pf_sk4(ae, be, ce, de, Xe, Ye, poe)) :
    {Eb.dom(128n, _, Dec.sk4(as, bs, cs, ds, Xs, Ys, pos)) == True{} : Bool}
  %Equal.sym(Eb.Path, Dec.sk4(as, bs, cs, ds, Xs, Ys, pos), Ea.cat(Ea.cat(Xs, Ys), Cs), pf_sk4(as, bs, cs, ds, Xs, Ys, pos)) :
    {Eb.dom(128n, Ea.cat(Ea.cat(Xe, Ye), Ce), _) == True{} : Bool}
  EbL.dom_add(128n, Ea.cat(Xe, Ye), Ea.cat(Xs, Ys), Ce, Cs, hc, hs)

# ==== the core: numerator steps beyond P V + denominator part ====

# Stock key 0's regrouped part
def ps_X(+L: Nat) -> Eb.Path:
  Ea.cat(Ea.chain(Dec.geo_s0(L)), Ea.comb(Dec.geo_s0(L)))

def ps_Y(+L: Nat) -> Eb.Path:
  Eb.Path{Dec.s_dr0(L), 16n, 0n, 0n, 0n, 1n, 0n, 0n}

# s_rt is the stock part's t32 + r32 (with the + 0 of the dom spare term)
def pc_srt(+L: Nat)
  -> {Nat.is_le(Dec.s_rt(L), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), 0n), 0n), 16n),
        Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L))), 0n)) == True{} : Bool}:
  +G = Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))
  +SA = Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L))
  +sb = Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n)
  NO.le_of_eq(Dec.s_rt(L), Nat.add(Nat.add(sb, SA), 0n),
    Equal.trans(Nat, Dec.s_rt(L), Nat.add(sb, SA), Nat.add(Nat.add(sb, SA), 0n),
      Equal.cong(Nat, Nat, t => Nat.add(Nat.add(t, 16n), SA), G, Nat.add(Nat.add(G, 0n), 0n), Equal.sym(Nat, Nat.add(Nat.add(G, 0n), 0n), G, pn_z2(G))),
      Equal.sym(Nat, Nat.add(Nat.add(sb, SA), 0n), Nat.add(sb, SA), Ar.ar_add_zero_r(Nat.add(sb, SA)))))

# t32: own + 16 <= (own0 + laterk0) + 16, with the + 0 terms of the path sums and of dom
def pc_t32(+L: Nat, +own: Nat, ho: {Nat.is_le(own, Dec.e_OE(L)) == True{} : Bool},
    hT: {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n),
        Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), 0n), 0n), 16n), 0n)) == True{} : Bool}:
  +G = Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n), 0n), Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n),
    Ar.ar_add_zero_r(Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n))) :
    {Nat.is_le(Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n), _) == True{} : Bool}
  NO.le_add_mono(Nat.add(Nat.add(own, 0n), 0n), Nat.add(Nat.add(G, 0n), 0n), 16n, 16n,
    NO.le_trans(Nat.add(Nat.add(own, 0n), 0n), own, Nat.add(Nat.add(G, 0n), 0n), NO.le_of_eq(Nat.add(Nat.add(own, 0n), 0n), own, pn_z2(own)),
      NO.le_trans(own, G, Nat.add(Nat.add(G, 0n), 0n), NO.le_trans(own, Dec.e_OE(L), G, ho, hT),
        NO.le_of_eq(G, Nat.add(Nat.add(G, 0n), 0n), Equal.sym(Nat, Nat.add(Nat.add(G, 0n), 0n), G, pn_z2(G))))),
    NO.le_refl(16n))

# r32 + t32 of the 3030 part up to e_rt: own + 16, folds, tree, denominator bound
def pc_rt(+L: Nat, +own: Nat, +fold: Nat, +dep: Nat,
    ho: {Nat.is_le(own, Dec.e_OE(L)) == True{} : Bool},
    hf: {Nat.is_le(fold, Dec.e_n0(L)) == True{} : Bool},
    hd: {Nat.is_le(dep, Dec.e_D(L)) == True{} : Bool},
    hR: {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n), Nat.add(Nat.add(fold, dep), Dec.e_dr(L))),
        Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), 0n), 0n), 16n),
          Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L))), 0n)) == True{} : Bool}:
  +dr = Dec.e_dr(L)
  +ebr = NO.le_add_mono(Nat.add(Nat.add(own, 0n), 0n), Dec.e_OE(L), 16n, 16n,
    NO.le_trans(Nat.add(Nat.add(own, 0n), 0n), own, Dec.e_OE(L), NO.le_of_eq(Nat.add(Nat.add(own, 0n), 0n), own, pn_z2(own)), ho),
    NO.le_refl(16n))
  +ear = NO.le_add_mono(Nat.add(fold, dep), Nat.add(Dec.e_n0(L), Dec.e_D(L)), dr, dr,
    NO.le_add_mono(fold, Dec.e_n0(L), dep, Dec.e_D(L), hf, hd), NO.le_refl(dr))
  NO.le_trans(Nat.add(Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n), Nat.add(Nat.add(fold, dep), dr)), Dec.e_rt(L),
    Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), 0n), 0n), 16n),
      Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L))), 0n),
    NO.le_add_mono(Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n), Nat.add(Dec.e_OE(L), 16n), Nat.add(Nat.add(fold, dep), dr),
      Nat.add(Nat.add(Dec.e_n0(L), Dec.e_D(L)), dr), ebr, ear),
    NO.le_trans(Dec.e_rt(L), Dec.s_rt(L), Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Dec.s_own0(L), Dec.s_laterk0(L)), 0n), 0n), 16n),
      Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L))), 0n), hR, pc_srt(L)))

# The key route's part dominated
def pc_key(+L: Nat, +x: Nat, +q: Nat, +g: Nat,
    +ho: {Nat.is_le(Dec.e_own(L, x, q, g), Dec.e_OE(L)) == True{} : Bool},
    hf: {Nat.is_le(Dec.e_fold(L, x, q), Dec.e_n0(L)) == True{} : Bool},
    hd: {Nat.is_le(Dec.e_depth(L, x), Dec.e_D(L)) == True{} : Bool},
    hT: {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool},
    hR: {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool})
  -> {Eb.dom(128n, Ea.cat(Dec.e_cc(L, x, q, g), Dec.e_dg(L)), Ea.cat(ps_X(L), ps_Y(L))) == True{} : Bool}:
  +own = Dec.e_own(L, x, q, g)
  +fold = Dec.e_fold(L, x, q)
  +dep = Dec.e_depth(L, x)
  +G = Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))
  EbP.eb_dom_mk(128n, Nat.add(Nat.add(fold, dep), Dec.e_dr(L)), Nat.add(Nat.add(Nat.add(own, 0n), 0n), 16n), 0n, 0n, 0n, 1n, 0n, 0n,
    Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L)), Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n), 0n, 0n, 0n, 1n, 0n, 0n,
    {==}, {==}, {==}, pc_t32(L, own, ho, hT), pc_rt(L, own, fold, dep, ho, hf, hd, hR), {==}, {==}, {==})

# The coefficient route's part (cs multiplies the tile: no MMA step on this route)
def pc_coef(+L: Nat, +x: Nat, +q: Nat,
    hf: {Nat.is_le(Dec.e_fold(L, x, q), Dec.e_n0(L)) == True{} : Bool},
    hd: {Nat.is_le(Dec.e_depth(L, x), Dec.e_D(L)) == True{} : Bool},
    hT: {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool},
    hR: {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool})
  -> {Eb.dom(128n, Ea.cat(Dec.e_cs(L, x, q), Dec.e_dg(L)), Ea.cat(ps_X(L), ps_Y(L))) == True{} : Bool}:
  +fold = Dec.e_fold(L, x, q)
  +dep = Dec.e_depth(L, x)
  +G = Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))
  +z = NO.le_zero(Dec.e_OE(L))
  EbP.eb_dom_mk(128n, Nat.add(Nat.add(fold, dep), Dec.e_dr(L)), Nat.add(Nat.add(Nat.add(0n, 0n), 0n), 16n), 0n, 0n, 0n, 1n, 0n, 0n,
    Nat.add(Nat.add(Dec.s_later0(L), 1n+Dec.s_after0(L)), Dec.s_dr0(L)), Nat.add(Nat.add(Nat.add(G, 0n), 0n), 16n), 0n, 0n, 0n, 1n, 0n, 0n,
    {==}, {==}, {==}, pc_t32(L, 0n, z, hT), pc_rt(L, 0n, fold, dep, z, hf, hd, hR), {==}, {==}, {==})

# The shared segments of the coefficient route against stock AQ's: zero in place of pconv
def pc_coef_rest(+kh: Nat, +ks: Nat, +po: Eb.Path)
  -> {Eb.dom(128n, Ea.cat(Ea.cat(Ea.cat(Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Dec.e_xs(), Eb.zero()))), Ea.cat(Ea.qrot(0n), Ea.div())), po),
        Ea.cat(Ea.cat(Ea.cat(Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Ea.s_xs(), Ea.pconv()))), Ea.cat(Ea.qrot(0n), Ea.div())), po)) == True{} : Bool}:
  +QD = Ea.cat(Ea.qrot(0n), Ea.div())
  +ne = Ea.cat(Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Dec.e_xs(), Eb.zero())))
  +ns = Ea.cat(Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Ea.s_xs(), Ea.pconv())))
  +d3 = EbL.dom_add(128n, Dec.e_xs(), Ea.s_xs(), Eb.zero(), Ea.pconv(), EbL.dom_refl(128n, Ea.s_xs()), {==})
  +d2 = EbL.dom_add(128n, Ea.qk(ks), Ea.qk(ks), Ea.cat(Dec.e_xs(), Eb.zero()), Ea.cat(Ea.s_xs(), Ea.pconv()), EbL.dom_refl(128n, Ea.qk(ks)), d3)
  +d1 = EbL.dom_add(128n, Ea.qrot(kh), Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Dec.e_xs(), Eb.zero())),
    Ea.cat(Ea.qk(ks), Ea.cat(Ea.s_xs(), Ea.pconv())), EbL.dom_refl(128n, Ea.qrot(kh)), d2)
  EbL.dom_add(128n, Ea.cat(ne, QD), Ea.cat(ns, QD), po, po, EbL.dom_add(128n, ne, ns, QD, QD, d1, EbL.dom_refl(128n, QD)), EbL.dom_refl(128n, po))

# ==== the totals (bend/err_attn_dec_p2.bend) ====

def pt_T(+L: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool}:
  Ar.ard_fst({Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool},
    {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}, P2.dec_p2(L, pos))

def pt_R(+L: Nat, pos: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}:
  Ar.ard_snd({Nat.is_le(Dec.e_OE(L), Nat.add(Dec.s_own0(L), Dec.s_laterk0(L))) == True{} : Bool},
    {Nat.is_le(Dec.e_rt(L), Dec.s_rt(L)) == True{} : Bool}, P2.dec_p2(L, pos))

# ==== dec_dom per key and route kind ====

def pl_dom(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat, l: Dec.DLeaf, +pos: {Nat.is_le(1n, L) == True{} : Bool},
    +ok: {Dec.key_ok(L, Dec.DKey{x, q, g, r}) == True{} : Bool})
  -> {Eb.dom(128n, Dec.elpis_route(L, x, q, g, l), Ea.stock_leaf(Dec.geo_s0(L), Dec.stock_of(l))) == True{} : Bool}:
  match l:
    case Dec.DQ{+kh, +ks, +i}:
      +lo = Nat.is_lt(i, 16n)
      pd_sk4(Ea.qrot(kh), Ea.qk(ks), Dec.e_xs(), Ea.pconv(), Dec.e_cc(L, x, q, g), Dec.e_dg(L), Dec.e_postb(lo),
        Ea.qrot(kh), Ea.qk(ks), Ea.s_xs(), Ea.pconv(), ps_X(L), ps_Y(L), Ea.s_postb(lo),
        pc_key(L, x, q, g, K.k_own(L, x, q, g, r, ok), K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, ok), pt_T(L, pos), pt_R(L, pos)),
        EbL.dom_refl(128n, Ea.cat(Ea.cat(Ea.cat(Ea.qrot(kh), Ea.cat(Ea.qk(ks), Ea.cat(Ea.s_xs(), Ea.pconv()))), Ea.cat(Ea.qrot(0n), Ea.div())), Ea.s_postb(lo))))
    case Dec.DK{+ks, +i}:
      +lo = Nat.is_lt(i, 16n)
      pd_sk4(Ea.deq(), Ea.qk(ks), Dec.e_xs(), Ea.pconv(), Dec.e_cc(L, x, q, g), Dec.e_dg(L), Dec.e_postb(lo),
        Ea.deq(), Ea.qk(ks), Ea.s_xs(), Ea.pconv(), ps_X(L), ps_Y(L), Ea.s_postb(lo),
        pc_key(L, x, q, g, K.k_own(L, x, q, g, r, ok), K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, ok), pt_T(L, pos), pt_R(L, pos)),
        EbL.dom_refl(128n, Ea.cat(Ea.cat(Ea.cat(Ea.deq(), Ea.cat(Ea.qk(ks), Ea.cat(Ea.s_xs(), Ea.pconv()))), Ea.cat(Ea.qrot(0n), Ea.div())), Ea.s_postb(lo))))
    case Dec.DV{+i}:
      +lo = Nat.is_lt(i, 16n)
      pd_sk1(Ea.deq(), Dec.e_cc(L, x, q, g), Dec.e_dg(L), Dec.e_postb(lo), Ea.deq(), ps_X(L), ps_Y(L), Ea.s_postb(lo),
        pc_key(L, x, q, g, K.k_own(L, x, q, g, r, ok), K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, ok), pt_T(L, pos), pt_R(L, pos)),
        EbL.dom_refl(128n, Ea.cat(Ea.cat(Ea.deq(), Ea.cat(Ea.qrot(0n), Ea.div())), Ea.s_postb(lo))))
    case Dec.DC{+kh, +ks, +i}:
      +lo = Nat.is_lt(i, 16n)
      pd_sk4(Ea.qrot(kh), Ea.qk(ks), Dec.e_xs(), Eb.zero(), Dec.e_cs(L, x, q), Dec.e_dg(L), Dec.e_postb(lo),
        Ea.qrot(kh), Ea.qk(ks), Ea.s_xs(), Ea.pconv(), ps_X(L), ps_Y(L), Ea.s_postb(lo),
        pc_coef(L, x, q, K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, ok), pt_T(L, pos), pt_R(L, pos)),
        pc_coef_rest(kh, ks, Ea.s_postb(lo)))
    case Dec.DG{}:
      EbL.dom_refl(128n, Ea.gate())

# The composite convention's coefficient paths: 3030's cs against stock's w and alphas
def pl_coef(+L: Nat, l: Dec.DLeaf) -> {Eb.dom(128n, Dec.e_coef(l), Dec.s_coef(L, l)) == True{} : Bool}:
  match l:
    case Dec.DQ{kh, ks, i}:
      EbP.eb_dom_mk(128n, 1n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, Nat.add(Nat.mul(1n+Dec.s_later0(L), 2n), 0n), 0n, 0n, 0n, 0n, 1n+Dec.s_later0(L), 0n, 0n,
        {==}, {==}, {==}, {==}, {==}, NO.le_zero(Dec.s_later0(L)), {==}, {==})
    case Dec.DK{ks, i}:
      EbP.eb_dom_mk(128n, 1n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, Nat.add(Nat.mul(1n+Dec.s_later0(L), 2n), 0n), 0n, 0n, 0n, 0n, 1n+Dec.s_later0(L), 0n, 0n,
        {==}, {==}, {==}, {==}, {==}, NO.le_zero(Dec.s_later0(L)), {==}, {==})
    case Dec.DV{i}:
      EbP.eb_dom_mk(128n, 1n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, Nat.add(Nat.mul(1n+Dec.s_later0(L), 2n), 0n), 0n, 0n, 0n, 0n, 1n+Dec.s_later0(L), 0n, 0n,
        {==}, {==}, {==}, {==}, {==}, NO.le_zero(Dec.s_later0(L)), {==}, {==})
    case Dec.DC{kh, ks, i}:
      EbL.dom_refl(128n, Eb.zero())
    case Dec.DG{}:
      EbL.dom_refl(128n, Eb.zero())

# ==== the laws ====

def Laws.dec_xs_eq():
  {==}

def Laws.dec_post_eq(lo):
  {==}

def Laws.dec_geo2():
  +lazy : Nat = 0n
  {==}

def Laws.dec_totals(L, pos):
  P2.dec_p2(L, pos)

def Laws.dec_key_bounds(L, x, q, g, r, pos, ok):
  +o = ok
  (K.k_own(L, x, q, g, r, o), K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, o))

def Laws.dec_den_bound(L, x, q, g, r, pos, ok):
  +o = ok
  +fd = NO.le_add_mono(Dec.e_fold(L, x, q), Dec.e_n0(L), Dec.e_depth(L, x), Dec.e_D(L), K.k_fold(L, x, q, pos), K.k_depth(L, x, q, g, r, o))
  +FD = Nat.add(Dec.e_fold(L, x, q), Dec.e_depth(L, x))
  +ND = Nat.add(Dec.e_n0(L), Dec.e_D(L))
  (NO.le_add_mono(2n, 2n, Nat.add(Dec.e_tsum(L, x, q, g, r), FD), Nat.add(Dec.e_TE(L), ND), NO.le_refl(2n),
     NO.le_add_mono(Dec.e_tsum(L, x, q, g, r), Dec.e_TE(L), FD, ND, K.k_tsum(L, x, q, g, r, o), fd)),
   NO.le_add_mono(2n, 2n, FD, Nat.add(Dec.e_TE(L), ND), NO.le_refl(2n),
     NO.le_trans(FD, ND, Nat.add(Dec.e_TE(L), ND), fd, NO.le_add_l(Dec.e_TE(L), ND))))

def Laws.dec_dom(L, k, l, pos, ok):
  match k:
    case Dec.DKey{+x, +q, +g, +r}:
      pl_dom(L, x, q, g, r, l, pos, ok)

def Laws.dec_dom_coef(L, k, l, pos, ok):
  EbL.dom_add(128n, Dec.elpis_leaf(L, k, l), Ea.stock_leaf(Dec.geo_s0(L), Dec.stock_of(l)), Dec.e_coef(l), Dec.s_coef(L, l),
    Laws.dec_dom(L, k, l, pos, ok), pl_coef(L, l))

# ==== domination is monotone in the dominating path ====

def pm_dom(+x: Nat, +ea: Nat, +eb: Nat, +ec: Nat, +ed: Nat, +eh: Nat, +ee: Nat, +ef: Nat, +eg: Nat,
    +sa: Nat, +sb: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +se: Nat, +sf: Nat, +sg: Nat,
    +ta: Nat, +tb: Nat, +tc: Nat, +td: Nat, +th: Nat, +te: Nat, +tf: Nat, +tg: Nat,
    parts: EbP.DomP(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg),
    +le: {Dec.path_le(Eb.Path{sa, sb, sc, sd, sh, se, sf, sg}, Eb.Path{ta, tb, tc, td, th, te, tf, tg}) == True{} : Bool})
  -> {Eb.dom(x, Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg}, Eb.Path{ta, tb, tc, td, th, te, tf, tg}) == True{} : Bool}:
  (c1, c2, c3, c4, c5, c6, c7, c8) = parts
  +B1 = Nat.is_le(sa, ta)
  +B2 = Nat.is_le(sb, tb)
  +B3 = Nat.is_le(sc, tc)
  +B4 = Nat.is_le(sd, td)
  +B5 = Nat.is_le(sh, th)
  +B6 = Nat.is_le(se, te)
  +B7 = Nat.is_le(sf, tf)
  +B8 = Nat.is_le(sg, tg)
  +R7 = Bool.and(B7, B8)
  +R6 = Bool.and(B6, R7)
  +R5 = Bool.and(B5, R6)
  +R4 = Bool.and(B4, R5)
  +R3 = Bool.and(B3, R4)
  +R2 = Bool.and(B2, R3)
  +q2 = NO.and_r(B1, R2, le)
  +q3 = NO.and_r(B2, R3, q2)
  +q4 = NO.and_r(B3, R4, q3)
  +q5 = NO.and_r(B4, R5, q4)
  +q6 = NO.and_r(B5, R6, q5)
  +q7 = NO.and_r(B6, R7, q6)
  +l1 = NO.and_l(B1, R2, le)
  +l2 = NO.and_l(B2, R3, q2)
  +l3 = NO.and_l(B3, R4, q3)
  +l4 = NO.and_l(B4, R5, q4)
  +l5 = NO.and_l(B5, R6, q5)
  +CAP = Nat.mul(x, Nat.sub(sh, eh))
  +CAP2 = Nat.mul(x, Nat.sub(th, eh))
  +capm = NO.le_mul_mono_r(Nat.sub(sh, eh), Nat.sub(th, eh), x, K.k_sub_mono(sh, th, eh, l5))
  +S1 = Nat.add(Nat.add(sd, sc), CAP)
  +S2 = Nat.add(Nat.add(td, tc), CAP2)
  +s12 = NO.le_add_mono(Nat.add(sd, sc), Nat.add(td, tc), CAP, CAP2, NO.le_add_mono(sd, td, sc, tc, l4, l3), capm)
  +X1 = Nat.mul(x, Nat.sub(S1, Nat.add(ed, ec)))
  +X2 = Nat.mul(x, Nat.sub(S2, Nat.add(ed, ec)))
  +xm = NO.le_mul_mono_r(Nat.sub(S1, Nat.add(ed, ec)), Nat.sub(S2, Nat.add(ed, ec)), x, K.k_sub_mono(S1, S2, Nat.add(ed, ec), s12))
  EbP.eb_dom_mk(x, ea, eb, ec, ed, eh, ee, ef, eg, ta, tb, tc, td, th, te, tf, tg,
    NO.le_trans(eh, sh, th, c1, l5),
    NO.le_trans(ed, Nat.add(sd, CAP), Nat.add(td, CAP2), c2, NO.le_add_mono(sd, td, CAP, CAP2, l4, capm)),
    NO.le_trans(Nat.add(ed, ec), S1, S2, c3, s12),
    NO.le_trans(eb, Nat.add(sb, X1), Nat.add(tb, X2), c4, NO.le_add_mono(sb, tb, X1, X2, l2, xm)),
    NO.le_trans(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), X1), Nat.add(Nat.add(tb, ta), X2), c5,
      NO.le_add_mono(Nat.add(sb, sa), Nat.add(tb, ta), X1, X2, NO.le_add_mono(sb, tb, sa, ta, l2, l1), xm)),
    NO.le_trans(ee, se, te, c6, NO.and_l(B6, R7, q6)),
    NO.le_trans(ef, sf, tf, c7, NO.and_l(B7, B8, q7)),
    NO.le_trans(eg, sg, tg, c8, NO.and_r(B7, B8, q7)))

def Laws.dec_dom_mono(x, e, s, s2, d, le):
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Eb.Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          match s2:
            case Eb.Path{+ta, +tb, +tc, +td, +th, +te, +tf, +tg}:
              pm_dom(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg, ta, tb, tc, td, th, te, tf, tg,
                EbP.eb_dom_parts(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg, d), le)
