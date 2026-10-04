# Proofs of bend/err_bound_laws.bend (core laws of the rounding-error bound vocabulary
# bend/err_bound.bend). Generic Nat facts come from bend/nat_order_laws.bend (proven in
# bend/nat_order_proof.bend). No @unsafe definitions, axioms, holes or foreign code; every def
# precedes its uses.
#
# dom_sigma is Abel summation over the class order, tier by tier. With kq = s.q8 - e.q8 (exact:
# e.q8 <= s.q8 is a dom condition), capc = x kq, spare = (s.t16 + s.r16 + capc) - (e.t16 + e.r16)
# (exact: the third dom condition) and K = spare * w.r16:
#   fine part:    a*wa + b*wb <= (sa*wa + sb*wb) + K      (eb_fine: one Abel step over wa <= wb with
#                 the x * spare t32 slots, then x * wb <= wc turns (x spare) wb into spare wc)
#   coarse part:  (c*wc + K) + (d*wd + h*wh) <= sc*wc + (sd*wd + sh*wh)
#                 (eb_coarse: one Abel step over wc <= wd with the spare joining e's r16 count and
#                 capc lent to s's t16 count; then x * wd <= wh turns (x kq) wd into kq wh, and
#                 h + kq = sh)
#   special part: term by term (ex2 / rcp / rsq matched kind by kind).
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as Laws
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP

# ==== Abel summation step ====

# p <= q and p + l <= q + m give l <= (q - p) + m
def eb_cancel_top(+l: Nat, +p: Nat, +m: Nat, +q: Nat, pq: {Nat.is_le(p, q) == True{} : Bool},
    sum: {Nat.is_le(Nat.add(p, l), Nat.add(q, m)) == True{} : Bool})
  -> {Nat.is_le(l, Nat.add(Nat.sub(q, p), m)) == True{} : Bool}:
  +r = Nat.sub(q, p)
  %NO.le_add_cancel(p, l, Nat.add(r, m)) : {_ == True{} : Bool}
  %NO.add_assoc(p, r, m) : {Nat.is_le(Nat.add(p, l), _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(p, r), q, NO.sub_add(q, p, pq)) :
    {Nat.is_le(Nat.add(p, l), Nat.add(_, m)) == True{} : Bool}
  sum

# One Abel step: wlo <= whi, p <= q and p + l <= q + m give l wlo + p whi <= m wlo + q whi
def eb_step(+l: Nat, +p: Nat, +m: Nat, +q: Nat, +wlo: Nat, +whi: Nat,
    w: {Nat.is_le(wlo, whi) == True{} : Bool}, +pq: {Nat.is_le(p, q) == True{} : Bool},
    sum: {Nat.is_le(Nat.add(p, l), Nat.add(q, m)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(l, wlo), Nat.mul(p, whi)), Nat.add(Nat.mul(m, wlo), Nat.mul(q, whi))) == True{} : Bool}:
  +r = Nat.sub(q, p)
  +L = Nat.add(Nat.mul(l, wlo), Nat.mul(p, whi))
  +rw = Nat.mul(r, whi)
  +mw = Nat.mul(m, wlo)
  +pw = Nat.mul(p, whi)
  %NO.sub_add(q, p, pq) : {Nat.is_le(L, Nat.add(mw, Nat.mul(_, whi))) == True{} : Bool}
  %NO.add_comm(r, p) : {Nat.is_le(L, Nat.add(mw, Nat.mul(_, whi))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(r, p), whi), Nat.add(rw, pw), NO.mul_add_l(r, p, whi)) :
    {Nat.is_le(L, Nat.add(mw, _)) == True{} : Bool}
  %NO.add_swap(rw, mw, pw) : {Nat.is_le(L, _) == True{} : Bool}
  %NO.add_assoc(rw, mw, pw) : {Nat.is_le(L, _) == True{} : Bool}
  NO.le_add_mono(Nat.mul(l, wlo), Nat.add(rw, mw), pw, pw,
    NO.le_trans(Nat.mul(l, wlo), Nat.mul(Nat.add(r, m), wlo), Nat.add(rw, mw),
      NO.le_mul_mono_l(l, Nat.add(r, m), wlo, eb_cancel_top(l, p, m, q, pq, sum)),
      NO.le_trans(Nat.mul(Nat.add(r, m), wlo), Nat.add(Nat.mul(r, wlo), mw), Nat.add(rw, mw),
        NO.le_of_eq(Nat.mul(Nat.add(r, m), wlo), Nat.add(Nat.mul(r, wlo), mw), NO.mul_add_l(r, m, wlo)),
        NO.le_add_mono(Nat.mul(r, wlo), rw, mw, mw, NO.le_mul_mono_r(wlo, whi, r, w), NO.le_refl(mw)))),
    NO.le_refl(pw))

# x wlo <= whi gives (x k) wlo <= k whi: x spare slots of the finer class weigh no more than one
# slot of the coarser class
def eb_xk(+x: Nat, +k: Nat, +wlo: Nat, +whi: Nat, hx: {Nat.is_le(Nat.mul(x, wlo), whi) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.mul(x, k), wlo), Nat.mul(k, whi)) == True{} : Bool}:
  %NO.mul_comm(k, x) : {Nat.is_le(Nat.mul(_, wlo), Nat.mul(k, whi)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.mul(k, x), wlo), Nat.mul(k, Nat.mul(x, wlo)), NO.mul_assoc(k, x, wlo)) :
    {Nat.is_le(_, Nat.mul(k, whi)) == True{} : Bool}
  NO.le_mul_mono_r(Nat.mul(x, wlo), whi, k, hx)

# ==== sigma assembly ====

# (P + K) + ((C + Z) + S) <= P + (Y2 + S2) from (C + K) + Z <= Y2 and S <= S2
def eb_tail(+P: Nat, +K: Nat, +C: Nat, +Z: Nat, +S: Nat, +Y2: Nat, +S2: Nat,
    coarse: {Nat.is_le(Nat.add(Nat.add(C, K), Z), Y2) == True{} : Bool},
    sp: {Nat.is_le(S, S2) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(P, K), Nat.add(Nat.add(C, Z), S)), Nat.add(P, Nat.add(Y2, S2))) == True{} : Bool}:
  +R = Nat.add(P, Nat.add(Y2, S2))
  %Equal.sym(Nat, Nat.add(Nat.add(P, K), Nat.add(Nat.add(C, Z), S)), Nat.add(P, Nat.add(K, Nat.add(Nat.add(C, Z), S))),
    NO.add_assoc(P, K, Nat.add(Nat.add(C, Z), S))) : {Nat.is_le(_, R) == True{} : Bool}
  %NO.add_assoc(K, Nat.add(C, Z), S) : {Nat.is_le(Nat.add(P, _), R) == True{} : Bool}
  %NO.add_swap(C, K, Z) : {Nat.is_le(Nat.add(P, Nat.add(_, S)), R) == True{} : Bool}
  %NO.add_assoc(C, K, Z) : {Nat.is_le(Nat.add(P, Nat.add(_, S)), R) == True{} : Bool}
  NO.le_add_mono(P, P, Nat.add(Nat.add(Nat.add(C, K), Z), S), Nat.add(Y2, S2), NO.le_refl(P),
    NO.le_add_mono(Nat.add(Nat.add(C, K), Z), Y2, S, S2, coarse, sp))

# sigma's right-nested sum A + (B + (C + (D + (H + S)))) from the fine, coarse and special bounds
def eb_combine(+A: Nat, +B: Nat, +C: Nat, +D: Nat, +H: Nat, +S: Nat,
    +A2: Nat, +B2: Nat, +C2: Nat, +D2: Nat, +H2: Nat, +S2: Nat, +K: Nat,
    fine: {Nat.is_le(Nat.add(A, B), Nat.add(Nat.add(A2, B2), K)) == True{} : Bool},
    coarse: {Nat.is_le(Nat.add(Nat.add(C, K), Nat.add(D, H)), Nat.add(C2, Nat.add(D2, H2))) == True{} : Bool},
    sp: {Nat.is_le(S, S2) == True{} : Bool})
  -> {Nat.is_le(Nat.add(A, Nat.add(B, Nat.add(C, Nat.add(D, Nat.add(H, S))))),
      Nat.add(A2, Nat.add(B2, Nat.add(C2, Nat.add(D2, Nat.add(H2, S2)))))) == True{} : Bool}:
  +Y = Nat.add(Nat.add(C, Nat.add(D, H)), S)
  +Y2 = Nat.add(Nat.add(C2, Nat.add(D2, H2)), S2)
  +LHS = Nat.add(A, Nat.add(B, Nat.add(C, Nat.add(D, Nat.add(H, S)))))
  +RHS = Nat.add(Nat.add(A2, B2), Y2)
  %NO.add_assoc(D2, H2, S2) : {Nat.is_le(LHS, Nat.add(A2, Nat.add(B2, Nat.add(C2, _)))) == True{} : Bool}
  %NO.add_assoc(C2, Nat.add(D2, H2), S2) : {Nat.is_le(LHS, Nat.add(A2, Nat.add(B2, _))) == True{} : Bool}
  %NO.add_assoc(A2, B2, Y2) : {Nat.is_le(LHS, _) == True{} : Bool}
  %NO.add_assoc(D, H, S) : {Nat.is_le(Nat.add(A, Nat.add(B, Nat.add(C, _))), RHS) == True{} : Bool}
  %NO.add_assoc(C, Nat.add(D, H), S) : {Nat.is_le(Nat.add(A, Nat.add(B, _)), RHS) == True{} : Bool}
  %NO.add_assoc(A, B, Y) : {Nat.is_le(_, RHS) == True{} : Bool}
  NO.le_trans(Nat.add(Nat.add(A, B), Y), Nat.add(Nat.add(Nat.add(A2, B2), K), Y), RHS,
    NO.le_add_mono(Nat.add(A, B), Nat.add(Nat.add(A2, B2), K), Y, Y, fine, NO.le_refl(Y)),
    eb_tail(Nat.add(A2, B2), K, C, Nat.add(D, H), S, Nat.add(C2, Nat.add(D2, H2)), S2, coarse, sp))

# ---- fine part (r32 / t32) ----

# eb + ea <= (sb + sa) + X gives eb + ea <= (sb + X) + sa
def eb_sum_fine(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +X: Nat,
    d5: {Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), X)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, X), sa)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(sb, X), sa), Nat.add(sb, Nat.add(X, sa)), NO.add_assoc(sb, X, sa)) :
    {Nat.is_le(Nat.add(eb, ea), _) == True{} : Bool}
  %NO.add_comm(sa, X) : {Nat.is_le(Nat.add(eb, ea), Nat.add(sb, _)) == True{} : Bool}
  %NO.add_assoc(sb, sa, X) : {Nat.is_le(Nat.add(eb, ea), _) == True{} : Bool}
  d5

def eb_fine_tail(+P: Nat, +sb: Nat, +X: Nat, +wb: Nat, +K: Nat,
    hx: {Nat.is_le(Nat.mul(X, wb), K) == True{} : Bool})
  -> {Nat.is_le(Nat.add(P, Nat.mul(Nat.add(sb, X), wb)), Nat.add(Nat.add(P, Nat.mul(sb, wb)), K)) == True{} : Bool}:
  +R = Nat.add(Nat.add(P, Nat.mul(sb, wb)), K)
  %Equal.sym(Nat, Nat.mul(Nat.add(sb, X), wb), Nat.add(Nat.mul(sb, wb), Nat.mul(X, wb)), NO.mul_add_l(sb, X, wb)) :
    {Nat.is_le(Nat.add(P, _), R) == True{} : Bool}
  %NO.add_assoc(P, Nat.mul(sb, wb), Nat.mul(X, wb)) : {Nat.is_le(_, R) == True{} : Bool}
  NO.le_add_mono(Nat.add(P, Nat.mul(sb, wb)), Nat.add(P, Nat.mul(sb, wb)), Nat.mul(X, wb), K,
    NO.le_refl(Nat.add(P, Nat.mul(sb, wb))), hx)

def eb_fine(+ea: Nat, +eb: Nat, +sa: Nat, +sb: Nat, +x: Nat, +k: Nat, +wa: Nat, +wb: Nat, +wc: Nat,
    hab: {Nat.is_le(wa, wb) == True{} : Bool}, hxc: {Nat.is_le(Nat.mul(x, wb), wc) == True{} : Bool},
    d4: {Nat.is_le(eb, Nat.add(sb, Nat.mul(x, k))) == True{} : Bool},
    d5: {Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), Nat.mul(x, k))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(ea, wa), Nat.mul(eb, wb)),
      Nat.add(Nat.add(Nat.mul(sa, wa), Nat.mul(sb, wb)), Nat.mul(k, wc))) == True{} : Bool}:
  +X = Nat.mul(x, k)
  NO.le_trans(Nat.add(Nat.mul(ea, wa), Nat.mul(eb, wb)), Nat.add(Nat.mul(sa, wa), Nat.mul(Nat.add(sb, X), wb)),
    Nat.add(Nat.add(Nat.mul(sa, wa), Nat.mul(sb, wb)), Nat.mul(k, wc)),
    eb_step(ea, eb, sa, Nat.add(sb, X), wa, wb, hab, d4, eb_sum_fine(ea, eb, sa, sb, X, d5)),
    eb_fine_tail(Nat.mul(sa, wa), sb, X, wb, Nat.mul(k, wc), eb_xk(x, k, wb, wc, hxc)))

# ---- coarse part (r16 / t16 / q8) ----

# ed + (ec + spare) == (sd + cap) + sc for spare = ((sd + sc) + cap) - (ed + ec), ed + ec <= (sd + sc) + cap
def eb_csum(+ed: Nat, +ec: Nat, +sd: Nat, +sc: Nat, +cap: Nat,
    d3: {Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), cap)) == True{} : Bool})
  -> {Nat.add(ed, Nat.add(ec, Nat.sub(Nat.add(Nat.add(sd, sc), cap), Nat.add(ed, ec)))) ==
      Nat.add(Nat.add(sd, cap), sc) : Nat}:
  +T = Nat.add(Nat.add(sd, sc), cap)
  +sp = Nat.sub(T, Nat.add(ed, ec))
  %NO.add_assoc(ed, ec, sp) : {_ == Nat.add(Nat.add(sd, cap), sc) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(sd, cap), sc), Nat.add(sd, Nat.add(cap, sc)), NO.add_assoc(sd, cap, sc)) :
    {Nat.add(Nat.add(ed, ec), sp) == _ : Nat}
  %NO.add_comm(sc, cap) : {Nat.add(Nat.add(ed, ec), sp) == Nat.add(sd, _) : Nat}
  %NO.add_assoc(sd, sc, cap) : {Nat.add(Nat.add(ed, ec), sp) == _ : Nat}
  NO.sub_add(T, Nat.add(ed, ec), d3)

# q8 tier: (x (sh - eh)) wd + eh wh <= sh wh from eh <= sh and x wd <= wh
def eb_q8(+eh: Nat, +sh: Nat, +x: Nat, +wd: Nat, +wh: Nat, d1: {Nat.is_le(eh, sh) == True{} : Bool},
    hxdh: {Nat.is_le(Nat.mul(x, wd), wh) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(Nat.mul(x, Nat.sub(sh, eh)), wd), Nat.mul(eh, wh)), Nat.mul(sh, wh)) == True{} : Bool}:
  +kq = Nat.sub(sh, eh)
  +L = Nat.add(Nat.mul(Nat.mul(x, kq), wd), Nat.mul(eh, wh))
  %NO.sub_add(sh, eh, d1) : {Nat.is_le(L, Nat.mul(_, wh)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(Nat.add(eh, kq), wh), Nat.add(Nat.mul(eh, wh), Nat.mul(kq, wh)), NO.mul_add_l(eh, kq, wh)) :
    {Nat.is_le(L, _) == True{} : Bool}
  %NO.add_comm(Nat.mul(kq, wh), Nat.mul(eh, wh)) : {Nat.is_le(L, _) == True{} : Bool}
  NO.le_add_mono(Nat.mul(Nat.mul(x, kq), wd), Nat.mul(kq, wh), Nat.mul(eh, wh), Nat.mul(eh, wh),
    eb_xk(x, kq, wd, wh, hxdh), NO.le_refl(Nat.mul(eh, wh)))

# (Cs + (sd + cap) wd) + H <= Cs + (sd wd + SH) from cap wd + H <= SH
def eb_ctail(+Cs: Nat, +sd: Nat, +cap: Nat, +wd: Nat, +H: Nat, +SH: Nat,
    hq: {Nat.is_le(Nat.add(Nat.mul(cap, wd), H), SH) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Cs, Nat.mul(Nat.add(sd, cap), wd)), H), Nat.add(Cs, Nat.add(Nat.mul(sd, wd), SH))) == True{} : Bool}:
  +R = Nat.add(Cs, Nat.add(Nat.mul(sd, wd), SH))
  +Q = Nat.mul(Nat.add(sd, cap), wd)
  %Equal.sym(Nat, Nat.add(Nat.add(Cs, Q), H), Nat.add(Cs, Nat.add(Q, H)), NO.add_assoc(Cs, Q, H)) :
    {Nat.is_le(_, R) == True{} : Bool}
  %Equal.sym(Nat, Q, Nat.add(Nat.mul(sd, wd), Nat.mul(cap, wd)), NO.mul_add_l(sd, cap, wd)) :
    {Nat.is_le(Nat.add(Cs, Nat.add(_, H)), R) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(sd, wd), Nat.mul(cap, wd)), H), Nat.add(Nat.mul(sd, wd), Nat.add(Nat.mul(cap, wd), H)),
    NO.add_assoc(Nat.mul(sd, wd), Nat.mul(cap, wd), H)) : {Nat.is_le(Nat.add(Cs, _), R) == True{} : Bool}
  NO.le_add_mono(Cs, Cs, Nat.add(Nat.mul(sd, wd), Nat.add(Nat.mul(cap, wd), H)), Nat.add(Nat.mul(sd, wd), SH),
    NO.le_refl(Cs),
    NO.le_add_mono(Nat.mul(sd, wd), Nat.mul(sd, wd), Nat.add(Nat.mul(cap, wd), H), SH, NO.le_refl(Nat.mul(sd, wd)), hq))

def eb_coarse(+ec: Nat, +ed: Nat, +eh: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +x: Nat, +wc: Nat, +wd: Nat, +wh: Nat,
    hcd: {Nat.is_le(wc, wd) == True{} : Bool}, hxdh: {Nat.is_le(Nat.mul(x, wd), wh) == True{} : Bool},
    d1: {Nat.is_le(eh, sh) == True{} : Bool},
    d2: {Nat.is_le(ed, Nat.add(sd, Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool},
    d3: {Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.mul(ec, wc),
        Nat.mul(Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec)), wc)),
        Nat.add(Nat.mul(ed, wd), Nat.mul(eh, wh))),
      Nat.add(Nat.mul(sc, wc), Nat.add(Nat.mul(sd, wd), Nat.mul(sh, wh)))) == True{} : Bool}:
  +cap = Nat.mul(x, Nat.sub(sh, eh))
  +k = Nat.sub(Nat.add(Nat.add(sd, sc), cap), Nat.add(ed, ec))
  +A = Nat.mul(Nat.add(ec, k), wc)
  +D = Nat.mul(ed, wd)
  +H = Nat.mul(eh, wh)
  +Cs = Nat.mul(sc, wc)
  +Q = Nat.mul(Nat.add(sd, cap), wd)
  +R = Nat.add(Cs, Nat.add(Nat.mul(sd, wd), Nat.mul(sh, wh)))
  %NO.mul_add_l(ec, k, wc) : {Nat.is_le(Nat.add(_, Nat.add(D, H)), R) == True{} : Bool}
  %NO.add_assoc(A, D, H) : {Nat.is_le(_, R) == True{} : Bool}
  NO.le_trans(Nat.add(Nat.add(A, D), H), Nat.add(Nat.add(Cs, Q), H), R,
    NO.le_add_mono(Nat.add(A, D), Nat.add(Cs, Q), H, H,
      eb_step(Nat.add(ec, k), ed, sc, Nat.add(sd, cap), wc, wd, hcd, d2,
        NO.le_of_eq(Nat.add(ed, Nat.add(ec, k)), Nat.add(Nat.add(sd, cap), sc), eb_csum(ed, ec, sd, sc, cap, d3))),
      NO.le_refl(H)),
    eb_ctail(Cs, sd, cap, wd, H, Nat.mul(sh, wh), eb_q8(eh, sh, x, wd, wh, d1, hxdh)))

# ---- special functions (ex2 / rcp / rsq) ----

def eb_spec(+ee: Nat, +ef: Nat, +eg: Nat, +se: Nat, +sf: Nat, +sg: Nat, +we: Nat, +wf: Nat, +wg: Nat,
    d6: {Nat.is_le(ee, se) == True{} : Bool}, d7: {Nat.is_le(ef, sf) == True{} : Bool},
    d8: {Nat.is_le(eg, sg) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(ee, we), Nat.add(Nat.mul(ef, wf), Nat.mul(eg, wg))),
      Nat.add(Nat.mul(se, we), Nat.add(Nat.mul(sf, wf), Nat.mul(sg, wg)))) == True{} : Bool}:
  NO.le_add_mono(Nat.mul(ee, we), Nat.mul(se, we), Nat.add(Nat.mul(ef, wf), Nat.mul(eg, wg)),
    Nat.add(Nat.mul(sf, wf), Nat.mul(sg, wg)), NO.le_mul_mono_l(ee, se, we, d6),
    NO.le_add_mono(Nat.mul(ef, wf), Nat.mul(sf, wf), Nat.mul(eg, wg), Nat.mul(sg, wg),
      NO.le_mul_mono_l(ef, sf, wf, d7), NO.le_mul_mono_l(eg, sg, wg, d8)))

# ==== dom: unpack and pack the eight conditions ====

# The eight conditions of Eb.dom(x, e, s) on the components of e and s, as a product.
def DomP(+x: Nat, +ea: Nat, +eb: Nat, +ec: Nat, +ed: Nat, +eh: Nat, +ee: Nat, +ef: Nat, +eg: Nat,
    +sa: Nat, +sb: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +se: Nat, +sf: Nat, +sg: Nat) -> Type:
  {Nat.is_le(eh, sh) == True{} : Bool} &
    {Nat.is_le(ed, Nat.add(sd, Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool} &
    {Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool} &
    {Nat.is_le(eb, Nat.add(sb, Nat.mul(x,
      Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))))) == True{} : Bool} &
    {Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), Nat.mul(x,
      Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))))) == True{} : Bool} &
    {Nat.is_le(ee, se) == True{} : Bool} &
    {Nat.is_le(ef, sf) == True{} : Bool} &
    {Nat.is_le(eg, sg) == True{} : Bool}

def eb_dom_parts(+x: Nat, +ea: Nat, +eb: Nat, +ec: Nat, +ed: Nat, +eh: Nat, +ee: Nat, +ef: Nat, +eg: Nat,
    +sa: Nat, +sb: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +se: Nat, +sf: Nat, +sg: Nat,
    +d: {Eb.dom(x, Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg}, Eb.Path{sa, sb, sc, sd, sh, se, sf, sg}) == True{} : Bool})
  -> DomP(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg):
  +CAP = Nat.mul(x, Nat.sub(sh, eh))
  +X = Nat.mul(x, Nat.sub(Nat.add(Nat.add(sd, sc), CAP), Nat.add(ed, ec)))
  +B1 = Nat.is_le(eh, sh)
  +B2 = Nat.is_le(ed, Nat.add(sd, CAP))
  +B3 = Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), CAP))
  +B4 = Nat.is_le(eb, Nat.add(sb, X))
  +B5 = Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), X))
  +B6 = Nat.is_le(ee, se)
  +B7 = Nat.is_le(ef, sf)
  +B8 = Nat.is_le(eg, sg)
  +R7 = Bool.and(B7, B8)
  +R6 = Bool.and(B6, R7)
  +R5 = Bool.and(B5, R6)
  +R4 = Bool.and(B4, R5)
  +R3 = Bool.and(B3, R4)
  +R2 = Bool.and(B2, R3)
  +q2 = NO.and_r(B1, R2, d)
  +q3 = NO.and_r(B2, R3, q2)
  +q4 = NO.and_r(B3, R4, q3)
  +q5 = NO.and_r(B4, R5, q4)
  +q6 = NO.and_r(B5, R6, q5)
  +q7 = NO.and_r(B6, R7, q6)
  (NO.and_l(B1, R2, d), NO.and_l(B2, R3, q2), NO.and_l(B3, R4, q3), NO.and_l(B4, R5, q4),
    NO.and_l(B5, R6, q5), NO.and_l(B6, R7, q6), NO.and_l(B7, B8, q7), NO.and_r(B7, B8, q7))

def eb_dom_mk(+x: Nat, +ea: Nat, +eb: Nat, +ec: Nat, +ed: Nat, +eh: Nat, +ee: Nat, +ef: Nat, +eg: Nat,
    +sa: Nat, +sb: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +se: Nat, +sf: Nat, +sg: Nat,
    p1: {Nat.is_le(eh, sh) == True{} : Bool},
    p2: {Nat.is_le(ed, Nat.add(sd, Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool},
    p3: {Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh)))) == True{} : Bool},
    p4: {Nat.is_le(eb, Nat.add(sb, Nat.mul(x,
      Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))))) == True{} : Bool},
    p5: {Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), Nat.mul(x,
      Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))))) == True{} : Bool},
    p6: {Nat.is_le(ee, se) == True{} : Bool},
    p7: {Nat.is_le(ef, sf) == True{} : Bool},
    p8: {Nat.is_le(eg, sg) == True{} : Bool})
  -> {Eb.dom(x, Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg}, Eb.Path{sa, sb, sc, sd, sh, se, sf, sg}) == True{} : Bool}:
  +CAP = Nat.mul(x, Nat.sub(sh, eh))
  +X = Nat.mul(x, Nat.sub(Nat.add(Nat.add(sd, sc), CAP), Nat.add(ed, ec)))
  +B1 = Nat.is_le(eh, sh)
  +B2 = Nat.is_le(ed, Nat.add(sd, CAP))
  +B3 = Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), CAP))
  +B4 = Nat.is_le(eb, Nat.add(sb, X))
  +B5 = Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), X))
  +B6 = Nat.is_le(ee, se)
  +B7 = Nat.is_le(ef, sf)
  +B8 = Nat.is_le(eg, sg)
  +R7 = Bool.and(B7, B8)
  +R6 = Bool.and(B6, R7)
  +R5 = Bool.and(B5, R6)
  +R4 = Bool.and(B4, R5)
  +R3 = Bool.and(B3, R4)
  +R2 = Bool.and(B2, R3)
  NO.and_intro(B1, R2, p1, NO.and_intro(B2, R3, p2, NO.and_intro(B3, R4, p3, NO.and_intro(B4, R5, p4,
    NO.and_intro(B5, R6, p5, NO.and_intro(B6, R7, p6, NO.and_intro(B7, B8, p7, p8)))))))

# ==== dom_sigma ====

def eb_sigma_k(+x: Nat, +wa: Nat, +wb: Nat, +wc: Nat, +wd: Nat, +wh: Nat, +we: Nat, +wf: Nat, +wg: Nat,
    +ea: Nat, +eb: Nat, +ec: Nat, +ed: Nat, +eh: Nat, +ee: Nat, +ef: Nat, +eg: Nat,
    +sa: Nat, +sb: Nat, +sc: Nat, +sd: Nat, +sh: Nat, +se: Nat, +sf: Nat, +sg: Nat,
    dp: DomP(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg),
    ord: {Eb.order(x, Eb.W{wa, wb, wc, wd, wh, we, wf, wg}) == True{} : Bool})
  -> {Nat.is_le(Eb.sigma(Eb.W{wa, wb, wc, wd, wh, we, wf, wg}, Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg}),
      Eb.sigma(Eb.W{wa, wb, wc, wd, wh, we, wf, wg}, Eb.Path{sa, sb, sc, sd, sh, se, sf, sg})) == True{} : Bool}:
  (d1, d2, d3, d4, d5, d6, d7, d8) = dp
  +O1 = Nat.is_le(wa, wb)
  +O2 = Nat.is_le(Nat.mul(x, wb), wc)
  +O3 = Nat.is_le(wc, wd)
  +O4 = Nat.is_le(Nat.mul(x, wd), wh)
  +o = ord
  +o2 = NO.and_r(O1, Bool.and(O2, Bool.and(O3, O4)), o)
  +o3 = NO.and_r(O2, Bool.and(O3, O4), o2)
  +k = Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))
  eb_combine(Nat.mul(ea, wa), Nat.mul(eb, wb), Nat.mul(ec, wc), Nat.mul(ed, wd), Nat.mul(eh, wh),
    Nat.add(Nat.mul(ee, we), Nat.add(Nat.mul(ef, wf), Nat.mul(eg, wg))),
    Nat.mul(sa, wa), Nat.mul(sb, wb), Nat.mul(sc, wc), Nat.mul(sd, wd), Nat.mul(sh, wh),
    Nat.add(Nat.mul(se, we), Nat.add(Nat.mul(sf, wf), Nat.mul(sg, wg))), Nat.mul(k, wc),
    eb_fine(ea, eb, sa, sb, x, k, wa, wb, wc, NO.and_l(O1, Bool.and(O2, Bool.and(O3, O4)), o),
      NO.and_l(O2, Bool.and(O3, O4), o2), d4, d5),
    eb_coarse(ec, ed, eh, sc, sd, sh, x, wc, wd, wh, NO.and_l(O3, O4, o3), NO.and_r(O3, O4, o3), d1, d2, d3),
    eb_spec(ee, ef, eg, se, sf, sg, we, wf, wg, d6, d7, d8))

def Laws.dom_sigma(x, w, e, s, ord, d):
  match w e s:
    case Eb.W{wa, wb, wc, wd, wh, we, wf, wg} Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg} Eb.Path{sa, sb, sc, sd, sh, se, sf, sg}:
      eb_sigma_k(x, wa, wb, wc, wd, wh, we, wf, wg, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg,
        eb_dom_parts(x, ea, eb, ec, ed, eh, ee, ef, eg, sa, sb, sc, sd, sh, se, sf, sg, d), ord)

# ==== sigma_add ====

# (a + b) w + R == (a w + R1) + (b w + R2) when R == R1 + R2
def eb_lin(+a: Nat, +b: Nat, +w: Nat, +R: Nat, +R1: Nat, +R2: Nat, h: {R == Nat.add(R1, R2) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(a, b), w), R) == Nat.add(Nat.add(Nat.mul(a, w), R1), Nat.add(Nat.mul(b, w), R2)) : Nat}:
  +RHS = Nat.add(Nat.add(Nat.mul(a, w), R1), Nat.add(Nat.mul(b, w), R2))
  %Equal.sym(Nat, R, Nat.add(R1, R2), h) : {Nat.add(Nat.mul(Nat.add(a, b), w), _) == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(a, b), w), Nat.add(Nat.mul(a, w), Nat.mul(b, w)), NO.mul_add_l(a, b, w)) :
    {Nat.add(_, Nat.add(R1, R2)) == RHS : Nat}
  NO.add_swap4(Nat.mul(a, w), Nat.mul(b, w), R1, R2)

def Laws.sigma_add(w, p, q):
  match w p q:
    case Eb.W{w1, w2, w3, w4, w5, w6, w7, w8} Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} Eb.Path{b1, b2, b3, b4, b5, b6, b7, b8}:
      +L8 = Nat.mul(Nat.add(a8, b8), w8)
      +P8 = Nat.mul(a8, w8)
      +Q8 = Nat.mul(b8, w8)
      +L7 = Nat.add(Nat.mul(Nat.add(a7, b7), w7), L8)
      +P7 = Nat.add(Nat.mul(a7, w7), P8)
      +Q7 = Nat.add(Nat.mul(b7, w7), Q8)
      +L6 = Nat.add(Nat.mul(Nat.add(a6, b6), w6), L7)
      +P6 = Nat.add(Nat.mul(a6, w6), P7)
      +Q6 = Nat.add(Nat.mul(b6, w6), Q7)
      +L5 = Nat.add(Nat.mul(Nat.add(a5, b5), w5), L6)
      +P5 = Nat.add(Nat.mul(a5, w5), P6)
      +Q5 = Nat.add(Nat.mul(b5, w5), Q6)
      +L4 = Nat.add(Nat.mul(Nat.add(a4, b4), w4), L5)
      +P4 = Nat.add(Nat.mul(a4, w4), P5)
      +Q4 = Nat.add(Nat.mul(b4, w4), Q5)
      +L3 = Nat.add(Nat.mul(Nat.add(a3, b3), w3), L4)
      +P3 = Nat.add(Nat.mul(a3, w3), P4)
      +Q3 = Nat.add(Nat.mul(b3, w3), Q4)
      +L2 = Nat.add(Nat.mul(Nat.add(a2, b2), w2), L3)
      +P2 = Nat.add(Nat.mul(a2, w2), P3)
      +Q2 = Nat.add(Nat.mul(b2, w2), Q3)
      +h8 = NO.mul_add_l(a8, b8, w8)
      +h7 = eb_lin(a7, b7, w7, L8, P8, Q8, h8)
      +h6 = eb_lin(a6, b6, w6, L7, P7, Q7, h7)
      +h5 = eb_lin(a5, b5, w5, L6, P6, Q6, h6)
      +h4 = eb_lin(a4, b4, w4, L5, P5, Q5, h5)
      +h3 = eb_lin(a3, b3, w3, L4, P4, Q4, h4)
      +h2 = eb_lin(a2, b2, w2, L3, P3, Q3, h3)
      eb_lin(a1, b1, w1, L2, P2, Q2, h2)

# ==== dom_refl ====

def Laws.dom_refl(x, p):
  match p:
    case Eb.Path{a, b, c, d, h, e, f, g}:
      +CAP = Nat.mul(x, Nat.sub(h, h))
      +X = Nat.mul(x, Nat.sub(Nat.add(Nat.add(d, c), CAP), Nat.add(d, c)))
      eb_dom_mk(x, a, b, c, d, h, e, f, g, a, b, c, d, h, e, f, g,
        NO.le_refl(h), NO.le_add_r(d, CAP), NO.le_add_r(Nat.add(d, c), CAP), NO.le_add_r(b, X),
        NO.le_add_r(Nat.add(b, a), X), NO.le_refl(e), NO.le_refl(f), NO.le_refl(g))

# ==== dom_trans ====

# a <= b + u and b <= c + v give a <= c + (v + u)
def eb_shift(+a: Nat, +b: Nat, +c: Nat, +u: Nat, +v: Nat,
    h1: {Nat.is_le(a, Nat.add(b, u)) == True{} : Bool}, h2: {Nat.is_le(b, Nat.add(c, v)) == True{} : Bool})
  -> {Nat.is_le(a, Nat.add(c, Nat.add(v, u))) == True{} : Bool}:
  %NO.add_assoc(c, v, u) : {Nat.is_le(a, _) == True{} : Bool}
  NO.le_trans(a, Nat.add(b, u), Nat.add(Nat.add(c, v), u), h1,
    NO.le_add_mono(b, Nat.add(c, v), u, u, h2, NO.le_refl(u)))

# a2 <= b2 + x k1 and b2 <= c2 + x k2 give a2 <= c2 + x K when K == k2 + k1
def eb_spare_trans(+a2: Nat, +b2: Nat, +c2: Nat, +x: Nat, +K: Nat, +k1: Nat, +k2: Nat,
    ek: {K == Nat.add(k2, k1) : Nat},
    h1: {Nat.is_le(a2, Nat.add(b2, Nat.mul(x, k1))) == True{} : Bool},
    h2: {Nat.is_le(b2, Nat.add(c2, Nat.mul(x, k2))) == True{} : Bool})
  -> {Nat.is_le(a2, Nat.add(c2, Nat.mul(x, K))) == True{} : Bool}:
  %Equal.sym(Nat, K, Nat.add(k2, k1), ek) : {Nat.is_le(a2, Nat.add(c2, Nat.mul(x, _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(k2, k1)), Nat.add(Nat.mul(x, k2), Nat.mul(x, k1)), NO.mul_add_r(x, k2, k1)) :
    {Nat.is_le(a2, Nat.add(c2, _)) == True{} : Bool}
  eb_shift(a2, b2, c2, Nat.mul(x, k1), Nat.mul(x, k2), h1, h2)

# leftover capacities chain exactly: (C + (v + u)) - A == ((B + u) - A) + ((C + v) - B)
def eb_spare_chain(+A: Nat, +B: Nat, +C: Nat, +u: Nat, +v: Nat,
    h1: {Nat.is_le(A, Nat.add(B, u)) == True{} : Bool}, h2: {Nat.is_le(B, Nat.add(C, v)) == True{} : Bool})
  -> {Nat.sub(Nat.add(C, Nat.add(v, u)), A) == Nat.add(Nat.sub(Nat.add(B, u), A), Nat.sub(Nat.add(C, v), B)) : Nat}:
  +s1 = Nat.sub(Nat.add(B, u), A)
  +s2 = Nat.sub(Nat.add(C, v), B)
  +RHS = Nat.add(s1, s2)
  %NO.add_assoc(C, v, u) : {Nat.sub(_, A) == RHS : Nat}
  %NO.sub_add(Nat.add(C, v), B, h2) : {Nat.sub(Nat.add(_, u), A) == RHS : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(B, s2), u), Nat.add(B, Nat.add(s2, u)), NO.add_assoc(B, s2, u)) :
    {Nat.sub(_, A) == RHS : Nat}
  %NO.add_comm(u, s2) : {Nat.sub(Nat.add(B, _), A) == RHS : Nat}
  %NO.add_assoc(B, u, s2) : {Nat.sub(_, A) == RHS : Nat}
  %NO.sub_add(Nat.add(B, u), A, h1) : {Nat.sub(Nat.add(_, s2), A) == RHS : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(A, s1), s2), Nat.add(A, Nat.add(s1, s2)), NO.add_assoc(A, s1, s2)) :
    {Nat.sub(_, A) == RHS : Nat}
  NO.add_sub(A, Nat.add(s1, s2))

# the r32 / t32 spare of a chain a -> b -> c is the sum of the spares of its links
def eb_sp_eq(+x: Nat, +a5: Nat, +b5: Nat, +c5: Nat, +EA: Nat, +EB: Nat, +EC: Nat,
    h51: {Nat.is_le(a5, b5) == True{} : Bool}, h52: {Nat.is_le(b5, c5) == True{} : Bool},
    h3a: {Nat.is_le(EA, Nat.add(EB, Nat.mul(x, Nat.sub(b5, a5)))) == True{} : Bool},
    h3b: {Nat.is_le(EB, Nat.add(EC, Nat.mul(x, Nat.sub(c5, b5)))) == True{} : Bool})
  -> {Nat.sub(Nat.add(EC, Nat.mul(x, Nat.sub(c5, a5))), EA) ==
      Nat.add(Nat.sub(Nat.add(EC, Nat.mul(x, Nat.sub(c5, b5))), EB),
        Nat.sub(Nat.add(EB, Nat.mul(x, Nat.sub(b5, a5))), EA)) : Nat}:
  +k1 = Nat.sub(b5, a5)
  +k2 = Nat.sub(c5, b5)
  +u = Nat.mul(x, k1)
  +v = Nat.mul(x, k2)
  +s1 = Nat.sub(Nat.add(EB, u), EA)
  +s2 = Nat.sub(Nat.add(EC, v), EB)
  %Equal.sym(Nat, Nat.sub(c5, a5), Nat.add(k2, k1), NO.sub_chain(a5, b5, c5, h51, h52)) :
    {Nat.sub(Nat.add(EC, Nat.mul(x, _)), EA) == Nat.add(s2, s1) : Nat}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(k2, k1)), Nat.add(v, u), NO.mul_add_r(x, k2, k1)) :
    {Nat.sub(Nat.add(EC, _), EA) == Nat.add(s2, s1) : Nat}
  %NO.add_comm(s1, s2) : {Nat.sub(Nat.add(EC, Nat.add(v, u)), EA) == _ : Nat}
  eb_spare_chain(EA, EB, EC, u, v, h3a, h3b)

def eb_trans_k(+x: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat, +a5: Nat, +a6: Nat, +a7: Nat, +a8: Nat,
    +b1: Nat, +b2: Nat, +b3: Nat, +b4: Nat, +b5: Nat, +b6: Nat, +b7: Nat, +b8: Nat,
    +c1: Nat, +c2: Nat, +c3: Nat, +c4: Nat, +c5: Nat, +c6: Nat, +c7: Nat, +c8: Nat,
    pa: DomP(x, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8),
    pb: DomP(x, b1, b2, b3, b4, b5, b6, b7, b8, c1, c2, c3, c4, c5, c6, c7, c8))
  -> {Eb.dom(x, Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8}, Eb.Path{c1, c2, c3, c4, c5, c6, c7, c8}) == True{} : Bool}:
  (p1, p2, p3, p4, p5, p6, p7, p8) = pa
  (q1, q2, q3, q4, q5, q6, q7, q8) = pb
  +P1 = p1
  +Q1 = q1
  +P3 = p3
  +Q3 = q3
  +EA = Nat.add(a4, a3)
  +EB = Nat.add(b4, b3)
  +EC = Nat.add(c4, c3)
  +kq = NO.sub_chain(a5, b5, c5, P1, Q1)
  +SPab = Nat.sub(Nat.add(EB, Nat.mul(x, Nat.sub(b5, a5))), EA)
  +SPbc = Nat.sub(Nat.add(EC, Nat.mul(x, Nat.sub(c5, b5))), EB)
  +SPac = Nat.sub(Nat.add(EC, Nat.mul(x, Nat.sub(c5, a5))), EA)
  +esp = eb_sp_eq(x, a5, b5, c5, EA, EB, EC, P1, Q1, P3, Q3)
  eb_dom_mk(x, a1, a2, a3, a4, a5, a6, a7, a8, c1, c2, c3, c4, c5, c6, c7, c8,
    NO.le_trans(a5, b5, c5, P1, Q1),
    eb_spare_trans(a4, b4, c4, x, Nat.sub(c5, a5), Nat.sub(b5, a5), Nat.sub(c5, b5), kq, p2, q2),
    eb_spare_trans(EA, EB, EC, x, Nat.sub(c5, a5), Nat.sub(b5, a5), Nat.sub(c5, b5), kq, P3, Q3),
    eb_spare_trans(a2, b2, c2, x, SPac, SPab, SPbc, esp, p4, q4),
    eb_spare_trans(Nat.add(a2, a1), Nat.add(b2, b1), Nat.add(c2, c1), x, SPac, SPab, SPbc, esp, p5, q5),
    NO.le_trans(a6, b6, c6, p6, q6), NO.le_trans(a7, b7, c7, p7, q7), NO.le_trans(a8, b8, c8, p8, q8))

def Laws.dom_trans(x, a, b, c, ab, bc):
  match a b c:
    case Eb.Path{a1, a2, a3, a4, a5, a6, a7, a8} Eb.Path{b1, b2, b3, b4, b5, b6, b7, b8} Eb.Path{c1, c2, c3, c4, c5, c6, c7, c8}:
      eb_trans_k(x, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8, c1, c2, c3, c4, c5, c6, c7, c8,
        eb_dom_parts(x, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8, ab),
        eb_dom_parts(x, b1, b2, b3, b4, b5, b6, b7, b8, c1, c2, c3, c4, c5, c6, c7, c8, bc))

# ==== dom_add ====

# a <= b + x k1 and a2 <= b2 + x k2 give a + a2 <= (b + b2) + x K when K == k1 + k2
def eb_d4_add(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, +x: Nat, +K: Nat, +k1: Nat, +k2: Nat,
    ek: {K == Nat.add(k1, k2) : Nat},
    h1: {Nat.is_le(a, Nat.add(b, Nat.mul(x, k1))) == True{} : Bool},
    h2: {Nat.is_le(a2, Nat.add(b2, Nat.mul(x, k2))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, a2), Nat.add(Nat.add(b, b2), Nat.mul(x, K))) == True{} : Bool}:
  %Equal.sym(Nat, K, Nat.add(k1, k2), ek) :
    {Nat.is_le(Nat.add(a, a2), Nat.add(Nat.add(b, b2), Nat.mul(x, _))) == True{} : Bool}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(k1, k2)), Nat.add(Nat.mul(x, k1), Nat.mul(x, k2)), NO.mul_add_r(x, k1, k2)) :
    {Nat.is_le(Nat.add(a, a2), Nat.add(Nat.add(b, b2), _)) == True{} : Bool}
  %NO.add_swap4(b, Nat.mul(x, k1), b2, Nat.mul(x, k2)) : {Nat.is_le(Nat.add(a, a2), _) == True{} : Bool}
  NO.le_add_mono(a, Nat.add(b, Nat.mul(x, k1)), a2, Nat.add(b2, Nat.mul(x, k2)), h1, h2)

# the two-class form of eb_d4_add (suffix sums of a concatenation)
def eb_d5_add(+pb: Nat, +pa: Nat, +ub: Nat, +ua: Nat, +qb: Nat, +qa: Nat, +vb: Nat, +va: Nat,
    +x: Nat, +K: Nat, +k1: Nat, +k2: Nat, ek: {K == Nat.add(k1, k2) : Nat},
    h1: {Nat.is_le(Nat.add(pb, pa), Nat.add(Nat.add(qb, qa), Nat.mul(x, k1))) == True{} : Bool},
    h2: {Nat.is_le(Nat.add(ub, ua), Nat.add(Nat.add(vb, va), Nat.mul(x, k2))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(pb, ub), Nat.add(pa, ua)),
      Nat.add(Nat.add(Nat.add(qb, vb), Nat.add(qa, va)), Nat.mul(x, K))) == True{} : Bool}:
  %NO.add_swap4(pb, pa, ub, ua) :
    {Nat.is_le(_, Nat.add(Nat.add(Nat.add(qb, vb), Nat.add(qa, va)), Nat.mul(x, K))) == True{} : Bool}
  %NO.add_swap4(qb, qa, vb, va) :
    {Nat.is_le(Nat.add(Nat.add(pb, pa), Nat.add(ub, ua)), Nat.add(_, Nat.mul(x, K))) == True{} : Bool}
  eb_d4_add(Nat.add(pb, pa), Nat.add(ub, ua), Nat.add(qb, qa), Nat.add(vb, va), x, K, k1, k2, ek, h1, h2)

# the r32 / t32 spare of a concatenation is the sum of the segments' spares
def eb_sp_add(+x: Nat, +p4: Nat, +p3: Nat, +u4: Nat, +u3: Nat, +q4: Nat, +q3: Nat, +v4: Nat, +v3: Nat,
    +Kq: Nat, +kq1: Nat, +kq2: Nat, ekq: {Kq == Nat.add(kq1, kq2) : Nat},
    f3: {Nat.is_le(Nat.add(p4, p3), Nat.add(Nat.add(q4, q3), Nat.mul(x, kq1))) == True{} : Bool},
    g3: {Nat.is_le(Nat.add(u4, u3), Nat.add(Nat.add(v4, v3), Nat.mul(x, kq2))) == True{} : Bool})
  -> {Nat.sub(Nat.add(Nat.add(Nat.add(q4, v4), Nat.add(q3, v3)), Nat.mul(x, Kq)), Nat.add(Nat.add(p4, u4), Nat.add(p3, u3))) ==
      Nat.add(Nat.sub(Nat.add(Nat.add(q4, q3), Nat.mul(x, kq1)), Nat.add(p4, p3)),
        Nat.sub(Nat.add(Nat.add(v4, v3), Nat.mul(x, kq2)), Nat.add(u4, u3))) : Nat}:
  +Q = Nat.add(q4, q3)
  +V = Nat.add(v4, v3)
  +X1 = Nat.mul(x, kq1)
  +X2 = Nat.mul(x, kq2)
  +Pc = Nat.add(Nat.add(p4, u4), Nat.add(p3, u3))
  +RHS = Nat.add(Nat.sub(Nat.add(Q, X1), Nat.add(p4, p3)), Nat.sub(Nat.add(V, X2), Nat.add(u4, u3)))
  %Equal.sym(Nat, Kq, Nat.add(kq1, kq2), ekq) :
    {Nat.sub(Nat.add(Nat.add(Nat.add(q4, v4), Nat.add(q3, v3)), Nat.mul(x, _)), Pc) == RHS : Nat}
  %Equal.sym(Nat, Nat.mul(x, Nat.add(kq1, kq2)), Nat.add(X1, X2), NO.mul_add_r(x, kq1, kq2)) :
    {Nat.sub(Nat.add(Nat.add(Nat.add(q4, v4), Nat.add(q3, v3)), _), Pc) == RHS : Nat}
  %NO.add_swap4(q4, q3, v4, v3) : {Nat.sub(Nat.add(_, Nat.add(X1, X2)), Pc) == RHS : Nat}
  %NO.add_swap4(Q, X1, V, X2) : {Nat.sub(_, Pc) == RHS : Nat}
  %NO.add_swap4(p4, p3, u4, u3) : {Nat.sub(Nat.add(Nat.add(Q, X1), Nat.add(V, X2)), _) == RHS : Nat}
  NO.sub_add_add(Nat.add(Q, X1), Nat.add(V, X2), Nat.add(p4, p3), Nat.add(u4, u3), f3, g3)

def eb_add_k(+x: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat, +p5: Nat, +p6: Nat, +p7: Nat, +p8: Nat,
    +q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat, +q8: Nat,
    +u1: Nat, +u2: Nat, +u3: Nat, +u4: Nat, +u5: Nat, +u6: Nat, +u7: Nat, +u8: Nat,
    +v1: Nat, +v2: Nat, +v3: Nat, +v4: Nat, +v5: Nat, +v6: Nat, +v7: Nat, +v8: Nat,
    pa: DomP(x, p1, p2, p3, p4, p5, p6, p7, p8, q1, q2, q3, q4, q5, q6, q7, q8),
    pb: DomP(x, u1, u2, u3, u4, u5, u6, u7, u8, v1, v2, v3, v4, v5, v6, v7, v8))
  -> {Eb.dom(x, Eb.add(Eb.Path{p1, p2, p3, p4, p5, p6, p7, p8}, Eb.Path{u1, u2, u3, u4, u5, u6, u7, u8}),
      Eb.add(Eb.Path{q1, q2, q3, q4, q5, q6, q7, q8}, Eb.Path{v1, v2, v3, v4, v5, v6, v7, v8})) == True{} : Bool}:
  (f1, f2, f3, f4, f5, f6, f7, f8) = pa
  (g1, g2, g3, g4, g5, g6, g7, g8) = pb
  +F1 = f1
  +G1 = g1
  +F3 = f3
  +G3 = g3
  +Kq = Nat.sub(Nat.add(q5, v5), Nat.add(p5, u5))
  +kq1 = Nat.sub(q5, p5)
  +kq2 = Nat.sub(v5, u5)
  +ekq = NO.sub_add_add(q5, v5, p5, u5, F1, G1)
  +SP = Nat.sub(Nat.add(Nat.add(Nat.add(q4, v4), Nat.add(q3, v3)), Nat.mul(x, Kq)), Nat.add(Nat.add(p4, u4), Nat.add(p3, u3)))
  +sp1 = Nat.sub(Nat.add(Nat.add(q4, q3), Nat.mul(x, kq1)), Nat.add(p4, p3))
  +sp2 = Nat.sub(Nat.add(Nat.add(v4, v3), Nat.mul(x, kq2)), Nat.add(u4, u3))
  +esp = eb_sp_add(x, p4, p3, u4, u3, q4, q3, v4, v3, Kq, kq1, kq2, ekq, F3, G3)
  eb_dom_mk(x, Nat.add(p1, u1), Nat.add(p2, u2), Nat.add(p3, u3), Nat.add(p4, u4), Nat.add(p5, u5),
    Nat.add(p6, u6), Nat.add(p7, u7), Nat.add(p8, u8),
    Nat.add(q1, v1), Nat.add(q2, v2), Nat.add(q3, v3), Nat.add(q4, v4), Nat.add(q5, v5),
    Nat.add(q6, v6), Nat.add(q7, v7), Nat.add(q8, v8),
    NO.le_add_mono(p5, q5, u5, v5, F1, G1),
    eb_d4_add(p4, u4, q4, v4, x, Kq, kq1, kq2, ekq, f2, g2),
    eb_d5_add(p4, p3, u4, u3, q4, q3, v4, v3, x, Kq, kq1, kq2, ekq, F3, G3),
    eb_d4_add(p2, u2, q2, v2, x, SP, sp1, sp2, esp, f4, g4),
    eb_d5_add(p2, p1, u2, u1, q2, q1, v2, v1, x, SP, sp1, sp2, esp, f5, g5),
    NO.le_add_mono(p6, q6, u6, v6, f6, g6), NO.le_add_mono(p7, q7, u7, v7, f7, g7),
    NO.le_add_mono(p8, q8, u8, v8, f8, g8))

def Laws.dom_add(x, e1, s1, e2, s2, d1, d2):
  match e1 s1 e2 s2:
    case Eb.Path{p1, p2, p3, p4, p5, p6, p7, p8} Eb.Path{q1, q2, q3, q4, q5, q6, q7, q8} Eb.Path{u1, u2, u3, u4, u5, u6, u7, u8} Eb.Path{v1, v2, v3, v4, v5, v6, v7, v8}:
      eb_add_k(x, p1, p2, p3, p4, p5, p6, p7, p8, q1, q2, q3, q4, q5, q6, q7, q8,
        u1, u2, u3, u4, u5, u6, u7, u8, v1, v2, v3, v4, v5, v6, v7, v8,
        eb_dom_parts(x, p1, p2, p3, p4, p5, p6, p7, p8, q1, q2, q3, q4, q5, q6, q7, q8, d1),
        eb_dom_parts(x, u1, u2, u3, u4, u5, u6, u7, u8, v1, v2, v3, v4, v5, v6, v7, v8, d2))
