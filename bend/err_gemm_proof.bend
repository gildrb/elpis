# Proofs of bend/err_gemm_laws.bend. No @unsafe definitions, axioms, holes or foreign code; every def
# precedes its uses. Generic Nat facts come from bend/nat_order_laws.bend, the vocabulary's dom_refl
# from bend/err_bound_laws.bend, lm_head's row independence from bend/lmhead_laws.bend (each with its
# proof module in scope).
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as EBL
import ./err_bound_proof.bend as EBP
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./err_gemm.bend as E
import ./err_gemm_laws.bend as Laws
import ./lmhead.bend as LH
import ./lmhead_laws.bend as LHL
import ./lmhead_proof.bend as LHP
import ./gemm_m16_wpart.bend as Wp
import ./tail_m16_sched.bend as TS
import ./mlp_m16_sched.bend as Mlp
import ./gemm_m16_wpart_laws.bend as WL
import ./gemm_m16_wpart_proof.bend as WP
import ./err_gemm_runs.bend as R
import ./err_gemm_runs_laws.bend as RL
import ./err_gemm_runs_proof.bend as RLP
import ./precision_elpis.bend as PE
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec

# ==== a sufficient condition for Eb.dom with symbolic fine (r32 / t32) counts ====
# Eb.dom's conjuncts split into the coarse tiers and special functions (g_coarse, closed numbers in
# every use below) and the two fine conjuncts, which only need: the fine total of e is at most B,
# B <= x * k, and k is at most dom's leftover coarse capacity (g_spare). So no use ever normalizes
# x * spare.

def g_coarse(+x: Nat, e: Eb.Path, s: Eb.Path) -> Bool:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Eb.Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          Bool.and(Nat.is_le(eh, sh),
            Bool.and(Nat.is_le(ed, Nat.add(sd, Nat.mul(x, Nat.sub(sh, eh)))),
              Bool.and(Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh)))),
                Bool.and(Nat.is_le(ee, se), Bool.and(Nat.is_le(ef, sf), Nat.is_le(eg, sg))))))

def g_spare(+x: Nat, e: Eb.Path, s: Eb.Path) -> Nat:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Eb.Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))

# t32 + r32, in dom's order.
def g_fine(e: Eb.Path) -> Nat:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      Nat.add(eb, ea)

def g_t32(e: Eb.Path) -> Nat:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      eb

def g_r32(e: Eb.Path) -> Nat:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      ea

# Reassemble dom from its eight conjuncts.
def dom_parts(+x: Nat, e: Eb.Path, s: Eb.Path, +hc: {g_coarse(x, e, s) == True{} : Bool},
    +h4: {Nat.is_le(g_t32(e), Nat.add(g_t32(s), Nat.mul(x, g_spare(x, e, s)))) == True{} : Bool},
    +h5: {Nat.is_le(g_fine(e), Nat.add(g_fine(s), Nat.mul(x, g_spare(x, e, s)))) == True{} : Bool})
  -> {Eb.dom(x, e, s) == True{} : Bool}:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Eb.Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          +capc = Nat.mul(x, Nat.sub(sh, eh))
          +SP = Nat.sub(Nat.add(Nat.add(sd, sc), capc), Nat.add(ed, ec))
          +C1 = Nat.is_le(eh, sh)
          +C2 = Nat.is_le(ed, Nat.add(sd, capc))
          +C3 = Nat.is_le(Nat.add(ed, ec), Nat.add(Nat.add(sd, sc), capc))
          +C4 = Nat.is_le(eb, Nat.add(sb, Nat.mul(x, SP)))
          +C5 = Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), Nat.mul(x, SP)))
          +C6 = Nat.is_le(ee, se)
          +C7 = Nat.is_le(ef, sf)
          +C8 = Nat.is_le(eg, sg)
          +R3 = Bool.and(C6, Bool.and(C7, C8))
          +R2 = Bool.and(C3, R3)
          +R1 = Bool.and(C2, R2)
          +r1 = NO.and_r(C1, R1, hc)
          +r2 = NO.and_r(C2, R2, r1)
          +r3 = NO.and_r(C3, R3, r2)
          +r6 = NO.and_r(C6, Bool.and(C7, C8), r3)
          NO.and_intro(C1, Bool.and(C2, Bool.and(C3, Bool.and(C4, Bool.and(C5, R3)))), NO.and_l(C1, R1, hc),
            NO.and_intro(C2, Bool.and(C3, Bool.and(C4, Bool.and(C5, R3))), NO.and_l(C2, R2, r1),
              NO.and_intro(C3, Bool.and(C4, Bool.and(C5, R3)), NO.and_l(C3, R3, r2),
                NO.and_intro(C4, Bool.and(C5, R3), h4,
                  NO.and_intro(C5, R3, h5,
                    NO.and_intro(C6, Bool.and(C7, C8), NO.and_l(C6, Bool.and(C7, C8), r3),
                      NO.and_intro(C7, C8, NO.and_l(C7, C8, r6), NO.and_r(C7, C8, r6))))))))

# Coarse tiers hold, e's fine total is at most B <= x * k and k <= spare: dom.
def dom_budget(+x: Nat, +k: Nat, +B: Nat, e: Eb.Path, s: Eb.Path, +hc: {g_coarse(x, e, s) == True{} : Bool},
    +hb: {Nat.is_le(g_fine(e), B) == True{} : Bool}, +hk: {Nat.is_le(B, Nat.mul(x, k)) == True{} : Bool},
    +hs: {Nat.is_le(k, g_spare(x, e, s)) == True{} : Bool})
  -> {Eb.dom(x, e, s) == True{} : Bool}:
  match e:
    case Eb.Path{+ea, +eb, +ec, +ed, +eh, +ee, +ef, +eg}:
      match s:
        case Eb.Path{+sa, +sb, +sc, +sd, +sh, +se, +sf, +sg}:
          +SPv = Nat.sub(Nat.add(Nat.add(sd, sc), Nat.mul(x, Nat.sub(sh, eh))), Nat.add(ed, ec))
          +hf = NO.le_trans(Nat.add(eb, ea), B, Nat.mul(x, SPv), hb,
            NO.le_trans(B, Nat.mul(x, k), Nat.mul(x, SPv), hk, NO.le_mul_mono_r(k, SPv, x, hs)))
          dom_parts(x, Eb.Path{ea, eb, ec, ed, eh, ee, ef, eg}, Eb.Path{sa, sb, sc, sd, sh, se, sf, sg}, hc,
            NO.le_trans(eb, Nat.add(eb, ea), Nat.add(sb, Nat.mul(x, SPv)), NO.le_add_r(eb, ea),
              NO.le_trans(Nat.add(eb, ea), Nat.mul(x, SPv), Nat.add(sb, Nat.mul(x, SPv)), hf,
                NO.le_add_l(sb, Nat.mul(x, SPv)))),
            NO.le_trans(Nat.add(eb, ea), Nat.mul(x, SPv), Nat.add(Nat.add(sb, sa), Nat.mul(x, SPv)), hf,
              NO.le_add_l(Nat.add(sb, sa), Nat.mul(x, SPv))))

# Coarse tiers hold and e's fine counts are at most s's (no exchange needed): dom.
def dom_le(+x: Nat, +e: Eb.Path, +s: Eb.Path, +hc: {g_coarse(x, e, s) == True{} : Bool},
    +h4: {Nat.is_le(g_t32(e), g_t32(s)) == True{} : Bool}, +hf: {Nat.is_le(g_fine(e), g_fine(s)) == True{} : Bool})
  -> {Eb.dom(x, e, s) == True{} : Bool}:
  +SP = g_spare(x, e, s)
  dom_parts(x, e, s, hc,
    NO.le_trans(g_t32(e), g_t32(s), Nat.add(g_t32(s), Nat.mul(x, SP)), h4, NO.le_add_r(g_t32(s), Nat.mul(x, SP))),
    NO.le_trans(g_fine(e), g_fine(s), Nat.add(g_fine(s), Nat.mul(x, SP)), hf, NO.le_add_r(g_fine(s), Nat.mul(x, SP))))

# ==== the m16 leaves ====

def m16_vb(+op: E.Op) -> Nat:
  Nat.add(1n, Nat.add(E.op_kt(op), E.op_grid(op)))

def m16_bnd(+op: E.Op, +tr: Nat) -> Nat:
  Nat.add(Nat.add(g_t32(E.m16_const(op, tr)), 0n), Nat.add(g_r32(E.m16_const(op, tr)), m16_vb(op)))

# A constant path plus V fine steps, V <= Vb.
def fine_add(+C: Eb.Path, +V: Nat, +Vb: Nat, +hv: {Nat.is_le(V, Vb) == True{} : Bool})
  -> {Nat.is_le(g_fine(Eb.add(C, E.seg(V, 0n, 0n))), Nat.add(Nat.add(g_t32(C), 0n), Nat.add(g_r32(C), Vb))) == True{} : Bool}:
  match C:
    case Eb.Path{+a, +b, +c, +d, +h, +e1, +f1, +g1}:
      NO.le_add_mono(Nat.add(b, 0n), Nat.add(b, 0n), Nat.add(a, V), Nat.add(a, Vb), NO.le_refl(Nat.add(b, 0n)),
        NO.le_add_mono(a, a, V, Vb, NO.le_refl(a), hv))

# The fine total of an m16 leaf from its coordinate bounds.
def m16_fine(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool})
  -> {Nat.is_le(g_fine(E.m16_path(op, tr, own, fa, pa)), m16_bnd(op, tr)) == True{} : Bool}:
  +L1 = Nat.is_le(1n, tr)
  +L2 = Nat.is_le(tr, E.fo())
  +L3 = Nat.is_le(own, 1n)
  +L4 = Nat.is_le(fa, E.op_kt(op))
  +L5 = Nat.is_le(1n+pa, E.op_grid(op))
  +q1 = NO.and_r(L1, Bool.and(L2, Bool.and(L3, Bool.and(L4, L5))), leaf)
  +q2 = NO.and_r(L2, Bool.and(L3, Bool.and(L4, L5)), q1)
  +q3 = NO.and_r(L3, Bool.and(L4, L5), q2)
  +hpa = NO.le_trans(pa, 1n+pa, E.op_grid(op), NO.le_succ(pa), NO.and_r(L4, L5, q3))
  +hv = NO.le_add_mono(own, 1n, Nat.add(fa, pa), Nat.add(E.op_kt(op), E.op_grid(op)), NO.and_l(L3, Bool.and(L4, L5), q2),
    NO.le_add_mono(fa, E.op_kt(op), pa, E.op_grid(op), NO.and_l(L4, L5, q3), hpa))
  fine_add(E.m16_const(op, tr), Nat.add(own, Nat.add(fa, pa)), m16_vb(op), hv)

# One m16 leaf against a witness s: the closed coarse / budget facts at k = 10.
def m16_dom(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +s: Eb.Path,
    +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool},
    +hc: {g_coarse(128n, E.m16_path(op, tr, own, fa, pa), s) == True{} : Bool},
    +hk: {Nat.is_le(m16_bnd(op, tr), Nat.mul(128n, 10n)) == True{} : Bool},
    +hs: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, tr, own, fa, pa), s)) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), s) == True{} : Bool}:
  dom_budget(128n, 10n, m16_bnd(op, tr), E.m16_path(op, tr, own, fa, pa), s, hc,
    m16_fine(op, tr, own, fa, pa, leaf), hk, hs)

# tr is 1 or 2 (1 <= tr <= FO = 2): the two closed cases, every other value refuted.
def m16_go(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +s: Eb.Path,
    +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool},
    +h1: {Nat.is_le(1n, tr) == True{} : Bool}, +h2: {Nat.is_le(tr, E.fo()) == True{} : Bool},
    +hc1: {g_coarse(128n, E.m16_path(op, 1n, own, fa, pa), s) == True{} : Bool},
    +hk1: {Nat.is_le(m16_bnd(op, 1n), Nat.mul(128n, 10n)) == True{} : Bool},
    +hs1: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 1n, own, fa, pa), s)) == True{} : Bool},
    +hc2: {g_coarse(128n, E.m16_path(op, 2n, own, fa, pa), s) == True{} : Bool},
    +hk2: {Nat.is_le(m16_bnd(op, 2n), Nat.mul(128n, 10n)) == True{} : Bool},
    +hs2: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 2n, own, fa, pa), s)) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), s) == True{} : Bool}:
  match tr:
    case 0n:
      Empty.absurd({Eb.dom(128n, E.m16_path(op, 0n, own, fa, pa), s) == True{} : Bool}, NO.false_true(h1))
    case 1n+t1:
      match t1:
        case 0n:
          m16_dom(op, 1n, own, fa, pa, s, leaf, hc1, hk1, hs1)
        case 1n+t2:
          match t2:
            case 0n:
              m16_dom(op, 2n, own, fa, pa, s, leaf, hc2, hk2, hs2)
            case 1n+t3:
              Empty.absurd({Eb.dom(128n, E.m16_path(op, 1n+1n+1n+t3, own, fa, pa), s) == True{} : Bool}, NO.false_true(h2))

def m16_two(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +s: Eb.Path,
    +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool},
    +hc1: {g_coarse(128n, E.m16_path(op, 1n, own, fa, pa), s) == True{} : Bool},
    +hk1: {Nat.is_le(m16_bnd(op, 1n), Nat.mul(128n, 10n)) == True{} : Bool},
    +hs1: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 1n, own, fa, pa), s)) == True{} : Bool},
    +hc2: {g_coarse(128n, E.m16_path(op, 2n, own, fa, pa), s) == True{} : Bool},
    +hk2: {Nat.is_le(m16_bnd(op, 2n), Nat.mul(128n, 10n)) == True{} : Bool},
    +hs2: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 2n, own, fa, pa), s)) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), s) == True{} : Bool}:
  +L1 = Nat.is_le(1n, tr)
  +L2 = Nat.is_le(tr, E.fo())
  +RR = Bool.and(Nat.is_le(own, 1n), Bool.and(Nat.is_le(fa, E.op_kt(op)), Nat.is_le(1n+pa, E.op_grid(op))))
  m16_go(op, tr, own, fa, pa, s, leaf, NO.and_l(L1, Bool.and(L2, RR), leaf),
    NO.and_l(L2, RR, NO.and_r(L1, Bool.and(L2, RR), leaf)), hc1, hk1, hs1, hc2, hk2, hs2)

# The closed per-(op, witness) case: all six facts by computation.
def m16_case(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +s: Eb.Path,
    +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool},
    +hc1: {g_coarse(128n, E.m16_path(op, 1n, own, fa, pa), s) == True{} : Bool},
    +hs1: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 1n, own, fa, pa), s)) == True{} : Bool},
    +hc2: {g_coarse(128n, E.m16_path(op, 2n, own, fa, pa), s) == True{} : Bool},
    +hs2: {Nat.is_le(10n, g_spare(128n, E.m16_path(op, 2n, own, fa, pa), s)) == True{} : Bool},
    +hk1: {Nat.is_le(m16_bnd(op, 1n), Nat.mul(128n, 10n)) == True{} : Bool},
    +hk2: {Nat.is_le(m16_bnd(op, 2n), Nat.mul(128n, 10n)) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), s) == True{} : Bool}:
  m16_two(op, tr, own, fa, pa, s, leaf, hc1, hk1, hs1, hc2, hk2, hs2)

# ==== (1) projections at m = 2 .. 8 ====

def W_ATTN() -> Eb.Path:
  Eb.Path{17n, 0n, 7n, 160n, 0n, 0n, 0n, 0n}

def W_GDN() -> Eb.Path:
  Eb.Path{19n, 0n, 3n, 128n, 0n, 0n, 0n, 0n}

def absurd_wl(+op: E.Op, +nt: Nat, h: {False{} == True{} : Bool})
  -> {E.proj_leaf(op, nt, E.wit_b(op, nt), 0n) == True{} : Bool} &
    {E.proj_wit(op, nt) == E.psel(E.is_attn(op), W_ATTN(), W_GDN()) : Eb.Path}:
  Empty.absurd({E.proj_leaf(op, nt, E.wit_b(op, nt), 0n) == True{} : Bool} &
    {E.proj_wit(op, nt) == E.psel(E.is_attn(op), W_ATTN(), W_GDN()) : Eb.Path}, NO.false_true(h))

# One closed computation per def (the kernel's step budget is per check).
def wa_leaf(+nt: Nat) -> Bool:
  E.proj_leaf(E.AttnQG{}, nt, E.wit_b(E.AttnQG{}, nt), 0n)

def wa_path(+nt: Nat) -> Eb.Path:
  E.proj_wit(E.AttnQG{}, nt)

def wg_leaf(+nt: Nat) -> Bool:
  E.proj_leaf(E.GdnQkv{}, nt, E.wit_b(E.GdnQkv{}, nt), 0n)

def wg_path(+nt: Nat) -> Eb.Path:
  E.proj_wit(E.GdnQkv{}, nt)

def wa_leaf0() -> {wa_leaf(0n) == True{} : Bool}:
  {==}

def wa_leaf1() -> {wa_leaf(1n) == True{} : Bool}:
  {==}

def wa_path0() -> {wa_path(0n) == W_ATTN() : Eb.Path}:
  {==}

def wa_path1() -> {wa_path(1n) == W_ATTN() : Eb.Path}:
  {==}

def wg_leaf0() -> {wg_leaf(0n) == True{} : Bool}:
  {==}

def wg_leaf1() -> {wg_leaf(1n) == True{} : Bool}:
  {==}

def wg_leaf2() -> {wg_leaf(2n) == True{} : Bool}:
  {==}

def wg_leaf3() -> {wg_leaf(3n) == True{} : Bool}:
  {==}

def wg_path0() -> {wg_path(0n) == W_GDN() : Eb.Path}:
  {==}

def wg_path1() -> {wg_path(1n) == W_GDN() : Eb.Path}:
  {==}

def wg_path2() -> {wg_path(2n) == W_GDN() : Eb.Path}:
  {==}

def wg_path3() -> {wg_path(3n) == W_GDN() : Eb.Path}:
  {==}

# Attention: column tiles 0, 1 of a 1024-column slice.
def wl_attn(+op: E.Op, +nt: Nat, +ia: {E.is_attn(op) == True{} : Bool}, col: {Nat.is_le(1n+nt, 2n) == True{} : Bool})
  -> {wa_leaf(nt) == True{} : Bool} & {wa_path(nt) == W_ATTN() : Eb.Path}:
  match nt:
    case 0n:
      (wa_leaf0(), wa_path0())
    case 1n+n1:
      match n1:
        case 0n:
          (wa_leaf1(), wa_path1())
        case 1n+n2:
          Empty.absurd({wa_leaf(1n+1n+n2) == True{} : Bool} & {wa_path(1n+1n+n2) == W_ATTN() : Eb.Path}, NO.false_true(col))

# GDN: column tiles 0 .. 3 of a 2048-column slice.
def wl_gdn(+nt: Nat, col: {Nat.is_le(1n+nt, 4n) == True{} : Bool})
  -> {wg_leaf(nt) == True{} : Bool} & {wg_path(nt) == W_GDN() : Eb.Path}:
  match nt:
    case 0n:
      (wg_leaf0(), wg_path0())
    case 1n+n1:
      match n1:
        case 0n:
          (wg_leaf1(), wg_path1())
        case 1n+n2:
          match n2:
            case 0n:
              (wg_leaf2(), wg_path2())
            case 1n+n3:
              match n3:
                case 0n:
                  (wg_leaf3(), wg_path3())
                case 1n+n4:
                  Empty.absurd({wg_leaf(1n+1n+1n+1n+n4) == True{} : Bool} & {wg_path(1n+1n+1n+1n+n4) == W_GDN() : Eb.Path},
                    NO.false_true(col))

def Laws.witness_leaves(op, nt, pj, col):
  match op:
    case E.AttnQG{}:
      wl_attn(E.AttnQG{}, nt, {==}, col)
    case E.AttnK{}:
      wl_attn(E.AttnK{}, nt, {==}, col)
    case E.AttnV{}:
      wl_attn(E.AttnV{}, nt, {==}, col)
    case E.GdnQkv{}:
      wl_gdn(nt, col)
    case E.GdnZ{}:
      wl_gdn(nt, col)
    case E.GdnBA{}:
      absurd_wl(E.GdnBA{}, nt, pj)
    case E.AttnO{}:
      absurd_wl(E.AttnO{}, nt, pj)
    case E.GdnOut{}:
      absurd_wl(E.GdnOut{}, nt, pj)
    case E.MlpGate{}:
      absurd_wl(E.MlpGate{}, nt, pj)
    case E.MlpUp{}:
      absurd_wl(E.MlpUp{}, nt, pj)
    case E.MlpDown{}:
      absurd_wl(E.MlpDown{}, nt, pj)
    case E.LmHead{}:
      absurd_wl(E.LmHead{}, nt, pj)

def absurd_dom(e: Eb.Path, s: Eb.Path, h: {False{} == True{} : Bool}) -> {Eb.dom(128n, e, s) == True{} : Bool}:
  Empty.absurd({Eb.dom(128n, e, s) == True{} : Bool}, NO.false_true(h))

# The closed facts of each op, one def per (op, witness).
def pc_qg(+tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.AttnQG{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.AttnQG{}, tr, own, fa, pa), W_ATTN()) == True{} : Bool}:
  m16_case(E.AttnQG{}, tr, own, fa, pa, W_ATTN(), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def pc_k(+tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.AttnK{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.AttnK{}, tr, own, fa, pa), W_ATTN()) == True{} : Bool}:
  m16_case(E.AttnK{}, tr, own, fa, pa, W_ATTN(), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def pc_v(+tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.AttnV{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.AttnV{}, tr, own, fa, pa), W_ATTN()) == True{} : Bool}:
  m16_case(E.AttnV{}, tr, own, fa, pa, W_ATTN(), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def pc_qkv(+tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.GdnQkv{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.GdnQkv{}, tr, own, fa, pa), W_GDN()) == True{} : Bool}:
  m16_case(E.GdnQkv{}, tr, own, fa, pa, W_GDN(), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def pc_z(+tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.GdnZ{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.GdnZ{}, tr, own, fa, pa), W_GDN()) == True{} : Bool}:
  m16_case(E.GdnZ{}, tr, own, fa, pa, W_GDN(), leaf, {==}, {==}, {==}, {==}, {==}, {==})

# The m16g leaf against the attention / GDN witness value.
def proj_core(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +pj: {E.is_proj(op) == True{} : Bool},
    +leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), E.psel(E.is_attn(op), W_ATTN(), W_GDN())) == True{} : Bool}:
  match op:
    case E.AttnQG{}:
      pc_qg(tr, own, fa, pa, leaf)
    case E.AttnK{}:
      pc_k(tr, own, fa, pa, leaf)
    case E.AttnV{}:
      pc_v(tr, own, fa, pa, leaf)
    case E.GdnQkv{}:
      pc_qkv(tr, own, fa, pa, leaf)
    case E.GdnZ{}:
      pc_z(tr, own, fa, pa, leaf)
    case E.GdnBA{}:
      absurd_dom(E.m16_path(E.GdnBA{}, tr, own, fa, pa), W_GDN(), pj)
    case E.AttnO{}:
      absurd_dom(E.m16_path(E.AttnO{}, tr, own, fa, pa), W_GDN(), pj)
    case E.GdnOut{}:
      absurd_dom(E.m16_path(E.GdnOut{}, tr, own, fa, pa), W_GDN(), pj)
    case E.MlpGate{}:
      absurd_dom(E.m16_path(E.MlpGate{}, tr, own, fa, pa), W_GDN(), pj)
    case E.MlpUp{}:
      absurd_dom(E.m16_path(E.MlpUp{}, tr, own, fa, pa), W_GDN(), pj)
    case E.MlpDown{}:
      absurd_dom(E.m16_path(E.MlpDown{}, tr, own, fa, pa), W_GDN(), pj)
    case E.LmHead{}:
      absurd_dom(E.m16_path(E.LmHead{}, tr, own, fa, pa), W_GDN(), pj)

def wit_eq(+op: E.Op, +nt: Nat,
    w: {E.proj_leaf(op, nt, E.wit_b(op, nt), 0n) == True{} : Bool} &
      {E.proj_wit(op, nt) == E.psel(E.is_attn(op), W_ATTN(), W_GDN()) : Eb.Path})
  -> {E.proj_wit(op, nt) == E.psel(E.is_attn(op), W_ATTN(), W_GDN()) : Eb.Path}:
  match w:
    case (a, b):
      b

def Laws.proj_m16g_dom(op, m, nt, tr, own, fa, pa, pj, rows, col, leaf):
  +hpj = pj
  +eq = wit_eq(op, nt, Laws.witness_leaves(op, nt, hpj, col))
  %Equal.sym(Eb.Path, E.proj_wit(op, nt), E.psel(E.is_attn(op), W_ATTN(), W_GDN()), eq) :
    {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), _) == True{} : Bool}
  proj_core(op, tr, own, fa, pa, hpj, leaf)

# ==== (2) projections at m = 1: the stock path itself ====

def Laws.proj_m1_dom(op, nt, b, j, pj, lf):
  EBL.dom_refl(128n, E.proj_stock(op, nt, b, j))

# ==== (3) the layer tail against the stock int8 GEMV ====

def tc_o(+ks: Nat, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.AttnO{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.AttnO{}, tr, own, fa, pa), E.tail_wit(E.AttnO{}, ks)) == True{} : Bool}:
  m16_case(E.AttnO{}, tr, own, fa, pa, E.tail_wit(E.AttnO{}, ks), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def tc_out(+ks: Nat, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.GdnOut{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.GdnOut{}, tr, own, fa, pa), E.tail_wit(E.GdnOut{}, ks)) == True{} : Bool}:
  m16_case(E.GdnOut{}, tr, own, fa, pa, E.tail_wit(E.GdnOut{}, ks), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def tc_g(+ks: Nat, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.MlpGate{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.MlpGate{}, tr, own, fa, pa), E.tail_wit(E.MlpGate{}, ks)) == True{} : Bool}:
  m16_case(E.MlpGate{}, tr, own, fa, pa, E.tail_wit(E.MlpGate{}, ks), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def tc_u(+ks: Nat, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.MlpUp{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.MlpUp{}, tr, own, fa, pa), E.tail_wit(E.MlpUp{}, ks)) == True{} : Bool}:
  m16_case(E.MlpUp{}, tr, own, fa, pa, E.tail_wit(E.MlpUp{}, ks), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def tc_d(+ks: Nat, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, +leaf: {E.m16_leaf(E.MlpDown{}, tr, own, fa, pa) == True{} : Bool})
  -> {Eb.dom(128n, E.m16_path(E.MlpDown{}, tr, own, fa, pa), E.tail_wit(E.MlpDown{}, ks)) == True{} : Bool}:
  m16_case(E.MlpDown{}, tr, own, fa, pa, E.tail_wit(E.MlpDown{}, ks), leaf, {==}, {==}, {==}, {==}, {==}, {==})

def Laws.tail_dom(op, m, ks, tr, own, fa, pa, tl, rows, leaf):
  match op:
    case E.AttnO{}:
      tc_o(ks, tr, own, fa, pa, leaf)
    case E.GdnOut{}:
      tc_out(ks, tr, own, fa, pa, leaf)
    case E.MlpGate{}:
      tc_g(ks, tr, own, fa, pa, leaf)
    case E.MlpUp{}:
      tc_u(ks, tr, own, fa, pa, leaf)
    case E.MlpDown{}:
      tc_d(ks, tr, own, fa, pa, leaf)
    case E.AttnQG{}:
      absurd_dom(E.m16_path(E.AttnQG{}, tr, own, fa, pa), E.tail_wit(E.AttnQG{}, ks), tl)
    case E.AttnK{}:
      absurd_dom(E.m16_path(E.AttnK{}, tr, own, fa, pa), E.tail_wit(E.AttnK{}, ks), tl)
    case E.AttnV{}:
      absurd_dom(E.m16_path(E.AttnV{}, tr, own, fa, pa), E.tail_wit(E.AttnV{}, ks), tl)
    case E.GdnQkv{}:
      absurd_dom(E.m16_path(E.GdnQkv{}, tr, own, fa, pa), E.tail_wit(E.GdnQkv{}, ks), tl)
    case E.GdnZ{}:
      absurd_dom(E.m16_path(E.GdnZ{}, tr, own, fa, pa), E.tail_wit(E.GdnZ{}, ks), tl)
    case E.GdnBA{}:
      absurd_dom(E.m16_path(E.GdnBA{}, tr, own, fa, pa), E.tail_wit(E.GdnBA{}, ks), tl)
    case E.LmHead{}:
      absurd_dom(E.m16_path(E.LmHead{}, tr, own, fa, pa), E.tail_wit(E.LmHead{}, ks), tl)

# ==== (4) b/a ====

# a - b <= a
def sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      NO.le_refl(1n+p)
    case 1n+p 1n+q:
      NO.le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), NO.le_succ(p))

def ba_fma_le(+p: Nat) -> {Nat.is_le(E.ba_fma(p), 10n) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      sub_le(10n, 1n+q)

def ba_rs_le(+w: Nat) -> {Nat.is_le(E.ba_rs(w), 16n) == True{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+q:
      sub_le(16n, 1n+q)

def Laws.ba_dom(m, p, w, hb, rows, hp, hw):
  +bb = E.ba_bias(hb)
  +X = Nat.add(E.ba_fma(p), Nat.add(5n, E.ba_rs(w)))
  +Y = Nat.add(Nat.sub(E.ba_chain(), 1n), 5n)
  +hX = NO.le_add_mono(E.ba_fma(p), 10n, Nat.add(5n, E.ba_rs(w)), Nat.add(5n, 16n), ba_fma_le(p),
    NO.le_add_mono(5n, 5n, E.ba_rs(w), 16n, NO.le_refl(5n), ba_rs_le(w)))
  +hXY = NO.le_trans(X, Nat.add(10n, Nat.add(5n, 16n)), Y, hX, {==})
  dom_le(128n, E.ba_path(p, w, hb), E.ba_wit(hb), {==}, {==},
    NO.le_add_mono(0n, 0n, Nat.add(X, bb), Nat.add(Y, bb), NO.le_refl(0n), NO.le_add_mono(X, Y, bb, bb, hXY, NO.le_refl(bb))))

# ==== (5) lm_head ====

def head_eq(+k: Nat, +n: Nat, +nt: Nat, +m: Nat, +r: Nat, +i: Nat, +j: Nat, +g: Nat, +c32: Bool,
    +hr: {Nat.is_lt(r, m) == True{} : Bool}, +hm: {Nat.is_le(m, 8n) == True{} : Bool})
  -> {E.head_path(k, n, nt, m, r, i, j, g, c32) == E.head_path(k, n, nt, 1n, 0n, i, j, g, c32) : Eb.Path}:
  %Equal.sym(LH.Order, LH.elem_order(LH.served_tab(), 6n, k, n, m, r, nt), LH.elem_order(LH.served_tab(), 6n, k, n, 1n, 0n, nt),
      LHL.served_order(k, n, nt, m, r, hr, hm)) :
    {E.tc_path(_, i, j, g, c32, False{}) == E.head_path(k, n, nt, 1n, 0n, i, j, g, c32) : Eb.Path}
  {==}

def head_dom2(+k: Nat, +n: Nat, +nt: Nat, +m: Nat, +r: Nat, +i: Nat, +j: Nat, +g: Nat, +c32: Bool,
    +eq: {E.head_path(k, n, nt, m, r, i, j, g, c32) == E.head_path(k, n, nt, 1n, 0n, i, j, g, c32) : Eb.Path})
  -> {Eb.dom(128n, E.head_path(k, n, nt, m, r, i, j, g, c32), E.head_path(k, n, nt, 1n, 0n, i, j, g, c32)) == True{} : Bool}:
  %Equal.sym(Eb.Path, E.head_path(k, n, nt, m, r, i, j, g, c32), E.head_path(k, n, nt, 1n, 0n, i, j, g, c32), eq) :
    {Eb.dom(128n, _, E.head_path(k, n, nt, 1n, 0n, i, j, g, c32)) == True{} : Bool}
  EBL.dom_refl(128n, E.head_path(k, n, nt, 1n, 0n, i, j, g, c32))

def Laws.head_dom(k, n, nt, m, r, i, j, g, c32, hr, hm):
  +eq = head_eq(k, n, nt, m, r, i, j, g, c32, hr, hm)
  (eq, head_dom2(k, n, nt, m, r, i, j, g, c32, eq))

# ==== (7) shape literals ====

def sl1() -> {Wp.kt_served() == 320n : Nat}:
  {==}

def sl2() -> {TS.kt0(TS.kin()) == 384n : Nat}:
  {==}

def sl3() -> {Mlp.kt1(Mlp.hidden()) == 320n : Nat}:
  {==}

def sl4() -> {Nat.mul(1088n, 16n) == Mlp.inter() : Nat}:
  {==}

def sl5() -> {Wp.grid_served() == 164n : Nat}:
  {==}

def sl6() -> {Mlp.grid() == 164n : Nat}:
  {==}

def sl7() -> {LH.tiles(5120n, 1024n, 4n) == 640n : Nat}:
  {==}

def sl8() -> {LH.tiles(5120n, 2048n, 4n) == 1280n : Nat}:
  {==}

def sl9() -> {LH.tiles_k(5120n, 4n) == 320n : Nat}:
  {==}

def sl10() -> {Nat.mul(2n, Nat.div(Nat.div(5120n, 2n), 32n)) == E.ba_chain() : Nat}:
  {==}

def Laws.shape_literals():
  (sl1(), sl2(), sl3(), sl4(), sl5(), sl6(), sl7(), sl8(), sl9(), sl10())

# ==== (8) the exact stock partition: (c g) b / g = c b ====

# divmod.go counts k steps of n and m down together, moving them into r.
def go_shift(+k: Nat, +n: Nat, +m: Nat, +d: Nat, +r: Nat)
  -> {Nat.divmod.go(Nat.add(k, n), Nat.add(k, m), d, r) == Nat.divmod.go(n, m, d, Nat.add(k, r)) : Nat & Nat}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      %NO.add_succ_r(kp, r) : {Nat.divmod.go(Nat.add(1n+kp, n), Nat.add(1n+kp, m), d, r) == Nat.divmod.go(n, m, d, _) : Nat & Nat}
      go_shift(kp, n, m, d, 1n+r)

# One block of g = 1 + gp steps adds one to the quotient.
def go_block(+gp: Nat, +n: Nat, +d: Nat)
  -> {Nat.divmod.go(Nat.add(1n+gp, n), gp, d, 0n) == Nat.divmod.go(n, gp, 1n+d, 0n) : Nat & Nat}:
  %NO.add_zero_r(gp) : {Nat.divmod.go(Nat.add(1n+gp, n), _, d, 0n) == Nat.divmod.go(n, _, 1n+d, 0n) : Nat & Nat}
  %NO.add_succ_r(gp, n) : {Nat.divmod.go(_, Nat.add(gp, 0n), d, 0n) == Nat.divmod.go(n, Nat.add(gp, 0n), 1n+d, 0n) : Nat & Nat}
  go_shift(gp, 1n+n, 0n, d, 0n)

def go_mul_step(+xp: Nat, +gp: Nat, +d: Nat,
    +ih: {Nat.divmod.go(Nat.mul(xp, 1n+gp), gp, 1n+d, 0n) == (Nat.add(xp, 1n+d), 0n) : Nat & Nat})
  -> {Nat.divmod.go(Nat.mul(xp, 1n+gp), gp, 1n+d, 0n) == (Nat.add(1n+xp, d), 0n) : Nat & Nat}:
  %NO.add_succ_r(xp, d) : {Nat.divmod.go(Nat.mul(xp, 1n+gp), gp, 1n+d, 0n) == (_, 0n) : Nat & Nat}
  ih

def go_mul(+x: Nat, +gp: Nat, +d: Nat)
  -> {Nat.divmod.go(Nat.mul(x, 1n+gp), gp, d, 0n) == (Nat.add(x, d), 0n) : Nat & Nat}:
  match x:
    case 0n:
      {==}
    case 1n+xp:
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.mul(1n+xp, 1n+gp), gp, d, 0n), Nat.divmod.go(Nat.mul(xp, 1n+gp), gp, 1n+d, 0n),
        (Nat.add(1n+xp, d), 0n), go_block(gp, Nat.mul(xp, 1n+gp), d), go_mul_step(xp, gp, d, go_mul(xp, gp, 1n+d)))

def div_mul(+y: Nat, +gp: Nat) -> {Nat.div(Nat.mul(y, 1n+gp), 1n+gp) == y : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.mul(y, 1n+gp), gp, 0n, 0n), (Nat.add(y, 0n), 0n), go_mul(y, gp, 0n)) :
    {Pair.fst(Nat, Nat, _) == y : Nat}
  NO.add_zero_r(y)

# (c g) b == (c b) g
def mul_swap(+c: Nat, +g: Nat, +b: Nat) -> {Nat.mul(Nat.mul(c, g), b) == Nat.mul(Nat.mul(c, b), g) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(c, g), b), Nat.mul(c, Nat.mul(g, b)), NO.mul_assoc(c, g, b)) :
    {_ == Nat.mul(Nat.mul(c, b), g) : Nat}
  %NO.mul_comm(b, g) : {Nat.mul(c, _) == Nat.mul(Nat.mul(c, b), g) : Nat}
  Equal.sym(Nat, Nat.mul(Nat.mul(c, b), g), Nat.mul(c, Nat.mul(b, g)), NO.mul_assoc(c, b, g))

def pe_attn(+b: Nat) -> {LH.slice_beg(b, 640n, 4n) == Nat.mul(160n, b) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(160n, 4n), b), Nat.mul(Nat.mul(160n, b), 4n), mul_swap(160n, 4n, b)) :
    {Nat.div(_, 4n) == Nat.mul(160n, b) : Nat}
  div_mul(Nat.mul(160n, b), 3n)

def pe_gdn(+b: Nat) -> {LH.slice_beg(b, 1280n, 10n) == Nat.mul(128n, b) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(128n, 10n), b), Nat.mul(Nat.mul(128n, b), 10n), mul_swap(128n, 10n, b)) :
    {Nat.div(_, 10n) == Nat.mul(128n, b) : Nat}
  div_mul(Nat.mul(128n, b), 9n)

def Laws.partition_exact(b):
  (pe_attn(b), pe_gdn(b))

def Laws.kt2_of_mul(x):
  div_mul(x, 15n)

# ==== (9) / (10) served leaves: tr from the trace, pa from the partition ====

def sub0(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a - (1 + c) <= a - 1
def sub_succ_le(+a: Nat, +c: Nat) -> {Nat.is_le(Nat.sub(a, 1n+c), Nat.sub(a, 1n)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, sub0(p)) : {Nat.is_le(Nat.sub(p, c), _) == True{} : Bool}
      sub_le(p, c)

# a < b gives 1 + a <= b.
def lt_le_succ(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(h))
    case 0n 1n+q:
      NO.le_zero(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+1n+p, 0n) == True{} : Bool}, NO.false_true(h))
    case 1n+p 1n+q:
      lt_le_succ(p, q, h)

# 1 + fin_adds(c, nc) <= nc for nc >= 1.
def fin_le(+c: Nat, +nc: Nat, +hn: {Nat.is_le(1n, nc) == True{} : Bool})
  -> {Nat.is_le(1n+E.fin_adds(c, nc), nc) == True{} : Bool}:
  match c:
    case 0n:
      NO.le_of_eq(Nat.add(1n, Nat.sub(nc, 1n)), nc, NO.sub_add(nc, 1n, hn))
    case 1n+cp:
      NO.le_trans(1n+Nat.sub(nc, 1n+cp), 1n+Nat.sub(nc, 1n), nc, sub_succ_le(nc, cp),
        NO.le_of_eq(Nat.add(1n, Nat.sub(nc, 1n)), nc, NO.sub_add(nc, 1n, hn)))

def last_le(+last: Nat, +G: Nat, hl: {Nat.is_lt(last, G) == True{} : Bool})
  -> {Nat.is_le(Nat.add(last, 1n), G) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(last, 1n), Nat.add(1n, last), NO.add_comm(last, 1n)) : {Nat.is_le(_, G) == True{} : Bool}
  lt_le_succ(last, G, hl)

# (last - first) + 1 <= G for last < G.
def nc_le(+last: Nat, +first: Nat, +G: Nat, hl: {Nat.is_lt(last, G) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.sub(last, first), 1n), G) == True{} : Bool}:
  NO.le_trans(Nat.add(Nat.sub(last, first), 1n), Nat.add(last, 1n), G,
    NO.le_add_mono(Nat.sub(last, first), last, 1n, 1n, sub_le(last, first), NO.le_refl(1n)), last_le(last, G, hl))

# From contrib_bounds' conjuncts (first <= last, last < G, 1 <= nc, nc <= max_contrib).
def pa_of(+c: Nat, +G: Nat, +first: Nat, +last: Nat, +mc: Nat,
    cb: {Nat.is_le(first, last) == True{} : Bool} & {Nat.is_lt(last, G) == True{} : Bool} &
      {Nat.is_le(1n, Nat.add(Nat.sub(last, first), 1n)) == True{} : Bool} &
      {Nat.is_le(Nat.add(Nat.sub(last, first), 1n), mc) == True{} : Bool})
  -> {Nat.is_le(1n+E.fin_adds(c, Nat.add(Nat.sub(last, first), 1n)), G) == True{} : Bool}:
  (c1, c2, c3, c4) = cb
  +NC = Nat.add(Nat.sub(last, first), 1n)
  NO.le_trans(1n+E.fin_adds(c, NC), NC, G, fin_le(c, NC, c3), nc_le(last, first, G, c2))

# 1 + pa <= G for every finisher slot of a group of the weighted partition.
def pa_le(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +g: Nat, +c: Nat,
    w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}, w1pos: {Nat.is_lt(0n, w1) == True{} : Bool},
    grid: {Nat.is_lt(0n, G) == True{} : Bool}, tiles: {Nat.is_lt(0n, KT) == True{} : Bool},
    group: {Nat.is_lt(g, groups) == True{} : Bool})
  -> {Nat.is_le(1n+E.fin_adds(c, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)), G) == True{} : Bool}:
  +T = Nat.mul(groups, KT)
  pa_of(c, G, Wp.first_contrib(g, KT, T, G, nsm, w0, w1), Wp.last_contrib(g, KT, T, G, nsm, w0, w1),
    Wp.max_contrib(groups, KT, G, nsm, w0, w1),
    WL.contrib_bounds(groups, KT, G, nsm, w0, w1, g, w0pos, w1pos, grid, tiles, group))

def pa_grid(+op: E.Op, +G: Nat, +pa: Nat, s_grid: {G == E.op_grid(op) : Nat}, h: {Nat.is_le(1n+pa, G) == True{} : Bool})
  -> {Nat.is_le(1n+pa, E.op_grid(op)) == True{} : Bool}:
  %s_grid : {Nat.is_le(1n+pa, _) == True{} : Bool}
  h

# The m16 leaf facts from tr's bounds, own, fa and pa.
def mk_leaf(+op: E.Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat, h1: {Nat.is_le(1n, tr) == True{} : Bool},
    h2: {Nat.is_le(tr, E.fo()) == True{} : Bool}, h3: {Nat.is_le(own, 1n) == True{} : Bool},
    h4: {Nat.is_le(fa, E.op_kt(op)) == True{} : Bool}, h5: {Nat.is_le(1n+pa, E.op_grid(op)) == True{} : Bool})
  -> {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool}:
  +L4 = Bool.and(Nat.is_le(fa, E.op_kt(op)), Nat.is_le(1n+pa, E.op_grid(op)))
  +L3 = Bool.and(Nat.is_le(own, 1n), L4)
  +L2 = Bool.and(Nat.is_le(tr, E.fo()), L3)
  NO.and_intro(Nat.is_le(1n, tr), L2, h1, NO.and_intro(Nat.is_le(tr, E.fo()), L3, h2,
    NO.and_intro(Nat.is_le(own, 1n), L4, h3,
      NO.and_intro(Nat.is_le(fa, E.op_kt(op)), Nat.is_le(1n+pa, E.op_grid(op)), h4, h5))))

def Laws.proj_m16g_served(op, m, nt, s, n, KT, i, own, fa, groups, G, nsm, w0, w1, g, c, pj, rows, col, tiles,
    it, ho, hf, w0pos, w1pos, grid, group, s_grid):
  +kt = tiles
  +TR = Diet.diet_m16g(s, n, KT, PE.pf(), PE.xr(), PE.fold(), PE.ws(), PE.xi())
  +tr = R.tr_at(TR, i)
  +pa = E.fin_adds(c, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))
  Laws.proj_m16g_dom(op, m, nt, tr, own, fa, pa, pj, rows, col,
    mk_leaf(op, tr, own, fa, pa, RL.tr_pos(TR, i, it), RL.tr_bound_m16g(s, n, KT, i, kt), ho, hf,
      pa_grid(op, G, pa, s_grid, pa_le(groups, KT, G, nsm, w0, w1, g, c, w0pos, w1pos, grid, kt, group))))

def Laws.tail_served(op, m, ks, s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, i, own, fa, groups, KT, G, nsm, w0, w1,
    g, c, tl, rows, kt0, kt1, kt2, ring1, ring2, it, ho, hf, w0pos, w1pos, grid, tiles, group, s_grid):
  +TR = Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, PE.pf(),
    PE.xr(), PE.fold(), PE.ws(), PE.xi())
  +tr = R.tr_at(TR, i)
  +pa = E.fin_adds(c, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))
  Laws.tail_dom(op, m, ks, tr, own, fa, pa, tl, rows,
    mk_leaf(op, tr, own, fa, pa, RL.tr_pos(TR, i, it),
      RL.tr_bound_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, i, kt0, kt1, kt2, ring1, ring2), ho, hf,
      pa_grid(op, G, pa, s_grid, pa_le(groups, KT, G, nsm, w0, w1, g, c, w0pos, w1pos, grid, tiles, group))))
