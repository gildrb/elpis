# Proofs of the ext 8201 fused-MLP schedule laws (mlp_m16_sched_laws.bend) about the Bend model
# mlp_m16_sched.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign
# proof code or answer tables; the patch 2001 v2 partition facts come from the proven
# gemm_m16_partition laws and lemmas. Every def precedes its uses.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_laws.bend as PLaws
import ./gemm_m16_partition_proof.bend as PP
import ./mlp_m16_sched.bend as Impl
import ./mlp_m16_sched_spec.bend as Spec
import ./mlp_m16_sched_laws.bend as Laws

# ==== (1), (5): slices are the v2 block ranges ====

def end1(+G: Nat, +H: Nat, +I: Nat, +b: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool})
  -> {Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)) == Impl.e1(G, H, I, b) : Nat}:
  PP.ar_sub_add(Impl.e1(G, H, I, b), Impl.s1(G, H, I, b),
    PP.ar_lt_le(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b),
      PP.p2_nonempty(b, Impl.total1(H, I), G, gpos, fits)))

def end2(+G: Nat, +H: Nat, +I: Nat, +b: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    fits: {Nat.is_le(G, Impl.total2(H, I)) == True{} : Bool})
  -> {Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)) == Impl.e2(G, H, I, b) : Nat}:
  PP.ar_sub_add(Impl.e2(G, H, I, b), Impl.s2(G, H, I, b),
    PP.ar_lt_le(Impl.s2(G, H, I, b), Impl.e2(G, H, I, b),
      PP.p2_nonempty(Impl.slice(b), Impl.total2(H, I), G, gpos, fits)))

def Laws.phase1_slice_owned(G, H, I, b, x, grid, fits):
  +gp = grid
  %Equal.sym(Nat, Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)), Impl.e1(G, H, I, b),
      end1(G, H, I, b, gp, fits))
    : {Bool.and(Nat.is_le(Impl.s1(G, H, I, b), x), Nat.is_lt(x, _)) ==
      PSpec.owns(b, x, Impl.total1(H, I), G) : Bool}
  PLaws.range_is_owned(2n, I, H, G, b, x, gp)

def Laws.phase1_exactly_once(G, H, I, x, grid, inside):
  PLaws.owners_exactly_one(2n, I, H, G, x, grid, inside)

def Laws.phase2_slice_owned(G, H, I, b, x, grid, fits):
  +gp = grid
  %Equal.sym(Nat, Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)), Impl.e2(G, H, I, b),
      end2(G, H, I, b, gp, fits))
    : {Bool.and(Nat.is_le(Impl.s2(G, H, I, b), x), Nat.is_lt(x, _)) ==
      PSpec.owns(Impl.slice(b), x, Impl.total2(H, I), G) : Bool}
  PLaws.range_is_owned(1n, H, I, G, Impl.slice(b), x, gp)

def Laws.phase2_exactly_once(G, H, I, x, grid, inside):
  PLaws.owners_exactly_one(1n, H, I, G, x, grid, inside)

# [u < n] + [n == u] == [u < n + 1]
def bit_step(+u: Nat, +n: Nat)
  -> {Nat.add(Spec.bit(Nat.is_lt(u, n)), Spec.bit(Nat.is_eq(n, u))) ==
    Spec.bit(Nat.is_lt(u, 1n+n)) : Nat}:
  match u n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+v 0n:
      %Equal.sym(Bool, Nat.is_lt(v, 0n), False{}, PP.ar_h_lt_zero(v)) : {0n == Spec.bit(_) : Nat}
      {==}
    case 1n+v 1n+q:
      bit_step(v, q)

def slice_hits_lt(+n: Nat, +u: Nat)
  -> {Laws.slice_hits(n, u) == Spec.bit(Nat.is_lt(u, n)) : Nat}:
  match n:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(u, 0n), False{}, PP.ar_h_lt_zero(u)) : {0n == Spec.bit(_) : Nat}
      {==}
    case 1n+m:
      %Equal.sym(Nat, Laws.slice_hits(m, u), Spec.bit(Nat.is_lt(u, m)), slice_hits_lt(m, u)) : {Nat.add(_, Spec.bit(Nat.is_eq(m, u))) ==
        Spec.bit(Nat.is_lt(u, 1n+m)) : Nat}
      bit_step(u, m)

def Laws.slice_permutation(G, u, inside):
  %Equal.sym(Nat, Laws.slice_hits(G, u), Spec.bit(Nat.is_lt(u, G)), slice_hits_lt(G, u)) : {_ == 1n : Nat}
  %Equal.sym(Bool, Nat.is_lt(u, G), True{}, inside) : {Spec.bit(_) == 1n : Nat}
  {==}

def Laws.phase1_v2(G, H, I, b, grid, shaped, fits):
  +gp = grid
  +fp = fits
  (end1(G, H, I, b, gp, fp),
    %PP.ar_add_sub(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b))
      : {Part.mainloop(Impl.s1(G, H, I, b), Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)),
          Impl.kt1(H)) ==
        PSpec.trace(_, Impl.s1(G, H, I, b), Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)),
          Impl.kt1(H)) : List<&2, PSpec.Ev>}
    PLaws.mainloop_trace(Impl.s1(G, H, I, b), Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)),
      Impl.kt1(H), PP.ar_le_add_r(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)),
      PP.p2_kt_pos(H, shaped)))

def Laws.phase2_v2(G, H, I, b, grid, shaped, fits):
  +gp = grid
  +fp = fits
  (end2(G, H, I, b, gp, fp),
    %PP.ar_add_sub(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b))
      : {Part.mainloop(Impl.s2(G, H, I, b), Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)),
          Impl.kt2(I)) ==
        PSpec.trace(_, Impl.s2(G, H, I, b), Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)),
          Impl.kt2(I)) : List<&2, PSpec.Ev>}
    PLaws.mainloop_trace(Impl.s2(G, H, I, b), Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)),
      Impl.kt2(I), PP.ar_le_add_r(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)),
      PP.p2_kt_pos(I, shaped)))

# ==== (4) ring ====

def Laws.ring2_slot(G, H, I, b):
  {==}

def sub_le(+a: Nat, +c: Nat) -> {Nat.is_le(Nat.sub(a, c), a) == True{} : Bool}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      PP.ar_le_refl(1n+p)
    case 1n+p 1n+q:
      PP.ar_le_trans(Nat.sub(p, q), p, 1n+p, sub_le(p, q), PP.ar_h_le_succ(p))

def Laws.ring_issue_in_time(i, pf):
  sub_le(i, Nat.sub(pf, 1n))

# (a + b) mod b == a mod b   (b >= 1)
def mod_add_self(+a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.mod(Nat.add(a, b), b) == Nat.mod(a, b) : Nat}:
  +d = Nat.div(a, b)
  PP.ard_snd({Nat.div(Nat.add(a, b), b) == 1n+d : Nat},
    {Nat.mod(Nat.add(a, b), b) == Nat.mod(a, b) : Nat},
    PP.ar_divmod_inj(Nat.div(Nat.add(a, b), b), Nat.mod(Nat.add(a, b), b), 1n+d, Nat.mod(a, b), b,
      PP.ard_dm_lt(Nat.add(a, b), b, pos), PP.ard_dm_lt(a, b, pos),
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(Nat.add(a, b), b), b), Nat.mod(Nat.add(a, b), b)),
        Nat.add(a, b), Nat.add(Nat.mul(1n+d, b), Nat.mod(a, b)),
        PP.ard_dm_eq(Nat.add(a, b), b, pos),
        Equal.sym(Nat, Nat.add(Nat.mul(1n+d, b), Nat.mod(a, b)), Nat.add(a, b),
          Equal.trans(Nat, Nat.add(Nat.add(b, Nat.mul(d, b)), Nat.mod(a, b)),
            Nat.add(b, Nat.add(Nat.mul(d, b), Nat.mod(a, b))), Nat.add(a, b),
            PP.ar_add_assoc(b, Nat.mul(d, b), Nat.mod(a, b)),
            Equal.trans(Nat, Nat.add(b, Nat.add(Nat.mul(d, b), Nat.mod(a, b))), Nat.add(b, a),
              Nat.add(a, b),
              Equal.cong(Nat, Nat, t => Nat.add(b, t), Nat.add(Nat.mul(d, b), Nat.mod(a, b)), a,
                PP.ard_dm_eq(a, b, pos)),
              PP.ar_add_comm(b, a)))))))

def issue_reuse(+i: Nat, +pf: Nat, pos: {Nat.is_lt(0n, pf) == True{} : Bool})
  -> {Impl.issue_step(Nat.add(i, pf), pf) == 1n+i : Nat}:
  match pf:
    case 0n:
      Empty.absurd({Impl.issue_step(Nat.add(i, 0n), 0n) == 1n+i : Nat}, PP.ar_false_true(pos))
    case 1n+q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, PP.ar_sub_zero_r(q))
        : {Nat.sub(Nat.add(i, 1n+q), _) == 1n+i : Nat}
      %Equal.trans(Nat, Nat.add(q, 1n+i), Nat.add(1n+i, q), Nat.add(i, 1n+q),
          PP.ar_add_comm(q, 1n+i),
          Equal.sym(Nat, Nat.add(i, 1n+q), 1n+Nat.add(i, q), PP.ar_add_succ_r(i, q)))
        : {Nat.sub(_, q) == 1n+i : Nat}
      PP.ar_add_sub(q, 1n+i)

def Laws.ring_reuse(i, pf, pos):
  +ps = pos
  (mod_add_self(i, pf, ps), issue_reuse(i, pf, ps))

# ==== (3) event levels ====

def ord_sigs1(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>)
  -> {Spec.ordered(Impl.sigs1(evs, rest), 0n) == Spec.ordered(rest, 0n) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          ord_sigs1(more, rest)
        case PSpec.Flush{g}:
          ord_sigs1(more, rest)

def ord_sigs1_sym(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>)
  -> {Spec.ordered(rest, 0n) == Spec.ordered(Impl.sigs1(evs, rest), 0n) : Bool}:
  Equal.sym(Bool, Spec.ordered(Impl.sigs1(evs, rest), 0n), Spec.ordered(rest, 0n),
    ord_sigs1(evs, rest))

def ord_waits2(ws: List<&2, Nat>, +from: Nat, h: {Nat.is_le(from, 2n) == True{} : Bool})
  -> {Spec.ordered(Impl.waits2(ws), from) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case p <> rest:
      %Equal.sym(Bool, Nat.is_le(from, 2n), True{}, h)
        : {Bool.and(_, Spec.ordered(Impl.waits2(rest), 2n)) == True{} : Bool}
      ord_waits2(rest, 2n, {==})

def Laws.events_ordered(G, H, I, b):
  %ord_sigs1_sym(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, b), Impl.waits2(Impl.waits(G, H, I, b))))
    : {_ == True{} : Bool}
  ord_waits2(Impl.waits(G, H, I, b), 1n, {==})

def or_true_r(x: Bool) -> {True{} == Bool.or(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Phase-1 signals are C1 signals at level 0: below any bound >= 1.
def sb_sigs1(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +c: Spec.Ctr, +q: Nat)
  -> {Spec.sigs_below(Impl.sigs1(evs, rest), c, 1n+q) == Spec.sigs_below(rest, c, 1n+q) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          sb_sigs1(more, rest, c, q)
        case PSpec.Flush{g}:
          %or_true_r(Bool.not(Spec.ctr_eq(Spec.C1{g}, c)))
            : {Bool.and(_, Spec.sigs_below(Impl.sigs1(more, rest), c, 1n+q)) ==
              Spec.sigs_below(rest, c, 1n+q) : Bool}
          sb_sigs1(more, rest, c, q)

def sb_waits2(ws: List<&2, Nat>, +c: Spec.Ctr, +bound: Nat)
  -> {Spec.sigs_below(Impl.waits2(ws), c, bound) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case p <> rest:
      sb_waits2(rest, c, bound)

def wf_sigs1(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +c: Spec.Ctr, +bound: Nat)
  -> {Spec.waits_from(Impl.sigs1(evs, rest), c, bound) == Spec.waits_from(rest, c, bound) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          wf_sigs1(more, rest, c, bound)
        case PSpec.Flush{g}:
          wf_sigs1(more, rest, c, bound)

def sb_sigs1_sym(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +c: Spec.Ctr, +q: Nat)
  -> {Spec.sigs_below(rest, c, 1n+q) == Spec.sigs_below(Impl.sigs1(evs, rest), c, 1n+q) : Bool}:
  Equal.sym(Bool, Spec.sigs_below(Impl.sigs1(evs, rest), c, 1n+q), Spec.sigs_below(rest, c, 1n+q),
    sb_sigs1(evs, rest, c, q))

def wf_sigs1_sym(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +c: Spec.Ctr, +bound: Nat)
  -> {Spec.waits_from(rest, c, bound) == Spec.waits_from(Impl.sigs1(evs, rest), c, bound) : Bool}:
  Equal.sym(Bool, Spec.waits_from(Impl.sigs1(evs, rest), c, bound), Spec.waits_from(rest, c, bound),
    wf_sigs1(evs, rest, c, bound))

# Phase-2 waits sit at level 2: at or above any bound <= 2.
def wf_waits2(ws: List<&2, Nat>, +c: Spec.Ctr, +bound: Nat,
    +h: {Nat.is_le(bound, 2n) == True{} : Bool})
  -> {Spec.waits_from(Impl.waits2(ws), c, bound) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case p <> rest:
      %Equal.sym(Bool, Nat.is_le(bound, 2n), True{}, h)
        : {Bool.and(Bool.or(Bool.not(Spec.ctr_eq(Spec.C2{p}, c)), _),
          Spec.waits_from(Impl.waits2(rest), c, bound)) == True{} : Bool}
      %or_true_r(Bool.not(Spec.ctr_eq(Spec.C2{p}, c)))
        : {Bool.and(_, Spec.waits_from(Impl.waits2(rest), c, bound)) == True{} : Bool}
      wf_waits2(rest, c, bound, h)

def sbw_sig_c1(+G: Nat, +H: Nat, +I: Nat, +d: Nat, +g: Nat)
  -> {Spec.sigs_below(Impl.events(G, H, I, d), Spec.C1{g}, 1n) == True{} : Bool}:
  %sb_sigs1_sym(Part.mainloop(Impl.s1(G, H, I, d), Impl.e1(G, H, I, d), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, d), Impl.waits2(Impl.waits(G, H, I, d))),
      Spec.C1{g}, 0n) : {_ == True{} : Bool}
  sb_waits2(Impl.waits(G, H, I, d), Spec.C1{g}, 1n)

def sbw_wait_c1(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +g: Nat)
  -> {Spec.waits_from(Impl.events(G, H, I, b), Spec.C1{g}, 1n) == True{} : Bool}:
  +fb = Impl.fin_pair(G, H, I, b)
  +np = Impl.pairs(I)
  +wb = Impl.waits(G, H, I, b)
  %wf_sigs1_sym(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(np, fb, Impl.waits2(wb)), Spec.C1{g}, 1n) : {_ == True{} : Bool}
  %or_true_r(Bool.not(Nat.is_eq(fb, g)))
    : {Bool.and(_, Bool.and(Bool.or(Bool.not(Nat.is_eq(Nat.add(np, fb), g)), True{}),
      Spec.waits_from(Impl.waits2(wb), Spec.C1{g}, 1n))) == True{} : Bool}
  %or_true_r(Bool.not(Nat.is_eq(Nat.add(np, fb), g)))
    : {Bool.and(_, Spec.waits_from(Impl.waits2(wb), Spec.C1{g}, 1n)) == True{} : Bool}
  wf_waits2(wb, Spec.C1{g}, 1n, {==})

def sbw_sig_c2(+G: Nat, +H: Nat, +I: Nat, +d: Nat, +p: Nat)
  -> {Spec.sigs_below(Impl.events(G, H, I, d), Spec.C2{p}, 2n) == True{} : Bool}:
  +fd = Impl.fin_pair(G, H, I, d)
  +wd = Impl.waits(G, H, I, d)
  %sb_sigs1_sym(Part.mainloop(Impl.s1(G, H, I, d), Impl.e1(G, H, I, d), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), fd, Impl.waits2(wd)), Spec.C2{p}, 1n) : {_ == True{} : Bool}
  %or_true_r(Bool.not(Nat.is_eq(fd, p)))
    : {Bool.and(_, Spec.sigs_below(Impl.waits2(wd), Spec.C2{p}, 2n)) == True{} : Bool}
  sb_waits2(wd, Spec.C2{p}, 2n)

def sbw_wait_c2(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat)
  -> {Spec.waits_from(Impl.events(G, H, I, b), Spec.C2{p}, 2n) == True{} : Bool}:
  %wf_sigs1_sym(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, b), Impl.waits2(Impl.waits(G, H, I, b))),
      Spec.C2{p}, 2n) : {_ == True{} : Bool}
  wf_waits2(Impl.waits(G, H, I, b), Spec.C2{p}, 2n, {==})

def Laws.signals_before_waits(G, H, I, b, d, c):
  match c:
    case Spec.C1{g}:
      (sbw_sig_c1(G, H, I, d, g), sbw_wait_c1(G, H, I, b, g))
    case Spec.C2{p}:
      (sbw_sig_c2(G, H, I, d, p), sbw_wait_c2(G, H, I, b, p))

# ==== small Bool / Nat helpers ====

def or_l_true(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def or_r_true(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def or_false(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool})
  -> {a == False{} : Bool} & {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool} & {b == False{} : Bool}, PP.ar_true_false(h))
    case False{}:
      ({==}, h)

def bit_mul_one(v: Bool) -> {Spec.bit(v) == Nat.mul(Spec.bit(v), 1n) : Nat}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def add_one(+c: Nat) -> {1n+c == Nat.add(c, 1n) : Nat}:
  Equal.trans(Nat, 1n+c, 1n+Nat.add(c, 0n), Nat.add(c, 1n),
    Equal.cong(Nat, Nat, t => 1n+t, c, Nat.add(c, 0n),
      Equal.sym(Nat, Nat.add(c, 0n), c, PP.ar_add_zero_r(c))),
    Equal.sym(Nat, Nat.add(c, 1n), 1n+Nat.add(c, 0n), PP.ar_add_succ_r(c, 0n)))

# np + x != p when p < np.
def eq_add_lt(+np: Nat, +x: Nat, +p: Nat, lt: {Nat.is_lt(p, np) == True{} : Bool})
  -> {False{} == Nat.is_eq(Nat.add(np, x), p) : Bool}:
  match np:
    case 0n:
      Empty.absurd({False{} == Nat.is_eq(Nat.add(0n, x), p) : Bool},
        PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, PP.ar_h_lt_zero(p)), lt)))
    case 1n+n:
      match p:
        case 0n:
          {==}
        case 1n+q:
          eq_add_lt(n, x, q, lt)

# f != np + p when f < np.
def eq_lt_add(+f: Nat, +np: Nat, +p: Nat, lt: {Nat.is_lt(f, np) == True{} : Bool})
  -> {False{} == Nat.is_eq(f, Nat.add(np, p)) : Bool}:
  match f:
    case 0n:
      match np:
        case 0n:
          Empty.absurd({False{} == Nat.is_eq(0n, Nat.add(0n, p)) : Bool}, PP.ar_false_true(lt))
        case 1n+n:
          {==}
    case 1n+e:
      match np:
        case 0n:
          Empty.absurd({False{} == Nat.is_eq(1n+e, Nat.add(0n, p)) : Bool},
            PP.ar_false_true(lt))
        case 1n+n:
          eq_lt_add(e, n, p, lt)

def eq_add_cancel(+np: Nat, +a: Nat, +b: Nat)
  -> {Nat.is_eq(a, b) == Nat.is_eq(Nat.add(np, a), Nat.add(np, b)) : Bool}:
  match np:
    case 0n:
      {==}
    case 1n+n:
      eq_add_cancel(n, a, b)

# ==== (2) counters ====

def sa_sigs1_c2(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +p: Nat)
  -> {Spec.sig_amount(rest, Spec.C2{p}) ==
    Spec.sig_amount(Impl.sigs1(evs, rest), Spec.C2{p}) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          sa_sigs1_c2(more, rest, p)
        case PSpec.Flush{g}:
          sa_sigs1_c2(more, rest, p)

def sa_waits2(ws: List<&2, Nat>, +c: Spec.Ctr)
  -> {0n == Spec.sig_amount(Impl.waits2(ws), c) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case q <> rest:
      sa_waits2(rest, c)

def wa_sigs1(evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +c: Spec.Ctr)
  -> {Spec.wait_amount(rest, c) == Spec.wait_amount(Impl.sigs1(evs, rest), c) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          wa_sigs1(more, rest, c)
        case PSpec.Flush{g}:
          wa_sigs1(more, rest, c)

def wa_waits2_c1(ws: List<&2, Nat>, +g: Nat)
  -> {0n == Spec.wait_amount(Impl.waits2(ws), Spec.C1{g}) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case q <> rest:
      wa_waits2_c1(rest, g)

def wa_waits2_occ(ws: List<&2, Nat>, +p: Nat)
  -> {Spec.occurs(ws, p) == Spec.wait_amount(Impl.waits2(ws), Spec.C2{p}) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case q <> rest:
      %wa_waits2_occ(rest, p)
        : {Nat.add(Spec.bit(Nat.is_eq(q, p)), Spec.occurs(rest, p)) ==
          Nat.add(Nat.mul(Spec.bit(Nat.is_eq(q, p)), 1n), _) : Nat}
      %bit_mul_one(Nat.is_eq(q, p))
        : {Nat.add(Spec.bit(Nat.is_eq(q, p)), Spec.occurs(rest, p)) ==
          Nat.add(_, Spec.occurs(rest, p)) : Nat}
      {==}

# Block b signals cnt2[p] 8 times iff its finish pair is p.
def blk_sig_c2(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat)
  -> {Nat.mul(Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, b), p)), 8n) ==
    Spec.sig_amount(Impl.events(G, H, I, b), Spec.C2{p}) : Nat}:
  +ws = Impl.waits(G, H, I, b)
  +M = Nat.mul(Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, b), p)), 8n)
  %sa_sigs1_c2(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, b), Impl.waits2(ws)), p)
    : {M == _ : Nat}
  %sa_waits2(ws, Spec.C2{p}) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def st_c2(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat)
  -> {Nat.mul(Impl.fin_count(G, H, I, n, p), 8n) ==
    Laws.sig_total(G, H, I, n, Spec.C2{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, m), p))
      +C = Impl.fin_count(G, H, I, m, p)
      %st_c2(G, H, I, m, p)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, Spec.sig_amount(Impl.events(G, H, I, m), Spec.C2{p})) : Nat}
      %blk_sig_c2(G, H, I, m, p)
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.finish_signals(G, H, I, p):
  Equal.trans(Nat, Laws.sig_total(G, H, I, G, Spec.C2{p}),
    Nat.mul(Impl.fin_count(G, H, I, G, p), 8n), Impl.exp2(G, H, I, p),
    Equal.sym(Nat, Nat.mul(Impl.fin_count(G, H, I, G, p), 8n),
      Laws.sig_total(G, H, I, G, Spec.C2{p}), st_c2(G, H, I, G, p)),
    PP.ar_mul_comm(Impl.fin_count(G, H, I, G, p), 8n))

# Block b waits on cnt1[p] (p < NP) with its 8 finisher warps iff its finish pair is p.
def blk_wait_c1(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat,
    lt: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool})
  -> {Nat.mul(Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, b), p)), 8n) ==
    Spec.wait_amount(Impl.events(G, H, I, b), Spec.C1{p}) : Nat}:
  +ws = Impl.waits(G, H, I, b)
  +fb = Impl.fin_pair(G, H, I, b)
  +np = Impl.pairs(I)
  +M = Nat.mul(Spec.bit(Nat.is_eq(fb, p)), 8n)
  %wa_sigs1(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(np, fb, Impl.waits2(ws)), Spec.C1{p})
    : {M == _ : Nat}
  %eq_add_lt(np, fb, p, lt)
    : {M == Nat.add(M, Nat.add(Nat.mul(Spec.bit(_), 8n),
      Spec.wait_amount(Impl.waits2(ws), Spec.C1{p}))) : Nat}
  %wa_waits2_c1(ws, p) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def wt_c1(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat,
    +lt: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool})
  -> {Nat.mul(Impl.fin_count(G, H, I, n, p), 8n) ==
    Laws.wait_total(G, H, I, n, Spec.C1{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, m), p))
      +C = Impl.fin_count(G, H, I, m, p)
      %wt_c1(G, H, I, m, p, lt)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, Spec.wait_amount(Impl.events(G, H, I, m), Spec.C1{p})) : Nat}
      %blk_wait_c1(G, H, I, m, p, lt)
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.gate_waiters(G, H, I, p, pair):
  Equal.trans(Nat, Laws.wait_total(G, H, I, G, Spec.C1{p}),
    Nat.mul(Impl.fin_count(G, H, I, G, p), 8n), Impl.wait1(G, H, I, p),
    Equal.sym(Nat, Nat.mul(Impl.fin_count(G, H, I, G, p), 8n),
      Laws.wait_total(G, H, I, G, Spec.C1{p}), wt_c1(G, H, I, G, p, pair)),
    PP.ar_mul_comm(Impl.fin_count(G, H, I, G, p), 8n))

# I = (I / 512) * 512 gives KT2 = I / 16 = (I / 512) * 32.
def kt2_pairs(+I: Nat, grp: {Nat.mod(I, 512n) == 0n : Nat})
  -> {Impl.kt2(I) == Nat.mul(Impl.pairs(I), 32n) : Nat}:
  +Q = Nat.div(I, 512n)
  %Equal.trans(Nat, Nat.mul(Q, 512n), Nat.add(Nat.mul(Q, 512n), 0n), I,
      Equal.sym(Nat, Nat.add(Nat.mul(Q, 512n), 0n), Nat.mul(Q, 512n),
        PP.ar_add_zero_r(Nat.mul(Q, 512n))),
      (%grp : {Nat.add(Nat.mul(Q, 512n), _) == I : Nat}
        PP.ard_dm_eq(I, 512n, {==})))
    : {Nat.div(_, 16n) == Nat.mul(Q, 32n) : Nat}
  %Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(Q, 32n), 16n), 0n), Nat.mul(Nat.mul(Q, 32n), 16n),
      Nat.mul(Q, 512n), PP.ar_add_zero_r(Nat.mul(Nat.mul(Q, 32n), 16n)),
      PP.ar_mul_assoc(Q, 32n, 16n))
    : {Nat.div(_, 16n) == Nat.mul(Q, 32n) : Nat}
  PP.ard_fst({Nat.div(Nat.add(Nat.mul(Nat.mul(Q, 32n), 16n), 0n), 16n) == Nat.mul(Q, 32n) : Nat},
    {Nat.mod(Nat.add(Nat.mul(Nat.mul(Q, 32n), 16n), 0n), 16n) == 0n : Nat},
    PP.ar_div_unique(Nat.mul(Q, 32n), 0n, 16n, {==}))

# Every finish pair is a real pair: fin_pair(b) < NP.
def fp_lt(+G: Nat, +H: Nat, +I: Nat, +b: Nat, shaped: {Nat.is_le(128n, I) == True{} : Bool},
    grp: {Nat.mod(I, 512n) == 0n : Nat})
  -> {Nat.is_lt(Impl.fin_pair(G, H, I, b), Impl.pairs(I)) == True{} : Bool}:
  +s = Impl.s2(G, H, I, b)
  +y = Nat.mod(s, Impl.kt2(I))
  %Equal.sym(Bool, Nat.is_lt(Nat.div(y, 32n), Impl.pairs(I)),
      Nat.is_lt(y, Nat.mul(Impl.pairs(I), 32n)), PP.ar_div_lt(Impl.pairs(I), y, 32n, {==}))
    : {_ == True{} : Bool}
  %kt2_pairs(I, grp) : {Nat.is_lt(y, _) == True{} : Bool}
  PP.ard_dm_lt(s, Impl.kt2(I), PP.p2_kt_pos(I, shaped))

# Block b waits on cnt1[NP + p] with its 8 finisher warps iff its finish pair is p.
def blk_wait_up(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat,
    fplt: {Nat.is_lt(Impl.fin_pair(G, H, I, b), Impl.pairs(I)) == True{} : Bool})
  -> {Nat.mul(Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, b), p)), 8n) ==
    Spec.wait_amount(Impl.events(G, H, I, b), Spec.C1{Nat.add(Impl.pairs(I), p)}) : Nat}:
  +ws = Impl.waits(G, H, I, b)
  +fb = Impl.fin_pair(G, H, I, b)
  +np = Impl.pairs(I)
  +M = Nat.mul(Spec.bit(Nat.is_eq(fb, p)), 8n)
  %wa_sigs1(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(np, fb, Impl.waits2(ws)), Spec.C1{Nat.add(np, p)})
    : {M == _ : Nat}
  %eq_lt_add(fb, np, p, fplt)
    : {M == Nat.add(Nat.mul(Spec.bit(_), 8n),
      Nat.add(Nat.mul(Spec.bit(Nat.is_eq(Nat.add(np, fb), Nat.add(np, p))), 8n),
        Spec.wait_amount(Impl.waits2(ws), Spec.C1{Nat.add(np, p)}))) : Nat}
  %eq_add_cancel(np, fb, p)
    : {M == Nat.add(Nat.mul(Spec.bit(_), 8n),
      Spec.wait_amount(Impl.waits2(ws), Spec.C1{Nat.add(np, p)})) : Nat}
  %wa_waits2_c1(ws, Nat.add(np, p)) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

def wt_up(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat,
    +shaped: {Nat.is_le(128n, I) == True{} : Bool}, +grp: {Nat.mod(I, 512n) == 0n : Nat})
  -> {Nat.mul(Impl.fin_count(G, H, I, n, p), 8n) ==
    Laws.wait_total(G, H, I, n, Spec.C1{Nat.add(Impl.pairs(I), p)}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +B = Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, m), p))
      +C = Impl.fin_count(G, H, I, m, p)
      %wt_up(G, H, I, m, p, shaped, grp)
        : {Nat.mul(Nat.add(C, B), 8n) ==
          Nat.add(_, Spec.wait_amount(Impl.events(G, H, I, m),
            Spec.C1{Nat.add(Impl.pairs(I), p)})) : Nat}
      %blk_wait_up(G, H, I, m, p, fp_lt(G, H, I, m, shaped, grp))
        : {Nat.mul(Nat.add(C, B), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, B, 8n)

def Laws.up_waiters(G, H, I, p, shaped, groups):
  Equal.trans(Nat, Laws.wait_total(G, H, I, G, Spec.C1{Nat.add(Impl.pairs(I), p)}),
    Nat.mul(Impl.fin_count(G, H, I, G, p), 8n), Impl.wait1(G, H, I, p),
    Equal.sym(Nat, Nat.mul(Impl.fin_count(G, H, I, G, p), 8n),
      Laws.wait_total(G, H, I, G, Spec.C1{Nat.add(Impl.pairs(I), p)}),
      wt_up(G, H, I, G, p, shaped, groups)),
    PP.ar_mul_comm(Impl.fin_count(G, H, I, G, p), 8n))

# ==== (2) wait lists: no duplicates, full coverage ====

def memb_to(+xs: List<&2, Nat>, -p: Nat, -q: Nat, pq: {p == q : Nat},
    h: {Spec.member(xs, p) == True{} : Bool}) -> {Spec.member(xs, q) == True{} : Bool}:
  %pq : {Spec.member(xs, _) == True{} : Bool}
  h

def memb_to_f(+xs: List<&2, Nat>, -p: Nat, -q: Nat, pq: {p == q : Nat},
    h: {Spec.member(xs, p) == False{} : Bool}) -> {Spec.member(xs, q) == False{} : Bool}:
  %pq : {Spec.member(xs, _) == False{} : Bool}
  h

def fresh_step(v: Bool, +p: Nat, +x: Nat, +seen: List<&2, Nat>, +go2: List<&2, Nat>,
    ev: {Spec.member(seen, p) == v : Bool}, h: {Spec.member(seen, x) == True{} : Bool},
    w: Bool, ew: {Nat.is_eq(p, x) == w : Bool},
    ih: {Spec.member(go2, x) == False{} : Bool})
  -> {Spec.member(Impl.waits.pick(v, p, go2), x) == False{} : Bool}:
  match v:
    case True{}:
      ih
    case False{}:
      match w:
        case True{}:
          Empty.absurd({Spec.member(p <> go2, x) == False{} : Bool},
            PP.ar_false_true(Equal.trans(Bool, False{}, Spec.member(seen, p), True{},
              Equal.sym(Bool, Spec.member(seen, p), False{}, ev),
              memb_to(seen, x, p, Equal.sym(Nat, p, x, PP.ar_eq_true(p, x, ew)), h))))
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(p, x), False{}, ew)
            : {Bool.or(_, Spec.member(go2, x)) == False{} : Bool}
          ih

# The pairs emitted from a scan are never already in `seen`.
def fresh_go(+I: Nat, +left: Nat, +it: Nat, +seen: List<&2, Nat>, +x: Nat,
    +h: {Spec.member(seen, x) == True{} : Bool})
  -> {Spec.member(Impl.waits.go(I, left, it, seen), x) == False{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      +p = Impl.pair_of(I, it)
      fresh_step(Spec.member(seen, p), p, x, seen, Impl.waits.go(I, r, 1n+it, p <> seen), {==}, h,
        Nat.is_eq(p, x), {==},
        fresh_go(I, r, 1n+it, p <> seen, x, or_r_true(Nat.is_eq(p, x), Spec.member(seen, x), h)))

def nd_step(v: Bool, +p: Nat, +go2: List<&2, Nat>, ih: {Spec.nodup(go2) == True{} : Bool},
    fr: {Spec.member(go2, p) == False{} : Bool})
  -> {Spec.nodup(Impl.waits.pick(v, p, go2)) == True{} : Bool}:
  match v:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Spec.member(go2, p), False{}, fr)
        : {Bool.and(Bool.not(_), Spec.nodup(go2)) == True{} : Bool}
      ih

def nodup_go(+I: Nat, +left: Nat, +it: Nat, +seen: List<&2, Nat>)
  -> {Spec.nodup(Impl.waits.go(I, left, it, seen)) == True{} : Bool}:
  match left:
    case 0n:
      {==}
    case 1n+r:
      +p = Impl.pair_of(I, it)
      nd_step(Spec.member(seen, p), p, Impl.waits.go(I, r, 1n+it, p <> seen),
        nodup_go(I, r, 1n+it, p <> seen),
        fresh_go(I, r, 1n+it, p <> seen, p,
          or_l_true(Nat.is_eq(p, p), Spec.member(seen, p), PP.ar_eq_refl(p))))

def Laws.waits_nodup(G, H, I, b):
  nodup_go(I, Impl.n2(G, H, I, b), Impl.s2(G, H, I, b), Nil{})

def cov0(v: Bool, +p: Nat, +go2: List<&2, Nat>)
  -> {Bool.or(v, Spec.member(Impl.waits.pick(v, p, go2), p)) == True{} : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(p, p), True{}, PP.ar_eq_refl(p))
        : {Bool.or(_, Spec.member(go2, p)) == True{} : Bool}
      {==}

def covs(v: Bool, +p: Nat, +q: Nat, +seen: List<&2, Nat>, +go2: List<&2, Nat>,
    ev: {Spec.member(seen, p) == v : Bool}, w: Bool, ew: {Nat.is_eq(p, q) == w : Bool},
    ih: {Bool.or(Bool.or(w, Spec.member(seen, q)), Spec.member(go2, q)) == True{} : Bool})
  -> {Bool.or(Spec.member(seen, q), Spec.member(Impl.waits.pick(v, p, go2), q)) == True{} : Bool}:
  match v:
    case True{}:
      match w:
        case True{}:
          %Equal.sym(Bool, Spec.member(seen, q), True{},
              memb_to(seen, p, q, PP.ar_eq_true(p, q, ew), ev))
            : {Bool.or(_, Spec.member(go2, q)) == True{} : Bool}
          {==}
        case False{}:
          ih
    case False{}:
      match w:
        case True{}:
          %Equal.sym(Bool, Nat.is_eq(p, q), True{}, ew)
            : {Bool.or(Spec.member(seen, q), Bool.or(_, Spec.member(go2, q))) == True{} : Bool}
          %or_true_r(Spec.member(seen, q)) : {_ == True{} : Bool}
          {==}
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(p, q), False{}, ew)
            : {Bool.or(Spec.member(seen, q), Bool.or(_, Spec.member(go2, q))) == True{} : Bool}
          ih

# Every iteration it + j (j < left) of a scan has its pair in `seen` or in the scan's output.
def cover_go(+I: Nat, +left: Nat, +it: Nat, +seen: List<&2, Nat>, +j: Nat,
    lt: {Nat.is_lt(j, left) == True{} : Bool})
  -> {Bool.or(Spec.member(seen, Impl.pair_of(I, Nat.add(it, j))),
    Spec.member(Impl.waits.go(I, left, it, seen), Impl.pair_of(I, Nat.add(it, j)))) ==
    True{} : Bool}:
  match left:
    case 0n:
      Empty.absurd({Bool.or(Spec.member(seen, Impl.pair_of(I, Nat.add(it, j))),
          Spec.member(Nil{}, Impl.pair_of(I, Nat.add(it, j)))) == True{} : Bool},
        PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{},
          Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, PP.ar_h_lt_zero(j)), lt)))
    case 1n+r:
      match j:
        case 0n:
          +p = Impl.pair_of(I, it)
          %Equal.sym(Nat, Nat.add(it, 0n), it, PP.ar_add_zero_r(it))
            : {Bool.or(Spec.member(seen, Impl.pair_of(I, _)),
              Spec.member(Impl.waits.go(I, 1n+r, it, seen), Impl.pair_of(I, _))) == True{} : Bool}
          cov0(Spec.member(seen, p), p, Impl.waits.go(I, r, 1n+it, p <> seen))
        case 1n+k:
          +p = Impl.pair_of(I, it)
          +q = Impl.pair_of(I, Nat.add(1n+it, k))
          %Equal.sym(Nat, Nat.add(it, 1n+k), 1n+Nat.add(it, k), PP.ar_add_succ_r(it, k))
            : {Bool.or(Spec.member(seen, Impl.pair_of(I, _)),
              Spec.member(Impl.waits.go(I, 1n+r, it, seen), Impl.pair_of(I, _))) == True{} : Bool}
          covs(Spec.member(seen, p), p, q, seen, Impl.waits.go(I, r, 1n+it, p <> seen), {==},
            Nat.is_eq(p, q), {==}, cover_go(I, r, 1n+it, p <> seen, k, lt))

def Laws.waits_cover(G, H, I, b, x, lo, hi):
  +l = lo
  +s = Impl.s2(G, H, I, b)
  +n = Impl.n2(G, H, I, b)
  +j = Nat.sub(x, s)
  %PP.ar_sub_add(x, s, l)
    : {Spec.member(Impl.waits(G, H, I, b), Impl.pair_of(I, _)) == True{} : Bool}
  cover_go(I, n, s, Nil{}, j,
    (%PP.ar_lt_add_cancel(s, j, n) : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.add(s, j), x, PP.ar_sub_add(x, s, l))
        : {Nat.is_lt(_, Nat.add(s, n)) == True{} : Bool}
      hi))

# ==== (2) cnt2 waiters ====

def occ_absent(+xs: List<&2, Nat>, +p: Nat, +h: {Spec.member(xs, p) == False{} : Bool})
  -> {0n == Spec.occurs(xs, p) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %Equal.sym(Bool, Nat.is_eq(y, p), False{},
          PP.ard_fst({Nat.is_eq(y, p) == False{} : Bool}, {Spec.member(rest, p) == False{} : Bool},
            or_false(Nat.is_eq(y, p), Spec.member(rest, p), h)))
        : {0n == Nat.add(Spec.bit(_), Spec.occurs(rest, p)) : Nat}
      occ_absent(rest, p,
        PP.ard_snd({Nat.is_eq(y, p) == False{} : Bool}, {Spec.member(rest, p) == False{} : Bool},
          or_false(Nat.is_eq(y, p), Spec.member(rest, p), h)))

def occ_step(v: Bool, +y: Nat, +p: Nat, +rest: List<&2, Nat>, ev: {Nat.is_eq(y, p) == v : Bool},
    ab: {Spec.member(rest, y) == False{} : Bool},
    ih: {Spec.bit(Spec.member(rest, p)) == Spec.occurs(rest, p) : Nat})
  -> {Spec.bit(Bool.or(v, Spec.member(rest, p))) == Nat.add(Spec.bit(v), Spec.occurs(rest, p)) : Nat}:
  match v:
    case True{}:
      %occ_absent(rest, p, memb_to_f(rest, y, p, PP.ar_eq_true(y, p, ev), ab))
        : {1n == Nat.add(1n, _) : Nat}
      {==}
    case False{}:
      ih

# In a duplicate-free list, occurrences are membership.
def occ_member(+ws: List<&2, Nat>, +p: Nat, nd: {Spec.nodup(ws) == True{} : Bool})
  -> {Spec.bit(Spec.member(ws, p)) == Spec.occurs(ws, p) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case y <> rest:
      +d = nd
      occ_step(Nat.is_eq(y, p), y, p, rest, {==},
        PP.p1l_not_true(Spec.member(rest, y),
          PP.ar_and_l(Bool.not(Spec.member(rest, y)), Spec.nodup(rest), d)),
        occ_member(rest, p, PP.ar_and_r(Bool.not(Spec.member(rest, y)), Spec.nodup(rest), d)))

def blk_wait_c2(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat)
  -> {Spec.bit(Spec.member(Impl.waits(G, H, I, b), p)) ==
    Spec.wait_amount(Impl.events(G, H, I, b), Spec.C2{p}) : Nat}:
  +ws = Impl.waits(G, H, I, b)
  %wa_sigs1(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, b), Impl.waits2(ws)), Spec.C2{p})
    : {Spec.bit(Spec.member(ws, p)) == _ : Nat}
  %wa_waits2_occ(ws, p) : {Spec.bit(Spec.member(ws, p)) == _ : Nat}
  occ_member(ws, p, Laws.waits_nodup(G, H, I, b))

def wt_c2(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat)
  -> {Impl.wait_blocks(G, H, I, n, p) == Laws.wait_total(G, H, I, n, Spec.C2{p}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +W = Impl.wait_blocks(G, H, I, m, p)
      %wt_c2(G, H, I, m, p)
        : {Nat.add(W, Spec.bit(Spec.member(Impl.waits(G, H, I, m), p))) ==
          Nat.add(_, Spec.wait_amount(Impl.events(G, H, I, m), Spec.C2{p})) : Nat}
      %blk_wait_c2(G, H, I, m, p)
        : {Nat.add(W, Spec.bit(Spec.member(Impl.waits(G, H, I, m), p))) == Nat.add(W, _) : Nat}
      {==}

def Laws.pair_waiters(G, H, I, p):
  Equal.sym(Nat, Impl.wait2(G, H, I, p), Laws.wait_total(G, H, I, G, Spec.C2{p}),
    wt_c2(G, H, I, G, p))

# ==== (6) finish jobs and ranks ====

def fh_step(v: Bool, +G: Nat, +H: Nat, +I: Nat, +b: Nat, +p: Nat, +x: Nat, +m: Nat,
    ev: {Nat.is_eq(Impl.fin_pair(G, H, I, b), p) == v : Bool},
    ih: {Impl.finisher_hits(G, H, I, b, p, x, m) ==
      Part.job_hits(Impl.fin_count(G, H, I, b, p), x, Impl.fin_count(G, H, I, G, p),
        Nat.mul(4n, m)) : Nat})
  -> {Nat.add(Impl.finisher_hits(G, H, I, b, p, x, m),
      Nat.mul(Spec.bit(v), Part.warp_hits(8n, Impl.fin_rank(G, H, I, b), x, Impl.fin_cnt(G, H, I, b),
        Nat.mul(4n, m)))) ==
    Part.job_hits(Nat.add(Impl.fin_count(G, H, I, b, p), Spec.bit(v)), x,
      Impl.fin_count(G, H, I, G, p), Nat.mul(4n, m)) : Nat}:
  match v:
    case True{}:
      +J = Nat.mul(4n, m)
      +K = Impl.fin_count(G, H, I, G, p)
      +C = Impl.fin_count(G, H, I, b, p)
      +JH = Part.job_hits(C, x, K, J)
      %Equal.sym(Nat, Impl.fin_pair(G, H, I, b), p,
          PP.ar_eq_true(Impl.fin_pair(G, H, I, b), p, ev))
        : {Nat.add(Impl.finisher_hits(G, H, I, b, p, x, m),
            Nat.mul(1n, Part.warp_hits(8n, Impl.fin_count(G, H, I, b, _), x,
              Impl.fin_count(G, H, I, G, _), J))) ==
          Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %Equal.sym(Nat, Impl.finisher_hits(G, H, I, b, p, x, m), JH, ih)
        : {Nat.add(_, Nat.mul(1n, Part.warp_hits(8n, C, x, K, J))) ==
          Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.mul(1n, Part.warp_hits(8n, C, x, K, J)), Part.warp_hits(8n, C, x, K, J),
          PP.ar_mul_one_l(Part.warp_hits(8n, C, x, K, J)))
        : {Nat.add(JH, _) == Part.job_hits(Nat.add(C, 1n), x, K, J) : Nat}
      %add_one(C) : {Nat.add(JH, Part.warp_hits(8n, C, x, K, J)) == Part.job_hits(_, x, K, J) : Nat}
      {==}
    case False{}:
      +J = Nat.mul(4n, m)
      +K = Impl.fin_count(G, H, I, G, p)
      +C = Impl.fin_count(G, H, I, b, p)
      +JH = Part.job_hits(C, x, K, J)
      %Equal.sym(Nat, Impl.finisher_hits(G, H, I, b, p, x, m), JH, ih)
        : {Nat.add(_, 0n) == Part.job_hits(Nat.add(C, 0n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.add(JH, 0n), JH, PP.ar_add_zero_r(JH))
        : {_ == Part.job_hits(Nat.add(C, 0n), x, K, J) : Nat}
      %Equal.sym(Nat, Nat.add(C, 0n), C, PP.ar_add_zero_r(C))
        : {JH == Part.job_hits(_, x, K, J) : Nat}
      {==}

# Reindexing: the finisher warps of pair p's blocks b < n are the v2 finish loop's (block, warp)
# pairs of the ranks 0 .. fin_count(n, p) - 1 over a k_p-block grid.
def fh_re(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat, +x: Nat, +m: Nat)
  -> {Impl.finisher_hits(G, H, I, n, p, x, m) ==
    Part.job_hits(Impl.fin_count(G, H, I, n, p), x, Impl.fin_count(G, H, I, G, p),
      Nat.mul(4n, m)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      fh_step(Nat.is_eq(Impl.fin_pair(G, H, I, b), p), G, H, I, b, p, x, m, {==},
        fh_re(G, H, I, b, p, x, m))

def Laws.finish_jobs_once(G, H, I, p, m, x, finished):
  Equal.trans(Nat, Impl.finisher_hits(G, H, I, G, p, x, m),
    Part.job_hits(Impl.fin_count(G, H, I, G, p), x, Impl.fin_count(G, H, I, G, p), Nat.mul(4n, m)),
    PSpec.bit(Nat.is_lt(x, Nat.mul(4n, m))),
    fh_re(G, H, I, G, p, x, m),
    PLaws.finish_jobs_once(x, Impl.fin_count(G, H, I, G, p), Nat.mul(4n, m), finished))

def fc_mono(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +k: Nat, +q: Nat)
  -> {Nat.is_le(Impl.fin_count(G, H, I, b, q), Impl.fin_count(G, H, I, Nat.add(b, k), q)) ==
    True{} : Bool}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(b, 0n), b, PP.ar_add_zero_r(b))
        : {Nat.is_le(Impl.fin_count(G, H, I, b, q), Impl.fin_count(G, H, I, _, q)) == True{} : Bool}
      PP.ar_le_refl(Impl.fin_count(G, H, I, b, q))
    case 1n+j:
      +C = Impl.fin_count(G, H, I, Nat.add(b, j), q)
      %Equal.sym(Nat, Nat.add(b, 1n+j), 1n+Nat.add(b, j), PP.ar_add_succ_r(b, j))
        : {Nat.is_le(Impl.fin_count(G, H, I, b, q), Impl.fin_count(G, H, I, _, q)) == True{} : Bool}
      PP.ar_le_trans(Impl.fin_count(G, H, I, b, q), C,
        Nat.add(C, Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, Nat.add(b, j)), q))),
        fc_mono(G, H, I, b, j, q),
        PP.ar_le_add_r(C, Spec.bit(Nat.is_eq(Impl.fin_pair(G, H, I, Nat.add(b, j)), q))))

# Block b's rank is below the count of its finish pair among blocks < n, for b < n.
def rank_below(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +n: Nat, lt: {Nat.is_lt(b, n) == True{} : Bool})
  -> {Nat.is_lt(Impl.fin_count(G, H, I, b, Impl.fin_pair(G, H, I, b)),
    Impl.fin_count(G, H, I, n, Impl.fin_pair(G, H, I, b))) == True{} : Bool}:
  +q = Impl.fin_pair(G, H, I, b)
  +c = Impl.fin_count(G, H, I, b, q)
  +K = Impl.fin_count(G, H, I, n, q)
  +le1b = Equal.trans(Bool, Nat.is_le(1n+b, n), Nat.is_lt(b, n), True{},
    Equal.sym(Bool, Nat.is_lt(b, n), Nat.is_le(1n+b, n), PP.ar_lt_succ_le(b, n)), lt)
  %Equal.sym(Bool, Nat.is_lt(c, K), Nat.is_le(1n+c, K), PP.ar_lt_succ_le(c, K))
    : {_ == True{} : Bool}
  PP.ar_le_trans(1n+c, Impl.fin_count(G, H, I, 1n+b, q), K,
    (%Equal.sym(Bool, Nat.is_eq(q, q), True{}, PP.ar_eq_refl(q))
        : {Nat.is_le(1n+c, Nat.add(c, Spec.bit(_))) == True{} : Bool}
      %add_one(c) : {Nat.is_le(1n+c, _) == True{} : Bool}
      PP.ar_le_refl(1n+c)),
    (%PP.ar_sub_add(n, 1n+b, le1b)
        : {Nat.is_le(Impl.fin_count(G, H, I, 1n+b, q), Impl.fin_count(G, H, I, _, q)) ==
          True{} : Bool}
      fc_mono(G, H, I, 1n+b, Nat.sub(n, 1n+b), q)))

def Laws.fin_rank_bound(G, H, I, b, inside):
  rank_below(G, H, I, b, G, inside)

def rank_lt(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +c: Nat, lt: {Nat.is_lt(b, c) == True{} : Bool},
    pair: {Impl.fin_pair(G, H, I, b) == Impl.fin_pair(G, H, I, c) : Nat})
  -> {Nat.is_lt(Impl.fin_rank(G, H, I, b), Impl.fin_rank(G, H, I, c)) == True{} : Bool}:
  %pair
    : {Nat.is_lt(Impl.fin_count(G, H, I, b, Impl.fin_pair(G, H, I, b)),
      Impl.fin_count(G, H, I, c, _)) == True{} : Bool}
  rank_below(G, H, I, b, c, lt)

def lt_self_of(+r: Nat, -s: Nat, same: {r == s : Nat}, h: {Nat.is_lt(r, s) == True{} : Bool})
  -> Empty:
  PP.ard_lt_self(r, (%Equal.sym(Nat, r, s, same) : {Nat.is_lt(r, _) == True{} : Bool}
    h))

def unique_tri(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +c: Nat, v: Bool,
    ev: {Nat.is_lt(b, c) == v : Bool}, w: Bool, ew: {Nat.is_lt(c, b) == w : Bool},
    pair: {Impl.fin_pair(G, H, I, b) == Impl.fin_pair(G, H, I, c) : Nat},
    rank: {Impl.fin_rank(G, H, I, b) == Impl.fin_rank(G, H, I, c) : Nat}) -> {b == c : Nat}:
  match v:
    case True{}:
      Empty.absurd({b == c : Nat}, lt_self_of(Impl.fin_rank(G, H, I, b), Impl.fin_rank(G, H, I, c),
        rank, rank_lt(G, H, I, b, c, ev, pair)))
    case False{}:
      match w:
        case True{}:
          Empty.absurd({b == c : Nat},
            lt_self_of(Impl.fin_rank(G, H, I, c), Impl.fin_rank(G, H, I, b),
              Equal.sym(Nat, Impl.fin_rank(G, H, I, b), Impl.fin_rank(G, H, I, c), rank),
              rank_lt(G, H, I, c, b, ew,
                Equal.sym(Nat, Impl.fin_pair(G, H, I, b), Impl.fin_pair(G, H, I, c), pair))))
        case False{}:
          PP.ar_le_antisym(b, c,
            PP.p2_not_false(Nat.is_le(b, c), Equal.trans(Bool, Bool.not(Nat.is_le(b, c)),
              Nat.is_lt(c, b), False{},
              Equal.sym(Bool, Nat.is_lt(c, b), Bool.not(Nat.is_le(b, c)), PP.ar_lt_not_le(c, b)),
              ew)),
            PP.p2_not_false(Nat.is_le(c, b), Equal.trans(Bool, Bool.not(Nat.is_le(c, b)),
              Nat.is_lt(b, c), False{},
              Equal.sym(Bool, Nat.is_lt(b, c), Bool.not(Nat.is_le(c, b)), PP.ar_lt_not_le(b, c)),
              ev)))

def Laws.fin_rank_unique(G, H, I, b, c, pair, rank):
  unique_tri(G, H, I, b, c, Nat.is_lt(b, c), {==}, Nat.is_lt(c, b), {==}, pair, rank)

# ==== (2) cnt1 signals: 8 per contributor block, nc contributors ====

def sa_sigs1_c1(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +g: Nat)
  -> {Nat.add(Nat.mul(PSpec.flushes(evs, g), 8n), Spec.sig_amount(rest, Spec.C1{g})) ==
    Spec.sig_amount(Impl.sigs1(evs, rest), Spec.C1{g}) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{h, it}:
          sa_sigs1_c1(more, rest, g)
        case PSpec.Flush{h}:
          +B = PSpec.bit(Nat.is_eq(h, g))
          +F = PSpec.flushes(more, g)
          +R = Spec.sig_amount(rest, Spec.C1{g})
          %sa_sigs1_c1(more, rest, g)
            : {Nat.add(Nat.mul(Nat.add(B, F), 8n), R) == Nat.add(Nat.mul(B, 8n), _) : Nat}
          Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(B, F), 8n), R),
            Nat.add(Nat.add(Nat.mul(B, 8n), Nat.mul(F, 8n)), R),
            Nat.add(Nat.mul(B, 8n), Nat.add(Nat.mul(F, 8n), R)),
            Equal.cong(Nat, Nat, t => Nat.add(t, R), Nat.mul(Nat.add(B, F), 8n),
              Nat.add(Nat.mul(B, 8n), Nat.mul(F, 8n)), PP.ar_mul_add_l(B, F, 8n)),
            PP.ar_add_assoc(Nat.mul(B, 8n), Nat.mul(F, 8n), R))

# Block b signals cnt1[g] 8 times per flush of g in its phase-1 loop.
def blk_sig_c1(+G: Nat, +H: Nat, +I: Nat, +b: Nat, +g: Nat)
  -> {Nat.mul(PSpec.flushes(Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H)),
      g), 8n) == Spec.sig_amount(Impl.events(G, H, I, b), Spec.C1{g}) : Nat}:
  +ml = Part.mainloop(Impl.s1(G, H, I, b), Impl.e1(G, H, I, b), Impl.kt1(H))
  +ws = Impl.waits(G, H, I, b)
  +M = Nat.mul(PSpec.flushes(ml, g), 8n)
  %sa_sigs1_c1(ml, Impl.finish(Impl.pairs(I), Impl.fin_pair(G, H, I, b), Impl.waits2(ws)), g)
    : {M == _ : Nat}
  %sa_waits2(ws, Spec.C1{g}) : {M == Nat.add(M, _) : Nat}
  Equal.sym(Nat, Nat.add(M, 0n), M, PP.ar_add_zero_r(M))

# Blocks b < n touching phase-1 group g.
def touch_count(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +g: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(touch_count(G, H, I, b, g),
        PSpec.bit(PSpec.touches(b, g, Impl.kt1(H), Impl.total1(H, I), G)))

def st_c1(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +g: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool})
  -> {Nat.mul(touch_count(G, H, I, n, g), 8n) == Laws.sig_total(G, H, I, n, Spec.C1{g}) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +T = PSpec.bit(PSpec.touches(m, g, Impl.kt1(H), Impl.total1(H, I), G))
      +C = touch_count(G, H, I, m, g)
      +F = PSpec.flushes(Part.mainloop(Impl.s1(G, H, I, m), Impl.e1(G, H, I, m), Impl.kt1(H)), g)
      %st_c1(G, H, I, m, g, grid, shaped)
        : {Nat.mul(Nat.add(C, T), 8n) ==
          Nat.add(_, Spec.sig_amount(Impl.events(G, H, I, m), Spec.C1{g})) : Nat}
      %Equal.trans(Nat, Nat.mul(T, 8n), Nat.mul(F, 8n),
          Spec.sig_amount(Impl.events(G, H, I, m), Spec.C1{g}),
          Equal.cong(Nat, Nat, t => Nat.mul(t, 8n), T, F,
            Equal.sym(Nat, F, T, PLaws.flush_once_iff_touches(2n, I, H, G, g, m, grid, shaped))),
          blk_sig_c1(G, H, I, m, g))
        : {Nat.mul(Nat.add(C, T), 8n) == Nat.add(Nat.mul(C, 8n), _) : Nat}
      PP.ar_mul_add_l(C, T, 8n)

# Blocks b < n below a.
def ltc(+n: Nat, +a: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(ltc(b, a), PSpec.bit(Nat.is_lt(b, a)))

def ltc_all(+n: Nat, +a: Nat, h: {Nat.is_le(n, a) == True{} : Bool}) -> {ltc(n, a) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +hh = h
      %Equal.sym(Nat, ltc(m, a), m,
          ltc_all(m, a, PP.ar_le_trans(m, 1n+m, a, PP.ar_h_le_succ(m), hh)))
        : {Nat.add(_, PSpec.bit(Nat.is_lt(m, a))) == 1n+m : Nat}
      %Equal.sym(Bool, Nat.is_lt(m, a), True{},
          Equal.trans(Bool, Nat.is_lt(m, a), Nat.is_le(1n+m, a), True{}, PP.ar_lt_succ_le(m, a), hh))
        : {Nat.add(m, PSpec.bit(_)) == 1n+m : Nat}
      Equal.sym(Nat, 1n+m, Nat.add(m, 1n), add_one(m))

def ltc_full_step(v: Bool, +m: Nat, +a: Nat, ev: {Nat.is_le(a, m) == v : Bool},
    h: {Nat.is_le(a, 1n+m) == True{} : Bool},
    ih: {Nat.is_le(a, m) == True{} : Bool} -> {ltc(m, a) == a : Nat})
  -> {Nat.add(ltc(m, a), PSpec.bit(Nat.is_lt(m, a))) == a : Nat}:
  match v:
    case True{}:
      +e = ev
      %Equal.sym(Nat, ltc(m, a), a, ih(e))
        : {Nat.add(_, PSpec.bit(Nat.is_lt(m, a))) == a : Nat}
      %Equal.sym(Bool, Nat.is_lt(m, a), False{},
          Equal.trans(Bool, Nat.is_lt(m, a), Bool.not(Nat.is_le(a, m)), False{},
            PP.ar_lt_not_le(m, a),
            Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(a, m), True{}, e)))
        : {Nat.add(a, PSpec.bit(_)) == a : Nat}
      PP.ar_add_zero_r(a)
    case False{}:
      +ltm = Equal.trans(Bool, Nat.is_lt(m, a), Bool.not(Nat.is_le(a, m)), True{},
        PP.ar_lt_not_le(m, a),
        Equal.cong(Bool, Bool, t => Bool.not(t), Nat.is_le(a, m), False{}, ev))
      %Equal.sym(Nat, ltc(m, a), m, ltc_all(m, a, PP.ar_lt_le(m, a, ltm)))
        : {Nat.add(_, PSpec.bit(Nat.is_lt(m, a))) == a : Nat}
      %Equal.sym(Bool, Nat.is_lt(m, a), True{}, ltm) : {Nat.add(m, PSpec.bit(_)) == a : Nat}
      %add_one(m) : {_ == a : Nat}
      PP.ar_le_antisym(1n+m, a,
        Equal.trans(Bool, Nat.is_le(1n+m, a), Nat.is_lt(m, a), True{},
          Equal.sym(Bool, Nat.is_lt(m, a), Nat.is_le(1n+m, a), PP.ar_lt_succ_le(m, a)), ltm),
        h)

def ltc_full(+n: Nat, +a: Nat, h: {Nat.is_le(a, n) == True{} : Bool}) -> {ltc(n, a) == a : Nat}:
  match n:
    case 0n:
      match a:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({0n == 1n+q : Nat}, PP.ar_false_true(h))
    case 1n+m:
      ltc_full_step(Nat.is_le(a, m), m, a, {==}, h, hh => ltc_full(m, a, hh))

# [lo <= b <= hi] + [b < lo] == [b < hi + 1]   (lo <= hi)
def pw_step(v: Bool, +b: Nat, +lo: Nat, +hi: Nat, ev: {Nat.is_lt(b, lo) == v : Bool},
    lohi: {Nat.is_le(lo, hi) == True{} : Bool})
  -> {Nat.add(PSpec.bit(Bool.and(Nat.is_le(lo, b), Nat.is_le(b, hi))), PSpec.bit(v)) ==
    PSpec.bit(Nat.is_lt(b, 1n+hi)) : Nat}:
  match v:
    case True{}:
      +e = ev
      %Equal.sym(Bool, Nat.is_le(lo, b), False{},
          PP.p1l_not_true(Nat.is_le(lo, b), Equal.trans(Bool, Bool.not(Nat.is_le(lo, b)),
            Nat.is_lt(b, lo), True{},
            Equal.sym(Bool, Nat.is_lt(b, lo), Bool.not(Nat.is_le(lo, b)), PP.ar_lt_not_le(b, lo)),
            e)))
        : {Nat.add(PSpec.bit(Bool.and(_, Nat.is_le(b, hi))), 1n) ==
          PSpec.bit(Nat.is_lt(b, 1n+hi)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(b, 1n+hi), True{},
          PP.ar_lt_le_trans(b, lo, 1n+hi, e,
            PP.ar_le_trans(lo, hi, 1n+hi, lohi, PP.ar_h_le_succ(hi))))
        : {1n == PSpec.bit(_) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(lo, b), True{},
          PP.p2_not_false(Nat.is_le(lo, b), Equal.trans(Bool, Bool.not(Nat.is_le(lo, b)),
            Nat.is_lt(b, lo), False{},
            Equal.sym(Bool, Nat.is_lt(b, lo), Bool.not(Nat.is_le(lo, b)), PP.ar_lt_not_le(b, lo)),
            ev)))
        : {Nat.add(PSpec.bit(Bool.and(_, Nat.is_le(b, hi))), 0n) ==
          PSpec.bit(Nat.is_lt(b, 1n+hi)) : Nat}
      %Equal.sym(Nat, Nat.add(PSpec.bit(Nat.is_le(b, hi)), 0n), PSpec.bit(Nat.is_le(b, hi)),
          PP.ar_add_zero_r(PSpec.bit(Nat.is_le(b, hi))))
        : {_ == PSpec.bit(Nat.is_lt(b, 1n+hi)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(b, 1n+hi), Nat.is_le(1n+b, 1n+hi), PP.ar_lt_succ_le(b, 1n+hi))
        : {PSpec.bit(Nat.is_le(b, hi)) == PSpec.bit(_) : Nat}
      {==}

def swap4(+a: Nat, +t: Nat, +c: Nat, +l: Nat)
  -> {Nat.add(Nat.add(a, t), Nat.add(c, l)) == Nat.add(Nat.add(a, c), Nat.add(t, l)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, t), Nat.add(c, l)), Nat.add(a, Nat.add(t, Nat.add(c, l))),
    Nat.add(Nat.add(a, c), Nat.add(t, l)),
    PP.ar_add_assoc(a, t, Nat.add(c, l)),
    Equal.trans(Nat, Nat.add(a, Nat.add(t, Nat.add(c, l))), Nat.add(a, Nat.add(c, Nat.add(t, l))),
      Nat.add(Nat.add(a, c), Nat.add(t, l)),
      Equal.cong(Nat, Nat, u => Nat.add(a, u), Nat.add(t, Nat.add(c, l)),
        Nat.add(c, Nat.add(t, l)), PP.ar_h_add_swap(t, c, l)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(t, l)), Nat.add(a, Nat.add(c, Nat.add(t, l))),
        PP.ar_add_assoc(a, c, Nat.add(t, l)))))

def cc_touch(+G: Nat, +H: Nat, +I: Nat, +g: Nat, +b: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {PSpec.touches(b, g, Impl.kt1(H), Impl.total1(H, I), G) ==
    Bool.and(Nat.is_le(Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G), b),
      Nat.is_le(b, Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G))) : Bool}:
  +lo = Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G)
  +hi = Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)
  PP.ard_fst({PSpec.touches(b, g, Impl.kt1(H), Impl.total1(H, I), G) ==
      Bool.and(Nat.is_le(lo, b), Nat.is_le(b, hi)) : Bool},
    {Nat.is_le(lo, hi) == True{} : Bool} & {Nat.is_lt(hi, G) == True{} : Bool},
    PLaws.contributors_contiguous(2n, I, H, G, g, b, grid, shaped, fits, group))

def cc_rest(+G: Nat, +H: Nat, +I: Nat, +g: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {Nat.is_le(Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G),
      Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)) == True{} : Bool} &
    {Nat.is_lt(Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G), G) == True{} : Bool}:
  +lo = Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G)
  +hi = Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)
  PP.ard_snd({PSpec.touches(0n, g, Impl.kt1(H), Impl.total1(H, I), G) ==
      Bool.and(Nat.is_le(lo, 0n), Nat.is_le(0n, hi)) : Bool},
    {Nat.is_le(lo, hi) == True{} : Bool} & {Nat.is_lt(hi, G) == True{} : Bool},
    PLaws.contributors_contiguous(2n, I, H, G, g, 0n, grid, shaped, fits, group))

# touch_count(n) + [blocks below lo] == [blocks below hi + 1]
def tele(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +g: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {Nat.add(touch_count(G, H, I, n, g), ltc(n, Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G))) ==
    ltc(n, 1n+Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      +lo = Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G)
      +hi = Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)
      +C = touch_count(G, H, I, m, g)
      +T = PSpec.bit(PSpec.touches(m, g, Impl.kt1(H), Impl.total1(H, I), G))
      +L = ltc(m, lo)
      +Lm = PSpec.bit(Nat.is_lt(m, lo))
      Equal.trans(Nat, Nat.add(Nat.add(C, T), Nat.add(L, Lm)), Nat.add(Nat.add(C, L), Nat.add(T, Lm)),
        Nat.add(ltc(m, 1n+hi), PSpec.bit(Nat.is_lt(m, 1n+hi))),
        swap4(C, T, L, Lm),
        (%Equal.sym(Nat, Nat.add(C, L), ltc(m, 1n+hi), tele(G, H, I, m, g, grid, shaped, fits, group))
            : {Nat.add(_, Nat.add(T, Lm)) == Nat.add(ltc(m, 1n+hi), PSpec.bit(Nat.is_lt(m, 1n+hi))) : Nat}
          %Equal.sym(Bool, PSpec.touches(m, g, Impl.kt1(H), Impl.total1(H, I), G),
              Bool.and(Nat.is_le(lo, m), Nat.is_le(m, hi)),
              cc_touch(G, H, I, g, m, grid, shaped, fits, group))
            : {Nat.add(ltc(m, 1n+hi), Nat.add(PSpec.bit(_), Lm)) ==
              Nat.add(ltc(m, 1n+hi), PSpec.bit(Nat.is_lt(m, 1n+hi))) : Nat}
          Equal.cong(Nat, Nat, t => Nat.add(ltc(m, 1n+hi), t),
            Nat.add(PSpec.bit(Bool.and(Nat.is_le(lo, m), Nat.is_le(m, hi))), Lm),
            PSpec.bit(Nat.is_lt(m, 1n+hi)),
            pw_step(Nat.is_lt(m, lo), m, lo, hi, {==},
              PP.ard_fst({Nat.is_le(lo, hi) == True{} : Bool}, {Nat.is_lt(hi, G) == True{} : Bool},
                cc_rest(G, H, I, g, grid, shaped, fits, group))))))

def sub_succ(+hi: Nat, +lo: Nat, h: {Nat.is_le(lo, hi) == True{} : Bool})
  -> {Nat.sub(1n+hi, lo) == 1n+Nat.sub(hi, lo) : Nat}:
  match hi lo:
    case 0n 0n:
      {==}
    case 1n+k 0n:
      {==}
    case 0n 1n+l:
      Empty.absurd({Nat.sub(1n, 1n+l) == 1n+Nat.sub(0n, 1n+l) : Nat}, PP.ar_false_true(h))
    case 1n+k 1n+l:
      sub_succ(k, l, h)

# The number of blocks touching phase-1 group g is nc(g).
def touch_nc(+G: Nat, +H: Nat, +I: Nat, +g: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {touch_count(G, H, I, G, g) == Part.nc(g, Impl.kt1(H), Impl.total1(H, I), G) : Nat}:
  +lo = Part.b_lo(g, Impl.kt1(H), Impl.total1(H, I), G)
  +hi = Part.b_hi(g, Impl.kt1(H), Impl.total1(H, I), G)
  +C = touch_count(G, H, I, G, g)
  +lohi = PP.ard_fst({Nat.is_le(lo, hi) == True{} : Bool}, {Nat.is_lt(hi, G) == True{} : Bool},
    cc_rest(G, H, I, g, grid, shaped, fits, group))
  +hig = PP.ard_snd({Nat.is_le(lo, hi) == True{} : Bool}, {Nat.is_lt(hi, G) == True{} : Bool},
    cc_rest(G, H, I, g, grid, shaped, fits, group))
  +hi1g = Equal.trans(Bool, Nat.is_le(1n+hi, G), Nat.is_lt(hi, G), True{},
    Equal.sym(Bool, Nat.is_lt(hi, G), Nat.is_le(1n+hi, G), PP.ar_lt_succ_le(hi, G)), hig)
  +E2 = Equal.trans(Nat, Nat.add(C, lo), Nat.add(C, ltc(G, lo)), 1n+hi,
    Equal.cong(Nat, Nat, t => Nat.add(C, t), lo, ltc(G, lo),
      Equal.sym(Nat, ltc(G, lo), lo,
        ltc_full(G, lo, PP.ar_le_trans(lo, hi, G, lohi, PP.ar_lt_le(hi, G, hig))))),
    Equal.trans(Nat, Nat.add(C, ltc(G, lo)), ltc(G, 1n+hi), 1n+hi,
      tele(G, H, I, G, g, grid, shaped, fits, group), ltc_full(G, 1n+hi, hi1g)))
  +E1 = Equal.trans(Nat, Nat.add(lo, C), Nat.add(C, lo), 1n+hi, PP.ar_add_comm(lo, C), E2)
  Equal.trans(Nat, C, Nat.sub(Nat.add(lo, C), lo), Part.nc(g, Impl.kt1(H), Impl.total1(H, I), G),
    Equal.sym(Nat, Nat.sub(Nat.add(lo, C), lo), C, PP.ar_add_sub(lo, C)),
    Equal.trans(Nat, Nat.sub(Nat.add(lo, C), lo), Nat.sub(1n+hi, lo),
      Part.nc(g, Impl.kt1(H), Impl.total1(H, I), G),
      Equal.cong(Nat, Nat, t => Nat.sub(t, lo), Nat.add(lo, C), 1n+hi, E1),
      Equal.trans(Nat, Nat.sub(1n+hi, lo), 1n+Nat.sub(hi, lo), Nat.add(Nat.sub(hi, lo), 1n),
        sub_succ(hi, lo, lohi), add_one(Nat.sub(hi, lo)))))

def sig_c1_nc(+G: Nat, +H: Nat, +I: Nat, +g: Nat, +grid: {Nat.is_lt(0n, G) == True{} : Bool},
    +shaped: {Nat.is_le(128n, H) == True{} : Bool},
    +fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool},
    +group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool})
  -> {Laws.sig_total(G, H, I, G, Spec.C1{g}) ==
    Nat.mul(8n, Part.nc(g, Impl.kt1(H), Impl.total1(H, I), G)) : Nat}:
  +C = touch_count(G, H, I, G, g)
  +N = Part.nc(g, Impl.kt1(H), Impl.total1(H, I), G)
  Equal.trans(Nat, Laws.sig_total(G, H, I, G, Spec.C1{g}), Nat.mul(C, 8n), Nat.mul(8n, N),
    Equal.sym(Nat, Nat.mul(C, 8n), Laws.sig_total(G, H, I, G, Spec.C1{g}),
      st_c1(G, H, I, G, g, grid, shaped)),
    Equal.trans(Nat, Nat.mul(C, 8n), Nat.mul(N, 8n), Nat.mul(8n, N),
      Equal.cong(Nat, Nat, t => Nat.mul(t, 8n), C, N, touch_nc(G, H, I, g, grid, shaped, fits, group)),
      PP.ar_mul_comm(N, 8n)))

def Laws.gate_signals(G, H, I, p, grid, shaped, fits, pair):
  +np = Impl.pairs(I)
  sig_c1_nc(G, H, I, p, grid, shaped, fits,
    PP.ar_lt_le_trans(p, np, Part.groups(2n, I), pair, PP.ar_le_add_r(np, Nat.add(np, 0n))))

def Laws.up_signals(G, H, I, p, grid, shaped, fits, pair):
  +np = Impl.pairs(I)
  sig_c1_nc(G, H, I, Nat.add(np, p), grid, shaped, fits,
    (%Equal.sym(Bool, Nat.is_lt(Nat.add(np, p), Nat.add(np, Nat.add(np, 0n))),
        Nat.is_lt(p, Nat.add(np, 0n)), PP.ar_lt_add_cancel(np, p, Nat.add(np, 0n)))
        : {_ == True{} : Bool}
      %Equal.sym(Nat, Nat.add(np, 0n), np, PP.ar_add_zero_r(np)) : {Nat.is_lt(p, _) == True{} : Bool}
      pair))

# ==== (6) pairs_finished at the served instance ====

# A block w < n with finish pair p makes k_p (over n blocks) positive.
def count_pos(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +w: Nat, +p: Nat,
    lt: {Nat.is_lt(w, n) == True{} : Bool}, fpw: {Impl.fin_pair(G, H, I, w) == p : Nat})
  -> {Nat.is_lt(0n, Impl.fin_count(G, H, I, n, p)) == True{} : Bool}:
  +q = Impl.fin_pair(G, H, I, w)
  %fpw : {Nat.is_lt(0n, Impl.fin_count(G, H, I, n, _)) == True{} : Bool}
  PP.ar_le_lt_trans(0n, Impl.fin_count(G, H, I, w, q), Impl.fin_count(G, H, I, n, q),
    PP.ar_h_le_zero(Impl.fin_count(G, H, I, w, q)), rank_below(G, H, I, w, n, lt))

# (k G + y) / G == k + y / G   (G >= 1)
def div_shift(+k: Nat, +y: Nat, +G: Nat, +pos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(k, G), y), G) == Nat.add(k, Nat.div(y, G)) : Nat}:
  +dy = Nat.div(y, G)
  +my = Nat.mod(y, G)
  %PP.ard_dm_eq(y, G, pos)
    : {Nat.div(Nat.add(Nat.mul(k, G), _), G) == Nat.add(k, dy) : Nat}
  %PP.ar_add_assoc(Nat.mul(k, G), Nat.mul(dy, G), my)
    : {Nat.div(_, G) == Nat.add(k, dy) : Nat}
  %PP.ar_mul_add_l(k, dy, G)
    : {Nat.div(Nat.add(_, my), G) == Nat.add(k, dy) : Nat}
  PP.ard_fst({Nat.div(Nat.add(Nat.mul(Nat.add(k, dy), G), my), G) == Nat.add(k, dy) : Nat},
    {Nat.mod(Nat.add(Nat.mul(Nat.add(k, dy), G), my), G) == my : Nat},
    PP.ar_div_unique(Nat.add(k, dy), my, G, PP.ard_dm_lt(y, G, pos)))

# w (q G + r) / G == w q + w r / G   (G >= 1)
def start_split(+w: Nat, +q: Nat, +r: Nat, +G: Nat, +pos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.add(Nat.mul(w, q), Nat.div(Nat.mul(w, r), G)) ==
    Nat.div(Nat.mul(w, Nat.add(Nat.mul(q, G), r)), G) : Nat}:
  +qG = Nat.mul(q, G)
  +E = Equal.trans(Nat, Nat.mul(w, Nat.add(qG, r)), Nat.mul(Nat.add(qG, r), w),
    Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(w, r)),
    PP.ar_mul_comm(w, Nat.add(qG, r)),
    Equal.trans(Nat, Nat.mul(Nat.add(qG, r), w), Nat.add(Nat.mul(qG, w), Nat.mul(r, w)),
      Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(w, r)),
      PP.ar_mul_add_l(qG, r, w),
      Equal.trans(Nat, Nat.add(Nat.mul(qG, w), Nat.mul(r, w)),
        Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(r, w)),
        Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(w, r)),
        Equal.cong(Nat, Nat, t => Nat.add(t, Nat.mul(r, w)), Nat.mul(qG, w),
          Nat.mul(Nat.mul(w, q), G),
          Equal.trans(Nat, Nat.mul(qG, w), Nat.mul(w, qG), Nat.mul(Nat.mul(w, q), G),
            PP.ar_mul_comm(qG, w),
            Equal.sym(Nat, Nat.mul(Nat.mul(w, q), G), Nat.mul(w, qG), PP.ar_mul_assoc(w, q, G)))),
        Equal.cong(Nat, Nat, t => Nat.add(Nat.mul(Nat.mul(w, q), G), t), Nat.mul(r, w),
          Nat.mul(w, r), PP.ar_mul_comm(r, w)))))
  Equal.sym(Nat, Nat.div(Nat.mul(w, Nat.add(qG, r)), G), Nat.add(Nat.mul(w, q), Nat.div(Nat.mul(w, r), G)),
    Equal.trans(Nat, Nat.div(Nat.mul(w, Nat.add(qG, r)), G),
      Nat.div(Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(w, r)), G),
      Nat.add(Nat.mul(w, q), Nat.div(Nat.mul(w, r), G)),
      Equal.cong(Nat, Nat, t => Nat.div(t, G), Nat.mul(w, Nat.add(qG, r)),
        Nat.add(Nat.mul(Nat.mul(w, q), G), Nat.mul(w, r)), E),
      div_shift(Nat.mul(w, q), Nat.mul(w, r), G, pos)))

# At the served instance total2 = 66 G + 56 (10880 = 66 * 164 + 56).
def total2_split(+G: Nat, +H: Nat, +I: Nat, sg: {G == Impl.grid() : Nat},
    sh: {H == Impl.hidden() : Nat}, si: {I == Impl.inter() : Nat})
  -> {Nat.add(Nat.mul(66n, G), 56n) == Impl.total2(H, I) : Nat}:
  %Equal.sym(Nat, H, Impl.hidden(), sh)
    : {Nat.add(Nat.mul(66n, G), 56n) == Impl.total2(_, I) : Nat}
  %Equal.sym(Nat, I, Impl.inter(), si)
    : {Nat.add(Nat.mul(66n, G), 56n) == Impl.total2(Impl.hidden(), _) : Nat}
  %Equal.sym(Nat, G, Impl.grid(), sg)
    : {Nat.add(Nat.mul(66n, _), 56n) == Impl.total2(Impl.hidden(), Impl.inter()) : Nat}
  {==}

def grid_pos(+G: Nat, sg: {G == Impl.grid() : Nat}) -> {Nat.is_lt(0n, G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid(), sg) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

# The finish pair of block w at the served instance, from a small closed computation chk.
def wit(+G: Nat, +H: Nat, +I: Nat, +sg: {G == Impl.grid() : Nat}, +sh: {H == Impl.hidden() : Nat},
    +si: {I == Impl.inter() : Nat}, +w: Nat, +p: Nat,
    chk: {Nat.div(Nat.mod(Nat.add(Nat.mul(w, 66n), Nat.div(Nat.mul(w, 56n), Impl.grid())),
      Impl.kt2(Impl.inter())), 32n) == p : Nat})
  -> {Impl.fin_pair(G, H, I, w) == p : Nat}:
  +pos = grid_pos(G, sg)
  %total2_split(G, H, I, sg, sh, si)
    : {Nat.div(Nat.mod(Nat.div(Nat.mul(w, _), G), Impl.kt2(I)), 32n) == p : Nat}
  %start_split(w, 66n, 56n, G, pos)
    : {Nat.div(Nat.mod(_, Impl.kt2(I)), 32n) == p : Nat}
  %Equal.sym(Nat, G, Impl.grid(), sg)
    : {Nat.div(Nat.mod(Nat.add(Nat.mul(w, 66n), Nat.div(Nat.mul(w, 56n), _)), Impl.kt2(I)), 32n) ==
      p : Nat}
  %Equal.sym(Nat, I, Impl.inter(), si)
    : {Nat.div(Nat.mod(Nat.add(Nat.mul(w, 66n), Nat.div(Nat.mul(w, 56n), Impl.grid())),
      Impl.kt2(_)), 32n) == p : Nat}
  chk

def wit_lt(+G: Nat, +w: Nat, sg: {G == Impl.grid() : Nat},
    chk: {Nat.is_lt(w, Impl.grid()) == True{} : Bool}) -> {Nat.is_lt(w, G) == True{} : Bool}:
  %Equal.sym(Nat, G, Impl.grid(), sg) : {Nat.is_lt(w, _) == True{} : Bool}
  chk

def pair34(+I: Nat, +p: Nat, si: {I == Impl.inter() : Nat},
    pair: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool})
  -> {Nat.is_lt(p, Impl.pairs(Impl.inter())) == True{} : Bool}:
  %si : {Nat.is_lt(p, Impl.pairs(_)) == True{} : Bool}
  pair

# One served pair p with its witness block w.
def served(+G: Nat, +H: Nat, +I: Nat, +sg: {G == Impl.grid() : Nat}, +sh: {H == Impl.hidden() : Nat},
    +si: {I == Impl.inter() : Nat}, +w: Nat, +p: Nat,
    chk: {Nat.div(Nat.mod(Nat.add(Nat.mul(w, 66n), Nat.div(Nat.mul(w, 56n), Impl.grid())),
      Impl.kt2(Impl.inter())), 32n) == p : Nat},
    inside: {Nat.is_lt(w, Impl.grid()) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.fin_count(G, H, I, G, p)) == True{} : Bool}:
  count_pos(G, H, I, G, w, p, wit_lt(G, w, sg, inside), wit(G, H, I, sg, sh, si, w, p, chk))

# k_p >= 1 for every pair p < 34 at G = 164, H = 5120, I = 17408: pair p's witness is the first
# block whose phase-2 slice starts in p (checked by a small closed computation per pair).
def Laws.pairs_finished(G, H, I, p, served_g, served_h, served_i, pair):
  match p:
    case 0n:
      served(G, H, I, served_g, served_h, served_i, 0n, 0n, {==}, {==})
    case 1n+p1:
      match p1:
        case 0n:
          served(G, H, I, served_g, served_h, served_i, 17n, 1n, {==}, {==})
        case 1n+p2:
          match p2:
            case 0n:
              served(G, H, I, served_g, served_h, served_i, 1n, 2n, {==}, {==})
            case 1n+p3:
              match p3:
                case 0n:
                  served(G, H, I, served_g, served_h, served_i, 18n, 3n, {==}, {==})
                case 1n+p4:
                  match p4:
                    case 0n:
                      served(G, H, I, served_g, served_h, served_i, 2n, 4n, {==}, {==})
                    case 1n+p5:
                      match p5:
                        case 0n:
                          served(G, H, I, served_g, served_h, served_i, 19n, 5n, {==}, {==})
                        case 1n+p6:
                          match p6:
                            case 0n:
                              served(G, H, I, served_g, served_h, served_i, 3n, 6n, {==}, {==})
                            case 1n+p7:
                              match p7:
                                case 0n:
                                  served(G, H, I, served_g, served_h, served_i, 20n, 7n, {==}, {==})
                                case 1n+p8:
                                  match p8:
                                    case 0n:
                                      served(G, H, I, served_g, served_h, served_i, 4n, 8n, {==}, {==})
                                    case 1n+p9:
                                      match p9:
                                        case 0n:
                                          served(G, H, I, served_g, served_h, served_i, 21n, 9n, {==}, {==})
                                        case 1n+p10:
                                          match p10:
                                            case 0n:
                                              served(G, H, I, served_g, served_h, served_i, 5n, 10n, {==}, {==})
                                            case 1n+p11:
                                              match p11:
                                                case 0n:
                                                  served(G, H, I, served_g, served_h, served_i, 22n, 11n, {==}, {==})
                                                case 1n+p12:
                                                  match p12:
                                                    case 0n:
                                                      served(G, H, I, served_g, served_h, served_i, 6n, 12n, {==}, {==})
                                                    case 1n+p13:
                                                      match p13:
                                                        case 0n:
                                                          served(G, H, I, served_g, served_h, served_i, 23n, 13n, {==}, {==})
                                                        case 1n+p14:
                                                          match p14:
                                                            case 0n:
                                                              served(G, H, I, served_g, served_h, served_i, 7n, 14n, {==}, {==})
                                                            case 1n+p15:
                                                              match p15:
                                                                case 0n:
                                                                  served(G, H, I, served_g, served_h, served_i, 24n, 15n, {==}, {==})
                                                                case 1n+p16:
                                                                  match p16:
                                                                    case 0n:
                                                                      served(G, H, I, served_g, served_h, served_i, 8n, 16n, {==}, {==})
                                                                    case 1n+p17:
                                                                      match p17:
                                                                        case 0n:
                                                                          served(G, H, I, served_g, served_h, served_i, 25n, 17n, {==}, {==})
                                                                        case 1n+p18:
                                                                          match p18:
                                                                            case 0n:
                                                                              served(G, H, I, served_g, served_h, served_i, 9n, 18n, {==}, {==})
                                                                            case 1n+p19:
                                                                              match p19:
                                                                                case 0n:
                                                                                  served(G, H, I, served_g, served_h, served_i, 26n, 19n, {==}, {==})
                                                                                case 1n+p20:
                                                                                  match p20:
                                                                                    case 0n:
                                                                                      served(G, H, I, served_g, served_h, served_i, 10n, 20n, {==}, {==})
                                                                                    case 1n+p21:
                                                                                      match p21:
                                                                                        case 0n:
                                                                                          served(G, H, I, served_g, served_h, served_i, 27n, 21n, {==}, {==})
                                                                                        case 1n+p22:
                                                                                          match p22:
                                                                                            case 0n:
                                                                                              served(G, H, I, served_g, served_h, served_i, 11n, 22n, {==}, {==})
                                                                                            case 1n+p23:
                                                                                              match p23:
                                                                                                case 0n:
                                                                                                  served(G, H, I, served_g, served_h, served_i, 44n, 23n, {==}, {==})
                                                                                                case 1n+p24:
                                                                                                  match p24:
                                                                                                    case 0n:
                                                                                                      served(G, H, I, served_g, served_h, served_i, 12n, 24n, {==}, {==})
                                                                                                    case 1n+p25:
                                                                                                      match p25:
                                                                                                        case 0n:
                                                                                                          served(G, H, I, served_g, served_h, served_i, 45n, 25n, {==}, {==})
                                                                                                        case 1n+p26:
                                                                                                          match p26:
                                                                                                            case 0n:
                                                                                                              served(G, H, I, served_g, served_h, served_i, 13n, 26n, {==}, {==})
                                                                                                            case 1n+p27:
                                                                                                              match p27:
                                                                                                                case 0n:
                                                                                                                  served(G, H, I, served_g, served_h, served_i, 46n, 27n, {==}, {==})
                                                                                                                case 1n+p28:
                                                                                                                  match p28:
                                                                                                                    case 0n:
                                                                                                                      served(G, H, I, served_g, served_h, served_i, 30n, 28n, {==}, {==})
                                                                                                                    case 1n+p29:
                                                                                                                      match p29:
                                                                                                                        case 0n:
                                                                                                                          served(G, H, I, served_g, served_h, served_i, 14n, 29n, {==}, {==})
                                                                                                                        case 1n+p30:
                                                                                                                          match p30:
                                                                                                                            case 0n:
                                                                                                                              served(G, H, I, served_g, served_h, served_i, 31n, 30n, {==}, {==})
                                                                                                                            case 1n+p31:
                                                                                                                              match p31:
                                                                                                                                case 0n:
                                                                                                                                  served(G, H, I, served_g, served_h, served_i, 15n, 31n, {==}, {==})
                                                                                                                                case 1n+p32:
                                                                                                                                  match p32:
                                                                                                                                    case 0n:
                                                                                                                                      served(G, H, I, served_g, served_h, served_i, 32n, 32n, {==}, {==})
                                                                                                                                    case 1n+p33:
                                                                                                                                      match p33:
                                                                                                                                        case 0n:
                                                                                                                                          served(G, H, I, served_g, served_h, served_i, 16n, 33n, {==}, {==})
                                                                                                                                        case 1n+p34:
                                                                                                                                          Empty.absurd({Nat.is_lt(0n, Impl.fin_count(G, H, I, G, Nat.add(34n, p34))) == True{} : Bool},
                                                                                                                                            PP.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(p34, 0n), True{}, Equal.sym(Bool, Nat.is_lt(p34, 0n), False{}, PP.ar_h_lt_zero(p34)), pair34(I, Nat.add(34n, p34), served_i, pair))))
