# Proofs of bend/err_pfix_laws.bend (ext 3031 prefill attention vs stock 355c6ee). Method: every composite path is
# rewritten to a normal form Path{r32, t32, 2, 0, 0, ex2, 1, 0} whose counts are sums of a few atoms; domination is then
# three Nat inequalities (t32, r32 + t32, ex2: the r16 / t16 / q8 / rcp / rsq counts are equal on both sides, so no
# exchange is needed). The r32 + t32 inequality is the budget: elpis's chain part is bounded by its chain head's
# (chain_head), its head score by stock's tile-0 score plus a masked-head penalty (head_pen), its combine plus penalty by
# the finite table gmax (err_pfix_tables), and the rest by stock's longer split and combine (budget). The integer facts
# about the kernel's divisions are err_pfix_geom_proof.bend. No @unsafe definitions, axioms, holes or foreign code; every
# def precedes its uses.
import Base
import ./err_bound.bend as Eb
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./err_pfix.bend as Ef
import ./err_pfix_geom_proof.bend as PG
import ./err_pfix_laws.bend as Laws

# ==== 1. counting atoms ====

def bitn(x: Bool) -> Nat:
  match x:
    case True{}:
      1n
    case False{}:
      0n

# r32 steps of a score segment: 1 interior, 2 masked
def scr(x: Bool) -> Nat:
  match x:
    case True{}:
      1n
    case False{}:
      2n

# r32 steps of an optional combine of c roundings (the sub plus c)
def cbr(x: Bool, +c: Nat) -> Nat:
  match x:
    case True{}:
      1n+c
    case False{}:
      0n

# ==== 2. normal forms (stated NF == term: `%nf : P`, P marking the term with _, rewrites the term into NF) ====

def rep_e(+m: Nat) -> {Eb.Path{Nat.double(m), 0n, 0n, 0n, 0n, m, 0n, 0n} == Ef.rep_add(m, Ef.e_later(), Eb.zero()) : Eb.Path}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      %rep_e(k) : {Eb.Path{Nat.double(1n+k), 0n, 0n, 0n, 0n, 1n+k, 0n, 0n} == Eb.add(Ef.e_later(), _) : Eb.Path}
      {==}

def rep_d(+m: Nat) -> {Eb.Path{Nat.double(m), 0n, 0n, 0n, 0n, m, 0n, 0n} == Ef.rep_add(m, Ef.den_later(), Eb.zero()) : Eb.Path}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      %rep_d(k) : {Eb.Path{Nat.double(1n+k), 0n, 0n, 0n, 0n, 1n+k, 0n, 0n} == Eb.add(Ef.den_later(), _) : Eb.Path}
      {==}

def rep_s(+m: Nat) -> {Eb.Path{Nat.double(m), Nat.double(m), 0n, 0n, 0n, m, 0n, 0n} == Ef.rep_add(m, Ef.s_later(), Eb.zero()) : Eb.Path}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      %rep_s(k) : {Eb.Path{Nat.double(1n+k), Nat.double(1n+k), 0n, 0n, 0n, 1n+k, 0n, 0n} == Eb.add(Ef.s_later(), _) : Eb.Path}
      {==}

def w_fold(x: Bool) -> {Eb.Path{bitn(x), 0n, 0n, 0n, 0n, 0n, 0n, 0n} == Ef.when(x, Ef.fold()) : Eb.Path}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def w_comb(x: Bool, +c: Nat) -> {Eb.Path{cbr(x, c), 0n, 0n, 0n, 0n, bitn(x), 0n, 0n} == Ef.when(x, Ef.comb(c)) : Eb.Path}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def w_score(x: Bool, +s: Nat) -> {Eb.Path{scr(x), Nat.sub(16n, s), 0n, 0n, 0n, 1n, 0n, 0n} == Ef.score(x, s) : Eb.Path}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a numerator / denominator part in normal form: Path{r, t, 0, 0, 0, x, 0, 0}
def part(+r: Nat, +t: Nat, +x: Nat) -> Eb.Path:
  Eb.Path{r, t, 0n, 0n, 0n, x, 0n, 0n}

# elpis numerator: r32 = [t > 0] + 2 a + comb + score, t32 = own + (16 - s), ex2 = a + [K > 1] + 1
def nf_enum(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, h: Bool, +s: Nat)
  -> {part(Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(a), Nat.add(cbr(Nat.is_lt(1n, K), Ef.chain_c(k, K)),
        scr(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I))))), Nat.add(Ef.own_t32(h), Nat.sub(16n, s)),
        Nat.add(a, Nat.add(bitn(Nat.is_lt(1n, K)), 1n))) == Ef.e_num(E, K, I, k, t, a, h, s) : Eb.Path}:
  +f = Nat.is_lt(0n, t)
  +k2 = Nat.is_lt(1n, K)
  +c = Ef.chain_c(k, K)
  +x1 = Nat.is_lt(Nat.add(Nat.mul(k, E), t), I)
  +NF = part(Nat.add(bitn(f), Nat.add(Nat.double(a), Nat.add(cbr(k2, c), scr(x1)))), Nat.add(Ef.own_t32(h), Nat.sub(16n, s)),
    Nat.add(a, Nat.add(bitn(k2), 1n)))
  %w_fold(f) : {NF == Eb.add(Ef.own(h), Eb.add(_, Eb.add(Ef.rep_add(a, Ef.e_later(), Eb.zero()),
    Eb.add(Ef.when(k2, Ef.comb(c)), Ef.score(x1, s))))) : Eb.Path}
  %rep_e(a) : {NF == Eb.add(Ef.own(h), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n}, Eb.add(_,
    Eb.add(Ef.when(k2, Ef.comb(c)), Ef.score(x1, s))))) : Eb.Path}
  %w_comb(k2, c) : {NF == Eb.add(Ef.own(h), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(a), 0n, 0n, 0n, 0n, a, 0n, 0n}, Eb.add(_, Ef.score(x1, s))))) : Eb.Path}
  %w_score(x1, s) : {NF == Eb.add(Ef.own(h), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(a), 0n, 0n, 0n, 0n, a, 0n, 0n},
      Eb.add(Eb.Path{cbr(k2, c), 0n, 0n, 0n, 0n, bitn(k2), 0n, 0n}, _)))) : Eb.Path}
  {==}

# elpis denominator: r32 = 5 + [t > 0] + 2 b + comb + score, t32 = 16 - s, ex2 = b + [K > 1] + 1
def nf_eden(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +b: Nat, +s: Nat)
  -> {part(5n+Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(b), Nat.add(cbr(Nat.is_lt(1n, K), Ef.chain_c(k, K)),
        scr(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I))))), Nat.sub(16n, s),
        Nat.add(b, Nat.add(bitn(Nat.is_lt(1n, K)), 1n))) == Ef.e_den(E, K, I, k, t, b, s) : Eb.Path}:
  +f = Nat.is_lt(0n, t)
  +k2 = Nat.is_lt(1n, K)
  +c = Ef.chain_c(k, K)
  +x1 = Nat.is_lt(Nat.add(Nat.mul(k, E), t), I)
  +NF = part(5n+Nat.add(bitn(f), Nat.add(Nat.double(b), Nat.add(cbr(k2, c), scr(x1)))), Nat.sub(16n, s),
    Nat.add(b, Nat.add(bitn(k2), 1n)))
  %w_fold(f) : {NF == Eb.add(Ef.den_in(), Eb.add(_, Eb.add(Ef.rep_add(b, Ef.den_later(), Eb.zero()),
    Eb.add(Ef.when(k2, Ef.comb(c)), Ef.score(x1, s))))) : Eb.Path}
  %rep_d(b) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n}, Eb.add(_,
    Eb.add(Ef.when(k2, Ef.comb(c)), Ef.score(x1, s))))) : Eb.Path}
  %w_comb(k2, c) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(b), 0n, 0n, 0n, 0n, b, 0n, 0n}, Eb.add(_, Ef.score(x1, s))))) : Eb.Path}
  %w_score(x1, s) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{bitn(f), 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(b), 0n, 0n, 0n, 0n, b, 0n, 0n},
      Eb.add(Eb.Path{cbr(k2, c), 0n, 0n, 0n, 0n, bitn(k2), 0n, 0n}, _)))) : Eb.Path}
  {==}

# stock witness numerator (split 0, tile 0, first half, N1 later tiles): r32 = 2 N1 + comb + score,
# t32 = 2 + 2 N1 + (16 - s), ex2 = N1 + [sp] + 1
def nf_wnum(+sp: Bool, +Ks: Nat, +I: Nat, +N1: Nat, +s: Nat)
  -> {part(Nat.add(Nat.double(N1), Nat.add(cbr(sp, Ks), scr(Nat.is_lt(0n, I)))), 2n+Nat.add(Nat.double(N1), Nat.sub(16n, s)),
        Nat.add(N1, Nat.add(bitn(sp), 1n))) == Ef.s_num(1n, sp, Ks, I, 0n, 0n, N1, False{}, s) : Eb.Path}:
  +x0 = Nat.is_lt(0n, I)
  +NF = part(Nat.add(Nat.double(N1), Nat.add(cbr(sp, Ks), scr(x0))), 2n+Nat.add(Nat.double(N1), Nat.sub(16n, s)),
    Nat.add(N1, Nat.add(bitn(sp), 1n)))
  %rep_s(N1) : {NF == Eb.add(Ef.own(False{}), Eb.add(_, Eb.add(Ef.when(sp, Ef.comb(Ks)), Ef.score(x0, s)))) : Eb.Path}
  %w_comb(sp, Ks) : {NF == Eb.add(Ef.own(False{}), Eb.add(Eb.Path{Nat.double(N1), Nat.double(N1), 0n, 0n, 0n, N1, 0n, 0n},
    Eb.add(_, Ef.score(x0, s)))) : Eb.Path}
  %w_score(x0, s) : {NF == Eb.add(Ef.own(False{}), Eb.add(Eb.Path{Nat.double(N1), Nat.double(N1), 0n, 0n, 0n, N1, 0n, 0n},
    Eb.add(Eb.Path{cbr(sp, Ks), 0n, 0n, 0n, 0n, bitn(sp), 0n, 0n}, _))) : Eb.Path}
  {==}

# stock witness denominator (split 0, tile 0): r32 = 5 + 2 N1 + comb + score, t32 = 16 - s, ex2 = N1 + [sp] + 1
def nf_wden(+sp: Bool, +Ks: Nat, +I: Nat, +N1: Nat, +s: Nat)
  -> {part(5n+Nat.add(Nat.double(N1), Nat.add(cbr(sp, Ks), scr(Nat.is_lt(0n, I)))), Nat.sub(16n, s),
        Nat.add(N1, Nat.add(bitn(sp), 1n))) == Ef.s_den(1n, sp, Ks, I, 0n, 0n, N1, s) : Eb.Path}:
  +x0 = Nat.is_lt(0n, I)
  +NF = part(5n+Nat.add(Nat.double(N1), Nat.add(cbr(sp, Ks), scr(x0))), Nat.sub(16n, s), Nat.add(N1, Nat.add(bitn(sp), 1n)))
  %rep_d(N1) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}, Eb.add(_,
    Eb.add(Ef.when(sp, Ef.comb(Ks)), Ef.score(x0, s))))) : Eb.Path}
  %w_comb(sp, Ks) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(N1), 0n, 0n, 0n, 0n, N1, 0n, 0n}, Eb.add(_, Ef.score(x0, s))))) : Eb.Path}
  %w_score(x0, s) : {NF == Eb.add(Ef.den_in(), Eb.add(Eb.Path{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n},
    Eb.add(Eb.Path{Nat.double(N1), 0n, 0n, 0n, 0n, N1, 0n, 0n},
      Eb.add(Eb.Path{cbr(sp, Ks), 0n, 0n, 0n, 0n, bitn(sp), 0n, 0n}, _)))) : Eb.Path}
  {==}

# ==== 3. domination from counts ====

# paths with equal r16 (2), t16, q8 (0), rcp (1), rsq (0): domination is t32 <= t32, t32 + r32 <= t32 + r32, ex2 <= ex2
def dom_simple(+ea: Nat, +eb: Nat, +ee: Nat, +sa: Nat, +sb: Nat, +se: Nat,
    h1: {Nat.is_le(eb, sb) == True{} : Bool}, h2: {Nat.is_le(Nat.add(eb, ea), Nat.add(sb, sa)) == True{} : Bool},
    h3: {Nat.is_le(ee, se) == True{} : Bool})
  -> {Eb.dom(128n, Eb.Path{ea, eb, 2n, 0n, 0n, ee, 1n, 0n}, Eb.Path{sa, sb, 2n, 0n, 0n, se, 1n, 0n}) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(sb, 0n), sb, NO.add_zero_r(sb)) :
    {Bool.and(Nat.is_le(eb, _), Bool.and(Nat.is_le(Nat.add(eb, ea), Nat.add(Nat.add(sb, sa), 0n)),
      Bool.and(Nat.is_le(ee, se), True{}))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.add(sb, sa), 0n), Nat.add(sb, sa), NO.add_zero_r(Nat.add(sb, sa))) :
    {Bool.and(Nat.is_le(eb, sb), Bool.and(Nat.is_le(Nat.add(eb, ea), _), Bool.and(Nat.is_le(ee, se), True{}))) == True{} : Bool}
  NO.and_intro(Nat.is_le(eb, sb), Bool.and(Nat.is_le(Nat.add(eb, ea), Nat.add(sb, sa)), Bool.and(Nat.is_le(ee, se), True{})), h1,
    NO.and_intro(Nat.is_le(Nat.add(eb, ea), Nat.add(sb, sa)), Bool.and(Nat.is_le(ee, se), True{}), h2,
      NO.and_intro(Nat.is_le(ee, se), True{}, h3, {==})))

# the composite of a numerator part, a denominator part and the fixed steps
def comp_nf(+rn: Nat, +tn: Nat, +xn: Nat, +rd: Nat, +td: Nat, +xd: Nat)
  -> {Eb.Path{Nat.add(rn, Nat.add(rd, 0n)), Nat.add(tn, Nat.add(td, 0n)), 2n, 0n, 0n, Nat.add(xn, Nat.add(xd, 0n)), 1n, 0n} ==
      Eb.add(part(rn, tn, xn), Eb.add(part(rd, td, xd), Ef.fixed())) : Eb.Path}:
  {==}

# ==== 4. arithmetic ====

def dbl_add(+x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), NO.add_succ_r(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      %dbl_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

def le_dbl(+a: Nat, +b: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.double(a), Nat.double(b)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.double(a), Nat.add(a, a), dbl_add(a)) : {Nat.is_le(_, Nat.double(b)) == True{} : Bool}
  %Equal.sym(Nat, Nat.double(b), Nat.add(b, b), dbl_add(b)) : {Nat.is_le(Nat.add(a, a), _) == True{} : Bool}
  +h = ab
  NO.le_add_mono(a, b, a, b, h, h)

def own_le2(h: Bool) -> {Nat.is_le(Ef.own_t32(h), 2n) == True{} : Bool}:
  match h:
    case False{}:
      {==}
    case True{}:
      {==}

# masked-head penalty: the chain's first tile is masked while stock's tile 0 is interior
def hp(xH: Bool, x0: Bool) -> Nat:
  match xH:
    case True{}:
      0n
    case False{}:
      bitn(x0)

def sc_head(+xH: Bool, +x0: Bool) -> {Nat.is_le(scr(xH), Nat.add(hp(xH, x0), scr(x0))) == True{} : Bool}:
  match xH x0:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def sc_any(+xT: Bool, +xH: Bool, +x0: Bool) -> {Nat.is_le(scr(xT), 1n+Nat.add(hp(xH, x0), scr(x0))) == True{} : Bool}:
  match xT xH x0:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# c + a <= c + b from a <= b
def cancel_intro(+c: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), NO.le_add_cancel(c, a, b)) : {_ == True{} : Bool}
  h

# 1 + 2 a + (C + score(T)) <= 2 + 2 a + (C + (hp + score(0))): a masked key costs at most one more r32 than the
# head's penalty and stock's tile-0 score together
def cb_succ(+a: Nat, +C: Nat, +xT: Bool, +xH: Bool, +x0: Bool)
  -> {Nat.is_le(1n+Nat.add(Nat.double(a), Nat.add(C, scr(xT))), 2n+Nat.add(Nat.double(a), Nat.add(C, Nat.add(hp(xH, x0), scr(x0))))) == True{} : Bool}:
  +HS = Nat.add(hp(xH, x0), scr(x0))
  %NO.add_succ_r(Nat.double(a), Nat.add(C, HS)) :
    {Nat.is_le(Nat.add(Nat.double(a), Nat.add(C, scr(xT))), _) == True{} : Bool}
  %NO.add_succ_r(C, HS) : {Nat.is_le(Nat.add(Nat.double(a), Nat.add(C, scr(xT))), Nat.add(Nat.double(a), _)) == True{} : Bool}
  NO.le_add_mono(Nat.double(a), Nat.double(a), Nat.add(C, scr(xT)), Nat.add(C, 1n+HS), NO.le_refl(Nat.double(a)),
    cancel_intro(C, scr(xT), 1n+HS, sc_any(xT, xH, x0)))

# A key at chain-local tile t with a later tiles of its chain (t + a <= NE1) costs, in its chain fold, comb C and score,
# no more than NE1 later tiles from the chain head plus the head's penalty over stock's tile-0 score:
#   [t > 0] + 2 a + (C + score(T0 + t)) <= 2 NE1 + (C + (hp + score(0)))
def chain_bound(+t: Nat, +T0: Nat, +a: Nat, +NE1: Nat, +I: Nat, +C: Nat,
    hta: {Nat.is_le(Nat.add(t, a), NE1) == True{} : Bool})
  -> {Nat.is_le(Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(a), Nat.add(C, scr(Nat.is_lt(Nat.add(T0, t), I))))),
       Nat.add(Nat.double(NE1), Nat.add(C, Nat.add(hp(Nat.is_lt(T0, I), Nat.is_lt(0n, I)), scr(Nat.is_lt(0n, I)))))) == True{} : Bool}:
  match t:
    case 0n:
      +xH = Nat.is_lt(T0, I)
      +x0 = Nat.is_lt(0n, I)
      +HS = Nat.add(hp(xH, x0), scr(x0))
      %Equal.sym(Nat, Nat.add(T0, 0n), T0, NO.add_zero_r(T0)) :
        {Nat.is_le(Nat.add(Nat.double(a), Nat.add(C, scr(Nat.is_lt(_, I)))), Nat.add(Nat.double(NE1), Nat.add(C, HS))) == True{} : Bool}
      NO.le_add_mono(Nat.double(a), Nat.double(NE1), Nat.add(C, scr(xH)), Nat.add(C, HS), le_dbl(a, NE1, hta),
        cancel_intro(C, scr(xH), HS, sc_head(xH, x0)))
    case 1n+u:
      +xH = Nat.is_lt(T0, I)
      +x0 = Nat.is_lt(0n, I)
      +xT = Nat.is_lt(Nat.add(T0, 1n+u), I)
      +Y = Nat.add(C, Nat.add(hp(xH, x0), scr(x0)))
      +h1a = NO.le_trans(1n+a, 1n+Nat.add(u, a), NE1, NO.le_add_l(u, a), hta)
      NO.le_trans(1n+Nat.add(Nat.double(a), Nat.add(C, scr(xT))), 2n+Nat.add(Nat.double(a), Y), Nat.add(Nat.double(NE1), Y),
        cb_succ(a, C, xT, xH, x0),
        NO.le_add_mono(Nat.double(1n+a), Nat.double(NE1), Y, Y, le_dbl(1n+a, NE1, h1a), NO.le_refl(Y)))

# chain_bound with the comb and penalty grouped: 2 NE1 + ((C + hp) + score(0))
def chain_bound2(+t: Nat, +T0: Nat, +a: Nat, +NE1: Nat, +I: Nat, +C: Nat,
    hta: {Nat.is_le(Nat.add(t, a), NE1) == True{} : Bool})
  -> {Nat.is_le(Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(a), Nat.add(C, scr(Nat.is_lt(Nat.add(T0, t), I))))),
       Nat.add(Nat.double(NE1), Nat.add(Nat.add(C, hp(Nat.is_lt(T0, I), Nat.is_lt(0n, I))), scr(Nat.is_lt(0n, I))))) == True{} : Bool}:
  +H = hp(Nat.is_lt(T0, I), Nat.is_lt(0n, I))
  +S0 = scr(Nat.is_lt(0n, I))
  %Equal.sym(Nat, Nat.add(Nat.add(C, H), S0), Nat.add(C, Nat.add(H, S0)), NO.add_assoc(C, H, S0)) :
    {Nat.is_le(Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(a), Nat.add(C, scr(Nat.is_lt(Nat.add(T0, t), I))))),
      Nat.add(Nat.double(NE1), _)) == True{} : Bool}
  chain_bound(t, T0, a, NE1, I, C, hta)

# (x + (G + s)) + (x2 + (G2 + s2)) == (s + s2) + ((x + x2) + (G + G2))
def perm6(+x: Nat, +G: Nat, +s: Nat, +x2: Nat, +G2: Nat, +s2: Nat)
  -> {Nat.add(Nat.add(x, Nat.add(G, s)), Nat.add(x2, Nat.add(G2, s2))) == Nat.add(Nat.add(s, s2), Nat.add(Nat.add(x, x2), Nat.add(G, G2))) : Nat}:
  +X = Nat.add(x, x2)
  +GG = Nat.add(G, G2)
  +SS = Nat.add(s, s2)
  Equal.trans(Nat, Nat.add(Nat.add(x, Nat.add(G, s)), Nat.add(x2, Nat.add(G2, s2))), Nat.add(X, Nat.add(Nat.add(G, s), Nat.add(G2, s2))),
    Nat.add(SS, Nat.add(X, GG)), NO.add_swap4(x, Nat.add(G, s), x2, Nat.add(G2, s2)),
    Equal.trans(Nat, Nat.add(X, Nat.add(Nat.add(G, s), Nat.add(G2, s2))), Nat.add(X, Nat.add(GG, SS)), Nat.add(SS, Nat.add(X, GG)),
      Equal.cong(Nat, Nat, y => Nat.add(X, y), Nat.add(Nat.add(G, s), Nat.add(G2, s2)), Nat.add(GG, SS), NO.add_swap4(G, s, G2, s2)),
      Equal.trans(Nat, Nat.add(X, Nat.add(GG, SS)), Nat.add(X, Nat.add(SS, GG)), Nat.add(SS, Nat.add(X, GG)),
        Equal.cong(Nat, Nat, y => Nat.add(X, y), Nat.add(GG, SS), Nat.add(SS, GG), NO.add_comm(GG, SS)),
        NO.add_swap(X, SS, GG))))

# a numerator part plus a denominator part (5 + ...) plus the fixed steps' 0, regrouped
def shape(+x: Nat, +G: Nat, +s: Nat, +x2: Nat, +G2: Nat, +s2: Nat)
  -> {Nat.add(Nat.add(x, Nat.add(G, s)), Nat.add(5n+Nat.add(x2, Nat.add(G2, s2)), 0n)) ==
      Nat.add(5n, Nat.add(Nat.add(s, s2), Nat.add(Nat.add(x, x2), Nat.add(G, G2)))) : Nat}:
  +A = Nat.add(x, Nat.add(G, s))
  +B = Nat.add(x2, Nat.add(G2, s2))
  %Equal.sym(Nat, Nat.add(5n+B, 0n), 5n+B, NO.add_zero_r(5n+B)) :
    {Nat.add(A, _) == Nat.add(5n, Nat.add(Nat.add(s, s2), Nat.add(Nat.add(x, x2), Nat.add(G, G2)))) : Nat}
  %Equal.sym(Nat, Nat.add(A, Nat.add(5n, B)), Nat.add(5n, Nat.add(A, B)), NO.add_swap(A, 5n, B)) :
    {_ == Nat.add(5n, Nat.add(Nat.add(s, s2), Nat.add(Nat.add(x, x2), Nat.add(G, G2)))) : Nat}
  %perm6(x, G, s, x2, G2, s2) : {Nat.add(5n, Nat.add(A, B)) == Nat.add(5n, _) : Nat}
  {==}

# stock's t32 part carries 2 N1 of P V tensor-core steps: (2 + (dN + T1)) + (T2 + 0) == dN + F
def eq_sb(+dN: Nat, +T1: Nat, +T2: Nat)
  -> {Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)) == Nat.add(dN, Nat.add(Nat.add(2n, T1), Nat.add(T2, 0n))) : Nat}:
  Equal.trans(Nat, Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)), Nat.add(Nat.add(dN, Nat.add(2n, T1)), Nat.add(T2, 0n)),
    Nat.add(dN, Nat.add(Nat.add(2n, T1), Nat.add(T2, 0n))),
    Equal.cong(Nat, Nat, y => Nat.add(y, Nat.add(T2, 0n)), Nat.add(2n, Nat.add(dN, T1)), Nat.add(dN, Nat.add(2n, T1)), NO.add_swap(2n, dN, T1)),
    NO.add_assoc(dN, Nat.add(2n, T1), Nat.add(T2, 0n)))

# (dN + F) + (5 + (SS + (YY + CC))) == F + (5 + (SS + ((dN + YY) + CC)))
def eq_rhs(+dN: Nat, +F: Nat, +SS: Nat, +YY: Nat, +CC: Nat)
  -> {Nat.add(Nat.add(dN, F), Nat.add(5n, Nat.add(SS, Nat.add(YY, CC)))) ==
      Nat.add(F, Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC)))) : Nat}:
  +W = Nat.add(SS, Nat.add(YY, CC))
  +M5 = Nat.add(5n, W)
  Equal.trans(Nat, Nat.add(Nat.add(dN, F), M5), Nat.add(dN, Nat.add(F, M5)), Nat.add(F, Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC)))),
    NO.add_assoc(dN, F, M5),
    Equal.trans(Nat, Nat.add(dN, Nat.add(F, M5)), Nat.add(F, Nat.add(dN, M5)), Nat.add(F, Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC)))),
      NO.add_swap(dN, F, M5),
      Equal.cong(Nat, Nat, y => Nat.add(F, y), Nat.add(dN, M5), Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC))),
        Equal.trans(Nat, Nat.add(dN, M5), Nat.add(5n, Nat.add(dN, W)), Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC))),
          NO.add_swap(dN, 5n, W),
          Equal.cong(Nat, Nat, y => Nat.add(5n, y), Nat.add(dN, W), Nat.add(SS, Nat.add(Nat.add(dN, YY), CC)),
            Equal.trans(Nat, Nat.add(dN, W), Nat.add(SS, Nat.add(dN, Nat.add(YY, CC))), Nat.add(SS, Nat.add(Nat.add(dN, YY), CC)),
              NO.add_swap(dN, SS, Nat.add(YY, CC)),
              Equal.cong(Nat, Nat, y => Nat.add(SS, y), Nat.add(dN, Nat.add(YY, CC)), Nat.add(Nat.add(dN, YY), CC),
                Equal.sym(Nat, Nat.add(Nat.add(dN, YY), CC), Nat.add(dN, Nat.add(YY, CC)), NO.add_assoc(dN, YY, CC)))))))))

# The r32 + t32 inequality of a composite from the chain bounds, own <= 2 and the budget
#   (2 NE1 + 2 NE1) + (G1 + G2) <= (2 N1 + (2 N1 + 2 N1)) + (CS + CS)
def sum_le(+o: Nat, +T1: Nat, +T2: Nat, +Pn: Nat, +Pd: Nat, +dNE: Nat, +G1: Nat, +G2: Nat, +s0: Nat, +dN: Nat, +CS: Nat,
    ho: {Nat.is_le(o, 2n) == True{} : Bool},
    hpn: {Nat.is_le(Pn, Nat.add(dNE, Nat.add(G1, s0))) == True{} : Bool},
    hpd: {Nat.is_le(Pd, Nat.add(dNE, Nat.add(G2, s0))) == True{} : Bool},
    hB: {Nat.is_le(Nat.add(Nat.add(dNE, dNE), Nat.add(G1, G2)), Nat.add(Nat.add(dN, Nat.add(dN, dN)), Nat.add(CS, CS))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.add(o, T1), Nat.add(T2, 0n)), Nat.add(Pn, Nat.add(5n+Pd, 0n))),
       Nat.add(Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)),
         Nat.add(Nat.add(dN, Nat.add(CS, s0)), Nat.add(5n+Nat.add(dN, Nat.add(CS, s0)), 0n)))) == True{} : Bool}:
  +F = Nat.add(Nat.add(2n, T1), Nat.add(T2, 0n))
  +Bn = Nat.add(dNE, Nat.add(G1, s0))
  +Bd = Nat.add(dNE, Nat.add(G2, s0))
  +Me = Nat.add(Bn, Nat.add(5n+Bd, 0n))
  +SS = Nat.add(s0, s0)
  +XX = Nat.add(dNE, dNE)
  +GG = Nat.add(G1, G2)
  +YY = Nat.add(dN, dN)
  +CC = Nat.add(CS, CS)
  +Ms = Nat.add(Nat.add(dN, Nat.add(CS, s0)), Nat.add(5n+Nat.add(dN, Nat.add(CS, s0)), 0n))
  +RHS = Nat.add(Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)), Ms)
  +L1 = Nat.add(F, Nat.add(5n, Nat.add(SS, Nat.add(XX, GG))))
  +R1 = Nat.add(F, Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC))))
  +step1 = NO.le_add_mono(Nat.add(Nat.add(o, T1), Nat.add(T2, 0n)), F, Nat.add(Pn, Nat.add(5n+Pd, 0n)), Me,
    NO.le_add_mono(Nat.add(o, T1), Nat.add(2n, T1), Nat.add(T2, 0n), Nat.add(T2, 0n),
      NO.le_add_mono(o, 2n, T1, T1, ho, NO.le_refl(T1)), NO.le_refl(Nat.add(T2, 0n))),
    NO.le_add_mono(Pn, Bn, Nat.add(5n+Pd, 0n), Nat.add(5n+Bd, 0n), hpn,
      NO.le_add_mono(5n+Pd, 5n+Bd, 0n, 0n, hpd, NO.le_refl(0n))))
  +eM = Equal.cong(Nat, Nat, y => Nat.add(F, y), Me, Nat.add(5n, Nat.add(SS, Nat.add(XX, GG))), shape(dNE, G1, s0, dNE, G2, s0))
  +eR = Equal.trans(Nat, RHS, Nat.add(Nat.add(dN, F), Nat.add(5n, Nat.add(SS, Nat.add(YY, CC)))), R1,
    Equal.trans(Nat, RHS, Nat.add(Nat.add(dN, F), Ms), Nat.add(Nat.add(dN, F), Nat.add(5n, Nat.add(SS, Nat.add(YY, CC)))),
      Equal.cong(Nat, Nat, y => Nat.add(y, Ms), Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)), Nat.add(dN, F), eq_sb(dN, T1, T2)),
      Equal.cong(Nat, Nat, y => Nat.add(Nat.add(dN, F), y), Ms, Nat.add(5n, Nat.add(SS, Nat.add(YY, CC))), shape(dN, CS, s0, dN, CS, s0))),
    eq_rhs(dN, F, SS, YY, CC))
  +core = cancel_intro(F, Nat.add(5n, Nat.add(SS, Nat.add(XX, GG))), Nat.add(5n, Nat.add(SS, Nat.add(Nat.add(dN, YY), CC))),
    cancel_intro(SS, Nat.add(XX, GG), Nat.add(Nat.add(dN, YY), CC), hB))
  NO.le_trans(Nat.add(Nat.add(Nat.add(o, T1), Nat.add(T2, 0n)), Nat.add(Pn, Nat.add(5n+Pd, 0n))), Nat.add(F, Me), RHS, step1,
    NO.le_trans(Nat.add(F, Me), L1, RHS, NO.le_of_eq(Nat.add(F, Me), L1, eM),
      NO.le_trans(L1, R1, RHS, core, NO.le_of_eq(R1, RHS, Equal.sym(Nat, RHS, R1, eR)))))

# ==== 5. finite tables (K <= 10 chains) ====

# the largest combine-plus-penalty count over the chains of K (pairs + tail of 3, err_pfix.bend chain_c)
def gmax(K: Nat) -> Nat:
  match K:
    case 0n:
      0n
    case 1n+K1:
      match K1:
        case 0n:
          0n
        case 1n+K2:
          match K2:
            case 0n:
              2n
            case 1n+K3:
              match K3:
                case 0n:
                  3n
                case 1n+K4:
                  match K4:
                    case 0n:
                      4n
                    case 1n+K5:
                      match K5:
                        case 0n:
                          5n
                        case 1n+K6:
                          match K6:
                            case 0n:
                              6n
                            case 1n+K7:
                              match K7:
                                case 0n:
                                  6n
                                case 1n+K8:
                                  match K8:
                                    case 0n:
                                      7n
                                    case 1n+K9:
                                      match K9:
                                        case 0n:
                                          7n
                                        case 1n+K10:
                                          8n

# the largest masked-head penalty of chain k of K: 1 iff k >= 1 and K <= k + 3 (err_pfix_geom_proof.bend pg_head_pen)
def pb(+k: Nat, +K: Nat) -> Nat:
  bitn(Bool.and(Nat.is_le(1n, k), Nat.is_le(K, Nat.add(k, 3n))))

def absurd_le(-G: Type, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(a, b) == False{} : Bool}) -> G:
  Empty.absurd(G, NO.false_true(Equal.trans(Bool, False{}, Nat.is_le(a, b), True{}, Equal.sym(Bool, Nat.is_le(a, b), False{}, f), h)))


# the chain table entry: chain k of K pays at most gmax(K) in combine roundings plus penalty
def GT(+K: Nat, +k: Nat) -> Type:
  {Nat.is_le(Nat.add(Ef.chain_c(k, K), pb(k, K)), gmax(K)) == True{} : Bool}

def g_tab_k(+K: Nat, +k: Nat, hk: {Nat.is_lt(k, K) == True{} : Bool}, h2: {Nat.is_le(2n, K) == True{} : Bool},
    h10: {Nat.is_le(K, 10n) == True{} : Bool}) -> GT(K, k):
  match K:
    case 0n:
      Empty.absurd(GT(0n, k), NO.false_true(h2))
    case 1n+K0:
      match K0:
        case 0n:
          Empty.absurd(GT(1n, k), NO.false_true(h2))
        case 1n+K1:
          match K1:
            case 0n:
              match k:
                case 0n:
                  {==}
                case 1n+j0:
                  match j0:
                    case 0n:
                      {==}
                    case 1n+j1:
                      match j1:
                        case 0n:
                          Empty.absurd(GT(2n, 2n), NO.false_true(hk))
                        case 1n+z:
                          Empty.absurd(GT(2n, 3n+z), NO.false_true(hk))
            case 1n+K2:
              match K2:
                case 0n:
                  match k:
                    case 0n:
                      {==}
                    case 1n+j0:
                      match j0:
                        case 0n:
                          {==}
                        case 1n+j1:
                          match j1:
                            case 0n:
                              {==}
                            case 1n+j2:
                              match j2:
                                case 0n:
                                  Empty.absurd(GT(3n, 3n), NO.false_true(hk))
                                case 1n+z:
                                  Empty.absurd(GT(3n, 4n+z), NO.false_true(hk))
                case 1n+K3:
                  match K3:
                    case 0n:
                      match k:
                        case 0n:
                          {==}
                        case 1n+j0:
                          match j0:
                            case 0n:
                              {==}
                            case 1n+j1:
                              match j1:
                                case 0n:
                                  {==}
                                case 1n+j2:
                                  match j2:
                                    case 0n:
                                      {==}
                                    case 1n+j3:
                                      match j3:
                                        case 0n:
                                          Empty.absurd(GT(4n, 4n), NO.false_true(hk))
                                        case 1n+z:
                                          Empty.absurd(GT(4n, 5n+z), NO.false_true(hk))
                    case 1n+K4:
                      match K4:
                        case 0n:
                          match k:
                            case 0n:
                              {==}
                            case 1n+j0:
                              match j0:
                                case 0n:
                                  {==}
                                case 1n+j1:
                                  match j1:
                                    case 0n:
                                      {==}
                                    case 1n+j2:
                                      match j2:
                                        case 0n:
                                          {==}
                                        case 1n+j3:
                                          match j3:
                                            case 0n:
                                              {==}
                                            case 1n+j4:
                                              match j4:
                                                case 0n:
                                                  Empty.absurd(GT(5n, 5n), NO.false_true(hk))
                                                case 1n+z:
                                                  Empty.absurd(GT(5n, 6n+z), NO.false_true(hk))
                        case 1n+K5:
                          match K5:
                            case 0n:
                              match k:
                                case 0n:
                                  {==}
                                case 1n+j0:
                                  match j0:
                                    case 0n:
                                      {==}
                                    case 1n+j1:
                                      match j1:
                                        case 0n:
                                          {==}
                                        case 1n+j2:
                                          match j2:
                                            case 0n:
                                              {==}
                                            case 1n+j3:
                                              match j3:
                                                case 0n:
                                                  {==}
                                                case 1n+j4:
                                                  match j4:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j5:
                                                      match j5:
                                                        case 0n:
                                                          Empty.absurd(GT(6n, 6n), NO.false_true(hk))
                                                        case 1n+z:
                                                          Empty.absurd(GT(6n, 7n+z), NO.false_true(hk))
                            case 1n+K6:
                              match K6:
                                case 0n:
                                  match k:
                                    case 0n:
                                      {==}
                                    case 1n+j0:
                                      match j0:
                                        case 0n:
                                          {==}
                                        case 1n+j1:
                                          match j1:
                                            case 0n:
                                              {==}
                                            case 1n+j2:
                                              match j2:
                                                case 0n:
                                                  {==}
                                                case 1n+j3:
                                                  match j3:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j4:
                                                      match j4:
                                                        case 0n:
                                                          {==}
                                                        case 1n+j5:
                                                          match j5:
                                                            case 0n:
                                                              {==}
                                                            case 1n+j6:
                                                              match j6:
                                                                case 0n:
                                                                  Empty.absurd(GT(7n, 7n), NO.false_true(hk))
                                                                case 1n+z:
                                                                  Empty.absurd(GT(7n, 8n+z), NO.false_true(hk))
                                case 1n+K7:
                                  match K7:
                                    case 0n:
                                      match k:
                                        case 0n:
                                          {==}
                                        case 1n+j0:
                                          match j0:
                                            case 0n:
                                              {==}
                                            case 1n+j1:
                                              match j1:
                                                case 0n:
                                                  {==}
                                                case 1n+j2:
                                                  match j2:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j3:
                                                      match j3:
                                                        case 0n:
                                                          {==}
                                                        case 1n+j4:
                                                          match j4:
                                                            case 0n:
                                                              {==}
                                                            case 1n+j5:
                                                              match j5:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+j6:
                                                                  match j6:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+j7:
                                                                      match j7:
                                                                        case 0n:
                                                                          Empty.absurd(GT(8n, 8n), NO.false_true(hk))
                                                                        case 1n+z:
                                                                          Empty.absurd(GT(8n, 9n+z), NO.false_true(hk))
                                    case 1n+K8:
                                      match K8:
                                        case 0n:
                                          match k:
                                            case 0n:
                                              {==}
                                            case 1n+j0:
                                              match j0:
                                                case 0n:
                                                  {==}
                                                case 1n+j1:
                                                  match j1:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j2:
                                                      match j2:
                                                        case 0n:
                                                          {==}
                                                        case 1n+j3:
                                                          match j3:
                                                            case 0n:
                                                              {==}
                                                            case 1n+j4:
                                                              match j4:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+j5:
                                                                  match j5:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+j6:
                                                                      match j6:
                                                                        case 0n:
                                                                          {==}
                                                                        case 1n+j7:
                                                                          match j7:
                                                                            case 0n:
                                                                              {==}
                                                                            case 1n+j8:
                                                                              match j8:
                                                                                case 0n:
                                                                                  Empty.absurd(GT(9n, 9n), NO.false_true(hk))
                                                                                case 1n+z:
                                                                                  Empty.absurd(GT(9n, 10n+z), NO.false_true(hk))
                                        case 1n+K9:
                                          match K9:
                                            case 0n:
                                              match k:
                                                case 0n:
                                                  {==}
                                                case 1n+j0:
                                                  match j0:
                                                    case 0n:
                                                      {==}
                                                    case 1n+j1:
                                                      match j1:
                                                        case 0n:
                                                          {==}
                                                        case 1n+j2:
                                                          match j2:
                                                            case 0n:
                                                              {==}
                                                            case 1n+j3:
                                                              match j3:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+j4:
                                                                  match j4:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+j5:
                                                                      match j5:
                                                                        case 0n:
                                                                          {==}
                                                                        case 1n+j6:
                                                                          match j6:
                                                                            case 0n:
                                                                              {==}
                                                                            case 1n+j7:
                                                                              match j7:
                                                                                case 0n:
                                                                                  {==}
                                                                                case 1n+j8:
                                                                                  match j8:
                                                                                    case 0n:
                                                                                      {==}
                                                                                    case 1n+j9:
                                                                                      match j9:
                                                                                        case 0n:
                                                                                          Empty.absurd(GT(10n, 10n), NO.false_true(hk))
                                                                                        case 1n+z:
                                                                                          Empty.absurd(GT(10n, 11n+z), NO.false_true(hk))
                                            case 1n+K10:
                                              Empty.absurd(GT(11n+K10, k), NO.false_true(h10))

def gm_le8(K: Nat) -> {Nat.is_le(gmax(K), 8n) == True{} : Bool}:
  match K:
    case 0n:
      {==}
    case 1n+K1:
      match K1:
        case 0n:
          {==}
        case 1n+K2:
          match K2:
            case 0n:
              {==}
            case 1n+K3:
              match K3:
                case 0n:
                  {==}
                case 1n+K4:
                  match K4:
                    case 0n:
                      {==}
                    case 1n+K5:
                      match K5:
                        case 0n:
                          {==}
                        case 1n+K6:
                          match K6:
                            case 0n:
                              {==}
                            case 1n+K7:
                              match K7:
                                case 0n:
                                  {==}
                                case 1n+K8:
                                  match K8:
                                    case 0n:
                                      {==}
                                    case 1n+K9:
                                      match K9:
                                        case 0n:
                                          {==}
                                        case 1n+K10:
                                          {==}

# gmax(K) <= K
def gm_le_k(+K: Nat) -> {Nat.is_le(gmax(K), K) == True{} : Bool}:
  match K:
    case 0n:
      {==}
    case 1n+K1:
      match K1:
        case 0n:
          {==}
        case 1n+K2:
          match K2:
            case 0n:
              {==}
            case 1n+K3:
              match K3:
                case 0n:
                  {==}
                case 1n+K4:
                  match K4:
                    case 0n:
                      {==}
                    case 1n+K5:
                      match K5:
                        case 0n:
                          {==}
                        case 1n+K6:
                          match K6:
                            case 0n:
                              {==}
                            case 1n+K7:
                              match K7:
                                case 0n:
                                  {==}
                                case 1n+K8:
                                  match K8:
                                    case 0n:
                                      {==}
                                    case 1n+K9:
                                      match K9:
                                        case 0n:
                                          {==}
                                        case 1n+K10:
                                          NO.le_trans(8n, 10n, 10n+K10, {==}, NO.le_add_r(10n, K10))

# the split-table inequality (halved budget, E, N = chain / split lengths, K chains, Ks splits):
#   2 (E - 1) + 1 + gmax(K) <= 2 (N - 1) + ((N - 1) + 1 + Ks)
def tab_ineq(+E: Nat, +N: Nat, +K: Nat, +Ks: Nat) -> Bool:
  Nat.is_le(Nat.add(Nat.double(Nat.sub(E, 1n)), 1n+gmax(K)), Nat.add(Nat.double(Nat.sub(N, 1n)), Nat.add(Nat.sub(N, 1n), 1n+Ks)))

# true unless the entry is in the split case's domain (feasible, E <= N, K >= 2, E >= 1, Ks >= 2) and violated
def tab(+E: Nat, +N: Nat, +K: Nat, +Ks: Nat) -> Bool:
  Bool.or(Nat.is_le(Nat.mul(Ks, N), Nat.mul(Nat.sub(K, 1n), E)), Bool.or(Nat.is_lt(N, E), Bool.or(Nat.is_lt(K, 2n),
    Bool.or(Nat.is_lt(E, 1n), Bool.or(Nat.is_lt(Ks, 2n), tab_ineq(E, N, K, Ks))))))

def ck_s(+E: Nat, +N: Nat, +K: Nat, +m: Nat) -> Bool:
  match m:
    case 0n:
      tab(E, N, K, 0n)
    case 1n+j:
      Bool.and(tab(E, N, K, 1n+j), ck_s(E, N, K, j))

def ck_k(+E: Nat, +N: Nat, +m: Nat) -> Bool:
  match m:
    case 0n:
      ck_s(E, N, 0n, 7n)
    case 1n+j:
      Bool.and(ck_s(E, N, 1n+j, 7n), ck_k(E, N, j))

def ck_e(+N: Nat, +m: Nat) -> Bool:
  match m:
    case 0n:
      ck_k(0n, N, 10n)
    case 1n+j:
      Bool.and(ck_k(1n+j, N, 10n), ck_e(N, j))

def ck_n(+m: Nat) -> Bool:
  match m:
    case 0n:
      ck_e(0n, 6n)
    case 1n+j:
      Bool.and(ck_e(1n+j, 6n), ck_n(j))

# every entry E, N <= 6, K <= 10, Ks <= 7 checked by computation
def ck_all() -> {ck_n(6n) == True{} : Bool}:
  {==}

def ck_s_at(+E: Nat, +N: Nat, +K: Nat, +d: Nat, +j: Nat, h: {ck_s(E, N, K, Nat.add(d, j)) == True{} : Bool})
  -> {tab(E, N, K, j) == True{} : Bool}:
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+i:
          NO.and_l(tab(E, N, K, 1n+i), ck_s(E, N, K, i), h)
    case 1n+e:
      ck_s_at(E, N, K, e, j, NO.and_r(tab(E, N, K, 1n+Nat.add(e, j)), ck_s(E, N, K, Nat.add(e, j)), h))

def ck_k_at(+E: Nat, +N: Nat, +d: Nat, +j: Nat, h: {ck_k(E, N, Nat.add(d, j)) == True{} : Bool})
  -> {ck_s(E, N, j, 7n) == True{} : Bool}:
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+i:
          NO.and_l(ck_s(E, N, 1n+i, 7n), ck_k(E, N, i), h)
    case 1n+e:
      ck_k_at(E, N, e, j, NO.and_r(ck_s(E, N, 1n+Nat.add(e, j), 7n), ck_k(E, N, Nat.add(e, j)), h))

def ck_e_at(+N: Nat, +d: Nat, +j: Nat, h: {ck_e(N, Nat.add(d, j)) == True{} : Bool})
  -> {ck_k(j, N, 10n) == True{} : Bool}:
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+i:
          NO.and_l(ck_k(1n+i, N, 10n), ck_e(N, i), h)
    case 1n+e:
      ck_e_at(N, e, j, NO.and_r(ck_k(1n+Nat.add(e, j), N, 10n), ck_e(N, Nat.add(e, j)), h))

def ck_n_at(+d: Nat, +j: Nat, h: {ck_n(Nat.add(d, j)) == True{} : Bool})
  -> {ck_e(j, 6n) == True{} : Bool}:
  match d:
    case 0n:
      match j:
        case 0n:
          h
        case 1n+i:
          NO.and_l(ck_e(1n+i, 6n), ck_n(i), h)
    case 1n+e:
      ck_n_at(e, j, NO.and_r(ck_e(1n+Nat.add(e, j), 6n), ck_n(Nat.add(e, j)), h))

# ==== 6. budget ====

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

def le_false(+a: Nat, +b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.is_le(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, NO.false_true(h))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(0n, 1n+bp) == False{} : Bool}, NO.false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      le_false(ap, bp, h)

# not (a <= b) gives b + 1 <= a
def lt_of_not_le(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(1n+b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(2n+bp, 0n) == True{} : Bool}, NO.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+ap 0n:
      NO.le_zero(ap)
    case 1n+ap 1n+bp:
      lt_of_not_le(ap, bp, h)

def or_r(x: Bool, -y: Bool, h: {Bool.or(x, y) == True{} : Bool}, hx: {x == False{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case False{}:
      h
    case True{}:
      Empty.absurd({y == True{} : Bool}, NO.false_true(Equal.sym(Bool, True{}, False{}, hx)))

# m == (m - j) + j for j <= m
def sub_plus(+m: Nat, +j: Nat, h: {Nat.is_le(j, m) == True{} : Bool}) -> {Nat.add(Nat.sub(m, j), j) == m : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(m, j), j), Nat.add(j, Nat.sub(m, j)), m, NO.add_comm(Nat.sub(m, j), j), NO.sub_add(m, j, h))

def sub0(+x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub1_mono(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, 1n), Nat.sub(b, 1n)) == True{} : Bool}:
  match a b:
    case 0n _:
      NO.le_zero(Nat.sub(b, 1n))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+ap, 1n), 0n) == True{} : Bool}, NO.false_true(h))
    case 1n+ap 1n+bp:
      %Equal.sym(Nat, Nat.sub(ap, 0n), ap, sub0(ap)) : {Nat.is_le(_, Nat.sub(bp, 0n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(bp, 0n), bp, sub0(bp)) : {Nat.is_le(ap, _) == True{} : Bool}
      h

def ck_n_le(+N: Nat, hN: {Nat.is_le(N, 6n) == True{} : Bool}) -> {ck_n(Nat.add(Nat.sub(6n, N), N)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.sub(6n, N), N), 6n, sub_plus(6n, N, hN)) : {ck_n(_) == True{} : Bool}
  ck_all()

def ck_e_le(+N: Nat, +E: Nat, hE: {Nat.is_le(E, 6n) == True{} : Bool}, h: {ck_e(N, 6n) == True{} : Bool})
  -> {ck_e(N, Nat.add(Nat.sub(6n, E), E)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.sub(6n, E), E), 6n, sub_plus(6n, E, hE)) : {ck_e(N, _) == True{} : Bool}
  h

def ck_k_le(+E: Nat, +N: Nat, +K: Nat, hK: {Nat.is_le(K, 10n) == True{} : Bool}, h: {ck_k(E, N, 10n) == True{} : Bool})
  -> {ck_k(E, N, Nat.add(Nat.sub(10n, K), K)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.sub(10n, K), K), 10n, sub_plus(10n, K, hK)) : {ck_k(E, N, _) == True{} : Bool}
  h

def ck_s_le(+E: Nat, +N: Nat, +K: Nat, +Ks: Nat, hKs: {Nat.is_le(Ks, 7n) == True{} : Bool}, h: {ck_s(E, N, K, 7n) == True{} : Bool})
  -> {ck_s(E, N, K, Nat.add(Nat.sub(7n, Ks), Ks)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.sub(7n, Ks), Ks), 7n, sub_plus(7n, Ks, hKs)) : {ck_s(E, N, K, _) == True{} : Bool}
  h

def tab_at(+E: Nat, +N: Nat, +K: Nat, +Ks: Nat, hE: {Nat.is_le(E, 6n) == True{} : Bool}, hN: {Nat.is_le(N, 6n) == True{} : Bool},
    hK: {Nat.is_le(K, 10n) == True{} : Bool}, hKs: {Nat.is_le(Ks, 7n) == True{} : Bool}) -> {tab(E, N, K, Ks) == True{} : Bool}:
  +h1 = ck_n_at(Nat.sub(6n, N), N, ck_n_le(N, hN))
  +h2 = ck_e_at(N, Nat.sub(6n, E), E, ck_e_le(N, E, hE, h1))
  +h3 = ck_k_at(E, N, Nat.sub(10n, K), K, ck_k_le(E, N, K, hK, h2))
  ck_s_at(E, N, K, Nat.sub(7n, Ks), Ks, ck_s_le(E, N, K, Ks, hKs, h3))

def split_small_b(+b: Bool, +E: Nat, +N: Nat, +K: Nat, +Ks: Nat, heq: {Nat.is_le(Ks, 7n) == b : Bool},
    hE1: {Nat.is_le(1n, E) == True{} : Bool}, hEN: {Nat.is_le(E, N) == True{} : Bool}, hN6: {Nat.is_le(N, 6n) == True{} : Bool},
    hK2: {Nat.is_le(2n, K) == True{} : Bool}, hK10: {Nat.is_le(K, 10n) == True{} : Bool}, hKs2: {Nat.is_le(2n, Ks) == True{} : Bool},
    hfz: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), Nat.mul(Ks, N)) == True{} : Bool}) -> {tab_ineq(E, N, K, Ks) == True{} : Bool}:
  match b:
    case True{}:
      +hEN2 = hEN
      +hN62 = hN6
      +ht = tab_at(E, N, K, Ks, NO.le_trans(E, N, 6n, hEN2, hN62), hN62, hK10, heq)
      +x5 = Bool.or(Nat.is_lt(Ks, 2n), tab_ineq(E, N, K, Ks))
      +x4 = Bool.or(Nat.is_lt(E, 1n), x5)
      +x3 = Bool.or(Nat.is_lt(K, 2n), x4)
      +x2 = Bool.or(Nat.is_lt(N, E), x3)
      or_r(Nat.is_lt(Ks, 2n), tab_ineq(E, N, K, Ks),
        or_r(Nat.is_lt(E, 1n), x5,
          or_r(Nat.is_lt(K, 2n), x4,
            or_r(Nat.is_lt(N, E), x3,
              or_r(Nat.is_le(Nat.mul(Ks, N), Nat.mul(Nat.sub(K, 1n), E)), x2, ht,
                le_false(Nat.mul(Ks, N), Nat.mul(Nat.sub(K, 1n), E), hfz)),
              lt_false(N, E, hEN2)),
            lt_false(K, 2n, hK2)),
          lt_false(E, 1n, hE1)),
        lt_false(Ks, 2n, hKs2))
    case False{}:
      +h8 = lt_of_not_le(Ks, 7n, heq)
      +S1 = Nat.sub(N, 1n)
      NO.le_add_mono(Nat.double(Nat.sub(E, 1n)), Nat.double(S1), 1n+gmax(K), Nat.add(S1, 1n+Ks),
        le_dbl(Nat.sub(E, 1n), S1, sub1_mono(E, N, hEN)),
        NO.le_trans(1n+gmax(K), 1n+Ks, Nat.add(S1, 1n+Ks), NO.le_trans(gmax(K), 8n, Ks, gm_le8(K), h8), NO.le_add_l(S1, 1n+Ks)))

def split_small(+E: Nat, +N: Nat, +K: Nat, +Ks: Nat,
    hE1: {Nat.is_le(1n, E) == True{} : Bool}, hEN: {Nat.is_le(E, N) == True{} : Bool}, hN6: {Nat.is_le(N, 6n) == True{} : Bool},
    hK2: {Nat.is_le(2n, K) == True{} : Bool}, hK10: {Nat.is_le(K, 10n) == True{} : Bool}, hKs2: {Nat.is_le(2n, Ks) == True{} : Bool},
    hfz: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), Nat.mul(Ks, N)) == True{} : Bool}) -> {tab_ineq(E, N, K, Ks) == True{} : Bool}:
  split_small_b(Nat.is_le(Ks, 7n), E, N, K, Ks, {==}, hE1, hEN, hN6, hK2, hK10, hKs2, hfz)

# the halved budget: 2 NE1 + g <= 2 N1 + (N1 + CS)
def HB(+NE1: Nat, +N1: Nat, +g: Nat, +CS: Nat) -> Type:
  {Nat.is_le(Nat.add(Nat.double(NE1), g), Nat.add(Nat.double(N1), Nat.add(N1, CS))) == True{} : Bool}

# one chain (no combine): g = 0
def hb_k1(+NE1: Nat, +N1: Nat, +CS: Nat, h: {Nat.is_le(NE1, N1) == True{} : Bool}) -> HB(NE1, N1, 0n, CS):
  %Equal.sym(Nat, Nat.add(Nat.double(NE1), 0n), Nat.double(NE1), NO.add_zero_r(Nat.double(NE1))) :
    {Nat.is_le(_, Nat.add(Nat.double(N1), Nat.add(N1, CS))) == True{} : Bool}
  NO.le_trans(Nat.double(NE1), Nat.double(N1), Nat.add(Nat.double(N1), Nat.add(N1, CS)), le_dbl(NE1, N1, h),
    NO.le_add_r(Nat.double(N1), Nat.add(N1, CS)))

# stock's chain is the whole row (unsplit, or a row inside split 0): NE1 + 1 <= N1, g <= N1 + 2
def hb_full(+NE1: Nat, +N1: Nat, +g: Nat, +CS: Nat, h1: {Nat.is_le(1n+NE1, N1) == True{} : Bool},
    hg: {Nat.is_le(g, 2n+N1) == True{} : Bool}) -> HB(NE1, N1, g, CS):
  +dNE = Nat.double(NE1)
  +dN = Nat.double(N1)
  +e = Equal.trans(Nat, Nat.add(dNE, 2n+N1), 1n+Nat.add(dNE, 1n+N1), 2n+Nat.add(dNE, N1), NO.add_succ_r(dNE, 1n+N1),
    Equal.cong(Nat, Nat, y => 1n+y, Nat.add(dNE, 1n+N1), 1n+Nat.add(dNE, N1), NO.add_succ_r(dNE, N1)))
  NO.le_trans(Nat.add(dNE, g), Nat.add(dNE, 2n+N1), Nat.add(dN, Nat.add(N1, CS)), cancel_intro(dNE, g, 2n+N1, hg),
    NO.le_trans(Nat.add(dNE, 2n+N1), 2n+Nat.add(dNE, N1), Nat.add(dN, Nat.add(N1, CS)), NO.le_of_eq(Nat.add(dNE, 2n+N1), 2n+Nat.add(dNE, N1), e),
      NO.le_trans(2n+Nat.add(dNE, N1), Nat.add(dN, N1), Nat.add(dN, Nat.add(N1, CS)),
        NO.le_add_mono(2n+dNE, dN, N1, N1, le_dbl(1n+NE1, N1, h1), NO.le_refl(N1)),
        cancel_intro(dN, N1, Nat.add(N1, CS), NO.le_add_r(N1, CS)))))

# stock split long enough (N >= 7): NE1 <= N1, N1 >= 6, g <= 9, CS >= 3
def hb_split7(+NE1: Nat, +N1: Nat, +g: Nat, +CS: Nat, h: {Nat.is_le(NE1, N1) == True{} : Bool}, h6: {Nat.is_le(6n, N1) == True{} : Bool},
    hg: {Nat.is_le(g, 9n) == True{} : Bool}, hcs: {Nat.is_le(3n, CS) == True{} : Bool}) -> HB(NE1, N1, g, CS):
  NO.le_add_mono(Nat.double(NE1), Nat.double(N1), g, Nat.add(N1, CS), le_dbl(NE1, N1, h),
    NO.le_trans(g, 9n, Nat.add(N1, CS), hg, NO.le_add_mono(6n, N1, 3n, CS, h6, hcs)))

# doubling the halved budget gives the r32 + t32 budget of sum_le
def double_up(+NE1: Nat, +N1: Nat, +G1: Nat, +G2: Nat, +g: Nat, +CS: Nat, hg1: {Nat.is_le(G1, g) == True{} : Bool},
    hg2: {Nat.is_le(G2, g) == True{} : Bool},
    +hh: {Nat.is_le(Nat.add(Nat.double(NE1), g), Nat.add(Nat.double(N1), Nat.add(N1, CS))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(Nat.double(NE1), Nat.double(NE1)), Nat.add(G1, G2)),
       Nat.add(Nat.add(Nat.double(N1), Nat.add(Nat.double(N1), Nat.double(N1))), Nat.add(CS, CS))) == True{} : Bool}:
  +dNE = Nat.double(NE1)
  +dN = Nat.double(N1)
  +R = Nat.add(dN, Nat.add(N1, CS))
  +RR = Nat.add(Nat.add(dN, Nat.add(dN, dN)), Nat.add(CS, CS))
  +eR = Equal.trans(Nat, Nat.add(R, R), Nat.add(Nat.add(dN, dN), Nat.add(Nat.add(N1, CS), Nat.add(N1, CS))), RR,
    NO.add_swap4(dN, Nat.add(N1, CS), dN, Nat.add(N1, CS)),
    Equal.trans(Nat, Nat.add(Nat.add(dN, dN), Nat.add(Nat.add(N1, CS), Nat.add(N1, CS))),
      Nat.add(Nat.add(dN, dN), Nat.add(Nat.add(N1, N1), Nat.add(CS, CS))), RR,
      Equal.cong(Nat, Nat, y => Nat.add(Nat.add(dN, dN), y), Nat.add(Nat.add(N1, CS), Nat.add(N1, CS)),
        Nat.add(Nat.add(N1, N1), Nat.add(CS, CS)), NO.add_swap4(N1, CS, N1, CS)),
      Equal.trans(Nat, Nat.add(Nat.add(dN, dN), Nat.add(Nat.add(N1, N1), Nat.add(CS, CS))),
        Nat.add(Nat.add(Nat.add(dN, dN), Nat.add(N1, N1)), Nat.add(CS, CS)), RR,
        Equal.sym(Nat, Nat.add(Nat.add(Nat.add(dN, dN), Nat.add(N1, N1)), Nat.add(CS, CS)),
          Nat.add(Nat.add(dN, dN), Nat.add(Nat.add(N1, N1), Nat.add(CS, CS))), NO.add_assoc(Nat.add(dN, dN), Nat.add(N1, N1), Nat.add(CS, CS))),
        Equal.cong(Nat, Nat, y => Nat.add(y, Nat.add(CS, CS)), Nat.add(Nat.add(dN, dN), Nat.add(N1, N1)), Nat.add(dN, Nat.add(dN, dN)),
          Equal.trans(Nat, Nat.add(Nat.add(dN, dN), Nat.add(N1, N1)), Nat.add(Nat.add(dN, dN), dN), Nat.add(dN, Nat.add(dN, dN)),
            Equal.cong(Nat, Nat, y => Nat.add(Nat.add(dN, dN), y), Nat.add(N1, N1), dN, Equal.sym(Nat, dN, Nat.add(N1, N1), dbl_add(N1))),
            NO.add_assoc(dN, dN, dN))))))
  NO.le_trans(Nat.add(Nat.add(dNE, dNE), Nat.add(G1, G2)), Nat.add(Nat.add(dNE, dNE), Nat.add(g, g)), RR,
    cancel_intro(Nat.add(dNE, dNE), Nat.add(G1, G2), Nat.add(g, g), NO.le_add_mono(G1, g, G2, g, hg1, hg2)),
    NO.le_trans(Nat.add(Nat.add(dNE, dNE), Nat.add(g, g)), Nat.add(R, R), RR,
      NO.le_trans(Nat.add(Nat.add(dNE, dNE), Nat.add(g, g)), Nat.add(Nat.add(dNE, g), Nat.add(dNE, g)), Nat.add(R, R),
        NO.le_of_eq(Nat.add(Nat.add(dNE, dNE), Nat.add(g, g)), Nat.add(Nat.add(dNE, g), Nat.add(dNE, g)), NO.add_swap4(dNE, dNE, g, g)),
        NO.le_add_mono(Nat.add(dNE, g), R, Nat.add(dNE, g), R, hh, hh)),
      NO.le_of_eq(Nat.add(R, R), RR, eR)))

# ==== 7. one composite ====

def t32_le(+o: Nat, +T1: Nat, +T2: Nat, +dN: Nat, ho: {Nat.is_le(o, 2n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.add(o, T1), Nat.add(T2, 0n)), Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n))) == True{} : Bool}:
  NO.le_add_mono(Nat.add(o, T1), 2n+Nat.add(dN, T1), Nat.add(T2, 0n), Nat.add(T2, 0n),
    NO.le_trans(Nat.add(o, T1), Nat.add(2n, T1), 2n+Nat.add(dN, T1), NO.le_add_mono(o, 2n, T1, T1, ho, NO.le_refl(T1)),
      NO.le_add_l(dN, T1)),
    NO.le_refl(Nat.add(T2, 0n)))

# a + (kb + 1) <= N1 + (sb + 1) from a + kb <= N1 + sb
def ex_part(+a: Nat, +kb: Nat, +N1: Nat, +sb: Nat, h: {Nat.is_le(Nat.add(a, kb), Nat.add(N1, sb)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, Nat.add(kb, 1n)), Nat.add(N1, Nat.add(sb, 1n))) == True{} : Bool}:
  %NO.add_assoc(a, kb, 1n) : {Nat.is_le(_, Nat.add(N1, Nat.add(sb, 1n))) == True{} : Bool}
  %NO.add_assoc(N1, sb, 1n) : {Nat.is_le(Nat.add(Nat.add(a, kb), 1n), _) == True{} : Bool}
  NO.le_add_mono(Nat.add(a, kb), Nat.add(N1, sb), 1n, 1n, h, NO.le_refl(1n))

# Every elpis composite (chains of E tiles, K chains) is dominated by stock's tile-0 composite (split 0 holding N1 + 1
# tiles, combine of Ks splits when sp), given the chain positions (t + a, td + b <= NE1), the combine-plus-penalty bound
# g of both chains, the halved budget and the ex2 counts.
def core(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, +h: Bool, +s: Nat, +kd: Nat, +td: Nat, +b: Nat, +s2: Nat,
    +N1: Nat, +sp: Bool, +Ks: Nat, +NE1: Nat, +g: Nat,
    hta: {Nat.is_le(Nat.add(t, a), NE1) == True{} : Bool},
    htb: {Nat.is_le(Nat.add(td, b), NE1) == True{} : Bool},
    hg1: {Nat.is_le(Nat.add(cbr(Nat.is_lt(1n, K), Ef.chain_c(k, K)), hp(Nat.is_lt(Nat.mul(k, E), I), Nat.is_lt(0n, I))), g) == True{} : Bool},
    hg2: {Nat.is_le(Nat.add(cbr(Nat.is_lt(1n, K), Ef.chain_c(kd, K)), hp(Nat.is_lt(Nat.mul(kd, E), I), Nat.is_lt(0n, I))), g) == True{} : Bool},
    +hh: {Nat.is_le(Nat.add(Nat.double(NE1), g), Nat.add(Nat.double(N1), Nat.add(N1, cbr(sp, Ks)))) == True{} : Bool},
    hxa: {Nat.is_le(Nat.add(a, bitn(Nat.is_lt(1n, K))), Nat.add(N1, bitn(sp))) == True{} : Bool},
    hxb: {Nat.is_le(Nat.add(b, bitn(Nat.is_lt(1n, K))), Nat.add(N1, bitn(sp))) == True{} : Bool})
  -> {Eb.dom(128n, Ef.elpis_leaf(E, K, I, k, t, a, h, s, kd, td, b, s2),
       Ef.stock_leaf(1n, sp, Ks, I, 0n, 0n, N1, False{}, s, 0n, 0n, N1, s2)) == True{} : Bool}:
  +k2 = Nat.is_lt(1n, K)
  +x0 = Nat.is_lt(0n, I)
  +C1 = cbr(k2, Ef.chain_c(k, K))
  +C2 = cbr(k2, Ef.chain_c(kd, K))
  +H1 = hp(Nat.is_lt(Nat.mul(k, E), I), x0)
  +H2 = hp(Nat.is_lt(Nat.mul(kd, E), I), x0)
  +S0 = scr(x0)
  +CS = cbr(sp, Ks)
  +dN = Nat.double(N1)
  +dNE = Nat.double(NE1)
  +o = Ef.own_t32(h)
  +T1 = Nat.sub(16n, s)
  +T2 = Nat.sub(16n, s2)
  +Pn = Nat.add(bitn(Nat.is_lt(0n, t)), Nat.add(Nat.double(a), Nat.add(C1, scr(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I)))))
  +Pd = Nat.add(bitn(Nat.is_lt(0n, td)), Nat.add(Nat.double(b), Nat.add(C2, scr(Nat.is_lt(Nat.add(Nat.mul(kd, E), td), I)))))
  +Xn = Nat.add(a, Nat.add(bitn(k2), 1n))
  +Xd = Nat.add(b, Nat.add(bitn(k2), 1n))
  +Xs = Nat.add(N1, Nat.add(bitn(sp), 1n))
  +SL = Ef.stock_leaf(1n, sp, Ks, I, 0n, 0n, N1, False{}, s, 0n, 0n, N1, s2)
  %nf_enum(E, K, I, k, t, a, h, s) : {Eb.dom(128n, Eb.add(_, Eb.add(Ef.e_den(E, K, I, kd, td, b, s2), Ef.fixed())), SL) == True{} : Bool}
  %nf_eden(E, K, I, kd, td, b, s2) : {Eb.dom(128n, Eb.add(part(Pn, Nat.add(o, T1), Xn), Eb.add(_, Ef.fixed())), SL) == True{} : Bool}
  %nf_wnum(sp, Ks, I, N1, s) : {Eb.dom(128n, Eb.add(part(Pn, Nat.add(o, T1), Xn), Eb.add(part(5n+Pd, T2, Xd), Ef.fixed())),
    Eb.add(_, Eb.add(Ef.s_den(1n, sp, Ks, I, 0n, 0n, N1, s2), Ef.fixed()))) == True{} : Bool}
  %nf_wden(sp, Ks, I, N1, s2) : {Eb.dom(128n, Eb.add(part(Pn, Nat.add(o, T1), Xn), Eb.add(part(5n+Pd, T2, Xd), Ef.fixed())),
    Eb.add(part(Nat.add(dN, Nat.add(CS, S0)), 2n+Nat.add(dN, T1), Xs), Eb.add(_, Ef.fixed()))) == True{} : Bool}
  dom_simple(Nat.add(Pn, Nat.add(5n+Pd, 0n)), Nat.add(Nat.add(o, T1), Nat.add(T2, 0n)), Nat.add(Xn, Nat.add(Xd, 0n)),
    Nat.add(Nat.add(dN, Nat.add(CS, S0)), Nat.add(5n+Nat.add(dN, Nat.add(CS, S0)), 0n)),
    Nat.add(2n+Nat.add(dN, T1), Nat.add(T2, 0n)), Nat.add(Xs, Nat.add(Xs, 0n)),
    t32_le(o, T1, T2, dN, own_le2(h)),
    sum_le(o, T1, T2, Pn, Pd, dNE, Nat.add(C1, H1), Nat.add(C2, H2), S0, dN, CS, own_le2(h),
      chain_bound2(t, Nat.mul(k, E), a, NE1, I, C1, hta),
      chain_bound2(td, Nat.mul(kd, E), b, NE1, I, C2, htb),
      double_up(NE1, N1, Nat.add(C1, H1), Nat.add(C2, H2), g, CS, hg1, hg2, hh)),
    NO.le_add_mono(Xn, Xs, Nat.add(Xd, 0n), Nat.add(Xs, 0n), ex_part(a, bitn(k2), N1, bitn(sp), hxa),
      NO.le_add_mono(Xd, Xs, 0n, 0n, ex_part(b, bitn(k2), N1, bitn(sp), hxb), NO.le_refl(0n))))

# ==== 8. from the kernel's integers to the core's hypotheses ====

def min_eq_l(+a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.min(1n+ap, 0n) == 1n+ap : Nat}, NO.false_true(h))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.min(ap, bp), ap, min_eq_l(ap, bp, h))

def le_min(+x: Nat, +a: Nat, +b: Nat, ha: {Nat.is_le(x, a) == True{} : Bool}, hb: {Nat.is_le(x, b) == True{} : Bool})
  -> {Nat.is_le(x, Nat.min(a, b)) == True{} : Bool}:
  match x a b:
    case 0n _ _:
      NO.le_zero(Nat.min(a, b))
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_le(1n+xp, Nat.min(0n, b)) == True{} : Bool}, NO.false_true(ha))
    case 1n+xp 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+xp, Nat.min(1n+ap, 0n)) == True{} : Bool}, NO.false_true(hb))
    case 1n+xp 1n+ap 1n+bp:
      le_min(xp, ap, bp, ha, hb)

def lt_succ(+T: Nat, +d: Nat, h: {Nat.is_le(T, d) == True{} : Bool}) -> {Nat.is_lt(T, 1n+d) == True{} : Bool}:
  match T d:
    case 0n _:
      {==}
    case 1n+tp 0n:
      Empty.absurd({Nat.is_lt(1n+tp, 1n) == True{} : Bool}, NO.false_true(h))
    case 1n+tp 1n+dp:
      lt_succ(tp, dp, h)

def lt0_le1(+I: Nat, h: {Nat.is_lt(0n, I) == True{} : Bool}) -> {Nat.is_le(1n, I) == True{} : Bool}:
  match I:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(h))
    case 1n+ip:
      NO.le_zero(ip)

def not_lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case _ 0n:
      NO.le_zero(a)
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, NO.false_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n+ap 1n+bp:
      not_lt_le(ap, bp, h)

def hp_same(+x: Bool) -> {hp(x, x) == 0n : Nat}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def pen_one(+k: Nat, +K: Nat, hh: {Nat.is_le(1n, k) == True{} : Bool} & {Nat.is_le(K, Nat.add(k, 3n)) == True{} : Bool})
  -> {Nat.is_le(1n, pb(k, K)) == True{} : Bool}:
  (h1, h3) = hh
  %Equal.sym(Bool, Nat.is_le(1n, k), True{}, h1) : {Nat.is_le(1n, bitn(Bool.and(_, Nat.is_le(K, Nat.add(k, 3n))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(K, Nat.add(k, 3n)), True{}, h3) : {Nat.is_le(1n, bitn(Bool.and(True{}, _))) == True{} : Bool}
  {==}

# the masked-head penalty is at most pb(k, K): it is 1 only for a chain head k E >= I >= 1, which is one of the last 3
def hp_le_pb_b(+xH: Bool, +x0: Bool, +E: Nat, +n: Nat, +K: Nat, +I: Nat, +k: Nat,
    eH: {Nat.is_lt(Nat.mul(k, E), I) == xH : Bool}, e0: {Nat.is_lt(0n, I) == x0 : Bool},
    hE: {Nat.is_le(1n, E) == True{} : Bool}, hI3: {Nat.is_le(n, Nat.add(I, 3n)) == True{} : Bool},
    klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool})
  -> {Nat.is_le(hp(xH, x0), pb(k, K)) == True{} : Bool}:
  match xH:
    case True{}:
      NO.le_zero(pb(k, K))
    case False{}:
      match x0:
        case False{}:
          NO.le_zero(pb(k, K))
        case True{}:
          pen_one(k, K, PG.pg_head_pen(E, n, K, I, k, hE, lt0_le1(I, e0), not_lt_le(Nat.mul(k, E), I, eH), hI3, klo))

def no_lt0(-G: Type, +x: Nat, h: {Nat.is_lt(x, 0n) == True{} : Bool}) -> G:
  match x:
    case 0n:
      Empty.absurd(G, NO.false_true(h))
    case 1n+xp:
      Empty.absurd(G, NO.false_true(h))

# chain k's combine plus penalty is at most g = cbr(K > 1, gmax(K))
def g_bound(+K: Nat, +k: Nat, +E: Nat, +I: Nat, +n: Nat, hk: {Nat.is_lt(k, K) == True{} : Bool},
    hK10: {Nat.is_le(K, 10n) == True{} : Bool}, hE: {Nat.is_le(1n, E) == True{} : Bool},
    hI3: {Nat.is_le(n, Nat.add(I, 3n)) == True{} : Bool}, klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(cbr(Nat.is_lt(1n, K), Ef.chain_c(k, K)), hp(Nat.is_lt(Nat.mul(k, E), I), Nat.is_lt(0n, I))),
       cbr(Nat.is_lt(1n, K), gmax(K))) == True{} : Bool}:
  match K:
    case 0n:
      match k:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.add(0n, hp(Nat.is_lt(0n, I), Nat.is_lt(0n, I))), 0n) == True{} : Bool}, NO.false_true(hk))
        case 1n+kp:
          Empty.absurd({Nat.is_le(Nat.add(0n, hp(Nat.is_lt(Nat.mul(1n+kp, E), I), Nat.is_lt(0n, I))), 0n) == True{} : Bool}, NO.false_true(hk))
    case 1n+K1:
      match K1:
        case 0n:
          match k:
            case 0n:
              %Equal.sym(Nat, hp(Nat.is_lt(0n, I), Nat.is_lt(0n, I)), 0n, hp_same(Nat.is_lt(0n, I))) : {Nat.is_le(Nat.add(0n, _), 0n) == True{} : Bool}
              {==}
            case 1n+kp:
              no_lt0({Nat.is_le(Nat.add(0n, hp(Nat.is_lt(Nat.mul(1n+kp, E), I), Nat.is_lt(0n, I))), 0n) == True{} : Bool}, kp, hk)
        case 1n+K2:
          +KK = {2n+K2 : Nat}
          +c = Ef.chain_c(k, KK)
          +xH = Nat.is_lt(Nat.mul(k, E), I)
          +x0 = Nat.is_lt(0n, I)
          NO.le_trans(Nat.add(c, hp(xH, x0)), Nat.add(c, pb(k, KK)), gmax(KK),
            cancel_intro(c, hp(xH, x0), pb(k, KK), hp_le_pb_b(xH, x0, E, n, KK, I, k, {==}, {==}, hE, hI3, klo)),
            g_tab_k(KK, k, hk, NO.le_zero(K2), hK10))

def lt_le_succ(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, NO.false_true(h))
    case 0n 1n+bp:
      NO.le_zero(bp)
    case 1n+ap 1n+bp:
      lt_le_succ(ap, bp, h)

# a row of the block (p < nh <= q64 + 64) has p <= q64 + 63
def ple63(+p: Nat, +nh: Nat, +q64: Nat, phi: {Nat.is_lt(p, nh) == True{} : Bool},
    nhi: {Nat.is_le(nh, Nat.add(q64, 64n)) == True{} : Bool}) -> {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool}:
  %NO.add_succ_r(q64, 63n) : {Nat.is_le(1n+p, _) == True{} : Bool}
  NO.le_trans(1n+p, nh, Nat.add(q64, 64n), lt_le_succ(p, nh, phi), nhi)

# t + 1 <= L gives t <= L - 1
def pred_le(+t: Nat, +L: Nat, h: {Nat.is_le(1n+t, L) == True{} : Bool}) -> {Nat.is_le(t, Nat.sub(L, 1n)) == True{} : Bool}:
  match L:
    case 0n:
      Empty.absurd({Nat.is_le(t, 0n) == True{} : Bool}, NO.false_true(h))
    case 1n+Lp:
      %Equal.sym(Nat, Nat.sub(Lp, 0n), Lp, sub0(Lp)) : {Nat.is_le(t, _) == True{} : Bool}
      h

def le_min_pair(+x: Nat, +a: Nat, +b: Nat, hh: {Nat.is_le(x, a) == True{} : Bool} & {Nat.is_le(x, b) == True{} : Bool})
  -> {Nat.is_le(x, Nat.min(a, b)) == True{} : Bool}:
  (ha, hb) = hh
  le_min(x, a, b, ha, hb)

# a key at chain-local tile t (t + 1 <= L, L = chain_len) has t + (L - 1 - t) <= min(E, n) - 1 later-tile positions
def pos_bound(+n: Nat, +E: Nat, +k: Nat, +t: Nat, htl: {Nat.is_le(1n+t, Ef.chain_len(n, E, k)) == True{} : Bool})
  -> {Nat.is_le(Nat.add(t, Nat.sub(Nat.sub(Ef.chain_len(n, E, k), 1n), t)), Nat.sub(Nat.min(E, n), 1n)) == True{} : Bool}:
  +L = Ef.chain_len(n, E, k)
  +L1 = Nat.sub(L, 1n)
  %Equal.sym(Nat, Nat.add(t, Nat.sub(L1, t)), L1, NO.sub_add(L1, t, pred_le(t, L, htl))) :
    {Nat.is_le(_, Nat.sub(Nat.min(E, n), 1n)) == True{} : Bool}
  sub1_mono(L, Nat.min(E, n), le_min_pair(L, E, n, PG.pg_chain_len(n, E, k)))

def succ_pred(+x: Nat, h: {Nat.is_le(1n, x) == True{} : Bool}) -> {1n+Nat.sub(x, 1n) == x : Nat}:
  match x:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, NO.false_true(h))
    case 1n+xp:
      %Equal.sym(Nat, Nat.sub(xp, 0n), xp, sub0(xp)) : {1n+_ == 1n+xp : Nat}
      {==}

def le_mul_E(+x: Nat, +E: Nat, +hE: {Nat.is_le(1n, E) == True{} : Bool}) -> {Nat.is_le(x, Nat.mul(x, E)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+xp:
      NO.le_add_mono(1n, E, xp, Nat.mul(xp, E), hE, le_mul_E(xp, E, hE))

def lt_of_succ_le(+a: Nat, +c: Nat, h: {Nat.is_le(1n+a, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a c:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, NO.false_true(h))
    case 0n 1n+cp:
      {==}
    case 1n+ap 1n+cp:
      lt_of_succ_le(ap, cp, h)

def lt_of_le_lt(+a: Nat, +b: Nat, +c: Nat, hab: {Nat.is_le(a, b) == True{} : Bool}, hbc: {Nat.is_lt(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  lt_of_succ_le(a, c, NO.le_trans(1n+a, 1n+b, c, hab, lt_le_succ(b, c, hbc)))

def lt_le_trans(+a: Nat, +b: Nat, +c: Nat, hab: {Nat.is_lt(a, b) == True{} : Bool}, hbc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  lt_of_succ_le(a, c, NO.le_trans(1n+a, b, c, lt_le_succ(a, b, hab), hbc))

def bitn_le1(+x: Bool) -> {Nat.is_le(bitn(x), 1n) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# with K >= 2 chains of E tiles: E + 1 <= n and K <= n
def k2_e(+K2: Nat, +E: Nat, +n: Nat, klo: {Nat.is_lt(Nat.mul(1n+K2, E), n) == True{} : Bool}) -> {Nat.is_le(1n+E, n) == True{} : Bool}:
  lt_le_succ(E, n, lt_of_le_lt(E, Nat.mul(1n+K2, E), n, NO.le_add_r(E, Nat.mul(K2, E)), klo))

def k2_n(+K2: Nat, +E: Nat, +n: Nat, hE: {Nat.is_le(1n, E) == True{} : Bool}, klo: {Nat.is_lt(Nat.mul(1n+K2, E), n) == True{} : Bool})
  -> {Nat.is_le(2n+K2, n) == True{} : Bool}:
  lt_le_succ(1n+K2, n, lt_of_le_lt(1n+K2, Nat.mul(1n+K2, E), n, le_mul_E(1n+K2, E, hE), klo))

def e_pred_le(+E: Nat, +n: Nat, hE: {Nat.is_le(1n, E) == True{} : Bool}, hEn: {Nat.is_le(1n+E, n) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.sub(E, 1n), Nat.sub(n, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.sub(E, 1n), E, succ_pred(E, hE)) : {Nat.is_le(_, Nat.sub(n, 1n)) == True{} : Bool}
  pred_le(E, n, hEn)

def g_le_n(+KK: Nat, +n: Nat, hn: {Nat.is_le(1n, n) == True{} : Bool}, hKn: {Nat.is_le(KK, n) == True{} : Bool})
  -> {Nat.is_le(1n+gmax(KK), 2n+Nat.sub(n, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.sub(n, 1n), n, succ_pred(n, hn)) : {Nat.is_le(gmax(KK), _) == True{} : Bool}
  NO.le_trans(gmax(KK), KK, n, gm_le_k(KK), hKn)

def ne_le_n(+E: Nat, +n: Nat) -> {Nat.is_le(Nat.sub(Nat.min(E, n), 1n), Nat.sub(n, 1n)) == True{} : Bool}:
  sub1_mono(Nat.min(E, n), n, PG.pg_min_le_r(E, n))

# stock's chain is the row (unsplit, or the row inside split 0): N = n
def hh_full(+K: Nat, +E: Nat, +n: Nat, +sp: Bool, +Ks: Nat, +hE: {Nat.is_le(1n, E) == True{} : Bool}, hn: {Nat.is_le(1n, n) == True{} : Bool},
    +klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool})
  -> HB(Nat.sub(Nat.min(E, n), 1n), Nat.sub(n, 1n), cbr(Nat.is_lt(1n, K), gmax(K)), cbr(sp, Ks)):
  match K:
    case 0n:
      hb_k1(Nat.sub(Nat.min(E, n), 1n), Nat.sub(n, 1n), cbr(sp, Ks), ne_le_n(E, n))
    case 1n+K1:
      match K1:
        case 0n:
          hb_k1(Nat.sub(Nat.min(E, n), 1n), Nat.sub(n, 1n), cbr(sp, Ks), ne_le_n(E, n))
        case 1n+K2:
          +KK = {2n+K2 : Nat}
          +hEn = k2_e(K2, E, n, klo)
          +N1 = Nat.sub(n, 1n)
          %Equal.sym(Nat, Nat.min(E, n), E, min_eq_l(E, n, NO.le_trans(E, 1n+E, n, NO.le_succ(E), hEn))) :
            {Nat.is_le(Nat.add(Nat.double(Nat.sub(_, 1n)), 1n+gmax(KK)), Nat.add(Nat.double(N1), Nat.add(N1, cbr(sp, Ks)))) == True{} : Bool}
          hb_full(Nat.sub(E, 1n), N1, 1n+gmax(KK), cbr(sp, Ks), e_pred_le(E, n, hE, hEn), g_le_n(KK, n, hn, k2_n(K2, E, n, hE, klo)))

# NE1 + 0 <= N1 + sb
def hrel_k1(+E: Nat, +n: Nat, +sb: Nat)
  -> {Nat.is_le(Nat.add(Nat.sub(Nat.min(E, n), 1n), 0n), Nat.add(Nat.sub(n, 1n), sb)) == True{} : Bool}:
  +NE1 = Nat.sub(Nat.min(E, n), 1n)
  +N1 = Nat.sub(n, 1n)
  %Equal.sym(Nat, Nat.add(NE1, 0n), NE1, NO.add_zero_r(NE1)) : {Nat.is_le(_, Nat.add(N1, sb)) == True{} : Bool}
  NO.le_trans(NE1, N1, Nat.add(N1, sb), ne_le_n(E, n), NO.le_add_r(N1, sb))

# NE1 + 1 <= N1 + sb when E + 1 <= n
def hrel_k2(+E: Nat, +n: Nat, +sb: Nat, +hE: {Nat.is_le(1n, E) == True{} : Bool}, +hEn: {Nat.is_le(1n+E, n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.sub(Nat.min(E, n), 1n), 1n), Nat.add(Nat.sub(n, 1n), sb)) == True{} : Bool}:
  +N1 = Nat.sub(n, 1n)
  %Equal.sym(Nat, Nat.min(E, n), E, min_eq_l(E, n, NO.le_trans(E, 1n+E, n, NO.le_succ(E), hEn))) :
    {Nat.is_le(Nat.add(Nat.sub(_, 1n), 1n), Nat.add(N1, sb)) == True{} : Bool}
  %NO.add_comm(1n, Nat.sub(E, 1n)) : {Nat.is_le(_, Nat.add(N1, sb)) == True{} : Bool}
  NO.le_trans(1n+Nat.sub(E, 1n), N1, Nat.add(N1, sb), e_pred_le(E, n, hE, hEn), NO.le_add_r(N1, sb))

# ex2 relation, stock's chain = the row: NE1 + [K > 1] <= N1 + sb
def hrel_full(+K: Nat, +E: Nat, +n: Nat, +sb: Nat, +hE: {Nat.is_le(1n, E) == True{} : Bool},
    +klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.sub(Nat.min(E, n), 1n), bitn(Nat.is_lt(1n, K))), Nat.add(Nat.sub(n, 1n), sb)) == True{} : Bool}:
  match K:
    case 0n:
      hrel_k1(E, n, sb)
    case 1n+K1:
      match K1:
        case 0n:
          hrel_k1(E, n, sb)
        case 1n+K2:
          hrel_k2(E, n, sb, hE, k2_e(K2, E, n, klo))

def ne_le_N(+E: Nat, +n: Nat, +N: Nat, hEN: {Nat.is_le(E, N) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(Nat.min(E, n), 1n), Nat.sub(N, 1n)) == True{} : Bool}:
  sub1_mono(Nat.min(E, n), N, NO.le_trans(Nat.min(E, n), E, N, PG.pg_min_le_l(E, n), hEN))

def le_of_lt(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  NO.le_trans(a, 1n+a, b, NO.le_succ(a), lt_le_succ(a, b, h))

def hh_split_b(+b: Bool, +K2: Nat, +E: Nat, +N: Nat, +n: Nat, +Ks: Nat, heq: {Nat.is_le(7n, N) == b : Bool},
    +hE: {Nat.is_le(1n, E) == True{} : Bool}, klo: {Nat.is_lt(Nat.mul(1n+K2, E), n) == True{} : Bool},
    hK10: {Nat.is_le(2n+K2, 10n) == True{} : Bool}, +hEN: {Nat.is_le(E, N) == True{} : Bool},
    +hKs2: {Nat.is_le(2n, Ks) == True{} : Bool}, hcov: {Nat.is_le(n, Nat.mul(Ks, N)) == True{} : Bool})
  -> HB(Nat.sub(E, 1n), Nat.sub(N, 1n), 1n+gmax(2n+K2), 1n+Ks):
  match b:
    case True{}:
      hb_split7(Nat.sub(E, 1n), Nat.sub(N, 1n), 1n+gmax(2n+K2), 1n+Ks, sub1_mono(E, N, hEN), sub1_mono(7n, N, heq),
        gm_le8(2n+K2), hKs2)
    case False{}:
      split_small(E, N, 2n+K2, Ks, hE, hEN, lt_of_not_le(7n, N, heq), NO.le_zero(K2), hK10, hKs2,
        lt_le_trans(Nat.mul(1n+K2, E), n, Nat.mul(Ks, N), klo, hcov))

# stock split, the row past split 0 (N = S < n, E <= N, Ks >= 2 splits covering n <= Ks N)
def hh_split(+K: Nat, +E: Nat, +n: Nat, +N: Nat, +Ks: Nat, +hE: {Nat.is_le(1n, E) == True{} : Bool},
    klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool}, hK10: {Nat.is_le(K, 10n) == True{} : Bool},
    +hEN: {Nat.is_le(E, N) == True{} : Bool}, hNn: {Nat.is_lt(N, n) == True{} : Bool},
    +hKs2: {Nat.is_le(2n, Ks) == True{} : Bool}, hcov: {Nat.is_le(n, Nat.mul(Ks, N)) == True{} : Bool})
  -> HB(Nat.sub(Nat.min(E, n), 1n), Nat.sub(N, 1n), cbr(Nat.is_lt(1n, K), gmax(K)), cbr(True{}, Ks)):
  match K:
    case 0n:
      hb_k1(Nat.sub(Nat.min(E, n), 1n), Nat.sub(N, 1n), 1n+Ks, ne_le_N(E, n, N, hEN))
    case 1n+K1:
      match K1:
        case 0n:
          hb_k1(Nat.sub(Nat.min(E, n), 1n), Nat.sub(N, 1n), 1n+Ks, ne_le_N(E, n, N, hEN))
        case 1n+K2:
          +N1 = Nat.sub(N, 1n)
          %Equal.sym(Nat, Nat.min(E, n), E, min_eq_l(E, n, NO.le_trans(E, N, n, hEN, le_of_lt(N, n, hNn)))) :
            {Nat.is_le(Nat.add(Nat.double(Nat.sub(_, 1n)), 1n+gmax(2n+K2)), Nat.add(Nat.double(N1), Nat.add(N1, 1n+Ks))) == True{} : Bool}
          hh_split_b(Nat.is_le(7n, N), K2, E, N, n, Ks, {==}, hE, klo, hK10, hEN, hKs2, hcov)

# ex2 relation, stock split: NE1 + [K > 1] <= N1 + 1
def hrel_split(+K: Nat, +E: Nat, +n: Nat, +N: Nat, hEN: {Nat.is_le(E, N) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.sub(Nat.min(E, n), 1n), bitn(Nat.is_lt(1n, K))), Nat.add(Nat.sub(N, 1n), 1n)) == True{} : Bool}:
  NO.le_add_mono(Nat.sub(Nat.min(E, n), 1n), Nat.sub(N, 1n), bitn(Nat.is_lt(1n, K)), 1n, ne_le_N(E, n, N, hEN),
    bitn_le1(Nat.is_lt(1n, K)))

# ==== 9. the laws ====

def min_eq_r(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.min(0n, 1n+bp) == 1n+bp : Nat}, NO.false_true(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.min(ap, bp), bp, min_eq_r(ap, bp, h))

def leaf_k(-T: Nat, -E: Nat, -n: Nat, hh: {Nat.add(Nat.mul(Nat.div(T, E), E), Nat.mod(T, E)) == T : Nat} &
    {Nat.is_lt(Nat.div(T, E), Ef.n_chains(n, E)) == True{} : Bool} &
    {Nat.is_le(1n+Nat.mod(T, E), Ef.chain_len(n, E, Nat.div(T, E))) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(T, E), Ef.n_chains(n, E)) == True{} : Bool}:
  (e, r) = hh
  (hk, ht) = r
  hk

def leaf_t(-T: Nat, -E: Nat, -n: Nat, hh: {Nat.add(Nat.mul(Nat.div(T, E), E), Nat.mod(T, E)) == T : Nat} &
    {Nat.is_lt(Nat.div(T, E), Ef.n_chains(n, E)) == True{} : Bool} &
    {Nat.is_le(1n+Nat.mod(T, E), Ef.chain_len(n, E, Nat.div(T, E))) == True{} : Bool})
  -> {Nat.is_le(1n+Nat.mod(T, E), Ef.chain_len(n, E, Nat.div(T, E))) == True{} : Bool}:
  (e, r) = hh
  (hk, ht) = r
  ht

def pair_l(-a: Nat, -b: Nat, -c: Nat, -d: Nat, hh: {Nat.is_lt(a, b) == True{} : Bool} & {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  (x, y) = hh
  x

def pair_r(-a: Nat, -b: Nat, -c: Nat, -d: Nat, hh: {Nat.is_lt(a, b) == True{} : Bool} & {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(c, d) == True{} : Bool}:
  (x, y) = hh
  y

def pair2_l(-a: Nat, -b: Nat, -c: Nat, -d: Nat, hh: {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_le(c, d) == True{} : Bool})
  -> {Nat.is_le(a, b) == True{} : Bool}:
  (x, y) = hh
  x

def pair2_r(-a: Nat, -b: Nat, -c: Nat, -d: Nat, hh: {Nat.is_le(a, b) == True{} : Bool} & {Nat.is_le(c, d) == True{} : Bool})
  -> {Nat.is_le(c, d) == True{} : Bool}:
  (x, y) = hh
  y

# the elpis side of a row (all its chain geometry) against a stock composite whose budget hh and ex2 relation hxr hold
def dom_e(+q64: Nat, +p: Nat, +T: Nat, +h: Bool, +s: Nat, +Td: Nat, +s2: Nat, +N1: Nat, +sp: Bool, +Ks: Nat,
    +phi63: {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool},
    tv: {Nat.is_le(T, Nat.div(p, 32n)) == True{} : Bool}, tdv: {Nat.is_le(Td, Nat.div(p, 32n)) == True{} : Bool},
    hh: {Nat.is_le(Nat.add(Nat.double(Nat.sub(Nat.min(Ef.e_len(q64), Ef.n_tiles(p)), 1n)),
        cbr(Nat.is_lt(1n, Ef.n_chains(Ef.n_tiles(p), Ef.e_len(q64))), gmax(Ef.n_chains(Ef.n_tiles(p), Ef.e_len(q64))))),
        Nat.add(Nat.double(N1), Nat.add(N1, cbr(sp, Ks)))) == True{} : Bool},
    +hxr: {Nat.is_le(Nat.add(Nat.sub(Nat.min(Ef.e_len(q64), Ef.n_tiles(p)), 1n), bitn(Nat.is_lt(1n, Ef.n_chains(Ef.n_tiles(p), Ef.e_len(q64))))),
        Nat.add(N1, bitn(sp))) == True{} : Bool})
  -> {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2),
       Ef.stock_leaf(1n, sp, Ks, Ef.interior_tiles(q64), 0n, 0n, N1, False{}, s, 0n, 0n, N1, s2)) == True{} : Bool}:
  +E = Ef.e_len(q64)
  +n = Ef.n_tiles(p)
  +K = Ef.n_chains(n, E)
  +I = Ef.interior_tiles(q64)
  +NE1 = Nat.sub(Nat.min(E, n), 1n)
  +k = Nat.div(T, E)
  +t = Nat.mod(T, E)
  +kd = Nat.div(Td, E)
  +td = Nat.mod(Td, E)
  +a = Nat.sub(Nat.sub(Ef.chain_len(n, E, k), 1n), t)
  +b = Nat.sub(Nat.sub(Ef.chain_len(n, E, kd), 1n), td)
  +hE = PG.pg_e_pos(q64)
  +hn = NO.le_zero(Nat.div(p, 32n))
  +klo = pair_l(Nat.mul(Nat.sub(K, 1n), E), n, n, Nat.mul(K, E), PG.pg_chains(n, E, hn, hE))
  +hK10 = PG.pg_k10(q64, p, phi63)
  +hI3 = PG.pg_masked3(q64, p, phi63)
  +hTn = lt_succ(T, Nat.div(p, 32n), tv)
  +hTdn = lt_succ(Td, Nat.div(p, 32n), tdv)
  +hta = pos_bound(n, E, k, t, leaf_t(T, E, n, PG.pg_leaf(n, E, T, hE, hTn)))
  +htb = pos_bound(n, E, kd, td, leaf_t(Td, E, n, PG.pg_leaf(n, E, Td, hE, hTdn)))
  +kb = bitn(Nat.is_lt(1n, K))
  +sb = bitn(sp)
  core(E, K, I, k, t, a, h, s, kd, td, b, s2, N1, sp, Ks, NE1, cbr(Nat.is_lt(1n, K), gmax(K)), hta, htb,
    g_bound(K, k, E, I, n, leaf_k(T, E, n, PG.pg_leaf(n, E, T, hE, hTn)), hK10, hE, hI3, klo),
    g_bound(K, kd, E, I, n, leaf_k(Td, E, n, PG.pg_leaf(n, E, Td, hE, hTdn)), hK10, hE, hI3, klo),
    hh,
    NO.le_trans(Nat.add(a, kb), Nat.add(NE1, kb), Nat.add(N1, sb),
      PG.pg_add_r_mono(a, NE1, kb, NO.le_trans(a, Nat.add(t, a), NE1, NO.le_add_l(t, a), hta)), hxr),
    NO.le_trans(Nat.add(b, kb), Nat.add(NE1, kb), Nat.add(N1, sb),
      PG.pg_add_r_mono(b, NE1, kb, NO.le_trans(b, Nat.add(td, b), NE1, NO.le_add_l(td, b), htb)), hxr))

def klo_of(+q64: Nat, +p: Nat) -> {Nat.is_lt(Nat.mul(Nat.sub(Ef.n_chains(Ef.n_tiles(p), Ef.e_len(q64)), 1n), Ef.e_len(q64)), Ef.n_tiles(p)) == True{} : Bool}:
  +E = Ef.e_len(q64)
  +n = Ef.n_tiles(p)
  pair_l(Nat.mul(Nat.sub(Ef.n_chains(n, E), 1n), E), n, n, Nat.mul(Ef.n_chains(n, E), E),
    PG.pg_chains(n, E, NO.le_zero(Nat.div(p, 32n)), PG.pg_e_pos(q64)))

# stock with ns >= 2 splits of S = split_len(nh, ns) tiles: the row past split 0 (S < n) or inside it (n <= S)
def dom_sp_b(+bb: Bool, +q64: Nat, +nh: Nat, +p: Nat, +ns: Nat, +T: Nat, +h: Bool, +s: Nat, +Td: Nat, +s2: Nat,
    heq: {Nat.is_lt(Ef.split_len(nh, ns), Ef.n_tiles(p)) == bb : Bool},
    +phi63: {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool},
    nlo: {Nat.is_lt(q64, nh) == True{} : Bool}, ns1: {Nat.is_le(1n, ns) == True{} : Bool}, ns8: {Nat.is_le(ns, 8n) == True{} : Bool},
    tv: {Nat.is_le(T, Nat.div(p, 32n)) == True{} : Bool}, tdv: {Nat.is_le(Td, Nat.div(p, 32n)) == True{} : Bool})
  -> {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2),
       Ef.stock_leaf(1n, True{}, Ef.cdiv(Ef.n_tiles(p), Ef.split_len(nh, ns)), Ef.interior_tiles(q64), 0n, 0n,
         Nat.sub(Nat.min(Ef.split_len(nh, ns), Ef.n_tiles(p)), 1n), False{}, s, 0n, 0n,
         Nat.sub(Nat.min(Ef.split_len(nh, ns), Ef.n_tiles(p)), 1n), s2)) == True{} : Bool}:
  match bb:
    case True{}:
      +E = Ef.e_len(q64)
      +n = Ef.n_tiles(p)
      +S = Ef.split_len(nh, ns)
      +K = Ef.n_chains(n, E)
      +I = Ef.interior_tiles(q64)
      +Ks = Ef.cdiv(n, S)
      +hE = PG.pg_e_pos(q64)
      +hES = PG.pg_split_ge_e(q64, nh, ns, nlo, ns1, ns8)
      +spos = NO.le_trans(1n, E, S, hE, hES)
      +hheq = heq
      %Equal.sym(Nat, Nat.min(S, n), S, min_eq_l(S, n, le_of_lt(S, n, hheq))) :
        {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_leaf(1n, True{}, Ks, I, 0n, 0n, Nat.sub(_, 1n), False{}, s,
          0n, 0n, Nat.sub(_, 1n), s2)) == True{} : Bool}
      dom_e(q64, p, T, h, s, Td, s2, Nat.sub(S, 1n), True{}, Ks, phi63, tv, tdv,
        hh_split(K, E, n, S, Ks, hE, klo_of(q64, p), PG.pg_k10(q64, p, phi63), hES, hheq,
          pair2_l(2n, Ks, n, Nat.mul(Ks, S), PG.pg_ks_split(n, S, spos, hheq)),
          pair2_r(2n, Ks, n, Nat.mul(Ks, S), PG.pg_ks_split(n, S, spos, hheq))),
        hrel_split(K, E, n, S, hES))
    case False{}:
      +E = Ef.e_len(q64)
      +n = Ef.n_tiles(p)
      +S = Ef.split_len(nh, ns)
      +K = Ef.n_chains(n, E)
      +I = Ef.interior_tiles(q64)
      +hE = PG.pg_e_pos(q64)
      +hn = NO.le_zero(Nat.div(p, 32n))
      +short = not_lt_le(S, n, heq)
      %Equal.sym(Nat, Nat.min(S, n), n, min_eq_r(S, n, short)) :
        {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_leaf(1n, True{}, Ef.cdiv(n, S), I, 0n, 0n, Nat.sub(_, 1n), False{}, s,
          0n, 0n, Nat.sub(_, 1n), s2)) == True{} : Bool}
      %Equal.sym(Nat, Ef.cdiv(n, S), 1n, PG.pg_ks_one(n, S, hn, short)) :
        {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_leaf(1n, True{}, _, I, 0n, 0n, Nat.sub(n, 1n), False{}, s,
          0n, 0n, Nat.sub(n, 1n), s2)) == True{} : Bool}
      dom_e(q64, p, T, h, s, Td, s2, Nat.sub(n, 1n), True{}, 1n, phi63, tv, tdv,
        hh_full(K, E, n, True{}, 1n, hE, hn, klo_of(q64, p)), hrel_full(K, E, n, 1n, hE, klo_of(q64, p)))

def dom_ns(+ns: Nat, +q64: Nat, +nh: Nat, +p: Nat, +T: Nat, +h: Bool, +s: Nat, +Td: Nat, +s2: Nat,
    nlo: {Nat.is_lt(q64, nh) == True{} : Bool}, +phi63: {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool},
    ns1: {Nat.is_le(1n, ns) == True{} : Bool}, ns8: {Nat.is_le(ns, 8n) == True{} : Bool},
    tv: {Nat.is_le(T, Nat.div(p, 32n)) == True{} : Bool}, tdv: {Nat.is_le(Td, Nat.div(p, 32n)) == True{} : Bool})
  -> {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_at(q64, nh, p, ns, s, s2)) == True{} : Bool}:
  match ns:
    case 0n:
      Empty.absurd({Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_at(q64, nh, p, 0n, s, s2)) == True{} : Bool},
        NO.false_true(ns1))
    case 1n+m:
      match m:
        case 0n:
          +E = Ef.e_len(q64)
          +n = Ef.n_tiles(p)
          +K = Ef.n_chains(n, E)
          +hE = PG.pg_e_pos(q64)
          dom_e(q64, p, T, h, s, Td, s2, Nat.sub(n, 1n), False{}, 1n, phi63, tv, tdv,
            hh_full(K, E, n, False{}, 1n, hE, NO.le_zero(Nat.div(p, 32n)), klo_of(q64, p)),
            hrel_full(K, E, n, 0n, hE, klo_of(q64, p)))
        case 1n+m2:
          dom_sp_b(Nat.is_lt(Ef.split_len(nh, 2n+m2), Ef.n_tiles(p)), q64, nh, p, 2n+m2, T, h, s, Td, s2, {==}, phi63, nlo, ns1, ns8,
            tv, tdv)

def Laws.pfix_dom(q64, nh, p, ns, T, h, s, Td, s2, nlo, nhi, plo, phi, ns1, ns8, tv, tdv):
  dom_ns(ns, q64, nh, p, T, h, s, Td, s2, nlo, ple63(p, nh, q64, phi, nhi), ns1, ns8, tv, tdv)

def Laws.pfix_witness(q64, nh, p, ns, s, s2):
  {==}

def Laws.pfix_chunk_invariant(u, i):
  PG.pg_chunk_invariant(u, i)
