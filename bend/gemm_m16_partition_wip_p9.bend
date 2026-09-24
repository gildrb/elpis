# WIP proofs: laws finish_job_decode, finish_job_encode (K:360-363).
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p9_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- Bool / pair helpers ----

def p9_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p9_tr(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {b == True{} : Bool})
  -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)

def p9_fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def p9_snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

# ---- Impl.job, staged: each stage abstracts one computed value for rewriting ----

def p9_jobc(+q: Nat, +r: Nat, +rem: Nat) -> Spec.Job:
  Spec.Job{q, r, Nat.sub(rem, Nat.mul(r, 4n))}

def p9_jobr(+q: Nat, +rem: Nat) -> Spec.Job:
  p9_jobc(q, Nat.div(rem, 4n), rem)

def p9_jobq(+q: Nat, +x: Nat, +m: Nat) -> Spec.Job:
  p9_jobr(q, Nat.sub(x, Nat.mul(Nat.mul(q, m), 4n)))

# ---- division facts ----

# a - (a / b) * b == a % b.
def p9_sub_mod(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.sub(a, Nat.mul(Nat.div(a, b), b)) == Nat.mod(a, b) : Nat}:
  %p9_fst({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, Arith.ar_divmod(a, b, pos))
    : {Nat.sub(_, Nat.mul(Nat.div(a, b), b)) == Nat.mod(a, b) : Nat}
  Arith.ar_add_sub(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b))

# a - (a / b) * b < b.
def p9_sub_mod_lt(+a: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(a, Nat.mul(Nat.div(a, b), b)), b) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(a, Nat.mul(Nat.div(a, b), b)), Nat.mod(a, b), p9_sub_mod(a, b, pos))
    : {Nat.is_lt(_, b) == True{} : Bool}
  p9_snd({Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat},
    {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}, Arith.ar_divmod(a, b, pos))

# (a / b) * b <= a.
def p9_div_mul_le(+a: Nat, +b: Nat, pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.div(a, b), b), a) == True{} : Bool}:
  p9_tr(Nat.is_le(Nat.mul(Nat.div(a, b), b), a), Nat.is_le(Nat.div(a, b), Nat.div(a, b)),
    Arith.ar_div_le(Nat.div(a, b), a, b, pos), Arith.ar_le_refl(Nat.div(a, b)))

# ---- decode ----

def p9_lt_zero_false(+groups: Nat, +x: Nat)
  -> {False{} == Nat.is_lt(x, Nat.mul(Nat.mul(groups, 0n), 4n)) : Bool}:
  %Equal.sym(Nat, Nat.mul(groups, 0n), 0n, Arith.ar_mul_zero_r(groups))
    : {False{} == Nat.is_lt(x, Nat.mul(_, 4n)) : Bool}
  Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, Arith.ar_h_lt_zero(x))

# A job index exists only if m * 4 > 0.
def p9_dec_pos(+groups: Nat, m: Nat, +x: Nat,
    inside: {Nat.is_lt(x, Nat.mul(Nat.mul(groups, m), 4n)) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool}:
  match m:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
        Arith.ar_false_true(Equal.trans(Bool, False{},
          Nat.is_lt(x, Nat.mul(Nat.mul(groups, 0n), 4n)), True{},
          p9_lt_zero_false(groups, x), inside)))
    case 1n+p:
      {==}

# q * (m * 4) == (q * m) * 4.
def p9_assoc(+q: Nat, +m: Nat)
  -> {Nat.mul(q, Nat.mul(m, 4n)) == Nat.mul(Nat.mul(q, m), 4n) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.mul(q, m), 4n), Nat.mul(q, Nat.mul(m, 4n)),
    Arith.ar_mul_assoc(q, m, 4n))

# (q * m) * 4 <= x for q = x / (m * 4).
def p9_dec_le(+x: Nat, +m: Nat, pos: {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(Nat.mul(Nat.div(x, Nat.mul(m, 4n)), m), 4n), x) == True{} : Bool}:
  %p9_assoc(Nat.div(x, Nat.mul(m, 4n)), m) : {Nat.is_le(_, x) == True{} : Bool}
  p9_div_mul_le(x, Nat.mul(m, 4n), pos)

# rem = x - (q * m) * 4 < m * 4 for q = x / (m * 4).
def p9_dec_rem_lt(+x: Nat, +m: Nat, +pos: {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(x, Nat.mul(Nat.mul(Nat.div(x, Nat.mul(m, 4n)), m), 4n)),
    Nat.mul(m, 4n)) == True{} : Bool}:
  %p9_assoc(Nat.div(x, Nat.mul(m, 4n)), m)
    : {Nat.is_lt(Nat.sub(x, _), Nat.mul(m, 4n)) == True{} : Bool}
  p9_sub_mod_lt(x, Nat.mul(m, 4n), pos)

def p9_inside(+groups: Nat, +m: Nat, +x: Nat,
    inside: {Nat.is_lt(x, Nat.mul(Nat.mul(groups, m), 4n)) == True{} : Bool})
  -> {Nat.is_lt(x, Nat.mul(groups, Nat.mul(m, 4n))) == True{} : Bool}:
  %Arith.ar_mul_assoc(groups, m, 4n) : {Nat.is_lt(x, _) == True{} : Bool}
  inside

# q < groups for q = x / (m * 4), x < (groups * m) * 4.
def p9_dec_g_lt(+groups: Nat, +m: Nat, +x: Nat,
    pos: {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool},
    inside: {Nat.is_lt(x, Nat.mul(Nat.mul(groups, m), 4n)) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(x, Nat.mul(m, 4n)), groups) == True{} : Bool}:
  p9_tr(Nat.is_lt(Nat.div(x, Nat.mul(m, 4n)), groups),
    Nat.is_lt(x, Nat.mul(groups, Nat.mul(m, 4n))),
    Arith.ar_div_lt(groups, x, Nat.mul(m, 4n), pos),
    p9_inside(groups, m, x, inside))

# job_ok of the staged decode (q, rem / 4, rem - (rem / 4) * 4) for any rem < m * 4.
def p9_ok_rem(+groups: Nat, +m: Nat, +q: Nat, +rem: Nat,
    qlt: {Nat.is_lt(q, groups) == True{} : Bool},
    rlt: {Nat.is_lt(rem, Nat.mul(m, 4n)) == True{} : Bool})
  -> {Spec.job_ok(p9_jobr(q, rem), groups, m) == True{} : Bool}:
  +r = Nat.div(rem, 4n)
  +c = Nat.sub(rem, Nat.mul(r, 4n))
  Arith.ar_and_intro(Nat.is_lt(q, groups), Bool.and(Nat.is_lt(r, m), Nat.is_lt(c, 4n)), qlt,
    Arith.ar_and_intro(Nat.is_lt(r, m), Nat.is_lt(c, 4n),
      p9_tr(Nat.is_lt(r, m), Nat.is_lt(rem, Nat.mul(m, 4n)),
        Arith.ar_div_lt(m, rem, 4n, {==}), rlt),
      p9_sub_mod_lt(rem, 4n, {==})))

# encode of the staged decode is (q * m) * 4 + rem.
def p9_enc_rem(+q: Nat, +m: Nat, +rem: Nat)
  -> {Spec.encode(p9_jobr(q, rem), m) == Nat.add(Nat.mul(Nat.mul(q, m), 4n), rem) : Nat}:
  +r = Nat.div(rem, 4n)
  +r4 = Nat.mul(r, 4n)
  +c = Nat.sub(rem, r4)
  +A = Nat.mul(Nat.mul(q, m), 4n)
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(q, m), r), 4n), Nat.add(A, r4),
    Arith.ar_mul_add_l(Nat.mul(q, m), r, 4n)) : {Nat.add(_, c) == Nat.add(A, rem) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(A, r4), c), Nat.add(A, Nat.add(r4, c)),
    Arith.ar_add_assoc(A, r4, c)) : {_ == Nat.add(A, rem) : Nat}
  %Equal.sym(Nat, Nat.add(r4, c), rem, Arith.ar_sub_add(rem, r4, p9_div_mul_le(rem, 4n, {==})))
    : {Nat.add(A, _) == Nat.add(A, rem) : Nat}
  {==}

def Laws.finish_job_decode(groups, m, x, inside):
  +ins = inside
  +pos = p9_dec_pos(groups, m, x, ins)
  +q = Nat.div(x, Nat.mul(m, 4n))
  +A = Nat.mul(Nat.mul(q, m), 4n)
  +rem = Nat.sub(x, A)
  (p9_ok_rem(groups, m, q, rem, p9_dec_g_lt(groups, m, x, pos, ins), p9_dec_rem_lt(x, m, pos)),
    Equal.trans(Nat, Spec.encode(p9_jobr(q, rem), m), Nat.add(A, rem), x,
      p9_enc_rem(q, m, rem), Arith.ar_sub_add(x, A, p9_dec_le(x, m, pos))))

# ---- encode ----

def p9_m4_pos(+m: Nat, pos: {Nat.is_lt(0n, m) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool}:
  p9_tr(Nat.is_lt(Nat.mul(0n, 4n), Nat.mul(m, 4n)), Nat.is_lt(0n, m),
    Arith.ar_mul_lt_cancel(0n, m, 4n, {==}), pos)

# r * 4 + 4 <= m * 4 for r < m.
def p9_succ_le(+r: Nat, +m: Nat, rlt: {Nat.is_lt(r, m) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(r, 4n), 4n), Nat.mul(m, 4n)) == True{} : Bool}:
  %Arith.ar_add_comm(4n, Nat.mul(r, 4n)) : {Nat.is_le(_, Nat.mul(m, 4n)) == True{} : Bool}
  Arith.ar_le_mul_mono(1n+r, m, 4n,
    p9_rt(Nat.is_lt(r, m), Nat.is_le(1n+r, m), Arith.ar_lt_succ_le(r, m), rlt))

# r * 4 + ch < m * 4 for r < m, ch < 4.
def p9_slt(+r: Nat, +m: Nat, +ch: Nat,
    rlt: {Nat.is_lt(r, m) == True{} : Bool},
    chlt: {Nat.is_lt(ch, 4n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(r, 4n), ch), Nat.mul(m, 4n)) == True{} : Bool}:
  Arith.ar_lt_le_trans(Nat.add(Nat.mul(r, 4n), ch), Nat.add(Nat.mul(r, 4n), 4n), Nat.mul(m, 4n),
    p9_tr(Nat.is_lt(Nat.add(Nat.mul(r, 4n), ch), Nat.add(Nat.mul(r, 4n), 4n)), Nat.is_lt(ch, 4n),
      Arith.ar_lt_add_cancel(Nat.mul(r, 4n), ch, 4n), chlt),
    p9_succ_le(r, m, rlt))

# encode(g, r, ch) == g * (m * 4) + (r * 4 + ch).
def p9_enc_split(+g: Nat, +m: Nat, +r: Nat, +ch: Nat)
  -> {Spec.encode(Spec.Job{g, r, ch}, m) ==
    Nat.add(Nat.mul(g, Nat.mul(m, 4n)), Nat.add(Nat.mul(r, 4n), ch)) : Nat}:
  +A = Nat.mul(Nat.mul(g, m), 4n)
  +r4 = Nat.mul(r, 4n)
  +R = Nat.add(Nat.mul(g, Nat.mul(m, 4n)), Nat.add(r4, ch))
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(g, m), r), 4n), Nat.add(A, r4),
    Arith.ar_mul_add_l(Nat.mul(g, m), r, 4n)) : {Nat.add(_, ch) == R : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(A, r4), ch), Nat.add(A, Nat.add(r4, ch)),
    Arith.ar_add_assoc(A, r4, ch)) : {_ == R : Nat}
  %p9_assoc(g, m) : {Nat.add(_, Nat.add(r4, ch)) == R : Nat}
  {==}

# (g * (m * 4) + s) - (g * m) * 4 == s.
def p9_sub_E(+g: Nat, +m: Nat, +s: Nat)
  -> {Nat.sub(Nat.add(Nat.mul(g, Nat.mul(m, 4n)), s), Nat.mul(Nat.mul(g, m), 4n)) == s : Nat}:
  %p9_assoc(g, m) : {Nat.sub(Nat.add(Nat.mul(g, Nat.mul(m, 4n)), s), _) == s : Nat}
  Arith.ar_add_sub(Nat.mul(g, Nat.mul(m, 4n)), s)

def p9_enc_job(+g: Nat, +m: Nat, +r: Nat, +ch: Nat,
    slt: {Nat.is_lt(Nat.add(Nat.mul(r, 4n), ch), Nat.mul(m, 4n)) == True{} : Bool},
    chlt: {Nat.is_lt(ch, 4n) == True{} : Bool})
  -> {Impl.job(Spec.encode(Spec.Job{g, r, ch}, m), m) == Spec.Job{g, r, ch} : Spec.Job}:
  +M = Nat.mul(m, 4n)
  +r4 = Nat.mul(r, 4n)
  +s = Nat.add(r4, ch)
  +E = Nat.add(Nat.mul(g, M), s)
  %Equal.sym(Nat, Spec.encode(Spec.Job{g, r, ch}, m), E, p9_enc_split(g, m, r, ch))
    : {Impl.job(_, m) == Spec.Job{g, r, ch} : Spec.Job}
  %Equal.sym(Nat, Nat.div(E, M), g,
    p9_fst({Nat.div(E, M) == g : Nat}, {Nat.mod(E, M) == s : Nat},
      Arith.ar_div_unique(g, s, M, slt)))
    : {p9_jobq(_, E, m) == Spec.Job{g, r, ch} : Spec.Job}
  %Equal.sym(Nat, Nat.sub(E, Nat.mul(Nat.mul(g, m), 4n)), s, p9_sub_E(g, m, s))
    : {p9_jobr(g, _) == Spec.Job{g, r, ch} : Spec.Job}
  %Equal.sym(Nat, Nat.div(s, 4n), r,
    p9_fst({Nat.div(s, 4n) == r : Nat}, {Nat.mod(s, 4n) == ch : Nat},
      Arith.ar_div_unique(r, ch, 4n, chlt)))
    : {p9_jobc(g, _, s) == Spec.Job{g, r, ch} : Spec.Job}
  %Equal.sym(Nat, Nat.sub(s, r4), ch, Arith.ar_add_sub(r4, ch))
    : {Spec.Job{g, r, _} == Spec.Job{g, r, ch} : Spec.Job}
  {==}

def p9_div_lt_g(+groups: Nat, +E: Nat, +M: Nat, +g: Nat, dq: {Nat.div(E, M) == g : Nat},
    glt: {Nat.is_lt(g, groups) == True{} : Bool})
  -> {Nat.is_lt(Nat.div(E, M), groups) == True{} : Bool}:
  %Equal.sym(Nat, Nat.div(E, M), g, dq) : {Nat.is_lt(_, groups) == True{} : Bool}
  glt

def p9_enc_lt(+groups: Nat, +m: Nat, +g: Nat, +r: Nat, +ch: Nat,
    glt: {Nat.is_lt(g, groups) == True{} : Bool},
    pos: {Nat.is_lt(0n, Nat.mul(m, 4n)) == True{} : Bool},
    slt: {Nat.is_lt(Nat.add(Nat.mul(r, 4n), ch), Nat.mul(m, 4n)) == True{} : Bool})
  -> {Nat.is_lt(Spec.encode(Spec.Job{g, r, ch}, m), Impl.jobs(groups, m)) == True{} : Bool}:
  +M = Nat.mul(m, 4n)
  +s = Nat.add(Nat.mul(r, 4n), ch)
  +E = Nat.add(Nat.mul(g, M), s)
  %Equal.sym(Nat, Spec.encode(Spec.Job{g, r, ch}, m), E, p9_enc_split(g, m, r, ch))
    : {Nat.is_lt(_, Nat.mul(Nat.mul(groups, m), 4n)) == True{} : Bool}
  %p9_assoc(groups, m) : {Nat.is_lt(E, _) == True{} : Bool}
  p9_rt(Nat.is_lt(Nat.div(E, M), groups), Nat.is_lt(E, Nat.mul(groups, M)),
    Arith.ar_div_lt(groups, E, M, pos),
    p9_div_lt_g(groups, E, M, g,
      p9_fst({Nat.div(E, M) == g : Nat}, {Nat.mod(E, M) == s : Nat},
        Arith.ar_div_unique(g, s, M, slt)),
      glt))

def p9_encode_parts(+groups: Nat, +m: Nat, +g: Nat, +r: Nat, +ch: Nat,
    +ok: {Spec.job_ok(Spec.Job{g, r, ch}, groups, m) == True{} : Bool})
  -> {Impl.job(Spec.encode(Spec.Job{g, r, ch}, m), m) == Spec.Job{g, r, ch} : Spec.Job} &
    {Nat.is_lt(Spec.encode(Spec.Job{g, r, ch}, m), Impl.jobs(groups, m)) == True{} : Bool}:
  +rest = Arith.ar_and_r(Nat.is_lt(g, groups), Bool.and(Nat.is_lt(r, m), Nat.is_lt(ch, 4n)), ok)
  +rlt = Arith.ar_and_l(Nat.is_lt(r, m), Nat.is_lt(ch, 4n), rest)
  +chlt = Arith.ar_and_r(Nat.is_lt(r, m), Nat.is_lt(ch, 4n), rest)
  +slt = p9_slt(r, m, ch, rlt, chlt)
  (p9_enc_job(g, m, r, ch, slt, chlt),
    p9_enc_lt(groups, m, g, r, ch,
      Arith.ar_and_l(Nat.is_lt(g, groups), Bool.and(Nat.is_lt(r, m), Nat.is_lt(ch, 4n)), ok),
      p9_m4_pos(m, Arith.ar_le_lt_trans(0n, r, m, Arith.ar_h_le_zero(r), rlt)),
      slt))

def p9_encode(+groups: Nat, +m: Nat, j: Spec.Job,
    ok: {Spec.job_ok(j, groups, m) == True{} : Bool})
  -> {Impl.job(Spec.encode(j, m), m) == j : Spec.Job} &
    {Nat.is_lt(Spec.encode(j, m), Impl.jobs(groups, m)) == True{} : Bool}:
  match j:
    case Spec.Job{g, r, ch}:
      p9_encode_parts(groups, m, g, r, ch, ok)

def Laws.finish_job_encode(groups, m, j, ok):
  p9_encode(groups, m, j, ok)
