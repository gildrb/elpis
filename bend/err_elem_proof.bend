# Proofs of bend/err_elem_laws.bend: case analysis, computation and rewriting only. No @unsafe
# definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as EbL
import ./err_bound_proof.bend as EbP
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP
import ./err_elem.bend as Ee
import ./err_elem_laws.bend as Laws

# ==== tensors between kernels ====

def Laws.dtype_eq(t):
  match t:
    case Ee.TStream{}:
      {==}
    case Ee.TNormOut{}:
      {==}
    case Ee.TSubOut{}:
      {==}
    case Ee.TMlpIn{}:
      {==}
    case Ee.TGateUp{}:
      {==}
    case Ee.TActOut{}:
      {==}
    case Ee.TMlpOut{}:
      {==}
    case Ee.TFinalOut{}:
      {==}

# ==== residual adds ====

def Laws.resid_eq(e, l):
  match e:
    case Ee.ETail{}:
      {==}
    case Ee.EResIn{}:
      {==}
    case Ee.ETorch{}:
      {==}

def Laws.resid_dom(e, l):
  match e:
    case Ee.ETail{}:
      {==}
    case Ee.EResIn{}:
      {==}
    case Ee.ETorch{}:
      {==}

# ==== rms_norm_kernel ====

def Laws.norm_reg_branch():
  {==}

# a < b, b <= c: a < c
def ee_lt_le(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, NO.false_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, NO.false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, NO.false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, NO.false_true(bc))
    case 1n+p 1n+q 1n+r:
      ee_lt_le(p, q, r, ab, bc)

# c <= x: not x < c
def ee_not_lt(+x: Nat, +c: Nat, hc: {Nat.is_le(c, x) == True{} : Bool}) -> {Nat.is_lt(x, c) == False{} : Bool}:
  match x c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(0n, 1n+q) == False{} : Bool}, NO.false_true(hc))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ee_not_lt(p, q, hc)

# Thread t's third strided column t + 2048 is past the 1280 columns.
def ee_third(+t: Nat) -> {Nat.is_lt(Nat.add(Nat.add(t, 1024n), 1024n), 1280n) == False{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(t, 1024n), 1024n), Nat.add(t, Nat.add(1024n, 1024n)), NO.add_assoc(t, 1024n, 1024n)) :
    {Nat.is_lt(_, 1280n) == False{} : Bool}
  ee_not_lt(Nat.add(t, 2048n), 1280n,
    NO.le_trans(1280n, 2048n, Nat.add(t, 2048n), {==}, NO.le_add_l(t, 2048n)))

# The second column's guard b decides both counts alike.
def ee_mid(+t: Nat, b: Bool, e: {Nat.is_lt(Nat.add(t, 1024n), 1280n) == b : Bool})
  -> {1n+Ee.guard(Nat.is_lt(Nat.add(t, 1024n), 1280n)) == 1n+Ee.strided(1279n, Nat.is_lt(Nat.add(t, 1024n), 1280n), Nat.add(t, 1024n), 1280n, 1024n) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(Nat.add(t, 1024n), 1280n), True{}, e) :
        {1n+Ee.guard(_) == 1n+Ee.strided(1279n, _, Nat.add(t, 1024n), 1280n, 1024n) : Nat}
      %Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.add(t, 1024n), 1024n), 1280n), False{}, ee_third(t)) :
        {2n == 2n+Ee.strided(1278n, _, Nat.add(Nat.add(t, 1024n), 1024n), 1280n, 1024n) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(Nat.add(t, 1024n), 1280n), False{}, e) :
        {1n+Ee.guard(_) == 1n+Ee.strided(1279n, _, Nat.add(t, 1024n), 1280n, 1024n) : Nat}
      {==}

def Laws.norm_ncols_eq(t, h):
  +h1 = ee_lt_le(t, 1024n, 1280n, h, {==})
  %Equal.sym(Bool, Nat.is_lt(t, 1280n), True{}, h1) :
    {Nat.add(Ee.guard(_), Ee.guard(Nat.is_lt(Nat.add(t, 1024n), 1280n))) == Ee.strided(1280n, _, t, 1280n, 1024n) : Nat}
  ee_mid(t, Nat.is_lt(Nat.add(t, 1024n), 1280n), {==})

def Laws.norm_plain_eq(l, d, h):
  match l:
    case Ee.NIn{}:
      {==}
    case Ee.NW{}:
      {==}
    case Ee.NSq{t, i, k}:
      %Laws.norm_ncols_eq(t, h) :
        {Ee.elpis_norm(Ee.NSq{t, i, k}, d) ==
          Ee.norm_out(Eb.add(Ee.r32(Nat.add(Ee.chain(_, i, k), Ee.reduce_steps())), Ee.rmf_rt()), d) : Eb.Path}
      {==}

def Laws.norm_input_dom(l, h):
  %Laws.norm_plain_eq(l, Ee.DF16{}, h) :
    {Eb.dom(128n, Ee.elpis_norm(l, Ee.DF16{}), _) == True{} : Bool}
  EbL.dom_refl(128n, Ee.elpis_norm(l, Ee.DF16{}))

def Laws.norm_final_dom(l, h):
  %Laws.norm_plain_eq(l, Ee.DF16{}, h) :
    {Eb.dom(128n, Ee.elpis_norm(l, Ee.DF16{}), _) == True{} : Bool}
  EbL.dom_refl(128n, Ee.elpis_norm(l, Ee.DF16{}))

# ==== tail post-attention norm ====

# Every (component, extra-add) case of the tail's sum-of-squares route against the stock witness.
def ee_tail_sq(k: Ee.Comp, b: Bool)
  -> {Eb.dom(128n, Ee.norm_out(Eb.add(Ee.tail_ssq(k, b), Ee.rmf_tail()), Ee.DF16{}),
       Ee.stock_norm(Ee.NSq{0n, 0n, Ee.CX{}}, Ee.DF16{})) == True{} : Bool}:
  match k b:
    case Ee.CX{} True{}:
      {==}
    case Ee.CX{} False{}:
      {==}
    case Ee.CY{} True{}:
      {==}
    case Ee.CY{} False{}:
      {==}
    case Ee.CZ{} True{}:
      {==}
    case Ee.CZ{} False{}:
      {==}
    case Ee.CW{} True{}:
      {==}
    case Ee.CW{} False{}:
      {==}

def Laws.tail_norm_dom(l):
  match l:
    case Ee.TIn{}:
      {==}
    case Ee.TW{}:
      {==}
    case Ee.TSq{ch, lane, k}:
      ee_tail_sq(k, Ee.tail_extra(ch))

def Laws.tail_witness_ok(l):
  match l:
    case Ee.TIn{}:
      {==}
    case Ee.TW{}:
      {==}
    case Ee.TSq{ch, lane, k}:
      {==}

# ==== SiLU(gate) * up ====

def Laws.act_ops_eq():
  {==}

def Laws.act_eq(l):
  match l:
    case Ee.AGateSig{}:
      {==}
    case Ee.AGateDir{}:
      {==}
    case Ee.AUp{}:
      {==}

def Laws.act_dom(l):
  match l:
    case Ee.AGateSig{}:
      {==}
    case Ee.AGateDir{}:
      {==}
    case Ee.AUp{}:
      {==}
