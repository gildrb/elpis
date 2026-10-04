# Proofs of the lm_head head-plan laws (lmhead_laws.bend) about the Bend model lmhead.bend.
# Structural evidence only: no unsafe definitions, axioms, holes or foreign proof code. The record
# facts are decided by evaluation for each m = 1 .. 8; everything else holds for symbolic operands.
import Base
import ./lmhead.bend as Impl
import ./lmhead_laws.bend as Laws
import ./norm_fuse_spec.bend as NSpec

# ==== Bool / Nat lemmas ====

def lh_Truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

# False == True is absurd.
def lh_false_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : lh_Truth(_)
  Unit{}

law lh_le_zero:
  for +c: Nat
  {Nat.is_le(0n, c) == True{} : Bool}

def lh_le_zero(c):
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

law lh_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def lh_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      lh_le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, lh_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, lh_false_true(bc))
    case 1n+p 1n+q 1n+r:
      lh_le_trans(p, q, r, ab, bc)

law lh_lt_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lh_lt_le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, lh_false_true(ab))
    case 0n 1n+q 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, lh_false_true(bc))
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, c) == True{} : Bool}, lh_false_true(ab))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, lh_false_true(bc))
    case 1n+p 1n+q 1n+r:
      lh_lt_le_trans(p, q, r, ab, bc)

# r < m gives 0 < m.
law lh_lt_pos:
  for +r: Nat
  for +m: Nat
  for hr: {Nat.is_lt(r, m) == True{} : Bool}
  {Nat.is_lt(0n, m) == True{} : Bool}

def lh_lt_pos(r, m, hr):
  match r m:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, lh_false_true(hr))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, lh_false_true(hr))
    case 1n+p 1n+q:
      {==}

# ==== the sub_k combine ====

# Both GI:479 paths give a combined row the full tree.
law lh_tb_true:
  for small: Bool
  for +t: Nat
  {Impl.tb_pick(small, t, True{}) == Impl.tb_full(t) : Impl.Tree}

def lh_tb_true(small, t):
  match small:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.tb_row_free(t, m, r, hr):
  %Equal.sym(Bool, Nat.is_lt(r, m), True{}, hr) : {Impl.tb_pick(Nat.is_le(m, 8n), t, _) == Impl.tb_full(t) : Impl.Tree}
  lh_tb_true(Nat.is_le(m, 8n), t)

# ==== (1) fixed record ====

def Laws.order_row_free(s, G, k, n, nt, m, r, hr, hm):
  +h16 = lh_lt_le_trans(r, m, 16n, hr, hm)
  +etb = Laws.tb_row_free(Impl.tbk(s), m, r, hr)
  %Equal.sym(Impl.Tree, Impl.tb_elem(Impl.tbk(s), m, r), Impl.tb_full(Impl.tbk(s)), etb) :
    {Impl.Order{Impl.segs_of(Impl.Coop{s, G}, k, n, nt), _, Nat.is_lt(r, m), Nat.is_lt(r, 16n)} ==
      Impl.order(s, G, k, n, 1n, 0n, nt) : Impl.Order}
  %Equal.sym(Bool, Nat.is_lt(r, m), True{}, hr) :
    {Impl.Order{Impl.segs_of(Impl.Coop{s, G}, k, n, nt), Impl.tb_full(Impl.tbk(s)), _, Nat.is_lt(r, 16n)} ==
      Impl.order(s, G, k, n, 1n, 0n, nt) : Impl.Order}
  %Equal.sym(Bool, Nat.is_lt(r, 16n), True{}, h16) :
    {Impl.Order{Impl.segs_of(Impl.Coop{s, G}, k, n, nt), Impl.tb_full(Impl.tbk(s)), True{}, _} ==
      Impl.order(s, G, k, n, 1n, 0n, nt) : Impl.Order}
  {==}

# ==== (2) the persisted records, m = 1 .. 8 (evaluation) ====

def Laws.served_records(m, pos, hm):
  match m:
    case 0n:
      Empty.absurd({Impl.dispatch(Impl.served_tab(), 6n, 0n) == Impl.Coop{4n, 82n} : Impl.Launch}, lh_false_true(pos))
    case 1n+m1:
      match m1:
        case 0n:
          {==}
        case 1n+m2:
          match m2:
            case 0n:
              {==}
            case 1n+m3:
              match m3:
                case 0n:
                  {==}
                case 1n+m4:
                  match m4:
                    case 0n:
                      {==}
                    case 1n+m5:
                      match m5:
                        case 0n:
                          {==}
                        case 1n+m6:
                          match m6:
                            case 0n:
                              {==}
                            case 1n+m7:
                              match m7:
                                case 0n:
                                  {==}
                                case 1n+m8:
                                  match m8:
                                    case 0n:
                                      {==}
                                    case 1n+m9:
                                      Empty.absurd({Impl.dispatch(Impl.served_tab(), 6n, 9n+m9) == Impl.Coop{4n, 82n} : Impl.Launch},
                                        lh_false_true(hm))

def Laws.served_order(k, n, nt, m, r, hr, hm):
  +erec = Laws.served_records(m, lh_lt_pos(r, m, hr), hm)
  %Equal.sym(Impl.Launch, Impl.dispatch(Impl.served_tab(), 6n, m), Impl.Coop{4n, 82n}, erec) :
    {Impl.order_of(Impl.RowSched{_, Impl.tb_of(_, m, r), Nat.is_lt(r, m), Nat.is_lt(r, 16n)}, k, n, nt) ==
      Impl.elem_order(Impl.served_tab(), 6n, k, n, 1n, 0n, nt) : Impl.Order}
  Laws.order_row_free(4n, 82n, k, n, nt, m, r, hr, lh_le_trans(m, 8n, 16n, hm, {==}))

# ==== (3) o_head ====

def Laws.o_head_served(dim, size, base, m, r, d, hd, hr, hm):
  +erec = Laws.served_records(m, lh_lt_pos(r, m, hr), hm)
  +etb = Laws.tb_row_free(Impl.tbk(4n), m, r, hr)
  +h16 = lh_lt_le_trans(r, m, 16n, hr, lh_le_trans(m, 8n, 16n, hm, {==}))
  %Equal.sym(Impl.Launch, Impl.dispatch(Impl.served_tab(), 6n, m), Impl.Coop{4n, 82n}, erec) :
    {Impl.HeadPlan{NSpec.warps_for(Nat.div(dim, 4n)), Impl.RowSched{_, Impl.tb_of(_, m, r), Nat.is_lt(r, m), Nat.is_lt(r, 16n)},
      Impl.fs_blocks(size)} ==
      Impl.hp_head(Impl.served_tab(), 6n, dim, size, Nat.add(base, d), 1n, 0n, 0n) : Impl.HeadPlan}
  %Equal.sym(Impl.Tree, Impl.tb_elem(Impl.tbk(4n), m, r), Impl.tb_full(Impl.tbk(4n)), etb) :
    {Impl.HeadPlan{NSpec.warps_for(Nat.div(dim, 4n)), Impl.RowSched{Impl.Coop{4n, 82n}, _, Nat.is_lt(r, m), Nat.is_lt(r, 16n)},
      Impl.fs_blocks(size)} ==
      Impl.hp_head(Impl.served_tab(), 6n, dim, size, Nat.add(base, d), 1n, 0n, 0n) : Impl.HeadPlan}
  %Equal.sym(Bool, Nat.is_lt(r, m), True{}, hr) :
    {Impl.HeadPlan{NSpec.warps_for(Nat.div(dim, 4n)), Impl.RowSched{Impl.Coop{4n, 82n}, Impl.tb_full(Impl.tbk(4n)), _, Nat.is_lt(r, 16n)},
      Impl.fs_blocks(size)} ==
      Impl.hp_head(Impl.served_tab(), 6n, dim, size, Nat.add(base, d), 1n, 0n, 0n) : Impl.HeadPlan}
  %Equal.sym(Bool, Nat.is_lt(r, 16n), True{}, h16) :
    {Impl.HeadPlan{NSpec.warps_for(Nat.div(dim, 4n)), Impl.RowSched{Impl.Coop{4n, 82n}, Impl.tb_full(Impl.tbk(4n)), True{}, _},
      Impl.fs_blocks(size)} ==
      Impl.hp_head(Impl.served_tab(), 6n, dim, size, Nat.add(base, d), 1n, 0n, 0n) : Impl.HeadPlan}
  {==}
