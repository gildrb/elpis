# Laws of the served verify head's per-row schedule (bend/lmhead.bend): the stock lm_head
# exl3_gemm_gr reduction order of a row does not depend on the call's row count m or the row index r
# (for a fixed (shape, grid) record, m <= 16), the persisted records the dispatch finds for the
# lm_head matrix are one and the same (shape 4, grid 82) for m = 1 .. 8, and hence the head plan
# (final norm launch shape, lm_head row schedule, argmax block split) of row r of an m-row round is
# that of row 0 of a 1-row round: RowInv's o_head for hp = hp_head(served_tab, 6, dim, size).
# A Nat model of schedules: float values, the MMA's internal order, lane slots and memory ordering
# are outside it (lmhead.bend header).
import Base
import ./lmhead.bend as Impl

# (1) Fixed record: for every shape s, grid G, matrix k x n and column tile nt, the reduction order of
# element (row r, nt) of an m-row call (r < m <= 16, one M tile) is that of row 0 of a 1-row call:
# the same blocks' k-segments and fold points in the same lock order, the same sub_k combine tree,
# written, first M tile.
law order_row_free:
  for +s: Nat
  for +G: Nat
  for +k: Nat
  for +n: Nat
  for +nt: Nat
  for +m: Nat
  for +r: Nat
  for +hr: {Nat.is_lt(r, m) == True{} : Bool}
  for +hm: {Nat.is_le(m, 16n) == True{} : Bool}
  {Impl.order(s, G, k, n, m, r, nt) == Impl.order(s, G, k, n, 1n, 0n, nt) : Impl.Order}

# (1') The same for the sub_k combine alone, for any TILEBLOCKS_K and any m >= r + 1 (both GI:479
# paths combine a row < size_m in the same order).
law tb_row_free:
  for +t: Nat
  for +m: Nat
  for +r: Nat
  for +hr: {Nat.is_lt(r, m) == True{} : Bool}
  {Impl.tb_elem(t, m, r) == Impl.tb_full(t) : Impl.Tree}

# (2) The persisted records: for m = 1 .. 8 the lm_head call (K = 6) looks up keys 2, 4, 8, finds
# shape 4 / grid 82 each time, and the record is accepted: the cooperative kernel on (4, 82).
law served_records:
  for +m: Nat
  for pos: {Nat.is_lt(0n, m) == True{} : Bool}
  for +hm: {Nat.is_le(m, 8n) == True{} : Bool}
  {Impl.dispatch(Impl.served_tab(), 6n, m) == Impl.Coop{4n, 82n} : Impl.Launch}

# (2') Through the dispatch: every element's reduction order of row r of an m-row lm_head call
# (r < m <= 8) is that of row 0 of a 1-row call.
law served_order:
  for +k: Nat
  for +n: Nat
  for +nt: Nat
  for +m: Nat
  for +r: Nat
  for +hr: {Nat.is_lt(r, m) == True{} : Bool}
  for +hm: {Nat.is_le(m, 8n) == True{} : Bool}
  {Impl.elem_order(Impl.served_tab(), 6n, k, n, m, r, nt) ==
    Impl.elem_order(Impl.served_tab(), 6n, k, n, 1n, 0n, nt) : Impl.Order}

# (3) RowInv's o_head for the served head plan, for every hidden size and vocabulary bound.
law o_head_served:
  for +dim: Nat
  for +size: Nat
  for +base: Nat
  for +m: Nat
  for +r: Nat
  for +d: Nat
  for hd: {Nat.is_le(d, r) == True{} : Bool}
  for +hr: {Nat.is_lt(r, m) == True{} : Bool}
  for +hm: {Nat.is_le(m, 8n) == True{} : Bool}
  {Impl.hp_head(Impl.served_tab(), 6n, dim, size, base, m, r, d) ==
    Impl.hp_head(Impl.served_tab(), 6n, dim, size, Nat.add(base, d), 1n, 0n, 0n) : Impl.HeadPlan}
