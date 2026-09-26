# Independent reference for the pruned int4 draft head of ext patch 9005c (9005c-eta-draft-q4-head-pruned-n896.patch):
# plain list / Nat definitions of what the column -> token id map, the kept blocks, the pruned top-k and the
# switch-back policy must be, written without the impl's structure (draft_head_idmap.bend). Every function is total
# and structural; nothing here is imported by production code.
#   - the id map is "every id t < V whose 128-block t / 128 is kept, ascending, then every other id t < V, ascending"
#     (a filter over [0, V), not the impl's per-block expansion);
#   - a ranking is the insertion sort by (value descending, token id ascending); top-k is its first k entries;
#   - valid policy states: the pruned head is chosen exactly when no hold is pending, the hold never exceeds
#     FALLBACK_HOLD, the window keeps at most FALLBACK_WINDOW flags with fewer than FALLBACK_TRIGGER set, and a pending
#     hold has an empty window.
import Base

def ids_bit(value: Bool) -> Nat:
  match value:
    case True{}:
      1n
    case False{}:
      0n

# x occurs in xs.
def ids_member(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), ids_member(rest, x))

# Occurrences of x in xs.
def ids_count(xs: List<&2, Nat>, +x: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      Nat.add(ids_bit(Nat.is_eq(y, x)), ids_count(rest, x))

# No value occurs twice.
def ids_nodup(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +rest:
      Bool.and(Bool.not(ids_member(rest, y)), ids_nodup(rest))

# Every entry is < n.
def ids_all_lt(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case y <> rest:
      Bool.and(Nat.is_lt(y, n), ids_all_lt(rest, n))

# Every entry is > x.
def ids_all_gt(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case y <> rest:
      Bool.and(Nat.is_lt(x, y), ids_all_gt(rest, x))

# Strictly increasing: every entry is below every later entry.
def ids_increasing(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +rest:
      Bool.and(ids_all_gt(rest, y), ids_increasing(rest))

# ==== kept blocks ====

# Kept blocks as the model expects them: distinct block indices < nb.
def ids_blocks_in(+kept: List<&2, Nat>, +nb: Nat) -> Bool:
  Bool.and(ids_nodup(kept), ids_all_lt(kept, nb))

# order is a permutation of [0, nb): nb entries, all distinct, all < nb.
def ids_is_perm(+order: List<&2, Nat>, +nb: Nat) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, Nat, order), nb), ids_blocks_in(order, nb))

# The accepted inputs of the kept-block selection: at least one block, the first n entries of order exist, are
# distinct and are whole 128-id blocks inside a vocabulary of `vocab` ids (128 * (b + 1) <= vocab).
def ids_prefix_ok(+order: List<&2, Nat>, +n: Nat, +vocab: Nat) -> Bool:
  +p = List.take(&2, Nat, order, n)
  Bool.and(Nat.is_lt(0n, n), Bool.and(Nat.is_eq(List.length(&2, Nat, p), n),
    Bool.and(ids_nodup(p), ids_all_lt(p, Nat.div(vocab, 128n)))))

# ==== the column -> token id map ====

def ids_pick(want: Bool, value: Bool) -> Bool:
  match want:
    case True{}:
      value
    case False{}:
      Bool.not(value)

def ids_range.cons(keep: Bool, +x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match keep:
    case True{}:
      x <> rest
    case False{}:
      rest

# Ids t in [lo, lo + len), ascending, whose block t / 128 is kept (want) or not kept (not want).
def ids_range(len: Nat, +want: Bool, +kept: List<&2, Nat>, +lo: Nat) -> List<&2, Nat>:
  match len:
    case 0n:
      Nil{}
    case 1n+rest:
      ids_range.cons(ids_pick(want, ids_member(kept, Nat.div(lo, 128n))), lo,
        ids_range(rest, want, kept, 1n+lo))

# The intended id map of a vocabulary of V = 128 nb ids: kept ids ascending, then the other ids ascending.
def ids_id_map(+kept: List<&2, Nat>, +nb: Nat) -> List<&2, Nat>:
  +V = Nat.mul(nb, 128n)
  List.append(&2, Nat, ids_range(V, True{}, kept, 0n), ids_range(V, False{}, kept, 0n))

# The kept ids ascending (the intended pruned column set).
def ids_kept_ids(+kept: List<&2, Nat>, +nb: Nat) -> List<&2, Nat>:
  ids_range(Nat.mul(nb, 128n), True{}, kept, 0n)

# ==== ranking ====

# A candidate: value v (larger is better; a stand-in for the kernel's fp32 value under its total order) and token t.
type IdmCand is Data:
  IdmCand{v: Nat, t: Nat}

def ids_v(+c: IdmCand) -> Nat:
  match c:
    case IdmCand{v, _}:
      v

def ids_t(+c: IdmCand) -> Nat:
  match c:
    case IdmCand{_, t}:
      t

# a ranks before b: larger value, or the same value and the lower token id.
def ids_before(+a: IdmCand, +b: IdmCand) -> Bool:
  Bool.or(Nat.is_lt(ids_v(b), ids_v(a)), Bool.and(Nat.is_eq(ids_v(a), ids_v(b)), Nat.is_lt(ids_t(a), ids_t(b))))

def ids_ceq(+a: IdmCand, +b: IdmCand) -> Bool:
  Bool.and(Nat.is_eq(ids_v(a), ids_v(b)), Nat.is_eq(ids_t(a), ids_t(b)))

def ids_cmember(xs: List<&2, IdmCand>, +c: IdmCand) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(ids_ceq(y, c), ids_cmember(rest, c))

def ids_cnodup(xs: List<&2, IdmCand>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +rest:
      Bool.and(Bool.not(ids_cmember(rest, y)), ids_cnodup(rest))

# Every entry of xs occurs in ys.
def ids_subset(xs: List<&2, IdmCand>, +ys: List<&2, IdmCand>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(ids_cmember(ys, x), ids_subset(rest, ys))

# The same entries (as sets).
def ids_same_set(+xs: List<&2, IdmCand>, +ys: List<&2, IdmCand>) -> Bool:
  Bool.and(ids_subset(xs, ys), ids_subset(ys, xs))

def ids_insert.sel(go: Bool, +c: IdmCand, +y: IdmCand, +rest: List<&2, IdmCand>, deeper: List<&2, IdmCand>)
  -> List<&2, IdmCand>:
  match go:
    case True{}:
      c <> y <> rest
    case False{}:
      y <> deeper

def ids_insert(ys: List<&2, IdmCand>, +c: IdmCand) -> List<&2, IdmCand>:
  match ys:
    case Nil{}:
      c <> Nil{}
    case +y <> +rest:
      ids_insert.sel(ids_before(c, y), c, y, rest, ids_insert(rest, c))

# The full ranking of a candidate list.
def ids_rank(xs: List<&2, IdmCand>) -> List<&2, IdmCand>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      ids_insert(ids_rank(rest), x)

def ids_keep_kept.cons(keep: Bool, +x: IdmCand, rest: List<&2, IdmCand>) -> List<&2, IdmCand>:
  match keep:
    case True{}:
      x <> rest
    case False{}:
      rest

# The entries whose token lies in a kept block, in order.
def ids_keep_kept(xs: List<&2, IdmCand>, +kept: List<&2, Nat>) -> List<&2, IdmCand>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      ids_keep_kept.cons(ids_member(kept, Nat.div(ids_t(x), 128n)), x, ids_keep_kept(rest, kept))

# The reference top-k of a candidate list: the first k entries of its full ranking.
def ids_topk(+k: Nat, xs: List<&2, IdmCand>) -> List<&2, IdmCand>:
  List.take(&2, IdmCand, ids_rank(xs), k)

# ==== switch-back policy ====

# Number of set flags.
def ids_trues(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      Nat.add(ids_bit(y), ids_trues(rest))

def ids_is_nil(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case y <> rest:
      False{}

def ids_is_zero(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      False{}

def ids_beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# A valid policy state (recent window, pending hold, head choice), for window W, trigger T and hold H: the pruned
# head is chosen iff hold == 0; hold <= H; at most W flags, fewer than T set; a pending hold has an empty window.
def ids_valid(+recent: List<&2, Bool>, +hold: Nat, +use: Bool, +W: Nat, +T: Nat, +H: Nat) -> Bool:
  Bool.and(ids_beq(use, ids_is_zero(hold)),
    Bool.and(Nat.is_le(hold, H),
      Bool.and(Nat.is_le(List.length(&2, Bool, recent), W),
        Bool.and(Nat.is_lt(ids_trues(recent), T),
          Bool.or(ids_is_zero(hold), ids_is_nil(recent))))))

# Policy state: recent = the window's out-of-subset flags (newest first), hold = full-head rounds left, use = the
# pruned head is chosen for this round.
type IdmPol is Data:
  IdmPol{recent: List<&2, Bool>, hold: Nat, use: Bool}

# A valid state of a policy in mode `adaptive`: a valid state, and no hold at all in static mode.
def ids_valid_pol(+adaptive: Bool, +st: IdmPol, +W: Nat, +T: Nat, +H: Nat) -> Bool:
  match st:
    case IdmPol{recent, hold, use}:
      Bool.and(Bool.or(adaptive, ids_is_zero(hold)), ids_valid(recent, hold, use, W, T, H))

def ids_falses(n: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      False{} <> ids_falses(p)
