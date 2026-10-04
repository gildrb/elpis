# Served-forward model for the ~rinv link (laws: rowinv_link_laws.bend; reference:
# rowinv_link_spec.bend). One verify round of an L-layer target over m rows, generic in every
# floating-point operation and in the kernel families:
#   - V: a row's hidden vector between layers; E: the entry a row leaves in a layer's committed
#     state (attention: its RoPE'd, CQ3-quantized K/V; GDN: its conv input / rule input); C: one
#     layer's committed state (K/V cache prefix; GDN recurrent state + conv window); P: a kernel
#     plan (everything a kernel's arithmetic sequence is a function of besides its operands:
#     positions, tile / slot / combine orders, split-K partitions and reduction orders, ...).
#   - emb (embedding), F (the layer's per-row output from its plan, the context state and the row's
#     input), ent (the entry a row adds), adv (append one entry to a layer state), head (final norm,
#     lm_head, greedy argmax) are template parameters: opaque deterministic functions, i.e. the same
#     plan and operands give the same result (hardware determinism is the named hypothesis
#     H_det in rowinv_link_laws.bend).
#   - plan(l, base, m, r, dep) / hp(base, m, r, dep): the plan of layer l / of the head for row r
#     of an m-row round whose row 0 sits at absolute position base, the row at logical depth dep
#     (absolute position base + dep).
#   - The round's shape T gives each row its path pth(sh, r) (root row 0 first, the row last) and,
#     per layer, the in-round rows its kernel folds into its context, in logical order,
#     gat(l, sh, r) (attention: the stash rows at the in-round columns; GDN: the rows whose rule
#     steps precede the row's own).
# Row r's output at layer l is F(l, plan, context, own input), where the context is the layer's
# committed state advanced by the entries of the gathered rows, in gather order. The rows of a
# layer are computed from the previous layer's outputs of all rows (one launch per layer).
# This is a proof model (lists), not a shipped artifact.
import Base

# The i-th element (z past the end).
def at(~V: Data, ~z: V, xs: List<&2, V>, +i: Nat) -> V:
  match xs:
    case Nil{}:
      z
    case +x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          at(~V, ~z, rest, j)

# The i-th row index of a path (0 past the end).
def nthn(xs: List<&2, Nat>, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          nthn(rest, j)

# A row's logical depth: its path length minus one (its absolute position is base + dep).
def dep(~T: Data, ~pth: T -> Nat -> List<&2, Nat>, +sh: T, +r: Nat) -> Nat:
  Nat.sub(List.length(&2, Nat, pth(sh, r)), 1n)

# The layer-l context of a row: the committed state c advanced by the entry of every gathered row
# a (in gather order), each computed by the row's own launch coordinates (base, m, a, dep(a)).
def ctx(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, rows: List<&2, Nat>, +l: Nat, c: C, +sh: T, +base: Nat,
    +m: Nat, +vals: List<&2, V>) -> C:
  match rows:
    case Nil{}:
      c
    case +a <> rest:
      ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, rest, l,
        adv(l, c, ent(l, plan(l, base, m, a, dep(~T, ~pth, sh, a)), at(~V, ~z, vals, a))), sh, base, m, vals)

# One layer launch: rows r .. r + k - 1 of the round, from the previous layer's outputs vals.
def layer(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat,
    +l: Nat, +c: C, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>) -> List<&2, V>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      F(l, plan(l, base, m, r, dep(~T, ~pth, sh, r)),
        ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, gat(l, sh, r), l, c, sh, base, m, vals),
        at(~V, ~z, vals, r)) <>
        layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, k1, 1n+r, l, c, sh, base, m, vals)

# The layers from l on, one committed state per layer (cs = the engine's committed state of every
# layer at the round start).
def fwd(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, cs: List<&2, C>,
    +l: Nat, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>) -> List<&2, V>:
  match cs:
    case Nil{}:
      vals
    case +c <> rest:
      fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, rest, 1n+l, sh, base, m,
        layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, c, sh, base, m, vals))

def embs(~V: Data, ~emb: U32 -> V, xs: List<&2, U32>) -> List<&2, V>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      emb(x) <> embs(~V, ~emb, rest)

# The head launch (final norm, lm_head, fused greedy argmax) over rows r .. r + k - 1.
def heads(~V: Data, ~P: Data, ~T: Data, ~z: V, ~head: P -> V -> U32, ~hp: Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, k: Nat, +r: Nat, +sh: T, +base: Nat, +m: Nat,
    +vals: List<&2, V>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      head(hp(base, m, r, dep(~T, ~pth, sh, r)), at(~V, ~z, vals, r)) <>
        heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, k1, 1n+r, sh, base, m, vals)

# The verify ids of a round: committed states cs, row 0 at absolute position base, row input
# tokens toks (row 0 = the anchor), shape sh; m = |toks| rows.
def tokens(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~emb: U32 -> V,
    ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C,
    ~head: P -> V -> U32, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, ~hp: Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, +cs: List<&2, C>,
    +base: Nat, +toks: List<&2, U32>, +sh: T) -> List<&2, U32>:
  +m = List.length(&2, U32, toks)
  heads(~V, ~P, ~T, ~z, ~head, ~hp, ~pth, m, 0n, sh, base, m,
    fwd(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, cs, 0n, sh, base, m, embs(~V, ~emb, toks)))

# The tokens along a path (row 0's token is the anchor): the part of a row's absolute prefix
# from the anchor on.
def stream(+toks: List<&2, U32>, ps: List<&2, Nat>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case +a <> rest:
      at(~U32, ~0, toks, a) <> stream(toks, rest)

# Decidable equality of row-index lists (the path obligations are stated as guarded Bool checks).
def nat_list_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case y <> yr:
          False{}
    case +x <> xr:
      match ys:
        case Nil{}:
          False{}
        case +y <> yr:
          Bool.and(Nat.is_eq(x, y), nat_list_eq(xr, yr))

# The engine's commit of a round: every layer's committed state advanced by the entries of the
# committed rows `rows` (the accepted path, root first), each entry as the round's forward computed it
# (the row's own launch coordinates and its layer input), layer by layer. Attention layers: the
# verify wrote row a's RoPE'd, quantized K/V at its slot and ext 3013 moves the path rows' slots to
# the committed positions (kv_compact_laws.commit_moves: slots 0 .. count - 1 then hold the path rows
# in order); GDN layers: the commit replay applies the path rows' rule steps from the round-start
# state with the verify's per-token arithmetic (gdn_rounds_laws.verify_split_point,
# gdn_tree_laws.tree_all_shapes: row_map / src_off read exactly the path).
def commit(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~T: Data, ~z: V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    ~pth: T -> Nat -> List<&2, Nat>, ~gat: Nat -> T -> Nat -> List<&2, Nat>, cs: List<&2, C>,
    +l: Nat, +rows: List<&2, Nat>, +sh: T, +base: Nat, +m: Nat, +vals: List<&2, V>) -> List<&2, C>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      ctx(~V, ~E, ~C, ~P, ~T, ~z, ~ent, ~adv, ~plan, ~pth, rows, l, c, sh, base, m, vals) <>
        commit(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, rest, 1n+l, rows, sh, base, m,
          layer(~V, ~E, ~C, ~P, ~T, ~z, ~F, ~ent, ~adv, ~plan, ~pth, ~gat, m, 0n, l, c, sh, base, m, vals))

# ---------------------------------------------------------------- mutation models (not the engine)
# Witnesses for rowinv_link_laws.plan_leak_differs / gather_drop_differs: one layer, a context that
# counts the folded entries, an output that shows its plan and context, a head that tests for 1.

def w_emb(t: U32) -> Nat:
  0n

def w_F(l: Nat, p: Nat, c: Nat, x: Nat) -> Nat:
  Nat.add(p, c)

def w_ent(l: Nat, p: Nat, x: Nat) -> Nat:
  1n

def w_adv(l: Nat, c: Nat, e: Nat) -> Nat:
  Nat.add(c, e)

def w_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def w_head(p: Nat, v: Nat) -> U32:
  w_bit(Nat.is_eq(v, 1n))

# A plan that depends only on the absolute position ...
def w_plan(l: Nat, base: Nat, m: Nat, r: Nat, d: Nat) -> Nat:
  0n

# ... and one that leaks the round size m (violates O_plan).
def w_plan_m(l: Nat, base: Nat, m: Nat, r: Nat, d: Nat) -> Nat:
  Nat.sub(m, 1n)

def w_hp(base: Nat, m: Nat, r: Nat, d: Nat) -> Nat:
  0n

# Chain paths 0 .. r; the honest gather (ancestors) and one that drops them (violates O_gat).
def w_path(+r: Nat) -> List<&2, Nat>:
  match r:
    case 0n:
      [0n]
    case 1n+q:
      List.append(&2, Nat, w_path(q), [1n+q])

def w_pth(sh: Nat, r: Nat) -> List<&2, Nat>:
  +r = r
  w_path(r)

def w_gat(l: Nat, sh: Nat, r: Nat) -> List<&2, Nat>:
  +r = r
  List.take(&2, Nat, w_path(r), r)

def w_gat_drop(l: Nat, sh: Nat, r: Nat) -> List<&2, Nat>:
  Nil{}
