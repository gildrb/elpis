# Reference for the ~rinv link (model: rowinv_link.bend; laws: rowinv_link_laws.bend): the token
# computed for an absolute prefix as ROW 0 OF A 1-ROW ROUND at every position. It does not import
# the served model.
#
# An absolute prefix is the prefill state pcs (one committed state per layer, as the prefill left
# it after the first n0 tokens) and the decode stream w (the tokens at positions n0, n0 + 1, ...;
# the last one is the row itself). Every decode position i is computed as the only row of a
# round: layer l's output is F(l, plan(l, i, 1, 0, 0), c, x) from the layer's committed state c of
# the positions before i and the row's input x, and the position then commits its entry
# ent(l, plan(l, i, 1, 0, 0), x) with adv. The head uses hp(i, 1, 0, 0). Evaluated layer by
# layer (layer l over all positions, then layer l + 1), which is the same function as position by
# position since position i of layer l reads only positions <= i of layer l.
import Base

# Layer l over positions i, i + 1, ... with inputs xs from committed state c: the outputs ...
def lo(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +l: Nat,
    +c: C, +i: Nat) -> List<&2, V>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      F(l, plan(l, i, 1n, 0n, 0n), c, x) <>
        lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i)

# ... and the committed state after them.
def ls(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C,
    ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, xs: List<&2, V>, +l: Nat, c: C, +i: Nat) -> C:
  match xs:
    case Nil{}:
      c
    case +x <> rest:
      ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, rest, l, adv(l, c, ent(l, plan(l, i, 1n, 0n, 0n), x)), 1n+i)

# Layers l, l + 1, ... (one prefill state each) applied to the layer-l inputs xs of positions i ..
def up(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E,
    ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, cs: List<&2, C>, +l: Nat,
    xs: List<&2, V>, +i: Nat) -> List<&2, V>:
  match cs:
    case Nil{}:
      xs
    case +c <> rest:
      up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), i)

# The committed state of every layer after positions i .. i + |xs| - 1.
def states(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    cs: List<&2, C>, +l: Nat, +xs: List<&2, V>, +i: Nat) -> List<&2, C>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      ls(~V, ~E, ~C, ~P, ~ent, ~adv, ~plan, xs, l, c, i) <>
        states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, rest, 1n+l, lo(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, xs, l, c, i), i)

def embs(~V: Data, ~emb: U32 -> V, xs: List<&2, U32>) -> List<&2, V>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      emb(x) <> embs(~V, ~emb, rest)

def last.go(~V: Data, xs: List<&2, V>, p: V) -> V:
  match xs:
    case Nil{}:
      p
    case y <> rest:
      last.go(~V, rest, y)

def last(~V: Data, ~z: V, xs: List<&2, V>) -> V:
  match xs:
    case Nil{}:
      z
    case x <> rest:
      last.go(~V, rest, x)

# Prefill + decode prefix: pcs is the committed state of every layer the prefill left after the
# first n0 tokens; w is the decode stream (positions n0 ..). The token of that absolute prefix is
# row 0 of a 1-row round at position n0 + |w| - 1.
def ref(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~head: P -> V -> U32,
    ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, ~hp: Nat -> Nat -> Nat -> Nat -> P, +pcs: List<&2, C>,
    +n0: Nat, +w: List<&2, U32>) -> U32:
  head(hp(Nat.add(n0, Nat.sub(List.length(&2, U32, w), 1n)), 1n, 0n, 0n),
    last(~V, ~z, up(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pcs, 0n, embs(~V, ~emb, w), n0)))

# The committed state of every layer once the decode tokens u (positions n0 ..) are committed by
# 1-row rounds.
def committed(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~emb: U32 -> V, ~F: Nat -> P -> C -> V -> V,
    ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P,
    +pcs: List<&2, C>, +n0: Nat, +u: List<&2, U32>) -> List<&2, C>:
  states(~V, ~E, ~C, ~P, ~F, ~ent, ~adv, ~plan, pcs, 0n, embs(~V, ~emb, u), n0)

# The token of a whole token prefix p: its first n0 tokens were prefilled (pf gives the committed
# state of every layer the prefill of those tokens leaves), the rest are decode positions.
def ref_prefix(~V: Data, ~E: Data, ~C: Data, ~P: Data, ~z: V, ~emb: U32 -> V,
    ~F: Nat -> P -> C -> V -> V, ~ent: Nat -> P -> V -> E, ~adv: Nat -> C -> E -> C,
    ~head: P -> V -> U32, ~plan: Nat -> Nat -> Nat -> Nat -> Nat -> P, ~hp: Nat -> Nat -> Nat -> Nat -> P,
    ~pf: List<&2, U32> -> List<&2, C>, ~n0: Nat, +p: List<&2, U32>) -> U32:
  ref(~V, ~E, ~C, ~P, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~plan, ~hp, pf(List.take(&2, U32, p, n0)), n0,
    List.drop(&2, U32, p, n0))
