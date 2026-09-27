# Obligations for the ext 5109 GDN tree verify and commit over the Nat model gdn_tree.bend against
# gdn_tree_spec.bend, for every served shape (all 5040 8-row parent arrays with parent[r] < r), decided by
# evaluation. States are symbolic (the rows applied since S0), so equal histories mean the same rule steps on
# the same rows in the same order: with one arithmetic body for ADV / REPLAY / PEEK (SASS diff gate) the same
# fp32 values. Out of scope: the host validation of the TreeDesc bytes (S4 derive, DESIGN.md 2.4), the fp32
# arithmetic itself, the CUDA code (the model is a transcription; the GPU differentials test conformance).
import Base
import ./gdn_tree.bend as Impl
import ./gdn_tree_spec.bend as Spec

def count_row(+r: Nat, outs: List<&2, Impl.Out>) -> Nat:
  match outs:
    case Nil{}:
      0n
    case Impl.Out{+x, _} <> rest:
      Nat.add(Spec.b2n(Nat.is_eq(x, r)), count_row(r, rest))

def hist_of(+r: Nat, outs: List<&2, Impl.Out>) -> List<&2, Nat>:
  match outs:
    case Nil{}:
      Nil{}
    case Impl.Out{+x, +h} <> rest:
      Spec.sel_l(Nat.is_eq(x, r), h, hist_of(r, rest))

def alt_from(xs: List<&2, Nat>, +p: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Bool.not(Nat.is_eq(p, x)), alt_from(rest, x))

def alternates(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      alt_from(rest, x)

def maxl(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.max(x, maxl(rest))

def rows_lt8(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case b <> rest:
      Bool.and(Nat.is_lt(Nat.mod(b, 16n), 8n), rows_lt8(rest))

def row_ok(+r: Nat, +par: List<&2, Nat>, +outs: List<&2, Impl.Out>) -> Bool:
  +P = Spec.path(par, r)
  +n = Spec.len(P)
  +emit = Bool.and(Nat.is_eq(count_row(r, outs), 1n), Spec.nat_eq_list(hist_of(r, outs), P))
  +win = Bool.and(Spec.nat_eq_list(Impl.window(par, r), Spec.verify_window(par, r)), Nat.is_le(maxl(Impl.window(par, r)), Nat.add(4n, r)))
  +rep = Spec.nat_eq_list(Impl.replay_rows(Impl.row_map(P, n), n), hist_of(r, outs))
  Bool.and(emit, Bool.and(win, rep))

def rows_ok.go(n: Nat, +r: Nat, +par: List<&2, Nat>, +outs: List<&2, Impl.Out>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(row_ok(r, par, outs), rows_ok.go(m, 1n+r, par, outs))

def prog_ok(+par: List<&2, Nat>) -> Bool:
  +bs = Impl.enc_all(Spec.prog(par))
  Bool.and(Nat.is_le(Spec.len(bs), 14n), rows_lt8(bs))

# (commit) every accepted node `last` and count <= depth[last] + 1: src_off in 0..11 strictly increasing, the
# tail offsets read inside the 11-entry buffer, and the conv window read equals the committed path's window
def inc_from(xs: List<&2, Nat>, +p: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      Bool.and(Nat.is_lt(p, x), inc_from(rest, x))

def alternates_inc(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> rest:
      inc_from(rest, x)

def commit_ok.go(n: Nat, +count: Nat, +P: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      +offs = Impl.src_off(P, count)
      +Pc = Spec.take(P, count)
      Bool.and(
        Bool.and(Spec.nat_eq_list(Impl.conv_read(count, offs), Spec.commit_window(Pc)),
          Bool.and(Bool.and(Nat.is_lt(Impl.buf_off(count, Spec.nth(offs, 3n)), 11n), Nat.is_le(Spec.nth(offs, 3n), 11n)),
            alternates_inc(offs))),
        commit_ok.go(m, 1n+count, P))


def commit_rows.go(n: Nat, +r: Nat, +par: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      +P = Spec.path(par, r)
      Bool.and(commit_ok.go(Spec.len(P), 1n, P), commit_rows.go(m, 1n+r, par))

def shape_w(+par: List<&2, Nat>, w: Impl.W) -> Bool:
  match w:
    case Impl.W{_, _, +outs, +bufs}:
      Bool.and(Bool.and(prog_ok(par), alternates(bufs)),
        Bool.and(rows_ok.go(8n, 0n, par, outs), commit_rows.go(8n, 0n, par)))

def shape_ok(+par: List<&2, Nat>) -> Bool:
  shape_w(par, Impl.run(par))


def all_ok(xs: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case p <> rest:
      Bool.and(shape_ok(p), all_ok(rest))

# (1)-(5) For all 5040 shapes: the program has <= 14 steps (prog[16]) with rows < 8; consecutive arithmetic
# steps use different dot1 buffers; every row is emitted exactly once, from state history path[r]; row r's conv
# window is the last K of the committed window and its path's inputs, reading only seq entries <= K + r
# (written before); the replay of path[r] under row_map reads exactly the rows of that history; every commit
# (last, count) reads the committed path's conv window with src_off strictly increasing in 0..11 inside the tail
law tree_all_shapes:
  {Nat.is_eq(List.length(&2, List<&2, Nat>, Spec.shapes()), 5040n) == True{} : Bool} &
  {all_ok(Spec.shapes()) == True{} : Bool}

# (6) CHAIN: the program is ADV 0..7 (gdn_rule_tokens' loop, buffers s & 1), windows slide by one row, and the
# commit maps are the identity (src_off 0..3), i.e. the cs12 launches
law tree_chain:
  {Spec.nat_eq_list(Impl.enc_all(Spec.prog(Spec.chain())), [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n]) == True{} : Bool} &
  {Spec.nat_eq_list(Impl.window(Spec.chain(), 5n), [6n, 7n, 8n, 9n]) == True{} : Bool} &
  {Spec.nat_eq_list(Impl.src_off(Spec.path(Spec.chain(), 7n), 5n), [0n, 1n, 2n, 3n]) == True{} : Bool}
