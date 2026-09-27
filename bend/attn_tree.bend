# TREE verify split kernel of ext patch 3012 (exllamav3_ext/attn_verify.cu split_body<KB, VB, TREE =
# true>: attn_verify_split_k3v3_tree / _k4v4_tree; offsets and smem in attn_verify.cuh), transcribed
# from the CUDA integer expressions over Nat: which tiles run once per leaf, which rows each pass
# admits, which stash row an in-round column holds in a pass, and the traps. H = attn_verify.cuh,
# C = attn_verify.cu. Everything not modelled here (the tile loop, lanes, slots, combine) is the
# 3006 kernel of attn_stride.bend, shared by both instantiations. The TreeDesc is the 128-byte
# host-validated descriptor of TreeDesign DESIGN.md 2.2; the kernel reads bytes 0..3 (header),
# 16..23 (depth), 32..39 (leaf_of), 40..47 (leaves) and 64..127 (path), modelled as the field
# lists of TreeDesc below (byte offsets H AV_TD_*). Independent reference: attn_tree_spec.bend;
# laws: attn_tree_laws.bend.
import Base

# The kernel's view of a TreeDesc: header bytes 0..3 and the four fields it reads, each a list of
# its bytes in row order (path: its 8 rows of 8 bytes, path[l][j] = byte 64 + 8 l + j)
type TreeDesc is Data:
  TreeDesc{magic: Nat, version: Nat, n_rows: Nat, n_leaf: Nat, depth: List<&2, Nat>, leaf_of: List<&2, Nat>, leaves: List<&2, Nat>, path: List<&2, List<&2, Nat>>}

# H AV_TD_* byte offsets (DESIGN.md 2.2)
def td_n_leaf() -> Nat:
  3n

def td_depth() -> Nat:
  16n

def td_leaf_of() -> Nat:
  32n

def td_leaves() -> Nat:
  40n

def td_path() -> Nat:
  64n

def pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# tree[off + i] for a field starting at off: the i-th byte of the field (0 past it; the kernel
# reads rows, leaves p < n_leaf and path bytes of rows < 8 only: attn_tree_laws.bend entry_ok /
# pass_ok)
def at(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+k:
          at(rest, k)

def n_leaf(d: TreeDesc) -> Nat:
  match d:
    case TreeDesc{mg, v, nr, nl, dp, lo, lv, pt}:
      nl

# C: depth[gid] = tree[AV_TD_DEPTH + gid]
def depth(d: TreeDesc, r: Nat) -> Nat:
  match d:
    case TreeDesc{mg, v, nr, nl, dp, lo, lv, pt}:
      at(dp, r)

# C: my_leaf = tree[AV_TD_LEAF_OF + gid]
def leaf_of(d: TreeDesc, r: Nat) -> Nat:
  match d:
    case TreeDesc{mg, v, nr, nl, dp, lo, lv, pt}:
      at(lo, r)

# C: lf = tree[AV_TD_LEAVES + pass]
def leaf(d: TreeDesc, p: Nat) -> Nat:
  match d:
    case TreeDesc{mg, v, nr, nl, dp, lo, lv, pt}:
      at(lv, p)

def row(xs: List<&2, List<&2, Nat>>, i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+k:
          row(rest, k)

# C: tree[AV_TD_PATH + AV_QPOS * lf + j] (row lf, byte j)
def path(d: TreeDesc, l: Nat, j: Nat) -> Nat:
  match d:
    case TreeDesc{mg, v, nr, nl, dp, lo, lv, pt}:
      at(row(pt, l), j)

# C entry trap: q_len != AV_QPOS || magic != 0x54 || version != 1 || n_rows != 8, then
# n_leaf < 1 || n_leaf >= AV_QPOS || my_depth >= AV_QPOS. True when the kernel does not trap.
def entry_ok(+q_len: Nat, d: TreeDesc, +gid: Nat) -> Bool:
  match d:
    case TreeDesc{mg, v, nr, +nl, dp, lo, lv, pt}:
      Bool.and(Nat.is_eq(q_len, 8n),
        Bool.and(Nat.is_eq(mg, 84n),
          Bool.and(Nat.is_eq(v, 1n),
            Bool.and(Nat.is_eq(nr, 8n),
              Bool.and(Nat.is_le(1n, nl),
                Bool.and(Nat.is_lt(nl, 8n), Nat.is_lt(at(dp, gid), 8n)))))))

# C: T0 = base / AV_T, T1 = (base + AV_QPOS - 1) / AV_T: the round's tail tiles
def tail_lo(+base: Nat) -> Nat:
  Nat.div(base, 64n)

def tail_hi(+base: Nat) -> Nat:
  Nat.div(Nat.add(base, 7n), 64n)

# C: q_abs = base + my_depth (TREE), the row's causal bound
def q_abs(+base: Nat, d: Nat) -> Nat:
  Nat.add(base, d)

# C: q_lim = my_leaf == lf ? q_abs : -1 on a tail tile (q_abs elsewhere), then `ok = row_ok && tok <=
# q_lim`: whether pass `lf` admits the row, and whether it lets kv position tok into the row
def in_pass(tail: Bool, +my_leaf: Nat, +lf: Nat) -> Bool:
  match tail:
    case True{}:
      Nat.is_eq(my_leaf, lf)
    case False{}:
      True{}

def sees(tail: Bool, +my_leaf: Nat, +lf: Nat, +tok: Nat, +qa: Nat) -> Bool:
  Bool.and(in_pass(tail, my_leaf, lf), Nat.is_le(tok, qa))

# C pass copy: in-round column c = base + j of the tile takes stash row
# src = j <= depth[lf] ? path[lf][j] : j (stash row k = slot base + k); `if (src >= AV_QPOS) __trap()`
def src(+j: Nat, +dl: Nat, +pj: Nat) -> Nat:
  pick(Nat.is_le(j, dl), pj, j)

# C: `if (lf >= AV_QPOS) __trap()` and the src trap, for pass p's column j. True when no trap.
def pass_ok(+d: TreeDesc, +p: Nat, +j: Nat) -> Bool:
  +lf = leaf(d, p)
  Bool.and(Nat.is_lt(lf, 8n), Nat.is_lt(src(j, depth(d, lf), path(d, lf, j)), 8n))

# C: the stash slot pass p puts at in-round column base + j: base + src(j, depth[lf], path[lf][j])
def slot(+d: TreeDesc, +p: Nat, +j: Nat) -> Nat:
  +lf = leaf(d, p)
  src(j, depth(d, lf), path(d, lf, j))

def bit(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# The passes p < k of a tail tile that let kv position tok into row r (the row's view of that tile
# column over the whole pass loop)
def pass_hits(+k: Nat, +d: TreeDesc, +r: Nat, +tok: Nat, +qa: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(pass_hits(p, d, r, tok, qa), bit(sees(True{}, leaf_of(d, r), leaf(d, p), tok, qa)))

# The passes p < k of a tail tile that admit row r (q_lim = q_abs)
def pass_count(+k: Nat, +d: TreeDesc, +r: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(pass_count(p, d, r), bit(in_pass(True{}, leaf_of(d, r), leaf(d, p))))
