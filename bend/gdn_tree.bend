# The ext 5109 GDN tree verify and tree commit (exllamav3_ext/gdn.cu), transcribed over Nat from the kernel's
# expressions; fp32 arithmetic is symbolic: a state is the list of rows applied since S0 (the rule step is one
# body for ADV / REPLAY / PEEK, SASS-checked), a window is the list of seq indices read.
#   - walker gdn_rule_tokens_tree: for t < n_prog: op = prog[t] >> 4, r = prog[t] & 15; op 2 (RELOAD):
#     state <- S0, no dot1 buffer; else dot1 buffer = step & 1, ++step; op 1 (PEEK) emits row r from the state
#     advanced by r and keeps the state; op 3 (REPLAY) advances without emitting; op 0 (ADV) advances and emits
#   - conv window of row s: d = depth[s], kk < K = 4: i = d - (K - 1) + kk,
#     seq index K + (i >= 0 ? path[s][i] : i)
#   - conv commit (batched_conv_rewind<MAP>, RewindPlans.check_maps): src_off[k] = seqidx(count + k) - count,
#     seqidx(L) = L < K ? L : K + P[L - K]; the job reads buffer offset size - m - K + src_off[k] (m = 8 - count
#     rejected) of the history-layout tail, which holds seq[SEQ - size + o] at offset o (SEQ = K + 8, size 11)
#   - replay (batched_state_replay<GATHER, MAP>): token s < count reads verify row row_map[s], row_map =
#     P then s for s >= count
# The TreeDesc fields (depth, path, prog bytes) are the host-validated ones: DESIGN.md 2.2, built here from the
# reference tree (gdn_tree_spec.bend). Proof model only (not shipped).
import Base
import ./gdn_tree_spec.bend as Spec

# ---- prog bytes: op << 4 | row
def enc(+o: Spec.Op) -> Nat:
  match o:
    case Spec.Op{+op, +row}:
      Nat.add(Nat.mul(op, 16n), row)

def enc_all(xs: List<&2, Spec.Op>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case o <> rest:
      enc(o) <> enc_all(rest)

# ---- the walker. Emitted row r with its state history
type Out is Data:
  Out{row: Nat, hist: List<&2, Nat>}

type W is Data:
  W{hist: List<&2, Nat>, step: Nat, outs: List<&2, Out>, bufs: List<&2, Nat>}

def walk_op(op: Nat, +r: Nat, +hist: List<&2, Nat>, +step: Nat, +outs: List<&2, Out>, +bufs: List<&2, Nat>) -> W:
      match op:
        case 0n:
          W{Spec.cat(hist, [r]), 1n+step, List.append(&2, Out, outs, [Out{r, Spec.cat(hist, [r])}]), Spec.cat(bufs, [Nat.mod(step, 2n)])}
        case 1n+o1:
          match o1:
            case 0n:
              W{hist, 1n+step, List.append(&2, Out, outs, [Out{r, Spec.cat(hist, [r])}]), Spec.cat(bufs, [Nat.mod(step, 2n)])}
            case 1n+o2:
              match o2:
                case 0n:
                  W{Nil{}, step, outs, bufs}
                case 1n+o3:
                  W{Spec.cat(hist, [r]), 1n+step, outs, Spec.cat(bufs, [Nat.mod(step, 2n)])}

def walk_one(+b: Nat, w: W) -> W:
  match w:
    case W{+hist, +step, +outs, +bufs}:
      walk_op(Nat.div(b, 16n), Nat.mod(b, 16n), hist, step, outs, bufs)


def walk(bs: List<&2, Nat>, w: W) -> W:
  match bs:
    case Nil{}:
      w
    case b <> rest:
      walk(rest, walk_one(b, w))

def run(+par: List<&2, Nat>) -> W:
  walk(enc_all(Spec.prog(par)), W{Nil{}, 0n, Nil{}, Nil{}})

# ---- conv window of row s (K = 4)
def win_idx(+d: Nat, +pth: List<&2, Nat>, +kk: Nat) -> Nat:
  +dk = Nat.add(d, kk)
  Spec.sel_n(Nat.is_lt(dk, 3n), Nat.sub(Nat.add(4n, dk), 3n), Nat.add(4n, Spec.nth(pth, Nat.sub(dk, 3n))))

def window(+par: List<&2, Nat>, +s: Nat) -> List<&2, Nat>:
  +d = Spec.depth(par, s)
  +pth = Spec.path(par, s)
  [win_idx(d, pth, 0n), win_idx(d, pth, 1n), win_idx(d, pth, 2n), win_idx(d, pth, 3n)]

# ---- conv commit
def seqidx(+P: List<&2, Nat>, +L: Nat) -> Nat:
  Spec.sel_n(Nat.is_lt(L, 4n), L, Nat.add(4n, Spec.nth(P, Nat.sub(L, 4n))))

def src_off(+P: List<&2, Nat>, +count: Nat) -> List<&2, Nat>:
  [Nat.sub(seqidx(P, count), count), Nat.sub(seqidx(P, Nat.add(count, 1n)), count),
   Nat.sub(seqidx(P, Nat.add(count, 2n)), count), Nat.sub(seqidx(P, Nat.add(count, 3n)), count)]

# buffer offset read for window entry v: size - m - K + v, m = 8 - count, size 11
def buf_off(+count: Nat, +v: Nat) -> Nat:
  Nat.add(Nat.sub(Nat.sub(11n, Nat.sub(8n, count)), 4n), v)

# the seq index the tail holds at offset o (SEQ 12, size 11)
def tail_seq(+o: Nat) -> Nat:
  Nat.add(o, 1n)

def conv_read(+count: Nat, offs: List<&2, Nat>) -> List<&2, Nat>:
  match offs:
    case Nil{}:
      Nil{}
    case v <> rest:
      tail_seq(buf_off(count, v)) <> conv_read(count, rest)

# ---- replay rows
def row_map(+P: List<&2, Nat>, +count: Nat) -> List<&2, Nat>:
  Spec.cat(Spec.take(P, count), Spec.range(count, 16n))

def replay_rows(+rm: List<&2, Nat>, +count: Nat) -> List<&2, Nat>:
  Spec.take(rm, count)
