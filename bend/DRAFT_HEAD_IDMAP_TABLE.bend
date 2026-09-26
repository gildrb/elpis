# Finite differential table of the pruned draft head model (bend/draft_head_idmap.bend, ext patch 9005c), compared
# byte for byte by bend/draft_head_idmap_diff.py against the patched tree's own Python (dflash2_head_blocks.py
# kept_blocks / PrunedHeadPolicy, Q4DraftHead's kept check, keep_cols, id_map and topk slicing) and the kernel's
# better() and epilogue statements compiled for the CPU. Every value below is an Impl def; the printer only enumerates.
# Rows (N = 896, then 1024; V = 248320, nb = 1940):
#   K vocab= block= n= n_alt= window= trigger= hold= topk=     the model's constants
#   O <1024 block ids>                                          the model's DRAFT_HEAD_BLOCK_ORDER
#   B N ok= head_ok= keep_cols= <kept blocks ascending>         kept_blocks(order, N), the two checks, 128 * len(set(kb))
#   M N r <128 token ids>                                       row r (columns 128 r .. 128 r + 127) of the id map
#   T N s id|full|pruned <value:token x16>                      top-16 of the identity call, the full call on the
#                                                               permuted copy, and the prefix call, value seed s
#   P sc i ev use hold len sum                                  policy trace (kept = N 896 blocks): event ev (a token,
#                                                               negative as -m, or r = reset), then the state
#   H c vocab= ok= kb <list>                                    Q4DraftHead's kept-block check on fixed lists
#   R c n= vocab= ok= blocks <list> order <list>                kept_blocks' check on fixed orders
# Value seeds: token t of seed (a, b, m) has value (a t + b) % m (all < 2^24, exact in fp32).
import Base
import ./draft_head_idmap.bend as Impl
import ./draft_head_idmap_spec.bend as Spec

def idt_num(+n: Nat) -> String:
  Nat.show(n)

def idt_bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# " x0 x1 ..."
def idt_join(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case +x <> rest:
      " " ++ idt_num(x) ++ idt_join(rest)

def idt_line.cons(+x: Nat, sr: String & List<&2, Nat>) -> String & List<&2, Nat>:
  (s, r) = sr
  (" " ++ idt_num(x) ++ s, r)

# The next n ids as " x0 x1 ...", and the rest of the list.
def idt_line(n: Nat, xs: List<&2, Nat>) -> String & List<&2, Nat>:
  match n:
    case 0n:
      ("", xs)
    case 1n+p:
      match xs:
        case Nil{}:
          ("", Nil{})
        case +x <> rest:
          idt_line.cons(x, idt_line(p, rest))

# fuel rows of 128 ids: sr is the next row and the rest.
def idt_rows(fuel: Nat, +N: Nat, +i: Nat, sr: String & List<&2, Nat>) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+f:
      (s, rest) = sr
      do IO<Unit>:
        IO.print("M " ++ idt_num(N) ++ " " ++ idt_num(i) ++ s)
        idt_rows(f, N, 1n+i, idt_line(128n, rest))

# ---- per-token values ----

type IdtSeed is Data:
  IdtSeed{a: Nat, b: Nat, m: Nat}

def idt_val(+sd: IdtSeed, +t: Nat) -> Nat:
  match sd:
    case IdtSeed{a, b, m}:
      Nat.mod(Nat.add(Nat.mul(a, t), b), m)

# Leaf of token t0 + stride * (path bits): a depth-d tree covers tokens t0, t0 + stride, ... (LSB-first lookup).
def idt_tree(d: Nat, +sd: IdtSeed, +t0: Nat, +stride: Nat) -> Impl.IdmVals:
  match d:
    case 0n:
      Impl.IdmLeaf{idt_val(sd, t0)}
    case 1n+p:
      +q = p
      l r = idt_tree(q, sd, t0, Nat.mul(2n, stride)) idt_tree(q, sd, Nat.add(t0, stride), Nat.mul(2n, stride))
      Impl.IdmNode{l, r}

def idt_cands(xs: List<&2, Spec.IdmCand>) -> String:
  match xs:
    case Nil{}:
      ""
    case +c <> rest:
      " " ++ idt_num(Spec.ids_v(c)) ++ ":" ++ idt_num(Spec.ids_t(c)) ++ idt_cands(rest)

def idt_seed_row(+N: Nat, +s: Nat, +sd: IdtSeed, +kept: List<&2, Nat>, +nb: Nat) -> IO(Unit):
  +vals = idt_tree(18n, sd, 0n, 1n)
  +k = Impl.idm_topk_k()
  +V = Nat.mul(nb, 128n)
  +tag = "T " ++ idt_num(N) ++ " " ++ idt_num(s)
  a b = Impl.idm_call(k, vals, None{}, V) Impl.idm_head_call(k, vals, kept, nb, False{})
  do IO<Unit>:
    IO.print(tag ++ " id" ++ idt_cands(a))
    IO.print(tag ++ " full" ++ idt_cands(b))
    IO.print(tag ++ " pruned" ++ idt_cands(Impl.idm_head_call(k, vals, kept, nb, True{})))

def idt_seeds() -> List<&2, IdtSeed>:
  [IdtSeed{40503n, 12345n, 1000003n}, IdtSeed{1n, 0n, 20000n}, IdtSeed{1n, 0n, 16777216n}, IdtSeed{16777213n, 977n, 16777216n}]

def idt_seed_rows(sds: List<&2, IdtSeed>, +N: Nat, +s: Nat, +kept: List<&2, Nat>, +nb: Nat) -> IO(Unit):
  match sds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case sd <> rest:
      do IO<Unit>:
        idt_seed_row(N, s, sd, kept, nb)
        idt_seed_rows(rest, N, 1n+s, kept, nb)

def idt_seed_heads(sds: List<&2, IdtSeed>, +s: Nat) -> IO(Unit):
  match sds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case sd <> rest:
      match sd:
        case IdtSeed{a, b, m}:
          do IO<Unit>:
            IO.print("S " ++ idt_num(s) ++ " " ++ idt_num(a) ++ " " ++ idt_num(b) ++ " " ++ idt_num(m))
            idt_seed_heads(rest, 1n+s)

def idt_blocks(+N: Nat, +nb: Nat) -> IO(Unit):
  +order = Impl.idm_order()
  +V = Nat.mul(nb, 128n)
  +kept = Impl.idm_kept_blocks(order, N)
  do IO<Unit>:
    IO.print("B " ++ idt_num(N) ++ " ok=" ++ idt_bit(Impl.idm_kept_ok(order, N, V)) ++ " head_ok=" ++ idt_bit(Impl.idm_head_ok(kept, V)) ++
      " keep_cols=" ++ idt_num(Impl.idm_keep_cols(kept)) ++ idt_join(kept))
    idt_rows(nb, N, 0n, idt_line(128n, Impl.idm_id_map(kept, nb)))
    idt_seed_rows(idt_seeds(), N, 0n, kept, nb)

# ---- policy traces ----

def idt_in(+t: Nat) -> Impl.IdmEv:
  Impl.IdmObs{Impl.IdmPos{t}}

def idt_neg(+m: Nat) -> Impl.IdmEv:
  Impl.IdmObs{Impl.IdmNeg{m}}

def idt_rep(n: Nat, +ev: Impl.IdmEv) -> List<&2, Impl.IdmEv>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      ev <> idt_rep(p, ev)

def idt_ev(+ev: Impl.IdmEv) -> String:
  match ev:
    case Impl.IdmReset{}:
      "r"
    case Impl.IdmObs{tok}:
      match tok:
        case Impl.IdmPos{t}:
          idt_num(t)
        case Impl.IdmNeg{m}:
          "-" ++ idt_num(1n+m)

def idt_trace(evs: List<&2, Impl.IdmEv>, +adaptive: Bool, +kept: List<&2, Nat>, +nb: Nat, +st: Spec.IdmPol, +sc: Nat, +i: Nat) -> IO(Unit):
  match evs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +ev <> rest:
      +nx = Impl.idm_event(adaptive, kept, nb, st, ev)
      +rc = Impl.idm_recent(nx)
      do IO<Unit>:
        IO.print("P " ++ idt_num(sc) ++ " " ++ idt_num(i) ++ " " ++ idt_ev(ev) ++ " " ++ idt_bit(Impl.idm_use(nx)) ++ " " ++
          idt_num(Impl.idm_hold(nx)) ++ " " ++ idt_num(List.length(&2, Bool, rc)) ++ " " ++ idt_num(Spec.ids_trues(rc)))
        idt_trace(rest, adaptive, kept, nb, nx, sc, 1n+i)

def idt_first_out.pick(isin: Bool, +b: Nat, next: Nat) -> Nat:
  match isin:
    case True{}:
      next
    case False{}:
      b

# First block >= b that is not kept (fuel bounds the search).
def idt_first_out(fuel: Nat, +kept: List<&2, Nat>, +b: Nat) -> Nat:
  match fuel:
    case 0n:
      b
    case 1n+f:
      idt_first_out.pick(Spec.ids_member(kept, b), b, idt_first_out(f, kept, 1n+b))

def idt_cat(a: List<&2, Impl.IdmEv>, b: List<&2, Impl.IdmEv>) -> List<&2, Impl.IdmEv>:
  List.append(&2, Impl.IdmEv, a, b)

def idt_policy(+nb: Nat) -> IO(Unit):
  +kept = Impl.idm_kept_blocks(Impl.idm_order(), Impl.idm_n_default())
  +V = Nat.mul(nb, 128n)
  +b1 = idt_first_out(nb, kept, 0n)
  +b2 = idt_first_out(nb, kept, 1n+b1)
  +IN = idt_in(5n)
  +O1 = idt_in(Nat.add(Nat.mul(b1, 128n), 7n))
  +O2 = idt_in(Nat.add(Nat.mul(b2, 128n), 3n))
  +R : Impl.IdmEv = Impl.IdmReset{}
  +s0 : List<&2, Impl.IdmEv> = idt_cat(idt_rep(10n, IN), idt_cat([O1, O2], idt_cat(idt_rep(40n, IN), idt_cat([R, IN, O1, IN, IN, IN, O2],
    idt_cat(idt_rep(130n, IN), [R, IN])))))
  +s1 : List<&2, Impl.IdmEv> = [idt_in(V), idt_neg(0n), idt_in(2147483647n), idt_in(1n+V), idt_neg(4n), idt_in(Nat.add(V, 640n)), O1, idt_in(V), O2,
    idt_neg(0n), idt_in(V), O1, R, O1, idt_neg(0n), idt_in(V)]
  +s2 : List<&2, Impl.IdmEv> = idt_cat([O1], idt_cat(idt_rep(30n, IN), idt_cat([O2], idt_cat(idt_rep(128n, IN), idt_cat([O1], idt_cat(idt_rep(31n, IN), [O2, IN]))))))
  +s3 : List<&2, Impl.IdmEv> = [O1, O2, O1, O2, R, O1, IN]
  +s4 : List<&2, Impl.IdmEv> = idt_cat([O1, O2, R, O1, O2], idt_cat(idt_rep(126n, IN), idt_cat([R, O1, IN, O2], idt_cat(idt_rep(127n, IN), [O1, O2]))))
  do IO<Unit>:
    idt_trace(s0, True{}, kept, nb, Impl.idm_init(), 0n, 0n)
    idt_trace(s1, True{}, kept, nb, Impl.idm_init(), 1n, 0n)
    idt_trace(s2, True{}, kept, nb, Impl.idm_init(), 2n, 0n)
    idt_trace(s3, False{}, kept, nb, Impl.idm_init(), 3n, 0n)
    idt_trace(s4, True{}, kept, nb, Impl.idm_init(), 4n, 0n)

# ---- the two checks on fixed block lists ----

def idt_head_row(+c: Nat, +kb: List<&2, Nat>, +vocab: Nat) -> IO(Unit):
  IO.print("H " ++ idt_num(c) ++ " vocab=" ++ idt_num(vocab) ++ " ok=" ++ idt_bit(Impl.idm_head_ok(kb, vocab)) ++ " kb" ++ idt_join(kb))

def idt_kept_row(+c: Nat, +order: List<&2, Nat>, +n: Nat, +vocab: Nat) -> IO(Unit):
  IO.print("R " ++ idt_num(c) ++ " n=" ++ idt_num(n) ++ " vocab=" ++ idt_num(vocab) ++ " ok=" ++ idt_bit(Impl.idm_kept_ok(order, n, vocab)) ++
    " blocks" ++ idt_join(Impl.idm_kept_blocks(order, n)) ++ " order" ++ idt_join(order))

def idt_checks() -> IO(Unit):
  do IO<Unit>:
    idt_head_row(0n, [0n, 1n, 2n], 384n)
    idt_head_row(1n, [0n, 2n, 1n], 384n)
    idt_head_row(2n, [0n, 1n, 1n], 384n)
    idt_head_row(3n, [0n, 3n], 384n)
    idt_head_row(4n, [], 384n)
    idt_head_row(5n, [0n], 200n)
    idt_head_row(6n, [0n], 128n)
    idt_head_row(7n, [1n, 1939n], 248320n)
    idt_kept_row(0n, [2n, 0n, 1n], 3n, 384n)
    idt_kept_row(1n, [2n, 0n, 2n], 3n, 384n)
    idt_kept_row(2n, [2n, 0n, 3n], 3n, 384n)
    idt_kept_row(3n, [2n, 0n], 3n, 384n)
    idt_kept_row(4n, [2n, 0n, 1n], 0n, 384n)
    idt_kept_row(5n, [5n, 1n, 3n, 0n], 3n, 768n)
    idt_kept_row(6n, [5n, 1n, 3n, 0n], 3n, 767n)
    idt_kept_row(7n, [5n, 1n, 3n, 1n], 4n, 768n)
    idt_kept_row(8n, [5n, 1n, 3n, 1n], 3n, 768n)

def main() -> IO(Unit):
  +nb = Nat.div(Impl.idm_vocab(), Impl.idm_block())
  do IO<Unit>:
    IO.print("K vocab=" ++ idt_num(Impl.idm_vocab()) ++ " block=" ++ idt_num(Impl.idm_block()) ++ " n=" ++ idt_num(Impl.idm_n_default()) ++
      " n_alt=" ++ idt_num(Impl.idm_n_alt()) ++ " window=" ++ idt_num(Impl.idm_window()) ++ " trigger=" ++ idt_num(Impl.idm_trigger()) ++
      " hold=" ++ idt_num(Impl.idm_hold_len()) ++ " topk=" ++ idt_num(Impl.idm_topk_k()))
    IO.print("O" ++ idt_join(Impl.idm_order()))
    idt_seed_heads(idt_seeds(), 0n)
    idt_blocks(Impl.idm_n_default(), nb)
    idt_blocks(Impl.idm_n_alt(), nb)
    idt_policy(nb)
    idt_checks()
