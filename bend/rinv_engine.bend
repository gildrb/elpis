# Engine-level model of one served speculative job (laws: rinv_laws.bend; proofs: rinv_proof.bend):
# the device round state and emitted ids of spec_inv.bend / spec_inv_tree.bend, plus the engine's
# committed state of every layer (rowinv_link.bend's cs), carried from round to round. Every round
# verifies its rows with the served forward (rowinv_link.tokens with the served plans of
# rowinv_served.bend), decides with the EXL3 acceptance reference, advances the device state with
# exl3_round.advance, emits the committed verify ids, and commits the accepted rows into cs with
# rowinv_link.commit. Nothing here assumes ~rinv: the verify ids are what the served forward computes
# from the committed state the previous rounds left.
#
# Source links (patches/exl3/0006-tree-verify.patch, the patched generator's round loop):
#   - chain rounds (:217-231): greedy_accept on the verify ids, then the GDN commit replays
#     window + 1 - num_rejected rows, num_rejected = window + 1 - count if not eos and count <= window
#     else 0, i.e. exl3_round.steps(count, eos, window) rows (gdn.cu:2830, the same formula on the
#     device path). Attention layers: the verify already wrote every row's K/V at base + r and the
#     committed length moves by count (exl3_round.advance).
#   - tree rounds (:195-216, :235-245): accept_tree, tree_path = accepted_path(rnd, count, last)
#     = rnd.paths[last] with len == count (:436-441); the GDN commit replays row_map(tree_path) and
#     ext 3013 (kv_compact) moves the path rows' K/V to base + depth. The rows committed are P[0..count)
#     of the matching path P (exl3_tree_accept_laws.committed_rows: last = P[count - 1]); rinv_proof
#     shows P[0..count) == rowinv_served.pth(tree_shape, last) == rnd.paths[last], so the host check
#     never fires on a legal tree. kv_compact_laws.commit_moves: slots 0 .. count - 1 then hold
#     P[0] .. P[count - 1]; gdn_tree_laws.tree_all_shapes: the replay under row_map reads exactly the
#     rows of the history path[last].
#   - every commit is guarded like the device's (exl3_round.writes, device_round.cu:110,
#     gdn.cu:2824-2832): only a running job with a usable decision (1 <= count <= window + 1) commits.
#
# eos rounds: on a chain round that reports eos the GDN replay applies window + 1 rows (steps), not
# count; the model commits exactly those rows. Such a round stops the job
# (exl3_round_laws.advance_eos_stops), and a stopped job emits nothing and keeps its device state
# (RoundSpec.committed(.., True) = [], exl3_round.advance leaves a stopped state as is), so the
# committed state after an eos round is never read by anything this model or its laws observe. Tree
# rounds replay P[0..count) also on eos (0006:209-216).
#
# The prefill: the first n0 = |prompt| - 1 prompt tokens are prefilled (pf gives the committed
# state of every layer the prefill leaves, a template: H_conform in rinv_laws.bend), the job starts at
# device position n0 and the first round's anchor is the last prompt token; afterwards the anchor is
# the last committed token (exl3_round_laws.advance_anchor). This is a proof model (lists), not a
# shipped artifact.
import Base
import ./rowinv_link.bend as Link
import ./rowinv_served.bend as Served
import ./gemm_m16_partition_spec.bend as PSpec
import ./spec_inv.bend as SIC
import ./spec_inv_tree.bend as SIT
import ./exl3_accept_spec.bend as Accept
import ./exl3_tree_accept_spec.bend as Tree
import ./exl3_round.bend as Round
import ./exl3_round_spec.bend as RoundSpec

# The job: device round state and emitted ids (spec_inv's Run) and the committed state of every layer.
type Eng<-C: Data> is Data:
  Eng{run: SIC.Run, cs: List<&2, C>}

def run(~C: Data, e: Eng<C>) -> SIC.Run:
  match e:
    case Eng{r, c}:
      r

def cs(~C: Data, e: Eng<C>) -> List<&2, C>:
  match e:
    case Eng{r, c}:
      c

def out(~C: Data, e: Eng<C>) -> List<&2, U32>:
  SIC.out(run(~C, e))

def position(~C: Data, e: Eng<C>) -> Nat:
  match e:
    case Eng{r, c}:
      match r:
        case SIC.Run{st, o}:
          Round.position(st)

# The last token of a sequence (0 for the empty one): the anchor of the next round.
def last_tok.go(xs: List<&2, U32>, p: U32) -> U32:
  match xs:
    case Nil{}:
      p
    case y <> rest:
      last_tok.go(rest, y)

def last_tok(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> rest:
      last_tok.go(rest, x)

# The commit guard: the job was running and the decision is usable.
def live(stopped: Bool, +count: Nat, +window: Nat) -> Bool:
  match stopped:
    case True{}:
      False{}
    case False{}:
      Round.writes(count, window)

def keep(~C: Data, b: Bool, x: List<&2, C>, y: List<&2, C>) -> List<&2, C>:
  match b:
    case True{}:
      x
    case False{}:
      y

# Every round drafts at most 7 tokens (8 verify rows; DFlash2 window <= 7).
def all_small(drafts: List<&2, List<&2, U32>>) -> Bool:
  match drafts:
    case Nil{}:
      True{}
    case ds <> rest:
      Bool.and(Nat.is_le(List.length(&2, U32, ds), 7n), all_small(rest))

# ---------------------------------------------------------------- chain rounds

# A chain round once its verify ids ts are known (rows toks = anchor <> ds, device state st, emitted
# ids o, committed state cs): acceptance, advance and emitted ids exactly as spec_inv.round, and the
# commit of the replayed rows 0 .. steps - 1 when the job runs and the decision is usable.
def chain_after(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +stops: List<&2, U32>,
    +cbase: Nat, +interval: Nat, +ds: List<&2, U32>, +toks: List<&2, U32>, +ts: List<&2, U32>, +st: Round.State,
    +o: List<&2, U32>, +cs: List<&2, C>) -> Eng<C>:
  +v = Accept.accept(ts, ds, stops, Round.budget(st), Round.checkpoint_of(st))
  +w = List.length(&2, U32, ds)
  Eng{SIC.Run{Round.advance(Accept.count(v), Accept.eos(v), w, cbase, interval, st),
      List.append(&2, U32, o, RoundSpec.committed(ts, Accept.count(v), Round.stopped(st)))},
    keep(~C, live(Round.stopped(st), Accept.count(v), w),
      Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth,
        ~Served.gat, cs, 0n, Served.pth(Served.Chain{}, Nat.sub(Round.steps(Accept.count(v), Accept.eos(v), w), 1n)),
        Served.Chain{}, Round.position(st), List.length(&2, U32, toks), Link.embs(~V, ~emb, toks)),
      cs)}

# One chain round: rows anchor <> ds at the device position, verified by the served forward.
def chain_round(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +prompt: List<&2, U32>,
    +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +ds: List<&2, U32>, e: Eng<C>) -> Eng<C>:
  match e:
    case Eng{SIC.Run{+st, +o}, +cs}:
      +toks = {last_tok(List.append(&2, U32, prompt, o)) <> ds : List<&2, U32>}
      chain_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, ds, toks,
        Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
          ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, Round.position(st), toks, Served.Chain{}),
        st, o, cs)

def chain_run(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +prompt: List<&2, U32>,
    +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, drafts: List<&2, List<&2, U32>>, e: Eng<C>) -> Eng<C>:
  match drafts:
    case Nil{}:
      e
    case +ds <> rest:
      chain_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, rest,
        chain_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, ds, e))

# The job: prefill state of the first n0 prompt tokens, device position n0, nothing emitted; then the
# chain rounds (one draft list per round).
def chain_job(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    +n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    drafts: List<&2, List<&2, U32>>, +budget: Nat, +anchor: Nat, +checkpoint: Nat) -> Eng<C>:
  chain_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, drafts,
    Eng{SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}}, pf(List.take(&2, U32, prompt, n0))})

# ---------------------------------------------------------------- tree rounds

# A tree round once its verify ids vs are known (rows toks = tree_toks(anchor, t)): acceptance,
# advance (window 7) and emitted ids exactly as spec_inv_tree.round, and the commit of the accepted
# path rows P[0..count) (P = the matching path) when the job runs and the decision is usable.
def tree_after(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +stops: List<&2, U32>,
    +cbase: Nat, +interval: Nat, +t: SIT.Draft, +toks: List<&2, U32>, +vs: List<&2, U32>, +st: Round.State,
    +o: List<&2, U32>, +cs: List<&2, C>) -> Eng<C>:
  +ns = SIT.nodes(t)
  +v = Tree.accept_tree(ns, vs, stops, Round.budget(st), Round.checkpoint_of(st))
  Eng{SIC.Run{Round.advance(Tree.count(v), Tree.eos(v), 7n, cbase, interval, st),
      List.append(&2, U32, o, RoundSpec.committed(SIT.path_ids(vs, ns), Tree.count(v), Round.stopped(st)))},
    keep(~C, live(Round.stopped(st), Tree.count(v), 7n),
      Link.commit(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), ~Served.pth,
        ~Served.gat, cs, 0n, List.take(&2, Nat, Tree.path(ns, vs), Tree.count(v)), Served.tree_shape(t),
        Round.position(st), List.length(&2, U32, toks), Link.embs(~V, ~emb, toks)),
      cs)}

# One tree round: rows anchor, x1 .. x7 of the drafted tree at the device position.
def tree_round(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +prompt: List<&2, U32>,
    +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, +t: SIT.Draft, e: Eng<C>) -> Eng<C>:
  match e:
    case Eng{SIC.Run{+st, +o}, +cs}:
      +toks = Served.tree_toks(last_tok(List.append(&2, U32, prompt, o)), t)
      tree_after(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~cfg, ~arr, ~wsi, stops, cbase, interval, t, toks,
        Link.tokens(~V, ~E, ~C, ~Served.Plan, ~Served.Shape, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
          ~Served.hplan(~cfg, ~arr, ~wsi), ~Served.pth, ~Served.gat, cs, Round.position(st), toks, Served.tree_shape(t)),
        st, o, cs)

def tree_run(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +prompt: List<&2, U32>,
    +stops: List<&2, U32>, +cbase: Nat, +interval: Nat, trees: List<&2, SIT.Draft>, e: Eng<C>) -> Eng<C>:
  match trees:
    case Nil{}:
      e
    case +t <> rest:
      tree_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, rest,
        tree_round(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, t, e))

def tree_job(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    +n0: Nat, +prompt: List<&2, U32>, +stops: List<&2, U32>, +cbase: Nat, +interval: Nat,
    trees: List<&2, SIT.Draft>, +budget: Nat, +anchor: Nat, +checkpoint: Nat) -> Eng<C>:
  tree_run(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, prompt, stops, cbase, interval, trees,
    Eng{SIC.Run{Round.State{n0, budget, anchor, checkpoint, False{}}, Nil{}}, pf(List.take(&2, U32, prompt, n0))})
