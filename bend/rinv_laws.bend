# Speculation adds zero error for the served engine: over the engine job model rinv_engine.bend
# (served verify forward rowinv_link.tokens with the served plans of rowinv_served.bend, EXL3
# acceptance, exl3_round advance, and the engine's own commit rowinv_link.commit carried from round to
# round), every round's verify ids are spec_inv's / spec_inv_tree's for the row function ref_row
# below, so the engine's job IS spec_inv's job (and spec_inv_tree's) for ref_row; ref_row ignores the
# row index, so ~rinv holds by reflexivity, and spec_inv_laws / spec_inv_tree_laws give the greedy
# decode of the engine's own target arithmetic. The hypothesis `commit` of rowinv_link_laws.compose
# (the committed state at a round start is what 1-row rounds over the committed decode stream leave)
# is not assumed: it is proven by induction over the rounds (laws served_chain_commit /
# served_tree_commit), from the prefill state pf(first n0 prompt tokens) and
# rowinv_served_laws.served_commit at every round.
#
# ref_row(p, r): the token of the absolute prefix p computed as row 0 of a 1-row round at every decode
# position, with the engine's arithmetic (rowinv_link_spec.ref_prefix: the first n0 tokens prefilled
# by pf, the rest decoded one per 1-row round with the served plans / head plans). It is the greedy
# decode of the engine's own target arithmetic: rowinv_link_spec.bend, rowinv_served.bend.
#
# Domain of every law: every opaque arithmetic V, E, C, z, emb, F, ent, adv, head (the model's only
# floating-point assumption is that each is a function, H_det / H_fp below), every configuration cfg
# the host admits (~hcfg: Served.cfg_ok), every split-K arrival order arr and workspace content wsi
# (the scheduler / stale slots: any functions), every prefill function pf and prefill length n0, every
# prompt of n0 + 1 tokens (the anchor of the first round is the last prompt token), every stop list,
# output budget, checkpoint base and interval, initial anchor index and checkpoint input, and every
# drafter: any list of draft lists of <= 7 tokens (chain rounds) or of legal 8-row trees with any
# tokens (tree rounds), including adaptive and adversarial ones.
#
# Remaining hypotheses (none is a Bend premise of the laws below; each is the reading of the opaque
# functions emb / F / ent / adv / head, of the plans, or of the models; detailed with source lines in
# rowinv_served_laws.bend and lmhead.bend):
#   H_det      every GPU kernel computes its result as a deterministic function of its plan and its
#              operands (same instruction sequence and operands, same bits, whichever block, warp, MMA
#              row slot or launch runs it): the opaque emb / F / ent / adv / head are functions.
#   H_fp       the floating-point arithmetic itself is opaque (no IEEE property is used); masked tiles,
#              non-admitting passes and identity merges are exact no-ops (alpha = 1, p = 0,
#              mma(c, 0 * finite) == c), and GDN ADV / REPLAY / PEEK share one arithmetic body (SASS
#              diff gate): the plan captures every m- or row-dependent choice.
#   H_mma      mma.m16n8k16 computes output row r from operand row r (and the B / C operands) only, in
#              an order independent of r and of the other rows' contents, including stale / NaN rows
#              past size_m (hardware, undocumented; lmhead.bend header). With H_slots (Hadamard warps
#              and accumulator slots run identical code per chunk / slot) and H_rowloc (final norm and
#              fused argmax read only their row; argmax = lowest index of the row maximum) this is the
#              head's row locality.
#   H_mem      the GPU memory model at the split-K barrier: a contributor's slot stores made before its
#              __threadfence + counter atomicAdd (or grid.sync) are visible to the finisher's slot loads
#              issued after its acquire poll observes the counter at the target 8 * nc (or after
#              grid.sync); counters are 0 at every launch start (self-reset, stream-ordered launches).
#              So the finisher sums exactly the contributors' partials (rowinv_served_laws header).
#   H_conform  every shipped kernel and host path conforms to its Bend model (the transcriptions and
#              their *_diff.py source links): the served forward is rowinv_link.tokens with
#              rowinv_served's plans, head plans and gathers; the acceptance is the EXL3 leaves (proven
#              equal to the references); the device advance is exl3_round.advance; the commit is
#              rowinv_link.commit over the rows rinv_engine names (0006-tree-verify.patch: chain replay
#              of exl3_round.steps rows, tree replay / kv_compact of the accepted path); the host
#              launches a split-K descriptor only when it passes Served.gdesc_ok; and the prefill state
#              is pf(first n0 prompt tokens), the engine's own prefill of those tokens, after which the
#              first verify round runs at device position n0 with the last prompt token as anchor
#              (|prompt| = n0 + 1, premise hlen).
#   deployment (H_deploy) the persisted lm_head autotune records are present and loaded and the
#              environment is default (lmhead.bend header); the host admits only cfg_ok configurations
#              (~hcfg), drafts of <= 7 tokens (premise small) and legal trees (premise legal); one
#              sequence per job.
import Base
import ./rinv_engine.bend as Eng
import ./rowinv_link_spec.bend as LSpec
import ./rowinv_served.bend as Served
import ./gemm_m16_partition_spec.bend as PSpec
import ./spec_inv.bend as SIC
import ./spec_inv_spec.bend as SIS
import ./spec_inv_tree.bend as SIT
import ./exl3_round.bend as Round

# The reference row function: the 1-row-round token of the whole prefix p (the row index is unused).
def ref_row(~V: Data, ~E: Data, ~C: Data, ~z: V, ~emb: U32 -> V, ~F: Nat -> Served.Plan -> C -> V -> V,
    ~ent: Nat -> Served.Plan -> V -> E, ~adv: Nat -> C -> E -> C, ~head: Served.Plan -> V -> U32, ~cfg: Served.Cfg,
    ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, ~pf: List<&2, U32> -> List<&2, C>,
    ~n0: Nat, p: List<&2, U32>, r: Nat) -> U32:
  LSpec.ref_prefix(~V, ~E, ~C, ~Served.Plan, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~Served.plan(~cfg, ~arr, ~wsi),
    ~Served.hplan(~cfg, ~arr, ~wsi), ~pf, ~n0, p)

# E1 (headline, chain): the served engine's chain job is spec_inv's job for ref_row at position n0:
# same device state and the same emitted tokens after any rounds, i.e. every round's verify ids (the
# served forward's, from the committed state the engine's own commits left) are spec_inv's targets.
law served_chain_job:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +drafts: List<&2, List<&2, U32>>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for small: {Eng.all_small(drafts) == True{} : Bool}
  {Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, drafts, budget, anchor, checkpoint)) ==
    SIC.job(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      drafts, n0, budget, anchor, checkpoint) : SIC.Run} &
  {Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, drafts, budget, anchor, checkpoint)) ==
    SIC.out(SIC.job(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase,
      interval, drafts, n0, budget, anchor, checkpoint)) : List<&2, U32>}

# E2 (`commit` closed, chain): after any rounds, a job that still runs sits at device position
# n0 + |out| and its committed state is the 1-row-rounds state of its committed decode stream (the last
# prompt token followed by the emitted tokens, without the last one, which is the next anchor), from the
# prefill state of the first n0 prompt tokens: rowinv_link_laws.compose's hypothesis `commit` holds at
# every round start.
law served_chain_commit:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +drafts: List<&2, List<&2, U32>>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for small: {Eng.all_small(drafts) == True{} : Bool}
  for running: {SIC.stopped(Eng.run(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt,
    stops, cbase, interval, drafts, budget, anchor, checkpoint))) == False{} : Bool}
  {Eng.cs(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint)) ==
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
      n0, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent,
        ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval, drafts, budget, anchor, checkpoint))), n0),
        List.length(&2, U32, Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt,
          stops, cbase, interval, drafts, budget, anchor, checkpoint))))) : List<&2, C>} &
  {Eng.position(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, drafts, budget, anchor, checkpoint)) ==
    Nat.add(n0, List.length(&2, U32, Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0,
      prompt, stops, cbase, interval, drafts, budget, anchor, checkpoint)))) : Nat}

# E3 (spec_inv_laws.prefix_of_greedy, ~rinv by reflexivity): with a positive budget, the engine's
# emitted tokens after any chain rounds are a prefix of the greedy decode of the prompt by ref_row.
law served_chain_greedy_prefix:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +drafts: List<&2, List<&2, U32>>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for small: {Eng.all_small(drafts) == True{} : Bool}
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  {List.take(&2, U32, SIS.greedy(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), budget, stops, prompt),
      List.length(&2, U32, Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops,
        cbase, interval, drafts, budget, anchor, checkpoint)))) ==
    Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts, budget, anchor, checkpoint)) : List<&2, U32>}

# E4 (spec_inv_laws.speculation_invariance, ~rinv by reflexivity): any two drafters given at least
# `budget` rounds both finish and the engine emits the same tokens for both: the greedy decode of the
# prompt by ref_row under the same budget and stop set.
law served_chain_spec_invariance:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +drafts1: List<&2, List<&2, U32>>
  for +drafts2: List<&2, List<&2, U32>>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for +small1: {Eng.all_small(drafts1) == True{} : Bool}
  for small2: {Eng.all_small(drafts2) == True{} : Bool}
  for +positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for +enough1: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts1)) == True{} : Bool}
  for +enough2: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts2)) == True{} : Bool}
  {Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts1, budget, anchor, checkpoint)) ==
    SIS.greedy(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), budget, stops, prompt) : List<&2, U32>} &
  {Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts1, budget, anchor, checkpoint)) ==
    Eng.out(~C, Eng.chain_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      drafts2, budget, anchor, checkpoint)) : List<&2, U32>}

# E5 (headline, trees): the served engine's tree job (legal 8-row trees, any tokens) is
# spec_inv_tree's job for ref_row at position n0: same device state and emitted tokens.
law served_tree_job:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +trees: List<&2, SIT.Draft>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for legal: {SIT.all_legal(trees) == True{} : Bool}
  {Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, trees, budget, anchor, checkpoint)) ==
    SIT.job(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase, interval,
      trees, n0, budget, anchor, checkpoint) : SIC.Run} &
  {Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, trees, budget, anchor, checkpoint)) ==
    SIC.out(SIT.job(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), prompt, stops, cbase,
      interval, trees, n0, budget, anchor, checkpoint)) : List<&2, U32>}

# E6 (`commit` closed, trees): as E2 for tree rounds (the commit of the accepted path rows).
law served_tree_commit:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +trees: List<&2, SIT.Draft>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for legal: {SIT.all_legal(trees) == True{} : Bool}
  for running: {SIC.stopped(Eng.run(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt,
    stops, cbase, interval, trees, budget, anchor, checkpoint))) == False{} : Bool}
  {Eng.cs(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      trees, budget, anchor, checkpoint)) ==
    LSpec.committed(~V, ~E, ~C, ~Served.Plan, ~emb, ~F, ~ent, ~adv, ~Served.plan(~cfg, ~arr, ~wsi), pf(List.take(&2, U32, prompt, n0)),
      n0, List.take(&2, U32, List.drop(&2, U32, List.append(&2, U32, prompt, Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent,
        ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval, trees, budget, anchor, checkpoint))), n0),
        List.length(&2, U32, Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt,
          stops, cbase, interval, trees, budget, anchor, checkpoint))))) : List<&2, C>} &
  {Eng.position(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase,
      interval, trees, budget, anchor, checkpoint)) ==
    Nat.add(n0, List.length(&2, U32, Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0,
      prompt, stops, cbase, interval, trees, budget, anchor, checkpoint)))) : Nat}

# E7 (spec_inv_tree_laws.tree_prefix_of_greedy, ~rinv by reflexivity): with a positive budget, the
# engine's emitted tokens after any legal tree rounds are a prefix of the greedy decode by ref_row.
law served_tree_greedy_prefix:
  for ~V: Data
  for ~E: Data
  for ~C: Data
  for ~z: V
  for ~emb: U32 -> V
  for ~F: Nat -> Served.Plan -> C -> V -> V
  for ~ent: Nat -> Served.Plan -> V -> E
  for ~adv: Nat -> C -> E -> C
  for ~head: Served.Plan -> V -> U32
  for ~cfg: Served.Cfg
  for ~arr: Nat -> Nat -> Nat -> List<&2, Nat>
  for ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>
  for ~hcfg: {Served.cfg_ok(cfg) == True{} : Bool}
  for ~pf: List<&2, U32> -> List<&2, C>
  for ~n0: Nat
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +cbase: Nat
  for +interval: Nat
  for +trees: List<&2, SIT.Draft>
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for hlen: {List.length(&2, U32, prompt) == 1n+n0 : Nat}
  for +legal: {SIT.all_legal(trees) == True{} : Bool}
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  {List.take(&2, U32, SIS.greedy(~ref_row(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, ~n0), budget, stops, prompt),
      List.length(&2, U32, Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops,
        cbase, interval, trees, budget, anchor, checkpoint)))) ==
    Eng.out(~C, Eng.tree_job(~V, ~E, ~C, ~z, ~emb, ~F, ~ent, ~adv, ~head, ~cfg, ~arr, ~wsi, ~pf, n0, prompt, stops, cbase, interval,
      trees, budget, anchor, checkpoint)) : List<&2, U32>}
