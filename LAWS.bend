# Accepted contract root. The EXL3 greedy speculative acceptance laws bind the
# scalar leaf executed by the serving path (bend/exl3_accept.bend, emitted via
# bend/EXL3_ACCEPT.bend) to its independent list reference
# (bend/exl3_accept_spec.bend). Compiler, C glue, ctypes ABI and machine
# arithmetic retain the explicit boundaries stated in those modules.
import Base
import ./bend/exl3_accept_laws.bend as Exl3AcceptLaws
import ./bend/gdn_replay_laws.bend as GdnReplayLaws
# m16 GEMM (patch 2001 v2) work partition and deterministic split-K reduction laws over the Nat
# model bend/gemm_m16_partition.bend and its reference bend/gemm_m16_partition_spec.bend.
import ./bend/gemm_m16_partition_laws.bend as GemmM16PartitionLaws
# Device round advance (DevicePipe advance kernel + count-reading consumers) over the Nat model
# bend/exl3_round.bend, composed with the exl3_accept laws.
import ./bend/exl3_round_laws.bend as Exl3RoundLaws
# Residual add + RMSNorm fusion (ext patch 7001): the fused RES_IN register path and the layer
# handshake (bend/norm_fuse.bend) against the unfused add + RES_NONE norm (bend/norm_fuse_spec.bend).
import ./bend/norm_fuse_laws.bend as NormFuseLaws
# Verify-attention split/combine partition (ext patch 3003, attn_verify.cu): exactly-once causal
# coverage and combine/split agreement over the Nat model bend/attn_split.bend.
import ./bend/attn_split_laws.bend as AttnSplitLaws
# DRAM roofline of one verify round: safetensors-header byte model (bend/roofline.bend) equal to the
# config-shape enumeration (bend/roofline_spec.bend); bandwidth/tokens ceilings and loss ledger over Nat.
import ./bend/roofline_laws.bend as RooflineLaws
# Draft-only int4 head kernel (ext patch 9001): tile partition (every vocab tile computed by exactly
# one warp) and per-tile fixed chunk / scale-group fold order over the Nat model
# bend/draft_head_partition.bend, reusing the m16 finisher law finish_jobs_once.
import ./bend/draft_head_partition_laws.bend as DraftHeadPartitionLaws
# Fused-MLP schedule of ext 8201 (persistent gate+up / finish / down launch): exactly-once coverage,
# counter totals, deadlock-free levels, cp.async ring, v2 split-K order and finish jobs over the
# Nat model bend/mlp_m16_sched.bend (table bend/MLP_M16_SCHED_TABLE.bend).
import ./bend/mlp_m16_sched_laws.bend as MlpM16SchedLaws
# Dense verify-attention partial-buffer bounds (ext patch 3004): every block the 3002 GQA split /
# combine grids store or read lies inside the dense_partial_blocks allocation, which is tight and
# equals the host's fail-closed extent, over the Nat model bend/attn_bounds.bend.
import ./bend/attn_bounds_laws.bend as AttnBoundsLaws
import ./bend/gemm_m16_group_laws.bend as GemmM16GroupLaws
# Fused GDN conv + gated delta rule + gated RMS norm verify kernel (ext patch 5101,
# gdn_conv_rule_norm_kernel) and the per-thread token routine it shares with the commit replay: thread
# maps, exactly-once coverage, conv channel ownership and the conv_sync handshake over the Nat model
# bend/gdn_fast.bend (reference bend/gdn_fast_spec.bend; routine tied to bend/gdn_replay.bend).
import ./bend/gdn_fast_laws.bend as GdnFastLaws
# DFlash2 draft attention mask (exl3 patch 0005): config -> _normalize_window -> GQA split kernel
# window start and mask (bend/draft_mask.bend) against the z-lab reference (bend/draft_mask_spec.bend).
import ./bend/draft_mask_laws.bend as DraftMaskLaws
# Verify attention as shipped by ext patch 3003 (fixed absolute kv chunks, attn_verify.cu): exactly-once
# causal coverage, one store per live chunk, row invariance (a row's tiles, chunks and combine list
# depend only on its absolute position) over the Nat model bend/attn_chunk.bend; supersedes the
# round-relative split modelled by bend/attn_split.bend.
import ./bend/attn_chunk_laws.bend as AttnChunkLaws
# ext 3003 buffers: split stores / combine reads are the row-major cells inside the checked sizes, the
# traps never fire, the host allocation (max of the 3004 dense size and the 3003 size) passes the checks,
# tiles stay inside one page (bend/attn_chunk_bounds.bend).
import ./bend/attn_chunk_bounds_laws.bend as AttnChunkBoundsLaws
# Row-invariant verify-attention partition (ext patch 3005): each query row splits its keys by its
# own absolute position (identically in every speculative round), every key < n is read in exactly
# one launched split, two passes compute every row once, and the row combines its own chunks in
# order, over the Nat model bend/attn_rowinv.bend (extends bend/attn_split.bend).
import ./bend/attn_rowinv_laws.bend as AttnRowinvLaws
# GDN across speculative rounds (ext 0003 verify / 0004 commit replay): committed state, outputs
# and conv window are those of one uninterrupted scan whatever the round cuts; verify-in-round
# equals replay-then-verify at every split point, over bend/gdn_rounds.bend (on bend/gdn_replay.bend).
import ./bend/gdn_rounds_laws.bend as GdnRoundsLaws
# Round-level speculation invariance: with per-row outputs a function of the absolute prefix, any
# two drafters emit the same tokens, the greedy output (bend/spec_inv.bend over the exl3_accept
# reference and the exl3_round advance; reference bend/spec_inv_spec.bend).
import ./bend/spec_inv_laws.bend as SpecInvLaws
# ext 3006 verify attention: strided absolute 64-token tiles, one partial slot per split CTA (bend/attn_stride.bend):
# exactly-once causal coverage, one store per live slot, row invariance, exact combine skip.
import ./bend/attn_stride_laws.bend as AttnStrideLaws
# ext 3006 buffers: stores / reads inside the checked sizes, host allocation fits, tiles in one page and in the table, traps never fire.
import ./bend/attn_stride_bounds_laws.bend as AttnStrideBoundsLaws
# ext 8202 layer tail (o_proj split-K + F0/N norm jobs + 8201 MLP, one launch; bend/tail_m16_sched.bend): phase-0 v2 partition, ring, jobs once, barrier order.
import ./bend/tail_m16_sched_laws.bend as TailM16SchedLaws
# ext 8204 deferred phase-1 publish (8201 MLP and 8202 tail; bend/mlp_m16_defer.bend): same counter events and main loop as 8201, every cnt1 signal after its group's flush, levels, counts and resets unchanged.
import ./bend/mlp_m16_defer_laws.bend as MlpM16DeferLaws
# ext 3007 fused pre-attention kernel (attn_small.cu attn_pre_kernel: deinterleave + head norm/RoPE + quantized cache append; bend/attn_pre.bend):
# head jobs once, q / gate / k halves from the deinterleave sources to rope's destinations exactly once, RoPE pairs equal to rope_kernel's and partitioning,
# K/V chunks tiling the heads and refining quant_cache_paged_kernel (source halves, base, words, page slot).
import ./bend/attn_pre_laws.bend as AttnPreLaws
# ext 5106 b/a GEMV split over k (gdn_conv_rule_norm_kernel KS 1/2, bend/gdn_ba_ksplit.bend): every half2 element of
# every task handled once by one (warp, lane, i); fixed per-task order (lane chain, shfl tree, warps 0..15) independent of S
# and of the other rows; the reduction reads completed partials after the barrier; S > 8 or k > 5120 falls back to KS 0.
# Supersedes gdn_fast's task_exactly_once for the served b/a path (that law still describes the KS 0 fallback).
import ./bend/gdn_ba_ksplit_laws.bend as GdnBaKsplitLaws
# ext 2105 grouped m16g projections (and 8205's schedule generator): slot-weighted split-K partition
# (bend/gemm_m16_wpart.bend): W / start / closed-form owner generic in (w0, w1, nsm, G, total), owner = the
# largest b with start(b) <= x, exactly-once ownership, (w, w) = v2, host guard, contributor slots and
# max_contrib bounds; served GDN / attention bundles at (100, 91): guard holds, max_contrib 7 / 8, launch fits.
import ./bend/gemm_m16_wpart_laws.bend as GemmM16WpartLaws
# ext 8205 slot-weighted 8201 MLP / 8202 tail schedule (bend/m16_wsched.bend over bend/gemm_m16_wpart.bend,
# per-phase weights, both table kinds, under the host guard): every phase's slices partition [0, T) exactly once
# (start 0, contiguous, non-empty, last end T); fc / nc are exactly each group's contributors, slots below nc <= mc;
# counter targets = signalled totals (8 per contributor / finisher warp), waiter passes, wait lists cover the slice
# without duplicates, finish ranks unique, levels stratified, 8204 program order; ring offsets = the phase-start
# tile's slot < PF; every partial slot inside its phase region and, under the host workspace check, below the
# workspace size; equal weights = the 8201 / 8202 tables and tail program; the tail's split boundaries, barriers
# and counter events independent of the token-row count m.
import ./bend/m16_wsched_laws.bend as M16WschedLaws
import ./bend/m16_wsched_tables_laws.bend as M16WschedTablesLaws
# ext 9005c pruned int4 draft head (dflash2_head_blocks.py, Q4DraftHead, dflash2_head.cu epilogue; bend/draft_head_idmap.bend,
# reference bend/draft_head_idmap_spec.bend): the column -> token id map is a bijection on [0, V) whose first 128 N columns are
# exactly the kept blocks' ids, strictly increasing; kept blocks = sorted(order[:N]) and every invalid table is rejected; top-k
# by (value desc, token id asc) does not depend on column order (full call on the permuted copy = identity call, prefix call =
# full ranking restricted to kept ids); the switch-back policy: valid initial state selecting pruned, validity preserved by
# every call, reset() = initial state, exactly FALLBACK_HOLD full rounds, out-of-range anchors not evidence, never pruned
# during a hold.
import ./bend/draft_head_idmap_laws.bend as DraftHeadIdmapLaws
# ext 3010 CUDA prefill attention (pattn_kernel.cuh; bend/pattn_sched.bend): lanes cover each tile key once, every causal (row, key) pair
# attended exactly once in its tile p / 32 and never elsewhere, no key past the row or the chunk, tiles inside one page,
# GQA (kv head, warp, block, row) <-> (q head, position) bijective, QK / PV span flush boundaries.
import ./bend/pattn_sched_laws.bend as PattnSchedLaws
# ext 3011 wide-tile prefill GEMM (hgemm_f16acc_wide.cuh + the sm86 route in hgemm_f16acc.cu; bend/hgemm_wide.bend): grouped raster a bijection
# between block ids and tiles, in-tile stores a bijection onto the 128 x 128 tile, composed: every output element (partial last M-stripe
# included) stored exactly once; per-element fp16 partials / fp32 add order equal to the served f16acc kernel's (the bit-exactness argument);
# A / B cp.async stage writes cover each stage exactly once; the route is the served-shape table (sm86, unbatched, M >= 1024, switch 0/1).
import ./bend/hgemm_wide_laws.bend as HgemmWideLaws
# ext 2106 instruction diet of the decode m16 main loops (8202 tail, 8201 MLP, 2102/2105 m16g; bend/m16_diet.bend
# DIET = true vs bend/m16_diet_spec.bend DIET = false), generic in every segment bound (all 8205b weighted slices),
# KT >= 1, ring override < PF and PF, XR, FOLD, W_STAGE, X_ITER >= 1 with FOLD | 2 XR (served Exl3M16Cfg<1,2> one instance):
# the countdown loop runs v2's iterations exactly (no extra / missing); per iteration the ring and activation byte
# offsets, x-chunk, fold and weight-issue decision / source equal DIET = false's; phase exit cursor and slots and the
# whole 8201 / tail / m16g traces are equal; every ring / ldmatrix offset inside its buffer; every weight tile copied
# exactly once in stream order (no skipped or duplicated issue).
import ./bend/m16_diet_laws.bend as M16DietLaws
# ext 2107 EXL3_M16_DIET mode 2 of the decode m16 kernels (bend/m16_diet2.bend vs bend/m16_diet2_spec.bend; with
# 2106's laws, which give mode 2's loop trace): the byte-permute window extraction equals the funnel-shift / bfe one and
# the windows at bit offsets 0..28 for every word pair; the hoisted per-lane word addresses + ring offset + t * 128 are
# the per-iteration ones; the mode-2 tile step equals mma_tile for every shared-memory content and every iteration of any
# trace; every word read stays in its ring slot and, in every iteration of the 8201 / tail / m16g traces, in the ring;
# EXL3_M16_DIET parses to 0 / 1 / 2 (default 2, else refused), diet(x) keeps 0..2, launchers run instance DIET = mode.
import ./bend/m16_diet2_laws.bend as M16Diet2Laws
# ext 5108 commit-replay input gather (bend/gdn_replay_gather.bend): the batched 16-byte loader stores exactly the k / v
# cells RULE_COMMIT reads (each once, every S <= 16, every v chunk), from the conv_out elements the old loader read, widened
# to the same fp32 bits; EXL3_GDN_REPLAY_GATHER parses 0 / 1 (default 1, else refused).
import ./bend/gdn_replay_gather_laws.bend as GdnReplayGatherLaws
# ext 2113 split-K slot discard (bend/m16_discard.bend vs bend/m16_discard_spec.bend): each m16g / 8201 / tail finish job
# discards exactly the 128-byte lines of its own chunk in the slots it summed (every active i, every line once), every
# element it loads lies in those lines, lines and slots name one job (rows < 16, chunks < 4, contributors < mc, the
# workspaces laid out apart), every cell of such a line is stored again by the next launch's contributors before any
# load, the loads precede the warp barrier and the discard, and every load observes its own launch's store (or its
# slot-0 sum) with discards on or off; EXL3_SPLITK_DISCARD parses 0 / 1 (default 1, else refused), discard(x) keeps 0..1.
import ./bend/m16_discard_laws.bend as M16DiscardLaws
# ext 3012 TREE verify attention (bend/attn_tree.bend, reference bend/attn_tree_spec.bend): for every legal 8-row shape the
# TreeDesc passes the kernel's traps, every row is admitted by exactly one pass of each tail tile, the serving leaf's path extends
# the row's path, and over the pass loop in-round column base + j enters row r once iff j <= depth[r], holding r's depth-j
# ancestor; committed tail-tile columns enter once; T0/T1 cover the round and are its last live tiles; CHAIN is the 3006 kernel.
import ./bend/attn_tree_laws.bend as AttnTreeLaws
# ext 5109 GDN tree verify (bend/gdn_tree.bend): for all 5040 8-row parent arrays the DFS program (<= 14 steps) emits every row once from state history path[r], dot1 buffers alternate per arithmetic step, each row's conv window is its ancestors' raw inputs after the committed window, and every accepted-path commit (row_map replay, src_off conv window) reads exactly the path; CHAIN = ADV 0..7 / identity maps.
import ./bend/gdn_tree_laws.bend as GdnTreeLaws
# 8-row tree verify acceptance (DESIGN.md §3(d), bend/exl3_tree_accept.bend, emitted via
# bend/EXL3_TREE_ACCEPT.bend): the scalar accept_tree / derive leaves equal the list reference
# bend/exl3_tree_accept_spec.bend (derive on every legal parent array); the chain shape is the
# chain leaf with k = 7 and derives CHAIN; the matching path is maximal and every committed row
# extends its predecessor; a round ends early only with eos or at the checkpoint; the reference
# descriptor satisfies §2.2 (paths, masks, leaves, leaf_of, the GDN program by emulation).
import ./bend/exl3_tree_accept_laws.bend as Exl3TreeAcceptLaws
# Tree speculation invariance (bend/spec_inv_tree.bend over the tree acceptance reference and the
# exl3_round advance): under ~rinv with row prefixes along the tree's ancestor paths, one tree
# round commits the greedy continuation and any tree rounds emit a prefix of greedy decoding.
import ./bend/spec_inv_tree_laws.bend as SpecInvTreeLaws
# The host TreeDesc reference (exl3_tree_accept_spec.derive) and the tree-attention reference
# (attn_tree_spec.desc) agree on the fields both read, on every legal parent array.
import ./bend/tree_desc_agree_laws.bend as TreeDescAgreeLaws
# ext 3020 8-warp prefill attention (exllamav3_ext/pattn8_kernel.cuh; bend/pattn8_sched.bend against 3010's model
# bend/pattn_sched.bend): warp w < 8 of pair < 3 runs 3010 warp 2 pair + w / 4 of query block 4 qc + w % 4 (forward,
# injective and onto; every 3010 block lies in a launched 64-row chunk); that warp has 3010's q head, positions, row
# bounds and mask state, computes in exactly 3010's tile iterations 0 .. ntiles - 1 in loop order (the CTA loop runs at
# least that many), keeps the same keys per tile (so every causal (row, key) pair is attended exactly once, in tile
# p / 32); warps past q_len compute and store nothing; the q prologue fills each warp's own rows; K / V tile chunks are
# issued exactly once for 256 (3020) and 192 (3010) threads. The per-warp arithmetic below the warp map is 3010's text
# (bend/pattn8_sched_diff.py), so outputs are bit-identical to 3010.
import ./bend/pattn8_sched_laws.bend as Pattn8SchedLaws
# ext 5112 SiLU-gate product in the prefill up-projection GEMM epilogue (exllamav3_ext/hgemm_act.cu; bend/act_fuse.bend
# against stock hgemm_recon + silu_mul, bend/act_fuse_spec.bend): every fused store (row, 2 c) is act_mul_kernel_h's half2
# index row n + c (N = 2 n, pair-aligned columns, a bijection onto the stock indices) and stores the same half2 operation
# term (same operands, same order, same rounding points) for both act_limit branches; the stock launch covers each index
# once; the fused route runs only with both switches on, sm86, K 5120 x N 17408, M >= 1024, where stock hgemm_recon takes
# the 3011 wide kernel (route and worthwhile() hold). K loop and store map are 3011's text (bend/act_fuse_diff.py).
import ./bend/act_fuse_laws.bend as ActFuseLaws
# ext 5111 GDN prefill conv on the fp32 qkv (modules/gated_delta_net_fn/conv1d.py; bend/gdn_conv_qkv.bend against the
# stock transpose / bf16 cast / split / contiguous path, bend/gdn_conv_qkv_spec.bend): each input read is the qkv element
# the stock transposed copy held at the stock kernel's address; each output (s, d) lands at its q / k / v view element
# (s, j) = view base + s width + j, the three views tile the buffer back to back and each view's layout is a bijection,
# so the store map is a bijection onto the buffer. The conv arithmetic is the stock kernels' text (bend/gdn_conv_qkv_diff.py).
import ./bend/gdn_conv_qkv_laws.bend as GdnConvQkvLaws
# ext 5110g merged 4096-row prefill pieces (generator/job.py; bend/prefill_merge.bend against the 2048-row step,
# bend/prefill_merge_spec.bend; text-only recurrent model, no prompt-cache page hit in the pieces): a merged step is
# exactly two 2048-row steps (ends k + mc and k + 2 mc, no last-page cut), any other step is the 2048-row step, a merge
# needs last_tok <= M4096_MAX_PROMPT (131072) and above it the whole schedule is the 2048-row one, the merged forward's
# rows are the two pieces' rows in order; the 3010 prefill attention row is chunk-independent and the 3011 wide-GEMM route
# is the same at M 2048 and 4096. NOT covered (checkpoint_positions shows it): recurrent checkpoints are stashed only at
# visited positions, and a merged run from a start = mc (mod 2 mc) skips pp-interval checkpoints the 2048 schedule takes.
import ./bend/prefill_merge_laws.bend as PrefillMergeLaws
# ext 3013 tree-verify KV commit (cache/kv_compact.py kv_moves, exllamav3_ext/kv_compact.cu; bend/kv_compact.bend against
# bend/kv_compact_spec.bend): for all 128 legal accepted paths of the 8-row window, the derived moves pass the extension's
# checks, the read-all-then-write kernel equals the sequential ascending copy, and slots 0 .. count - 1 end up holding the
# path rows (what a chain verify of the path writes). Logical slots; phys injective by the distinct-page check.
import ./bend/kv_compact_laws.bend as KvCompactLaws
# The ~rinv link, generic (bend/rowinv_link.bend served-forward model over L layers with opaque
# arithmetic, reference bend/rowinv_link_spec.bend = every position computed as row 0 of a 1-row
# round after the prefill): if every layer's kernel plan depends only on the row's absolute
# position (O_plan / O_head), every layer gathers exactly the row's ancestors in logical order
# (O_gat), the round's paths form a tree (W_last / W_pre / W_rng / W_dep) and the committed state
# is the 1-row rounds' (commit), then every verify row's token is its absolute prefix's token; and
# the engine's commit of a row's path leaves exactly the 1-row rounds' committed state (commit_path).
import ./bend/rowinv_link_laws.bend as RowinvLinkLaws
# The ~rinv link for the served configuration (bend/rowinv_served.bend: chain rounds of 1..8 rows
# and the 5040 legal 8-row trees; plans from the 3006 / m16 / m16g / 8201 / 8205 / 5106 Nat models;
# gathers from the 3012 / 5109 models): every obligation discharged from the per-kernel laws, with
# no hypothesis left on plans: the 3006 split grid S = max(1, SMs // kv_heads) >= 1 (grid_pos), the
# split-K counter barrier sums exactly the group's contributors in ascending order for every
# arrival order and stale workspace (splitk_group), and the head plan (final norm, stock lm_head,
# fused argmax split) is the 1-row plan (served_o_head). The only premise is the host's descriptor
# guard (~hcfg, Served.cfg_ok).
import ./bend/rowinv_served_laws.bend as RowinvServedLaws
# Stock lm_head head plan (bend/lmhead.bend: stock exl3_gemm_gr dispatch, persisted autotune record,
# tensor-core fold schedule, final norm width, fused-greedy argmax split): row r of an m-row call
# (m <= 8) has the 1-row call's element order and head plan (H_lmhead of the ~rinv link).
import ./bend/lmhead_laws.bend as LmHeadLaws
# ~rinv closed for the served engine (bend/rinv_engine.bend, the engine's chain / tree jobs with its
# own commits, 0006 + 3013 + 5109): while a job runs, its committed state is the 1-row rounds' state
# of its committed stream (served_chain_commit / served_tree_commit, so `commit` is proven), every
# round's verify ids are the served forward's, and the output is a prefix of the greedy decode of
# the prompt by ref_row (one token per round, served plans), for every drafter: chains of at most 7
# drafts per round and every list of legal 8-row trees (served_*_job, served_*_greedy_prefix,
# served_chain_spec_invariance). Remaining trust base, outside Bend: deterministic kernels (H_det),
# opaque arithmetic (H_fp), mma.m16n8k16 row-locality (H_mma), row-local norm / argmax and slot code
# (H_slots / H_rowloc), the GPU memory model at the split-K barrier (H_mem), code conformance to the
# models (H_conform, *_diff.py) and deployment facts (H_deploy).
import ./bend/rinv_laws.bend as RinvLaws
# Rounding-error bounds (bend/err_bound.bend): a Path counts the rounding steps from one input
# term to one output by class (fp32 RN, fp32 tensor-core, fp16 RN, fp16 tensor-core, int8
# activation, special functions). For every assignment of per-class bounds in the class order,
# a dominated path has a sum of bounds (sigma) no larger than its dominator; with Higham's
# Lemma 3.1 (error factor sigma / (1 - sigma), increasing) that is a no-larger worst-case
# rounding error bound. Domination composes over path segments, is reflexive and transitive.
import ./bend/nat_order_laws.bend as NatOrderLaws
import ./bend/err_bound_laws.bend as ErrBoundLaws
# Error bounds, norms and elementwise decode ops (bend/err_elem.bend: stock 355c6ee M=1 vs the
# elpis verify path, file:line cited, bend/err_elem_diff.py source and SASS link): every tensor
# between kernels keeps stock's dtype; residual adds round as stock's; the input and final
# RMSNorm paths equal stock's; the layer tail's post-attention RMSNorm is dominated (exchange
# 128) on every leaf; SiLU(gate) * up runs stock's operations in stock's order.
import ./bend/err_elem_laws.bend as ErrElemLaws
# Error bounds, decode Gated DeltaNet (bend/err_gdn.bend: stock 355c6ee M=1 split path vs the
# elpis verify kernel gdn_conv_rule_norm_kernel, file:line cited, bend/err_gdn_diff.py): both
# compute the same exact recurrence with the same operations in the same order (conv, SiLU, l2
# norm, delta rule, gated norm; fp32 state) except the b/a GEMV, which sums the same products
# (a bijection of terms) in fewer steps (at most 30 fp32 steps per term vs stock's 165); every
# elpis route from an input term to an output, across tokens through the state and the conv
# window, is dominated (exchange 128) by a real stock route with the same bf16 / log1pf steps.
import ./bend/err_gdn_laws.bend as ErrGdnLaws
# Error bounds, decode attention (bend/err_attn.bend: stock 355c6ee M=1 Triton paged decode vs
# the elpis verify kernels, file:line cited, bend/err_attn_diff.py): the pre kernel (q / k norm,
# RoPE) has stock's rope_kernel arithmetic on every route; at context 2 both sides share one
# tile, one slot and the denominator. The attention core is NOT dominated by stock's today
# (bend/err_attn_finding_laws.bend, proven counterexample, discharged in PROOF.bend): output
# back-rotation chain, sequential denominator sum, 20-slot combine, P.V chain length.
import ./bend/err_attn_laws.bend as ErrAttnLaws
# Error bounds, prefill (bend/err_prefill.bend: stock 355c6ee Triton prefill attention, conv and
# f16acc GEMM vs elpis 3010 / 3020 / 3022 v4, 5111, 3011 / 5112, file:line cited,
# bend/err_prefill_diff.py): the score segment (QK, scale, exp2) is stock's path; against unsplit
# stock every 3022 v4 P.V leaf of a row seeing 3 or more key tiles is dominated (exchange 128);
# the 5111 GDN conv runs stock's step sequence on both routes; every 3011 / 5112 GEMM product term
# has stock's path. NOT dominated today (bend/err_prefill_finding_laws.bend, proven
# counterexamples, discharged in PROOF.bend): rows seeing 1-2 tiles (denominator depth) and rows
# of block tables >= 8192 keys against stock's 2-way split (ex2 rescale count).
import ./bend/err_prefill_laws.bend as ErrPrefillLaws
# Error bounds, decode GEMMs (bend/err_gemm.bend: stock 355c6ee M=1 dispatch (sliced exl3_mgemm,
# int8 sq GEMV, gdn_ba_gemv, stock lm_head) vs the elpis verify kernels (m16g fold-32, 8201 /
# 8202 tail phases, 5106 b/a k-split), file:line cited, bend/err_gemm_diff.py): for m = 1..8 and
# every leaf, attention q|gate / k / v and GDN qkv / z are dominated (m >= 2; stock's own kernel
# at m = 1), o_proj / out_proj / MLP gate / up / down are dominated by stock's int8-activation
# GEMV, GDN b/a by stock's lane chain, and lm_head has stock's per-row reduction order.
import ./bend/err_gemm_laws.bend as ErrGemmLaws
# The run schedules the GEMM bounds use (bend/err_gemm_runs.bend over the DIET traces of
# bend/m16_diet.bend and the stock partition of bend/precision_stock.bend): every fp16 run of the
# served m16g and tail traces is at most FOLD = 2 k16 tiles (ext 3023 fold-32) for every block
# slice, every tile event sits at run position 1 .. FOLD, and the stock main loop's fp16 runs are
# exactly the column pieces of a block's slice.
import ./bend/err_gemm_runs_laws.bend as ErrGemmRunsLaws
# Error bounds, decode attention with ext 3030 (bend/err_attn_dec.bend, model of the fixed
# attn_verify kernels; stock side bend/err_attn.bend; bend/err_attn_dec_diff.py source, SASS-count
# and replay links): for every context length L >= 1, every live key and every route kind (q, K,
# V, the tile coefficient, the gate), the elpis path is dominated (exchange 128) by stock M=1
# decode's path of the same kind, with the coefficients' own ex2 / FADD steps counted kind by kind.
# 3030: integer running max (exact power-of-two rescales), per-tile p sums by a balanced tree,
# per-tile fresh fp32 P.V accumulators joined by one fma, a pairwise combine tree, and stock's
# two-step tensor-core output rotation.
import ./bend/err_attn_dec_laws.bend as ErrAttnDecLaws
# Error bounds, prefill attention with ext 3031 (bend/err_pfix.bend, model of the fixed pattn /
# pattn8 kernels; stock side bend/err_prefill.bend): for every 64-row block, every row and every
# stock split count 1..8, every elpis composite (any numerator and denominator tile, either k16
# half, any score steps) is dominated (exchange 128) by stock's tile-0 composite, which is a real
# stock leaf; the chain plan is the same in every chunking that starts at a multiple of 64.
# 3031: per-thread balanced-tree denominators (depth 5, as stock's tl.sum) and online-softmax
# chains of E = (q_abs64 + 256) / 256 tiles, never longer than a stock split, combined with
# stock's weights.
import ./bend/err_pfix_laws.bend as ErrPfixLaws
