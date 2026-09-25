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
