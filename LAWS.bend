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
