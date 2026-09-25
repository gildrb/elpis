# Proof-only entry point: no main, no foreign proof code and no axioms.
# Discharges every law reachable from LAWS.bend.
import Base
import ./LAWS.bend as Laws
import ./bend/exl3_accept_proof.bend as Exl3AcceptProof
import ./bend/gdn_replay_proof.bend as GdnReplayProof
import ./bend/gemm_m16_partition_proof.bend as GemmM16PartitionProof
import ./bend/exl3_round_proof.bend as Exl3RoundProof
import ./bend/norm_fuse_proof.bend as NormFuseProof
import ./bend/attn_split_proof.bend as AttnSplitProof
import ./bend/roofline_proof.bend as RooflineProof
import ./bend/draft_head_partition_proof.bend as DraftHeadPartitionProof
import ./bend/mlp_m16_sched_proof.bend as MlpM16SchedProof
import ./bend/attn_bounds_proof.bend as AttnBoundsProof
import ./bend/gemm_m16_group_proof.bend as GemmM16GroupProof
import ./bend/gdn_fast_proof.bend as GdnFastProof
import ./bend/draft_mask_proof.bend as DraftMaskProof
import ./bend/attn_chunk_proof.bend as AttnChunkProof
import ./bend/attn_chunk_bounds_proof.bend as AttnChunkBoundsProof
