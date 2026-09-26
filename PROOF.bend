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
import ./bend/attn_rowinv_proof.bend as AttnRowinvProof
import ./bend/gdn_rounds_proof.bend as GdnRoundsProof
import ./bend/spec_inv_proof.bend as SpecInvProof
import ./bend/attn_stride_proof.bend as AttnStrideProof
import ./bend/attn_stride_bounds_proof.bend as AttnStrideBoundsProof
import ./bend/tail_m16_sched_proof.bend as TailM16SchedProof
import ./bend/mlp_m16_defer_proof.bend as MlpM16DeferProof
import ./bend/attn_pre_proof.bend as AttnPreProof
import ./bend/gdn_ba_ksplit_proof.bend as GdnBaKsplitProof
import ./bend/gemm_m16_wpart_proof.bend as GemmM16WpartProof
import ./bend/m16_wsched_tables_proof.bend as M16WschedTablesProof
import ./bend/m16_wsched_proof.bend as M16WschedProof
import ./bend/draft_head_idmap_proof.bend as DraftHeadIdmapProof
import ./bend/pattn_sched_proof.bend as PattnSchedProof
import ./bend/hgemm_wide_proof.bend as HgemmWideProof
import ./bend/m16_diet_proof.bend as M16DietProof
import ./bend/m16_diet2_proof.bend as M16Diet2Proof
