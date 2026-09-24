# Proof-only entry point: no main, no foreign proof code and no axioms.
# Discharges every law reachable from LAWS.bend.
import Base
import ./LAWS.bend as Laws
import ./bend/exl3_accept_proof.bend as Exl3AcceptProof
import ./bend/gdn_replay_proof.bend as GdnReplayProof
import ./bend/gemm_m16_partition_proof.bend as GemmM16PartitionProof
import ./bend/exl3_round_proof.bend as Exl3RoundProof
import ./bend/norm_fuse_proof.bend as NormFuseProof
