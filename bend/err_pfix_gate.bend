# Proof-only gate for the ext 3031 prefill attention error-bound laws (bend/err_pfix_laws.bend, the contract) and
# everything they rest on: the chain-geometry facts (err_pfix_geom_proof.bend), the division laws
# (gemm_m16_partition_proof.bend) and the Nat order laws (nat_order_proof.bend). Prints ALL PROOFS CHECK only when every
# law is discharged. No main, no foreign code, no axioms.
import Base
import ./nat_order_proof.bend as NatOrderProof
import ./gemm_m16_partition_proof.bend as GemmM16PartitionProof
import ./err_pfix_geom_proof.bend as ErrPfixGeomProof
import ./err_pfix_proof.bend as ErrPfixProof
