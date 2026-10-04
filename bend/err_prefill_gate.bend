# Proof-only gate for the prefill error-bound laws (bend/err_prefill_laws.bend, the contract) and the finding
# (bend/err_prefill_finding_laws.bend: refutations for ext 3022 v4 prefill attention), and everything they rest on:
# the error-bound core laws (err_bound_proof.bend), the Nat order laws (nat_order_proof.bend) and the 3011
# wide-GEMM laws (hgemm_wide_proof.bend, for k_order). Prints ALL PROOFS CHECK only when every law is discharged.
# No main, no foreign code, no axioms.
import Base
import ./nat_order_proof.bend as NatOrderProof
import ./err_bound_proof.bend as ErrBoundProof
import ./hgemm_wide_proof.bend as HgemmWideProof
import ./err_prefill_proof.bend as ErrPrefillProof
import ./err_prefill_finding_proof.bend as ErrPrefillFindingProof
