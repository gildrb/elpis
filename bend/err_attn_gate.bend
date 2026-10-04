# Proof-only gate for the decode-attention error-bound laws: the contract laws
# (bend/err_attn_laws.bend, proofs bend/err_attn_proof.bend) and the current kernel's finding
# (bend/err_attn_finding_laws.bend, proofs bend/err_attn_finding_proof.bend), both over the model
# bend/err_attn.bend. Prints ALL PROOFS CHECK only when every law is discharged. No main, no foreign
# code, no axioms.
import Base
import ./err_attn_proof.bend as ErrAttnProof
import ./err_attn_finding_proof.bend as ErrAttnFindingProof
