# Proof-only gate for the decode / verify attention error-bound laws after ext 3030
# (bend/err_attn_dec_laws.bend, proofs bend/err_attn_dec_proof.bend over the model
# bend/err_attn_dec.bend and the stock model of bend/err_attn.bend). Prints ALL PROOFS CHECK only when
# every law is discharged. No main, no foreign code, no axioms.
import Base
import ./err_attn_dec_proof.bend as ErrAttnDecProof
