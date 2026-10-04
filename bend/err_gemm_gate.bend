# Proof gate of the decode-GEMM error-bound laws: every law of bend/err_gemm_laws.bend, discharged by
# bend/err_gemm_proof.bend (which imports the proof modules of err_bound, nat_order and lmhead).
# Check: bend bend/err_gemm_gate.bend --verdict (prints ALL PROOFS CHECK).
import Base
import ./err_gemm_laws.bend as Laws
import ./err_gemm_proof.bend as Proof
