# Proof gate of the decode-GEMM precision law (draft): every law of bend/precision_laws.bend, discharged
# by bend/precision_proof.bend, which imports the proof modules of the schedule laws it uses
# (gemm_m16_partition, m16_diet, exl3_round). No main, no foreign proof code and no axioms.
# Check: bend bend/precision_gate.bend (prints ALL PROOFS CHECK). LAWS.bend is unchanged; the proposed
# LAWS.bend lines are in the PrecisionLaw report.
import Base
import ./precision_laws.bend as Laws
import ./precision_proof.bend as Proof
