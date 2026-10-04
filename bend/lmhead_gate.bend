# Proof gate of the lm_head head-plan laws: every law of bend/lmhead_laws.bend, discharged by
# bend/lmhead_proof.bend. No main, no foreign proof code and no axioms.
# Check: bend bend/lmhead_gate.bend (prints ALL PROOFS CHECK). LAWS.bend is unchanged; the proposed
# LAWS.bend lines are in /tmp/kernel-work/LmHead/LAWS-proposal.md.
import Base
import ./lmhead_laws.bend as Laws
import ./lmhead_proof.bend as Proof
