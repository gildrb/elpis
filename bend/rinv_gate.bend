# Proof-only gate for the closed ~rinv: the served engine's job (rinv_engine.bend) is spec_inv's /
# spec_inv_tree's job for the 1-row-round reference row function, so speculation adds zero error
# (rinv_laws.bend). rinv_proof.bend imports the proof module of every law it uses (the served link
# rowinv_served_proof / rowinv_link_proof, spec_inv_proof, spec_inv_tree_proof and the EXL3 acceptance /
# round / tree proofs), so this file prints ALL PROOFS CHECK only when the whole chain is proven.
# No main, no foreign code, no axioms.
import Base
import ./rinv_proof.bend as RinvProof
