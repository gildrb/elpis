# Proof-only gate for the ~rinv link (PROOF-style; the repo gate PROOF.bend imports the same two
# proof modules): the generic composition (rowinv_link_proof: per-layer obligations compose into
# ~rinv) and its served instance (rowinv_served_proof: the obligations discharged from the existing
# per-kernel laws, the adapters to spec_inv / spec_inv_tree). Each proof module imports the proof
# modules of every law it uses (a law without its proof in scope is refused), so this file prints
# ALL PROOFS CHECK only when the whole chain is proven. No main, no foreign code, no axioms.
import Base
import ./rowinv_link_proof.bend as RowinvLinkProof
import ./rowinv_served_proof.bend as RowinvServedProof
