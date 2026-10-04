# Proof-only gate for the error-bound core laws (bend/err_bound_laws.bend: dom_sigma, sigma_add,
# dom_add, dom_refl, dom_trans) and the shared Nat lemma laws they use (bend/nat_order_laws.bend).
# Prints ALL PROOFS CHECK only when both proof modules discharge every law. No main, no foreign
# code, no axioms.
import Base
import ./nat_order_proof.bend as NatOrderProof
import ./err_bound_proof.bend as ErrBoundProof
