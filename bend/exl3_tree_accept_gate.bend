# Proof gate of the tree acceptor artifact (bend/exl3_build.py): every law of
# bend/exl3_tree_accept_laws.bend, discharged by the accept, derive and path proof
# modules. No main, no foreign proof code and no axioms.
import Base
import ./exl3_tree_accept_laws.bend as Laws
import ./exl3_tree_accept_proof.bend as AcceptProof
import ./exl3_tree_derive_proof.bend as DeriveProof
import ./exl3_tree_path_proof.bend as PathProof
