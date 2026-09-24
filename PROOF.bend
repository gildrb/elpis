# Proof-only entry point: no main, no foreign proof code and no axioms.
# Discharges every law reachable from LAWS.bend.
import Base
import ./LAWS.bend as Laws
import ./bend/exl3_accept_proof.bend as Exl3AcceptProof
