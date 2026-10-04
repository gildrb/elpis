# Proof gate of the decode norm / elementwise error-bound laws: every law of
# bend/err_elem_laws.bend, discharged by bend/err_elem_proof.bend (with the core laws of
# bend/err_bound_laws.bend from bend/err_bound_proof.bend). No main, no foreign proof code and no
# axioms. Check: bend bend/err_elem_gate.bend --verdict (prints ALL PROOFS CHECK). Source link:
# python3 bend/err_elem_diff.py [--sass SO] STOCK_PACKAGE_DIR.
import Base
import ./err_bound_laws.bend as EbL
import ./err_bound_proof.bend as EbP
import ./err_elem_laws.bend as Laws
import ./err_elem_proof.bend as Proof
