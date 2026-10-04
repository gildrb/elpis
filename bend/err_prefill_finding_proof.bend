# Proofs of bend/err_prefill_finding_laws.bend by computation (the counterexamples are concrete rows). No @unsafe
# definitions, axioms, holes or foreign code.
import Base
import ./err_bound.bend as Eb
import ./err_prefill.bend as Ep
import ./err_prefill_finding_laws.bend as Laws

def Laws.pv_unsplit_false():
  ({==}, {==})

def Laws.pv_split_false():
  ({==}, {==}, {==})
