# Core laws of the rounding-error bound vocabulary (bend/err_bound.bend).
import Base
import ./err_bound.bend as Eb

# Domination bounds sigma: for EVERY class-bound assignment w in the class order at exchange
# rate x, a path dominated by another has a sigma no larger than it. With Higham's Lemma 3.1
# (the error factor sigma / (1 - sigma) increases with sigma) this is: the dominated path's
# worst-case rounding error bound is no larger.
law dom_sigma:
  for +x: Nat
  for +w: Eb.W
  for +e: Eb.Path
  for +s: Eb.Path
  for ord: {Eb.order(x, w) == True{} : Bool}
  for d: {Eb.dom(x, e, s) == True{} : Bool}
  {Nat.is_le(Eb.sigma(w, e), Eb.sigma(w, s)) == True{} : Bool}

# sigma is additive over path concatenation (segments of a path compose).
law sigma_add:
  for +w: Eb.W
  for +p: Eb.Path
  for +q: Eb.Path
  {Eb.sigma(w, Eb.add(p, q)) == Nat.add(Eb.sigma(w, p), Eb.sigma(w, q)) : Nat}

# Domination composes over concatenation: segment-wise domination gives domination of the
# concatenated paths.
law dom_add:
  for +x: Nat
  for +e1: Eb.Path
  for +s1: Eb.Path
  for +e2: Eb.Path
  for +s2: Eb.Path
  for d1: {Eb.dom(x, e1, s1) == True{} : Bool}
  for d2: {Eb.dom(x, e2, s2) == True{} : Bool}
  {Eb.dom(x, Eb.add(e1, e2), Eb.add(s1, s2)) == True{} : Bool}

# Domination is reflexive (an unchanged path is never worse) and transitive.
law dom_refl:
  for +x: Nat
  for +p: Eb.Path
  {Eb.dom(x, p, p) == True{} : Bool}

law dom_trans:
  for +x: Nat
  for +a: Eb.Path
  for +b: Eb.Path
  for +c: Eb.Path
  for ab: {Eb.dom(x, a, b) == True{} : Bool}
  for bc: {Eb.dom(x, b, c) == True{} : Bool}
  {Eb.dom(x, a, c) == True{} : Bool}
