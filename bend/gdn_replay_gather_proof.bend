# Proofs of the ext 5108 loader laws (gdn_replay_gather_laws.bend) about the Bend model gdn_replay_gather.bend.
# Structural evidence only: no unsafe definitions, axioms, holes or foreign proof code. The finite coverage and
# thread facts are decided by the checker's evaluation; the address and lane laws are proven for symbolic
# operands from the Nat library of gemm_m16_partition_proof.bend.
import Base
import ./gdn_replay_gather.bend as Impl
import ./gdn_replay_gather_spec.bend as Spec
import ./gdn_replay_gather_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def Laws.gather_cover():
  {==}

def Laws.gather_threads():
  {==}

def Laws.gather_widen(b0, b1):
  ({==}, {==})

def Laws.gather_knob():
  ({==}, {==}, {==}, {==}, {==}, {==})

def Laws.chunk_lanes(x, n, xr):
  (Ar.ard_tr(Nat.is_lt(Nat.div(x, 8n), n), Nat.is_lt(x, Nat.mul(n, 8n)), Ar.ar_div_lt(n, x, 8n, {==}), xr),
   Ar.ard_dm_lt(x, 8n, {==}),
   Ar.ard_dm_eq(x, 8n, {==}))

# k: ((sF + (K + P)) + q) == sF + (K + (P + q))
def rg_k(+SF: Nat, +K: Nat, +P: Nat, +q: Nat)
  -> {Nat.add(Nat.add(SF, Nat.add(K, P)), q) == Nat.add(SF, Nat.add(K, Nat.add(P, q))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(SF, Nat.add(K, P)), q), Nat.add(SF, Nat.add(Nat.add(K, P), q)),
    Nat.add(SF, Nat.add(K, Nat.add(P, q))),
    Ar.ar_add_assoc(SF, Nat.add(K, P), q),
    Equal.cong(Nat, Nat, z => Nat.add(SF, z), Nat.add(Nat.add(K, P), q), Nat.add(K, Nat.add(P, q)), Ar.ar_add_assoc(K, P, q)))

# v: ((sF + ((B + C) + P)) + q) == sF + (B + ((C + P) + q))
def rg_v(+SF: Nat, +Bh: Nat, +C: Nat, +P: Nat, +q: Nat)
  -> {Nat.add(Nat.add(SF, Nat.add(Nat.add(Bh, C), P)), q) == Nat.add(SF, Nat.add(Bh, Nat.add(Nat.add(C, P), q))) : Nat}:
  +in1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Bh, C), P), q), Nat.add(Nat.add(Bh, C), Nat.add(P, q)),
    Nat.add(Bh, Nat.add(C, Nat.add(P, q))),
    Ar.ar_add_assoc(Nat.add(Bh, C), P, q), Ar.ar_add_assoc(Bh, C, Nat.add(P, q)))
  +in2 = Equal.cong(Nat, Nat, z => Nat.add(Bh, z), Nat.add(Nat.add(C, P), q), Nat.add(C, Nat.add(P, q)), Ar.ar_add_assoc(C, P, q))
  +inner = Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Bh, C), P), q), Nat.add(Bh, Nat.add(C, Nat.add(P, q))),
    Nat.add(Bh, Nat.add(Nat.add(C, P), q)), in1, Equal.sym(Nat, Nat.add(Bh, Nat.add(Nat.add(C, P), q)), Nat.add(Bh, Nat.add(C, Nat.add(P, q))), in2))
  Equal.trans(Nat, Nat.add(Nat.add(SF, Nat.add(Nat.add(Bh, C), P)), q), Nat.add(SF, Nat.add(Nat.add(Nat.add(Bh, C), P), q)),
    Nat.add(SF, Nat.add(Bh, Nat.add(Nat.add(C, P), q))),
    Ar.ar_add_assoc(SF, Nat.add(Nat.add(Bh, C), P), q),
    Equal.cong(Nat, Nat, z => Nat.add(SF, z), Nat.add(Nat.add(Nat.add(Bh, C), P), q), Nat.add(Bh, Nat.add(Nat.add(C, P), q)), inner))

def rg_by(k: Bool, +F: Nat, +Nk: Nat, +kh: Nat, +h: Nat, +c: Nat, +s: Nat, +p: Nat, +q: Nat)
  -> {Impl.src_by(k, F, Nk, kh, h, c, s, p, q) == Impl.old_src(F, Nk, kh, h, Impl.at(Impl.dst_by(k, c, s, p), q)) : Nat}:
  match k:
    case True{}:
      rg_k(Nat.mul(s, F), Nat.mul(Nat.add(Nk, kh), 128n), Nat.mul(p, 8n), q)
    case False{}:
      rg_v(Nat.mul(s, F), Nat.add(Nat.mul(Nat.mul(2n, Nk), 128n), Nat.mul(h, 128n)), Nat.mul(c, 32n),
        Nat.mul(Nat.sub(p, 16n), 8n), q)

def Laws.gather_src(F, Nk, kh, h, c, e, q):
  rg_by(Impl.is_k(e), F, Nk, kh, h, c, Impl.e_s(e), Impl.e_p(e), q)
