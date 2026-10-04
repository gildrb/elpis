# Proofs of bend/err_attn_laws.bend: case analysis, computation and rewriting only. No @unsafe
# definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./err_bound.bend as Eb
import ./err_bound_laws.bend as EbL
import ./err_bound_proof.bend as EbP
import ./err_attn.bend as Ea
import ./err_attn_laws.bend as Laws

# ==== pre stage ====

def pre_src_sq(w: Nat, hi: Bool, nw: Ea.Nw) -> {Ea.s_src(nw, Ea.SSq{w, hi}) == Ea.e_src(nw, Ea.SSq{w, hi}) : Eb.Path}:
  match w hi nw:
    case 0n True{} Ea.NwF16{}:
      {==}
    case 0n True{} Ea.NwBf16{}:
      {==}
    case 0n False{} Ea.NwF16{}:
      {==}
    case 0n False{} Ea.NwBf16{}:
      {==}
    case 1n+p True{} Ea.NwF16{}:
      {==}
    case 1n+p True{} Ea.NwBf16{}:
      {==}
    case 1n+p False{} Ea.NwF16{}:
      {==}
    case 1n+p False{} Ea.NwBf16{}:
      {==}

def pre_src_eq(nw: Ea.Nw, s: Ea.Src) -> {Ea.s_src(nw, s) == Ea.e_src(nw, s) : Eb.Path}:
  match nw s:
    case Ea.NwF16{} Ea.SIn{}:
      {==}
    case Ea.NwBf16{} Ea.SIn{}:
      {==}
    case Ea.NwF16{} Ea.SW{}:
      {==}
    case Ea.NwBf16{} Ea.SW{}:
      {==}
    case Ea.NwF16{} Ea.SSq{w, hi}:
      pre_src_sq(w, hi, Ea.NwF16{})
    case Ea.NwBf16{} Ea.SSq{w, hi}:
      pre_src_sq(w, hi, Ea.NwBf16{})

def pre_rope_eq(r: Ea.Rot, v: Ea.Via) -> {Ea.s_rope(r, v) == Ea.e_rope(r, v) : Eb.Path}:
  match r v:
    case Ea.RotNo{} _:
      {==}
    case Ea.RotYes{} Ea.VSelf{}:
      {==}
    case Ea.RotYes{} Ea.VPartner{}:
      {==}

def Laws.pre_eq(nw, r, l):
  match l:
    case Ea.PreLeaf{v, s}:
      %pre_src_eq(nw, s) : {Eb.add(_, Ea.e_rope(r, v)) == Eb.add(Ea.s_src(nw, s), Ea.s_rope(r, v)) : Eb.Path}
      %pre_rope_eq(r, v) : {Eb.add(Ea.s_src(nw, s), _) == Eb.add(Ea.s_src(nw, s), Ea.s_rope(r, v)) : Eb.Path}
      {==}

def Laws.pre_dom(nw, r, l):
  %Laws.pre_eq(nw, r, l) : {Eb.dom(128n, Ea.elpis_pre(nw, r, l), _) == True{} : Bool}
  EbL.dom_refl(128n, Ea.elpis_pre(nw, r, l))

# ==== attention core ====

def Laws.geo2_eq():
  {==}
