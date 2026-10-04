# Lemmas on the aligned binary trees of bend/err_attn_dec.bend (tdepth, tbound): a live position's
# adds are at most the tree's levels below the live count, and that count is monotone. Structural
# induction only: no @unsafe definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./attn_stride.bend as St
import ./err_attn_dec.bend as Dec
import ./gemm_m16_partition_proof.bend as Ar
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP

# bit(b) <= 1
def tr_bit_le1(b: Bool) -> {Nat.is_le(St.bit(b), 1n) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# x < 0 is false
def tr_lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# An absurd hypothesis x < 0
def tr_lt0(-G: Type, +x: Nat, h: {Nat.is_lt(x, 0n) == True{} : Bool}) -> G:
  Empty.absurd(G, Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{},
    Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, tr_lt_zero(x)), h)))

# tbound(K, n) <= K
def tr_tbound_le(+K: Nat, +n: Nat) -> {Nat.is_le(Dec.tbound(K, n), K) == True{} : Bool}:
  match K:
    case 0n:
      {==}
    case 1n+k:
      NO.le_add_mono(St.bit(Nat.is_lt(1n, n)), 1n, Dec.tbound(k, Dec.halfup(n)), k,
        tr_bit_le1(Nat.is_lt(1n, n)), tr_tbound_le(k, Dec.halfup(n)))

# n <= m gives ceil(n / 2) <= ceil(m / 2)
def tr_halfup_mono(n: Nat, +m: Nat, h: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_le(Dec.halfup(n), Dec.halfup(m)) == True{} : Bool}:
  match n:
    case 0n:
      NO.le_zero(Dec.halfup(m))
    case 1n+p:
      match p:
        case 0n:
          match m:
            case 0n:
              Empty.absurd({Nat.is_le(Dec.halfup(1n), Dec.halfup(0n)) == True{} : Bool}, Ar.ar_false_true(h))
            case 1n+mp:
              match mp:
                case 0n:
                  {==}
                case 1n+mq:
                  NO.le_zero(Dec.halfup(mq))
        case 1n+pp:
          match m:
            case 0n:
              Empty.absurd({Nat.is_le(Dec.halfup(2n+pp), Dec.halfup(0n)) == True{} : Bool}, Ar.ar_false_true(h))
            case 1n+mp:
              match mp:
                case 0n:
                  Empty.absurd({Nat.is_le(Dec.halfup(2n+pp), Dec.halfup(1n)) == True{} : Bool}, Ar.ar_false_true(h))
                case 1n+mq:
                  tr_halfup_mono(pp, mq, h)

# n <= m gives bit(1 < n) <= bit(1 < m)
def tr_bit_mono(n: Nat, +m: Nat, h: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_le(St.bit(Nat.is_lt(1n, n)), St.bit(Nat.is_lt(1n, m))) == True{} : Bool}:
  match n:
    case 0n:
      NO.le_zero(St.bit(Nat.is_lt(1n, m)))
    case 1n+p:
      match p:
        case 0n:
          NO.le_zero(St.bit(Nat.is_lt(1n, m)))
        case 1n+pp:
          match m:
            case 0n:
              Empty.absurd({Nat.is_le(St.bit(Nat.is_lt(1n, 2n+pp)), St.bit(Nat.is_lt(1n, 0n))) == True{} : Bool},
                Ar.ar_false_true(h))
            case 1n+mp:
              match mp:
                case 0n:
                  Empty.absurd({Nat.is_le(St.bit(Nat.is_lt(1n, 2n+pp)), St.bit(Nat.is_lt(1n, 1n))) == True{} : Bool},
                    Ar.ar_false_true(h))
                case 1n+mq:
                  {==}

# n <= m gives tbound(K, n) <= tbound(K, m)
def tr_tbound_mono(+K: Nat, +n: Nat, +m: Nat, +h: {Nat.is_le(n, m) == True{} : Bool})
  -> {Nat.is_le(Dec.tbound(K, n), Dec.tbound(K, m)) == True{} : Bool}:
  match K:
    case 0n:
      {==}
    case 1n+k:
      NO.le_add_mono(St.bit(Nat.is_lt(1n, n)), St.bit(Nat.is_lt(1n, m)),
        Dec.tbound(k, Dec.halfup(n)), Dec.tbound(k, Dec.halfup(m)),
        tr_bit_mono(n, m, h), tr_tbound_mono(k, Dec.halfup(n), Dec.halfup(m), tr_halfup_mono(n, m, h)))

# x < n gives floor(x / 2) < ceil(n / 2)
def tr_half_lt(x: Nat, +n: Nat, h: {Nat.is_lt(x, n) == True{} : Bool})
  -> {Nat.is_lt(Dec.half(x), Dec.halfup(n)) == True{} : Bool}:
  match x:
    case 0n:
      match n:
        case 0n:
          Empty.absurd({Nat.is_lt(Dec.half(0n), Dec.halfup(0n)) == True{} : Bool}, Ar.ar_false_true(h))
        case 1n+np:
          match np:
            case 0n:
              {==}
            case 1n+nq:
              {==}
    case 1n+p:
      match p:
        case 0n:
          match n:
            case 0n:
              Empty.absurd({Nat.is_lt(Dec.half(1n), Dec.halfup(0n)) == True{} : Bool}, Ar.ar_false_true(h))
            case 1n+np:
              match np:
                case 0n:
                  Empty.absurd({Nat.is_lt(Dec.half(1n), Dec.halfup(1n)) == True{} : Bool}, Ar.ar_false_true(h))
                case 1n+nq:
                  {==}
        case 1n+pp:
          match n:
            case 0n:
              Empty.absurd({Nat.is_lt(Dec.half(2n+pp), Dec.halfup(0n)) == True{} : Bool}, Ar.ar_false_true(h))
            case 1n+np:
              match np:
                case 0n:
                  Empty.absurd({Nat.is_lt(Dec.half(2n+pp), Dec.halfup(1n)) == True{} : Bool}, Ar.ar_false_true(h))
                case 1n+nq:
                  tr_half_lt(pp, nq, h)

# x < n gives bit(flip(x) < n) <= bit(1 < n): a live position meets a live sibling only at levels
# whose block size is below n
def tr_flip_bit(x: Nat, +n: Nat, h: {Nat.is_lt(x, n) == True{} : Bool})
  -> {Nat.is_le(St.bit(Nat.is_lt(Dec.flip(x), n)), St.bit(Nat.is_lt(1n, n))) == True{} : Bool}:
  match x:
    case 0n:
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(St.bit(Nat.is_lt(Dec.flip(0n), 0n)), St.bit(Nat.is_lt(1n, 0n))) == True{} : Bool},
            Ar.ar_false_true(h))
        case 1n+np:
          match np:
            case 0n:
              {==}
            case 1n+nq:
              {==}
    case 1n+p:
      match n:
        case 0n:
          Empty.absurd({Nat.is_le(St.bit(Nat.is_lt(Dec.flip(1n+p), 0n)), St.bit(Nat.is_lt(1n, 0n))) == True{} : Bool},
            Ar.ar_false_true(h))
        case 1n+np:
          match np:
            case 0n:
              tr_lt0({Nat.is_le(St.bit(Nat.is_lt(Dec.flip(1n+p), 1n)), St.bit(Nat.is_lt(1n, 1n))) == True{} : Bool}, p, h)
            case 1n+nq:
              tr_bit_le1(Nat.is_lt(Dec.flip(1n+p), 2n+nq))

# x < n gives tdepth(K, x, n) <= tbound(K, n)
def tr_tdepth_le(+K: Nat, +x: Nat, +n: Nat, +h: {Nat.is_lt(x, n) == True{} : Bool})
  -> {Nat.is_le(Dec.tdepth(K, x, n), Dec.tbound(K, n)) == True{} : Bool}:
  match K:
    case 0n:
      {==}
    case 1n+k:
      NO.le_add_mono(St.bit(Nat.is_lt(Dec.flip(x), n)), St.bit(Nat.is_lt(1n, n)),
        Dec.tdepth(k, Dec.half(x), Dec.halfup(n)), Dec.tbound(k, Dec.halfup(n)),
        tr_flip_bit(x, n, h), tr_tdepth_le(k, Dec.half(x), Dec.halfup(n), tr_half_lt(x, n, h)))
