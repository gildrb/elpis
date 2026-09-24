# Production leaf for one ExLlamaV3 greedy speculative verify round.
# Fixed scalar registers, no heap collection: verify ids t0..t7 (k + 1 used),
# proposals p0..p6 (k used), up to four stop-id slots (ns used), remaining
# output budget and checkpoint (0 = no boundary). Positions are unrolled and
# evaluated lazily in the generator's serial order; the independent list
# reference is exl3_accept_spec.bend and the refinement is proved.
import Base
import ./exl3_accept_spec.bend as Spec

# Stop-set membership over the first `count` of four slots, in slot order.
def stop1(count: Nat, s3: U32, token: U32) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(U32.is_eq(s3, token), False{})

def stop2(count: Nat, s2: U32, s3: U32, +token: U32) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(U32.is_eq(s2, token), stop1(rest, s3, token))

def stop3(count: Nat, s1: U32, s2: U32, s3: U32, +token: U32) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(U32.is_eq(s1, token), stop2(rest, s2, s3, token))

def stop4(count: Nat, s0: U32, s1: U32, s2: U32, s3: U32, +token: U32) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(U32.is_eq(s0, token), stop3(rest, s1, s2, s3, token))

# Position 7 exists only when k = 7: it is the final (bonus) position.
def last(stop: Bool, exhausted: Bool) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{8n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{8n, True{}}
        case False{}:
          Spec.Verdict{8n, False{}}

def at7(+budget: Nat, +ns: Nat, +s0: U32, +s1: U32, +s2: U32, +s3: U32,
    t7: U32) -> Spec.Verdict:
  last(stop4(ns, s0, s1, s2, s3, t7), Nat.is_ge(8n, budget))

# decideN applies the rules at position N (count N + 1) in order: stop,
# exhausted budget, final position, mismatch or checkpoint; else position N+1.
def decide6(stop: Bool, exhausted: Bool, final: Bool, reject: Bool,
    budget: Nat, ns: Nat, s0: U32, s1: U32, s2: U32, s3: U32,
    t7: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{7n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{7n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{7n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{7n, False{}}
                case False{}:
                  at7(budget, ns, s0, s1, s2, s3, t7)

def at6(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t6: U32, t7: U32,
    p6: U32) -> Spec.Verdict:
  decide6(stop4(ns, s0, s1, s2, s3, t6), Nat.is_ge(7n, budget),
    Nat.is_eq(k, 6n), Bool.or(U32.is_ne(p6, t6), Nat.is_eq(7n, checkpoint)),
    budget, ns, s0, s1, s2, s3, t7)

def decide5(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t6: U32, t7: U32, p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{6n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{6n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{6n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{6n, False{}}
                case False{}:
                  at6(k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6)

def at5(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t5: U32, t6: U32, t7: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  decide5(stop4(ns, s0, s1, s2, s3, t5), Nat.is_ge(6n, budget),
    Nat.is_eq(k, 5n), Bool.or(U32.is_ne(p5, t5), Nat.is_eq(6n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6)

def decide4(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t5: U32, t6: U32, t7: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{5n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{5n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{5n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{5n, False{}}
                case False{}:
                  at5(k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7,
                    p5, p6)

def at4(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t4: U32, t5: U32, t6: U32, t7: U32,
    p4: U32, p5: U32, p6: U32) -> Spec.Verdict:
  decide4(stop4(ns, s0, s1, s2, s3, t4), Nat.is_ge(5n, budget),
    Nat.is_eq(k, 4n), Bool.or(U32.is_ne(p4, t4), Nat.is_eq(5n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6)

def decide3(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t4: U32, t5: U32, t6: U32, t7: U32, p4: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{4n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{4n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{4n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{4n, False{}}
                case False{}:
                  at4(k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6,
                    t7, p4, p5, p6)

def at3(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t3: U32, t4: U32, t5: U32, t6: U32,
    t7: U32, p3: U32, p4: U32, p5: U32, p6: U32) -> Spec.Verdict:
  decide3(stop4(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
    Nat.is_eq(k, 3n), Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6)

def decide2(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t3: U32, t4: U32, t5: U32, t6: U32, t7: U32, p3: U32,
    p4: U32, p5: U32, p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{3n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{3n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{3n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{3n, False{}}
                case False{}:
                  at3(k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5,
                    t6, t7, p3, p4, p5, p6)

def at2(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t2: U32, t3: U32, t4: U32, t5: U32,
    t6: U32, t7: U32, p2: U32, p3: U32, p4: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  decide2(stop4(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
    Nat.is_eq(k, 2n), Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4,
    p5, p6)

def decide1(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t2: U32, t3: U32, t4: U32, t5: U32, t6: U32, t7: U32,
    p2: U32, p3: U32, p4: U32, p5: U32, p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{2n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{2n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{2n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{2n, False{}}
                case False{}:
                  at2(k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4,
                    t5, t6, t7, p2, p3, p4, p5, p6)

def at1(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t1: U32, t2: U32, t3: U32, t4: U32,
    t5: U32, t6: U32, t7: U32, p1: U32, p2: U32, p3: U32, p4: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  decide1(stop4(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
    Nat.is_eq(k, 1n), Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2,
    p3, p4, p5, p6)

def decide0(stop: Bool, exhausted: Bool, final: Bool, reject: Bool, k: Nat,
    budget: Nat, checkpoint: Nat, ns: Nat, s0: U32, s1: U32, s2: U32,
    s3: U32, t1: U32, t2: U32, t3: U32, t4: U32, t5: U32, t6: U32, t7: U32,
    p1: U32, p2: U32, p3: U32, p4: U32, p5: U32,
    p6: U32) -> Spec.Verdict:
  match stop:
    case True{}:
      Spec.Verdict{1n, True{}}
    case False{}:
      match exhausted:
        case True{}:
          Spec.Verdict{1n, True{}}
        case False{}:
          match final:
            case True{}:
              Spec.Verdict{1n, False{}}
            case False{}:
              match reject:
                case True{}:
                  Spec.Verdict{1n, False{}}
                case False{}:
                  at1(k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3,
                    t4, t5, t6, t7, p1, p2, p3, p4, p5, p6)

# The executed entry: k proposals (1..7 in the served domain), remaining
# output budget, checkpoint count (0 = none), ns stop slots, then t0..t7 and
# p0..p6. Registers past k + 1 targets, k proposals or ns slots are ignored.
def accept(+k: Nat, +budget: Nat, +checkpoint: Nat, +ns: Nat, +s0: U32,
    +s1: U32, +s2: U32, +s3: U32, +t0: U32, t1: U32, t2: U32, t3: U32,
    t4: U32, t5: U32, t6: U32, t7: U32, p0: U32, p1: U32, p2: U32, p3: U32,
    p4: U32, p5: U32, p6: U32) -> Spec.Verdict:
  decide0(stop4(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
    Nat.is_eq(k, 0n), Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
    k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1,
    p2, p3, p4, p5, p6)
