# Proofs of the EXL3 greedy acceptance laws. Structural evidence only: no
# unsafe definitions, axioms, holes, foreign proof code or answer tables.
import Base
import ./exl3_accept.bend as Impl
import ./exl3_accept_spec.bend as Spec
import ./exl3_accept_laws.bend as Laws

def Truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

def false_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : Truth(_)
  Unit{}

# Stop slots and the list reference agree slot by slot for every count.
def stop_member(+ns: Nat, +s0: U32, +s1: U32, +s2: U32, +s3: U32, +token: U32)
  -> {Impl.stop4(ns, s0, s1, s2, s3, token) ==
    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), token) : Bool}:
  match ns:
    case 0n:
      {==}
    case 1n+n1:
      match n1:
        case 0n:
          {==}
        case 1n+n2:
          match n2:
            case 0n:
              {==}
            case 1n+n3:
              match n3:
                case 0n:
                  {==}
                case 1n+n4:
                  {==}

# Position 0 continues: the rules agree case by case, then the next position.
def continues0(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t1: U32, -t2: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32,
    -p1: U32, -p2: U32, -p3: U32, -p4: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at1(k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6,
        t7, p1, p2, p3, p4, p5, p6) == Spec.decide(rest, 1n)
      : Spec.Verdict})
  -> {Impl.decide0(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 0n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step0(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t1: U32, -t2: U32, -t3: U32, -t4: U32, -t5: U32,
    -t6: U32, -t7: U32, -p1: U32, -p2: U32, -p3: U32, -p4: U32, -p5: U32,
    -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at1(k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6,
        t7, p1, p2, p3, p4, p5, p6) == Spec.decide(rest, 1n)
      : Spec.Verdict})
  -> {Impl.decide0(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 0n)
    : Spec.Verdict}:
  %hs : {Impl.decide0(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 0n) : Spec.Verdict}
  continues0(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4,
      t5, t6, t7, p1, p2, p3, p4, p5, p6, rest, next)

# Position 0 is final (k = 0): its target is the bonus token.
def ends0(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t1: U32, -t2: U32,
    -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p1: U32, -p2: U32,
    -p3: U32, -p4: U32, -p5: U32, -p6: U32)
  -> {Impl.decide0(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t1,
        t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 0n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final0(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t1: U32, -t2: U32, -t3: U32, -t4: U32, -t5: U32,
    -t6: U32, -t7: U32, -p1: U32, -p2: U32, -p3: U32, -p4: U32, -p5: U32,
    -p6: U32)
  -> {Impl.decide0(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t1,
        t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 0n)
    : Spec.Verdict}:
  %hs : {Impl.decide0(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t1,
        t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 0n) : Spec.Verdict}
  ends0(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5,
      t6, t7, p1, p2, p3, p4, p5, p6)

# Position 1 continues: the rules agree case by case, then the next position.
def continues1(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t2: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p2: U32,
    -p3: U32, -p4: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at2(k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7,
        p2, p3, p4, p5, p6) == Spec.decide(rest, 2n)
      : Spec.Verdict})
  -> {Impl.decide1(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 1n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step1(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t2: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32,
    -t7: U32, -p2: U32, -p3: U32, -p4: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at2(k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7,
        p2, p3, p4, p5, p6) == Spec.decide(rest, 2n)
      : Spec.Verdict})
  -> {Impl.decide1(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 1n)
    : Spec.Verdict}:
  %hs : {Impl.decide1(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 1n) : Spec.Verdict}
  continues1(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5,
      t6, t7, p2, p3, p4, p5, p6, rest, next)

# Position 1 is final (k = 1): its target is the bonus token.
def ends1(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t2: U32, -t3: U32,
    -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p2: U32, -p3: U32, -p4: U32,
    -p5: U32, -p6: U32)
  -> {Impl.decide1(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t2,
        t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 1n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final1(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t2: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32,
    -t7: U32, -p2: U32, -p3: U32, -p4: U32, -p5: U32, -p6: U32)
  -> {Impl.decide1(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t2,
        t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 1n)
    : Spec.Verdict}:
  %hs : {Impl.decide1(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t2,
        t3, t4, t5, t6, t7, p2, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 1n) : Spec.Verdict}
  ends1(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6,
      t7, p2, p3, p4, p5, p6)

# Position 2 continues: the rules agree case by case, then the next position.
def continues2(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p3: U32, -p4: U32,
    -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at3(k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3,
        p4, p5, p6) == Spec.decide(rest, 3n)
      : Spec.Verdict})
  -> {Impl.decide2(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t3, t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 2n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step2(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32,
    -p3: U32, -p4: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at3(k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3,
        p4, p5, p6) == Spec.decide(rest, 3n)
      : Spec.Verdict})
  -> {Impl.decide2(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t3, t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 2n)
    : Spec.Verdict}:
  %hs : {Impl.decide2(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t3, t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 2n) : Spec.Verdict}
  continues2(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6,
      t7, p3, p4, p5, p6, rest, next)

# Position 2 is final (k = 2): its target is the bonus token.
def ends2(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t3: U32, -t4: U32,
    -t5: U32, -t6: U32, -t7: U32, -p3: U32, -p4: U32, -p5: U32, -p6: U32)
  -> {Impl.decide2(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t3,
        t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 2n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final2(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32,
    -p3: U32, -p4: U32, -p5: U32, -p6: U32)
  -> {Impl.decide2(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t3,
        t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 2n)
    : Spec.Verdict}:
  %hs : {Impl.decide2(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t3,
        t4, t5, t6, t7, p3, p4, p5, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 2n) : Spec.Verdict}
  ends2(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7,
      p3, p4, p5, p6)

# Position 3 continues: the rules agree case by case, then the next position.
def continues3(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p4: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at4(k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5,
        p6) == Spec.decide(rest, 4n)
      : Spec.Verdict})
  -> {Impl.decide3(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t4, t5, t6, t7, p4, p5, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 3n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step3(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p4: U32,
    -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at4(k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5,
        p6) == Spec.decide(rest, 4n)
      : Spec.Verdict})
  -> {Impl.decide3(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t4, t5, t6, t7, p4, p5, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 3n)
    : Spec.Verdict}:
  %hs : {Impl.decide3(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t4, t5, t6, t7, p4, p5, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 3n) : Spec.Verdict}
  continues3(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7,
      p4, p5, p6, rest, next)

# Position 3 is final (k = 3): its target is the bonus token.
def ends3(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t4: U32, -t5: U32,
    -t6: U32, -t7: U32, -p4: U32, -p5: U32, -p6: U32)
  -> {Impl.decide3(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t4,
        t5, t6, t7, p4, p5, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 3n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final3(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t4: U32, -t5: U32, -t6: U32, -t7: U32, -p4: U32,
    -p5: U32, -p6: U32)
  -> {Impl.decide3(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t4,
        t5, t6, t7, p4, p5, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 3n)
    : Spec.Verdict}:
  %hs : {Impl.decide3(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t4,
        t5, t6, t7, p4, p5, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 3n) : Spec.Verdict}
  ends3(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4,
      p5, p6)

# Position 4 continues: the rules agree case by case, then the next position.
def continues4(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t5: U32, -t6: U32, -t7: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at5(k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6) == Spec.decide(rest, 5n)
      : Spec.Verdict})
  -> {Impl.decide4(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t5, t6, t7, p5, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 4n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step4(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t5: U32, -t6: U32, -t7: U32, -p5: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at5(k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6) == Spec.decide(rest, 5n)
      : Spec.Verdict})
  -> {Impl.decide4(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t5, t6, t7, p5, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 4n)
    : Spec.Verdict}:
  %hs : {Impl.decide4(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t5, t6, t7, p5, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 4n) : Spec.Verdict}
  continues4(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5,
      p6, rest, next)

# Position 4 is final (k = 4): its target is the bonus token.
def ends4(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t5: U32, -t6: U32,
    -t7: U32, -p5: U32, -p6: U32)
  -> {Impl.decide4(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t5,
        t6, t7, p5, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 4n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final4(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t5: U32, -t6: U32, -t7: U32, -p5: U32, -p6: U32)
  -> {Impl.decide4(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t5,
        t6, t7, p5, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 4n)
    : Spec.Verdict}:
  %hs : {Impl.decide4(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t5,
        t6, t7, p5, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 4n) : Spec.Verdict}
  ends4(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6)

# Position 5 continues: the rules agree case by case, then the next position.
def continues5(s: Bool, e: Bool, r: Bool, -k: Nat, -budget: Nat,
    -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32,
    -t6: U32, -t7: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at6(k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6) == Spec.decide(rest, 6n)
      : Spec.Verdict})
  -> {Impl.decide5(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t6, t7, p6) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 5n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step5(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t6: U32, -t7: U32, -p6: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at6(k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6) == Spec.decide(rest, 6n)
      : Spec.Verdict})
  -> {Impl.decide5(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t6, t7, p6) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 5n)
    : Spec.Verdict}:
  %hs : {Impl.decide5(s, e, False{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3,
        t6, t7, p6) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 5n) : Spec.Verdict}
  continues5(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6,
      rest, next)

# Position 5 is final (k = 5): its target is the bonus token.
def ends5(s: Bool, e: Bool, -r: Bool, -k: Nat, -budget: Nat, -checkpoint: Nat,
    -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t6: U32, -t7: U32,
    -p6: U32)
  -> {Impl.decide5(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t6,
        t7, p6) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 5n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final5(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -k: Nat, -budget: Nat, -checkpoint: Nat, -ns: Nat, -s0: U32, -s1: U32,
    -s2: U32, -s3: U32, -t6: U32, -t7: U32, -p6: U32)
  -> {Impl.decide5(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t6,
        t7, p6) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 5n)
    : Spec.Verdict}:
  %hs : {Impl.decide5(s, e, True{}, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t6,
        t7, p6) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 5n) : Spec.Verdict}
  ends5(s, e, r, k, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6)

# Position 6 continues: the rules agree case by case, then the next position.
def continues6(s: Bool, e: Bool, r: Bool, -budget: Nat, -ns: Nat, -s0: U32,
    -s1: U32, -s2: U32, -s3: U32, -t7: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at7(budget, ns, s0, s1, s2, s3, t7) == Spec.decide(rest, 7n)
      : Spec.Verdict})
  -> {Impl.decide6(s, e, False{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide(Spec.Facts{s, e, False{}, r} <> rest, 6n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          match r:
            case True{}:
              {==}
            case False{}:
              next

def step6(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, r: Bool,
    -budget: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t7: U32,
    -rest: List<&2, Spec.Facts>,
    next: {Impl.at7(budget, ns, s0, s1, s2, s3, t7) == Spec.decide(rest, 7n)
      : Spec.Verdict})
  -> {Impl.decide6(s, e, False{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide(Spec.Facts{listed, e, False{}, r} <> rest, 6n)
    : Spec.Verdict}:
  %hs : {Impl.decide6(s, e, False{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide(Spec.Facts{_, e, False{}, r} <> rest, 6n) : Spec.Verdict}
  continues6(s, e, r, budget, ns, s0, s1, s2, s3, t7, rest, next)

# Position 6 is final (k = 6): its target is the bonus token.
def ends6(s: Bool, e: Bool, -r: Bool, -budget: Nat, -ns: Nat, -s0: U32,
    -s1: U32, -s2: U32, -s3: U32, -t7: U32)
  -> {Impl.decide6(s, e, True{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 6n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final6(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool, -r: Bool,
    -budget: Nat, -ns: Nat, -s0: U32, -s1: U32, -s2: U32, -s3: U32, -t7: U32)
  -> {Impl.decide6(s, e, True{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 6n)
    : Spec.Verdict}:
  %hs : {Impl.decide6(s, e, True{}, r, budget, ns, s0, s1, s2, s3, t7) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 6n) : Spec.Verdict}
  ends6(s, e, r, budget, ns, s0, s1, s2, s3, t7)

# Position 7 is final whenever it is reached in the k <= 7 domain.
def ends7(s: Bool, e: Bool)
  -> {Impl.last(s, e) ==
    Spec.decide([Spec.Facts{s, e, True{}, False{}}], 7n) : Spec.Verdict}:
  match s:
    case True{}:
      {==}
    case False{}:
      match e:
        case True{}:
          {==}
        case False{}:
          {==}

def final7(+s: Bool, -listed: Bool, hs: {s == listed : Bool}, e: Bool)
  -> {Impl.last(s, e) ==
    Spec.decide([Spec.Facts{listed, e, True{}, False{}}], 7n) : Spec.Verdict}:
  %hs : {Impl.last(s, e) ==
    Spec.decide([Spec.Facts{_, e, True{}, False{}}], 7n) : Spec.Verdict}
  ends7(s, e)

# Each supported k composes its position lemmas from the final position back
# to position 0; k >= 8 contradicts the domain hypothesis.
def Laws.leaf_refinement(k, valid, budget, checkpoint, ns, s0, s1, s2, s3, t0,
    t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6):
  match k:
    case 0n:
      final0(Impl.stop4(ns, s0, s1, s2, s3, t0),
        Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
        stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
        Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
        0n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6)
    case 1n+k1:
      match k1:
        case 0n:
          step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
            Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
            stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
            Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
            1n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
            Spec.facts([t1], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
              checkpoint),
            final1(Impl.stop4(ns, s0, s1, s2, s3, t1),
              Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
              stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
              Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
              1n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6))
        case 1n+k2:
          match k2:
            case 0n:
              step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                2n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                Spec.facts([t1, t2], [p1], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                  checkpoint),
                step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                  Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                  stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                  Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                  2n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                  Spec.facts([t2], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                    checkpoint),
                  final2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                    stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                    Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                    2n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6)))
            case 1n+k3:
              match k3:
                case 0n:
                  step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                    stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                    Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                    3n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                    Spec.facts([t1, t2, t3], [p1, p2], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                      checkpoint),
                    step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                      Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                      stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                      Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                      3n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                      Spec.facts([t2, t3], [p2], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                        checkpoint),
                      step2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                        Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                        stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                        Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                        3n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6,
                        Spec.facts([t3], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 3n, budget,
                          checkpoint),
                        final3(Impl.stop4(ns, s0, s1, s2, s3, t3),
                          Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t3),
                          stop_member(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
                          Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
                          3n, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6))))
                case 1n+k4:
                  match k4:
                    case 0n:
                      step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                        Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                        stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                        Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                        4n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                        Spec.facts([t1, t2, t3, t4], [p1, p2, p3], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                          checkpoint),
                        step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                          Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                          stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                          Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                          4n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                          Spec.facts([t2, t3, t4], [p2, p3], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                            checkpoint),
                          step2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                            Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                            stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                            Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                            4n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6,
                            Spec.facts([t3, t4], [p3], List.take(&2, U32, [s0, s1, s2, s3], ns), 3n, budget,
                              checkpoint),
                            step3(Impl.stop4(ns, s0, s1, s2, s3, t3),
                              Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t3),
                              stop_member(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
                              Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
                              4n, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6,
                              Spec.facts([t4], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 4n, budget,
                                checkpoint),
                              final4(Impl.stop4(ns, s0, s1, s2, s3, t4),
                                Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t4),
                                stop_member(ns, s0, s1, s2, s3, t4), Nat.is_ge(5n, budget),
                                Bool.or(U32.is_ne(p4, t4), Nat.is_eq(5n, checkpoint)),
                                4n, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6)))))
                    case 1n+k5:
                      match k5:
                        case 0n:
                          step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                            Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                            stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                            Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                            5n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                            Spec.facts([t1, t2, t3, t4, t5], [p1, p2, p3, p4], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                              checkpoint),
                            step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                              Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                              stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                              Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                              5n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                              Spec.facts([t2, t3, t4, t5], [p2, p3, p4], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                                checkpoint),
                              step2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                                Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                                stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                                Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                                5n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6,
                                Spec.facts([t3, t4, t5], [p3, p4], List.take(&2, U32, [s0, s1, s2, s3], ns), 3n, budget,
                                  checkpoint),
                                step3(Impl.stop4(ns, s0, s1, s2, s3, t3),
                                  Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t3),
                                  stop_member(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
                                  Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
                                  5n, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6,
                                  Spec.facts([t4, t5], [p4], List.take(&2, U32, [s0, s1, s2, s3], ns), 4n, budget,
                                    checkpoint),
                                  step4(Impl.stop4(ns, s0, s1, s2, s3, t4),
                                    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t4),
                                    stop_member(ns, s0, s1, s2, s3, t4), Nat.is_ge(5n, budget),
                                    Bool.or(U32.is_ne(p4, t4), Nat.is_eq(5n, checkpoint)),
                                    5n, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6,
                                    Spec.facts([t5], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 5n, budget,
                                      checkpoint),
                                    final5(Impl.stop4(ns, s0, s1, s2, s3, t5),
                                      Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t5),
                                      stop_member(ns, s0, s1, s2, s3, t5), Nat.is_ge(6n, budget),
                                      Bool.or(U32.is_ne(p5, t5), Nat.is_eq(6n, checkpoint)),
                                      5n, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6))))))
                        case 1n+k6:
                          match k6:
                            case 0n:
                              step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                                Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                                stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                                Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                                6n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                                Spec.facts([t1, t2, t3, t4, t5, t6], [p1, p2, p3, p4, p5], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                                  checkpoint),
                                step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                                  Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                                  stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                                  Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                                  6n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                                  Spec.facts([t2, t3, t4, t5, t6], [p2, p3, p4, p5], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                                    checkpoint),
                                  step2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                                    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                                    stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                                    Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                                    6n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6,
                                    Spec.facts([t3, t4, t5, t6], [p3, p4, p5], List.take(&2, U32, [s0, s1, s2, s3], ns), 3n, budget,
                                      checkpoint),
                                    step3(Impl.stop4(ns, s0, s1, s2, s3, t3),
                                      Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t3),
                                      stop_member(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
                                      Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
                                      6n, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6,
                                      Spec.facts([t4, t5, t6], [p4, p5], List.take(&2, U32, [s0, s1, s2, s3], ns), 4n, budget,
                                        checkpoint),
                                      step4(Impl.stop4(ns, s0, s1, s2, s3, t4),
                                        Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t4),
                                        stop_member(ns, s0, s1, s2, s3, t4), Nat.is_ge(5n, budget),
                                        Bool.or(U32.is_ne(p4, t4), Nat.is_eq(5n, checkpoint)),
                                        6n, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6,
                                        Spec.facts([t5, t6], [p5], List.take(&2, U32, [s0, s1, s2, s3], ns), 5n, budget,
                                          checkpoint),
                                        step5(Impl.stop4(ns, s0, s1, s2, s3, t5),
                                          Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t5),
                                          stop_member(ns, s0, s1, s2, s3, t5), Nat.is_ge(6n, budget),
                                          Bool.or(U32.is_ne(p5, t5), Nat.is_eq(6n, checkpoint)),
                                          6n, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6,
                                          Spec.facts([t6], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 6n, budget,
                                            checkpoint),
                                          final6(Impl.stop4(ns, s0, s1, s2, s3, t6),
                                            Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t6),
                                            stop_member(ns, s0, s1, s2, s3, t6), Nat.is_ge(7n, budget),
                                            Bool.or(U32.is_ne(p6, t6), Nat.is_eq(7n, checkpoint)),
                                            budget, ns, s0, s1, s2, s3, t7)))))))
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  step0(Impl.stop4(ns, s0, s1, s2, s3, t0),
                                    Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t0),
                                    stop_member(ns, s0, s1, s2, s3, t0), Nat.is_ge(1n, budget),
                                    Bool.or(U32.is_ne(p0, t0), Nat.is_eq(1n, checkpoint)),
                                    7n, budget, checkpoint, ns, s0, s1, s2, s3, t1, t2, t3, t4, t5, t6, t7, p1, p2, p3, p4, p5, p6,
                                    Spec.facts([t1, t2, t3, t4, t5, t6, t7], [p1, p2, p3, p4, p5, p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 1n, budget,
                                      checkpoint),
                                    step1(Impl.stop4(ns, s0, s1, s2, s3, t1),
                                      Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t1),
                                      stop_member(ns, s0, s1, s2, s3, t1), Nat.is_ge(2n, budget),
                                      Bool.or(U32.is_ne(p1, t1), Nat.is_eq(2n, checkpoint)),
                                      7n, budget, checkpoint, ns, s0, s1, s2, s3, t2, t3, t4, t5, t6, t7, p2, p3, p4, p5, p6,
                                      Spec.facts([t2, t3, t4, t5, t6, t7], [p2, p3, p4, p5, p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 2n, budget,
                                        checkpoint),
                                      step2(Impl.stop4(ns, s0, s1, s2, s3, t2),
                                        Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t2),
                                        stop_member(ns, s0, s1, s2, s3, t2), Nat.is_ge(3n, budget),
                                        Bool.or(U32.is_ne(p2, t2), Nat.is_eq(3n, checkpoint)),
                                        7n, budget, checkpoint, ns, s0, s1, s2, s3, t3, t4, t5, t6, t7, p3, p4, p5, p6,
                                        Spec.facts([t3, t4, t5, t6, t7], [p3, p4, p5, p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 3n, budget,
                                          checkpoint),
                                        step3(Impl.stop4(ns, s0, s1, s2, s3, t3),
                                          Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t3),
                                          stop_member(ns, s0, s1, s2, s3, t3), Nat.is_ge(4n, budget),
                                          Bool.or(U32.is_ne(p3, t3), Nat.is_eq(4n, checkpoint)),
                                          7n, budget, checkpoint, ns, s0, s1, s2, s3, t4, t5, t6, t7, p4, p5, p6,
                                          Spec.facts([t4, t5, t6, t7], [p4, p5, p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 4n, budget,
                                            checkpoint),
                                          step4(Impl.stop4(ns, s0, s1, s2, s3, t4),
                                            Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t4),
                                            stop_member(ns, s0, s1, s2, s3, t4), Nat.is_ge(5n, budget),
                                            Bool.or(U32.is_ne(p4, t4), Nat.is_eq(5n, checkpoint)),
                                            7n, budget, checkpoint, ns, s0, s1, s2, s3, t5, t6, t7, p5, p6,
                                            Spec.facts([t5, t6, t7], [p5, p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 5n, budget,
                                              checkpoint),
                                            step5(Impl.stop4(ns, s0, s1, s2, s3, t5),
                                              Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t5),
                                              stop_member(ns, s0, s1, s2, s3, t5), Nat.is_ge(6n, budget),
                                              Bool.or(U32.is_ne(p5, t5), Nat.is_eq(6n, checkpoint)),
                                              7n, budget, checkpoint, ns, s0, s1, s2, s3, t6, t7, p6,
                                              Spec.facts([t6, t7], [p6], List.take(&2, U32, [s0, s1, s2, s3], ns), 6n, budget,
                                                checkpoint),
                                              step6(Impl.stop4(ns, s0, s1, s2, s3, t6),
                                                Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t6),
                                                stop_member(ns, s0, s1, s2, s3, t6), Nat.is_ge(7n, budget),
                                                Bool.or(U32.is_ne(p6, t6), Nat.is_eq(7n, checkpoint)),
                                                budget, ns, s0, s1, s2, s3, t7,
                                                Spec.facts([t7], [], List.take(&2, U32, [s0, s1, s2, s3], ns), 7n, budget,
                                                  checkpoint),
                                                final7(Impl.stop4(ns, s0, s1, s2, s3, t7),
                                                  Spec.member(List.take(&2, U32, [s0, s1, s2, s3], ns), t7),
                                                  stop_member(ns, s0, s1, s2, s3, t7), Nat.is_ge(8n, budget)))))))))
                                case 1n+k8:
                                  Empty.absurd({Impl.accept(8n+k8, budget, checkpoint, ns, s0, s1, s2,
                                    s3, t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6) ==
                                    Spec.accept(List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 9n+k8),
                                      List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], 8n+k8),
                                      List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint) : Spec.Verdict},
                                    false_true(valid))

# Small constructor and order facts, derived by transport and induction.
def true_false(equal: {True{} == False{} : Bool}) -> Empty:
  %equal : Truth(_)
  Unit{}

def Positive(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_succ(-n: Nat, equal: {0n == 1n+n : Nat}) -> Empty:
  %equal : Positive(_)
  Unit{}

def pred(value: Nat) -> Nat:
  match value:
    case 0n:
      0n
    case 1n+p:
      p

def succ_injective(-a: Nat, -b: Nat, equal: {1n+a == 1n+b : Nat})
  -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, equal)

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(n: Nat, -m: Nat)
  -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lt_succ_le(a: Nat, b: Nat, less: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, false_true(less))
    case 0n 1n+q:
      le_zero(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, false_true(less))
    case 1n+p 1n+q:
      lt_succ_le(p, q, less)

def cmp_ge_false(value: Cmp, ge: {Cmp.is_ge(value) == False{} : Bool})
  -> {Cmp.is_lt(value) == True{} : Bool}:
  match value:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, true_false(ge))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, true_false(ge))

# Below the checkpoint and not equal to it after one more token: still below.
def lt_next(c: Nat, bound: Nat, below: {Nat.is_lt(c, bound) == True{} : Bool},
    distinct: {Nat.is_eq(1n+c, bound) == False{} : Bool})
  -> {Nat.is_lt(1n+c, bound) == True{} : Bool}:
  match c bound:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, false_true(below))
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(2n+p, 0n) == True{} : Bool}, false_true(below))
    case 0n 1n+q:
      match q:
        case 0n:
          Empty.absurd({Nat.is_lt(1n, 1n) == True{} : Bool}, true_false(distinct))
        case 1n+r:
          {==}
    case 1n+p 1n+q:
      lt_next(p, q, below, distinct)

def and_left(a: Bool, -b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(both))
    case True{}:
      {==}

def and_right(a: Bool, -b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_true(both))
    case True{}:
      both

def not_true(a: Bool, negated: {Bool.not(a) == True{} : Bool})
  -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, false_true(negated))

def not_or_right(a: Bool, b: Bool,
    negated: {Bool.not(Bool.or(a, b)) == True{} : Bool})
  -> {b == False{} : Bool}:
  match a:
    case False{}:
      not_true(b, negated)
    case True{}:
      Empty.absurd({b == False{} : Bool}, false_true(negated))

def and_equal(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool,
    left: {a == a2 : Bool}, right: {b == b2 : Bool})
  -> {Bool.and(a, b) == Bool.and(a2, b2) : Bool}:
  %left : {Bool.and(a, b) == Bool.and(_, b2) : Bool}
  %right : {Bool.and(a, b) == Bool.and(a, _) : Bool}
  {==}

# Facts-level characterization. decide's counter only offsets the count.
def bump(value: Spec.Verdict) -> Spec.Verdict:
  match value:
    case Spec.Verdict{n, flag}:
      Spec.Verdict{1n+n, flag}

def decide_shift(facts: List<&2, Spec.Facts>, +c: Nat)
  -> {bump(Spec.decide(facts, c)) == Spec.decide(facts, 1n+c) : Spec.Verdict}:
  match facts:
    case Nil{}:
      {==}
    case Spec.Facts{s, e, f, r} <> rest:
      match s:
        case True{}:
          {==}
        case False{}:
          match e:
            case True{}:
              {==}
            case False{}:
              match f:
                case True{}:
                  {==}
                case False{}:
                  match r:
                    case True{}:
                      {==}
                    case False{}:
                      decide_shift(rest, 1n+c)

def fclosed(facts: List<&2, Spec.Facts>) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Spec.Facts{s, e, f, r} <> rest:
      match f:
        case True{}:
          True{}
        case False{}:
          fclosed(rest)

def fpasses(passed: Nat, facts: List<&2, Spec.Facts>) -> Bool:
  match passed:
    case 0n:
      True{}
    case 1n+more:
      match facts:
        case Nil{}:
          False{}
        case Spec.Facts{s, e, f, r} <> rest:
          Bool.and(Bool.not(f), Bool.and(Bool.not(s), Bool.and(Bool.not(e),
            Bool.and(Bool.not(r), fpasses(more, rest)))))

def fhalts(facts: List<&2, Spec.Facts>, passed: Nat, +flag: Bool) -> Bool:
  match facts:
    case Nil{}:
      False{}
    case Spec.Facts{s, e, f, r} <> rest:
      match passed:
        case 0n:
          Bool.and(Bool.or(f, Bool.or(flag, r)), Spec.same(flag, Bool.or(s, e)))
        case 1n+more:
          fhalts(rest, more, flag)

def fexplains(+count: Nat, +flag: Bool, +facts: List<&2, Spec.Facts>) -> Bool:
  match count:
    case 0n:
      False{}
    case 1n+passed:
      Bool.and(fpasses(passed, facts), fhalts(facts, passed, flag))

def explained_step(value: Spec.Verdict, -rest: List<&2, Spec.Facts>,
    known: {fexplains(Spec.count(value), Spec.eos(value), rest) == True{} : Bool})
  -> {fexplains(Spec.count(bump(value)), Spec.eos(bump(value)),
    Spec.Facts{False{}, False{}, False{}, False{}} <> rest) == True{} : Bool}:
  match value:
    case Spec.Verdict{n, flag}:
      match n:
        case 0n:
          Empty.absurd({fexplains(1n, flag,
            Spec.Facts{False{}, False{}, False{}, False{}} <> rest) == True{}
            : Bool}, false_true(known))
        case 1n+m:
          known

def explained_facts(+facts: List<&2, Spec.Facts>,
    closed: {fclosed(facts) == True{} : Bool})
  -> {fexplains(Spec.count(Spec.decide(facts, 0n)),
    Spec.eos(Spec.decide(facts, 0n)), facts) == True{} : Bool}:
  match facts:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, false_true(closed))
    case Spec.Facts{s, e, f, r} <> rest:
      match s:
        case True{}:
          match f:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match e:
            case True{}:
              match f:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match f:
                case True{}:
                  {==}
                case False{}:
                  match r:
                    case True{}:
                      {==}
                    case False{}:
                      %decide_shift(rest, 0n) : {fexplains(Spec.count(_),
                        Spec.eos(_), Spec.Facts{False{}, False{}, False{},
                        False{}} <> rest) == True{} : Bool}
                      explained_step(Spec.decide(rest, 0n), rest,
                        explained_facts(rest, closed))

def lt_bump(passed: Nat, value: Spec.Verdict,
    known: {Nat.is_lt(passed, Spec.count(value)) == True{} : Bool})
  -> {Nat.is_lt(1n+passed, Spec.count(bump(value))) == True{} : Bool}:
  match value:
    case Spec.Verdict{n, flag}:
      known

def positive_bump(value: Spec.Verdict)
  -> {Nat.is_lt(0n, Spec.count(bump(value))) == True{} : Bool}:
  match value:
    case Spec.Verdict{n, flag}:
      {==}

# The maximality goal after one more passing position, named for refutations.
def Nope(more: Nat, facts: List<&2, Spec.Facts>) -> Type:
  {Nat.is_lt(1n+more, Spec.count(Spec.decide(facts, 0n))) == True{} : Bool}

def maximal_facts(+passed: Nat, +facts: List<&2, Spec.Facts>,
    closed: {fclosed(facts) == True{} : Bool},
    passing: {fpasses(passed, facts) == True{} : Bool})
  -> {Nat.is_lt(passed, Spec.count(Spec.decide(facts, 0n))) == True{} : Bool}:
  match passed facts:
    case _ Nil{}:
      Empty.absurd({Nat.is_lt(passed, 0n) == True{} : Bool}, false_true(closed))
    case 0n Spec.Facts{s, e, f, r} <> rest:
      match s:
        case True{}:
          {==}
        case False{}:
          match e:
            case True{}:
              {==}
            case False{}:
              match f:
                case True{}:
                  {==}
                case False{}:
                  match r:
                    case True{}:
                      {==}
                    case False{}:
                      %decide_shift(rest, 0n) : {Nat.is_lt(0n, Spec.count(_)) ==
                        True{} : Bool}
                      positive_bump(Spec.decide(rest, 0n))
    case 1n+more Spec.Facts{s, e, f, r} <> rest:
      match s:
        case True{}:
          match f:
            case True{}:
              Empty.absurd(Nope(more, Spec.Facts{True{}, e, True{}, r} <> rest),
                false_true(passing))
            case False{}:
              Empty.absurd(Nope(more, Spec.Facts{True{}, e, False{}, r} <> rest),
                false_true(passing))
        case False{}:
          match e:
            case True{}:
              match f:
                case True{}:
                  Empty.absurd(Nope(more,
                    Spec.Facts{False{}, True{}, True{}, r} <> rest),
                    false_true(passing))
                case False{}:
                  Empty.absurd(Nope(more,
                    Spec.Facts{False{}, True{}, False{}, r} <> rest),
                    false_true(passing))
            case False{}:
              match f:
                case True{}:
                  Empty.absurd(Nope(more,
                    Spec.Facts{False{}, False{}, True{}, r} <> rest),
                    false_true(passing))
                case False{}:
                  match r:
                    case True{}:
                      Empty.absurd(Nope(more,
                        Spec.Facts{False{}, False{}, False{}, True{}} <> rest),
                        false_true(passing))
                    case False{}:
                      %decide_shift(rest, 0n) : {Nat.is_lt(1n+more,
                        Spec.count(_)) == True{} : Bool}
                      lt_bump(more, Spec.decide(rest, 0n),
                        maximal_facts(more, rest, closed, passing))

# Token-level predicates are the facts-level ones over Spec.facts.
def passes_facts(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat)
  -> {Spec.passes(passed, targets, proposals, stops, committed, budget,
    checkpoint) == fpasses(passed, Spec.facts(targets, proposals, stops,
    committed, budget, checkpoint)) : Bool}:
  match passed:
    case 0n:
      {==}
    case 1n+more:
      match targets:
        case Nil{}:
          {==}
        case +t <> rest:
          match proposals:
            case Nil{}:
              {==}
            case +p <> others:
              Equal.cong(Bool, Bool,
                tail => Bool.and(Bool.not(Spec.member(stops, t)),
                  Bool.and(Bool.not(Nat.is_ge(1n+committed, budget)),
                    Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))), tail))),
                Spec.passes(more, rest, others, stops, 1n+committed, budget,
                  checkpoint),
                fpasses(more, Spec.facts(rest, others, stops, 1n+committed,
                  budget, checkpoint)),
                passes_facts(more, rest, others, stops, 1n+committed, budget,
                  checkpoint))

def halts_facts(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat, +flag: Bool)
  -> {Spec.halts(passed, targets, proposals, stops, committed, budget,
    checkpoint, flag) == fhalts(Spec.facts(targets, proposals, stops,
    committed, budget, checkpoint), passed, flag) : Bool}:
  match passed:
    case 0n:
      match targets:
        case Nil{}:
          {==}
        case t <> rest:
          match proposals:
            case Nil{}:
              {==}
            case p <> others:
              {==}
    case 1n+more:
      match targets:
        case Nil{}:
          {==}
        case t <> rest:
          match proposals:
            case Nil{}:
              {==}
            case p <> others:
              halts_facts(more, rest, others, stops, 1n+committed, budget,
                checkpoint, flag)

def explains_facts(+count: Nat, +flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat)
  -> {Spec.explains(count, flag, targets, proposals, stops, budget,
    checkpoint) == fexplains(count, flag, Spec.facts(targets, proposals,
    stops, 0n, budget, checkpoint)) : Bool}:
  match count:
    case 0n:
      {==}
    case 1n+passed:
      and_equal(
        Spec.passes(passed, targets, proposals, stops, 0n, budget, checkpoint),
        fpasses(passed, Spec.facts(targets, proposals, stops, 0n, budget,
          checkpoint)),
        Spec.halts(passed, targets, proposals, stops, 0n, budget, checkpoint,
          flag),
        fhalts(Spec.facts(targets, proposals, stops, 0n, budget, checkpoint),
          passed, flag),
        passes_facts(passed, targets, proposals, stops, 0n, budget,
          checkpoint),
        halts_facts(passed, targets, proposals, stops, 0n, budget, checkpoint,
          flag))

def closed_facts(+targets: List<&2, U32>, +proposals: List<&2, U32>,
    +stops: List<&2, U32>, +committed: Nat, +budget: Nat, +checkpoint: Nat,
    shaped: {List.length(&2, U32, targets) ==
      1n+List.length(&2, U32, proposals) : Nat})
  -> {fclosed(Spec.facts(targets, proposals, stops, committed, budget,
    checkpoint)) == True{} : Bool}:
  match targets:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool},
        zero_succ(List.length(&2, U32, proposals), shaped))
    case t <> rest:
      match proposals:
        case Nil{}:
          {==}
        case p <> others:
          closed_facts(rest, others, stops, 1n+committed, budget, checkpoint,
            succ_injective(List.length(&2, U32, rest),
              1n+List.length(&2, U32, others), shaped))

def Laws.accept_explained(targets, proposals, stops, budget, checkpoint,
    shaped):
  Equal.trans(Bool,
    Spec.explains(Spec.count(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), Spec.eos(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), targets, proposals, stops, budget, checkpoint),
    fexplains(Spec.count(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), Spec.eos(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), Spec.facts(targets, proposals, stops, 0n, budget,
      checkpoint)),
    True{},
    explains_facts(Spec.count(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), Spec.eos(Spec.accept(targets, proposals, stops, budget,
      checkpoint)), targets, proposals, stops, budget, checkpoint),
    explained_facts(Spec.facts(targets, proposals, stops, 0n, budget,
      checkpoint), closed_facts(targets, proposals, stops, 0n, budget,
      checkpoint, shaped)))

def Laws.accept_maximal(passed, targets, proposals, stops, budget, checkpoint,
    shaped, passing):
  maximal_facts(passed,
    Spec.facts(targets, proposals, stops, 0n, budget, checkpoint),
    closed_facts(targets, proposals, stops, 0n, budget, checkpoint,
      shaped),
    Equal.trans(Bool,
      fpasses(passed, Spec.facts(targets, proposals, stops, 0n, budget,
        checkpoint)),
      Spec.passes(passed, targets, proposals, stops, 0n, budget, checkpoint),
      True{},
      Equal.sym(Bool,
        Spec.passes(passed, targets, proposals, stops, 0n, budget, checkpoint),
        fpasses(passed, Spec.facts(targets, proposals, stops, 0n, budget,
          checkpoint)),
        passes_facts(passed, targets, proposals, stops, 0n, budget,
          checkpoint)),
      passing))

def Laws.accept_progress(targets, proposals, stops, budget, checkpoint,
    shaped):
  Laws.accept_maximal(0n, targets, proposals, stops, budget, checkpoint,
    shaped, {==})

# Bounds read off an explained verdict.
def halts_length(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat, +flag: Bool,
    halting: {Spec.halts(passed, targets, proposals, stops, committed, budget,
      checkpoint, flag) == True{} : Bool})
  -> {Nat.is_lt(passed, List.length(&2, U32, targets)) == True{} : Bool}:
  match passed:
    case 0n:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, false_true(halting))
        case t <> rest:
          {==}
    case 1n+more:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_lt(1n+more, 0n) == True{} : Bool},
            false_true(halting))
        case t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd({Nat.is_lt(1n+more,
                1n+List.length(&2, U32, rest)) == True{} : Bool},
                false_true(halting))
            case p <> others:
              halts_length(more, rest, others, stops, 1n+committed, budget,
                checkpoint, flag, halting)

def halts_proposals(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat, +flag: Bool,
    halting: {Spec.halts(passed, targets, proposals, stops, committed, budget,
      checkpoint, flag) == True{} : Bool})
  -> {Nat.is_le(passed, List.length(&2, U32, proposals)) == True{} : Bool}:
  match passed:
    case 0n:
      le_zero(List.length(&2, U32, proposals))
    case 1n+more:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_le(1n+more, List.length(&2, U32, proposals)) ==
            True{} : Bool}, false_true(halting))
        case t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd({Nat.is_le(1n+more, 0n) == True{} : Bool},
                false_true(halting))
            case p <> others:
              halts_proposals(more, rest, others, stops, 1n+committed, budget,
                checkpoint, flag, halting)

# The last passing position of 1 + passed passing positions is below budget.
def passes_budget(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat,
    passing: {Spec.passes(1n+passed, targets, proposals, stops, committed,
      budget, checkpoint) == True{} : Bool})
  -> {Nat.is_lt(1n+Nat.add(passed, committed), budget) == True{} : Bool}:
  match passed:
    case 0n:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_lt(1n+committed, budget) == True{} : Bool},
            false_true(passing))
        case +t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd({Nat.is_lt(1n+committed, budget) == True{} : Bool},
                false_true(passing))
            case +p <> others:
              cmp_ge_false(Nat.cmp(1n+committed, budget),
                not_true(Nat.is_ge(1n+committed, budget),
                  and_left(Bool.not(Nat.is_ge(1n+committed, budget)),
                    Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))), True{}),
                    and_right(Bool.not(Spec.member(stops, t)),
                      Bool.and(Bool.not(Nat.is_ge(1n+committed, budget)),
                        Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                          Nat.is_eq(1n+committed, checkpoint))), True{})),
                      passing))))
    case 1n+more:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_lt(2n+Nat.add(more, committed), budget) ==
            True{} : Bool}, false_true(passing))
        case +t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd({Nat.is_lt(2n+Nat.add(more, committed), budget) ==
                True{} : Bool}, false_true(passing))
            case +p <> others:
              %add_succ(more, committed) : {Nat.is_lt(1n+_, budget) == True{}
                : Bool}
              passes_budget(more, rest, others, stops, 1n+committed, budget,
                checkpoint,
                and_right(Bool.not(Bool.or(U32.is_ne(p, t),
                  Nat.is_eq(1n+committed, checkpoint))),
                  Spec.passes(1n+more, rest, others, stops, 1n+committed,
                    budget, checkpoint),
                  and_right(Bool.not(Nat.is_ge(1n+committed, budget)),
                    Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))),
                      Spec.passes(1n+more, rest, others, stops, 1n+committed,
                        budget, checkpoint)),
                    and_right(Bool.not(Spec.member(stops, t)),
                      Bool.and(Bool.not(Nat.is_ge(1n+committed, budget)),
                        Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                          Nat.is_eq(1n+committed, checkpoint))),
                          Spec.passes(1n+more, rest, others, stops,
                            1n+committed, budget, checkpoint))), passing))))

# Starting below the checkpoint, passing positions stay below it.
def passes_checkpoint(+passed: Nat, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +committed: Nat,
    +budget: Nat, +checkpoint: Nat,
    passing: {Spec.passes(passed, targets, proposals, stops, committed,
      budget, checkpoint) == True{} : Bool},
    below: {Nat.is_lt(committed, checkpoint) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(passed, committed), checkpoint) == True{} : Bool}:
  match passed:
    case 0n:
      below
    case 1n+more:
      match targets:
        case Nil{}:
          Empty.absurd({Nat.is_lt(1n+Nat.add(more, committed), checkpoint) ==
            True{} : Bool}, false_true(passing))
        case +t <> rest:
          match proposals:
            case Nil{}:
              Empty.absurd({Nat.is_lt(1n+Nat.add(more, committed),
                checkpoint) == True{} : Bool}, false_true(passing))
            case +p <> others:
              +tail = and_right(Bool.not(Nat.is_ge(1n+committed, budget)),
                Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                  Nat.is_eq(1n+committed, checkpoint))),
                  Spec.passes(more, rest, others, stops, 1n+committed, budget,
                    checkpoint)),
                and_right(Bool.not(Spec.member(stops, t)),
                  Bool.and(Bool.not(Nat.is_ge(1n+committed, budget)),
                    Bool.and(Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))),
                      Spec.passes(more, rest, others, stops, 1n+committed,
                        budget, checkpoint))), passing))
              %add_succ(more, committed) : {Nat.is_lt(_, checkpoint) ==
                True{} : Bool}
              passes_checkpoint(more, rest, others, stops, 1n+committed,
                budget, checkpoint,
                and_right(Bool.not(Bool.or(U32.is_ne(p, t),
                  Nat.is_eq(1n+committed, checkpoint))),
                  Spec.passes(more, rest, others, stops, 1n+committed, budget,
                    checkpoint), tail),
                lt_next(committed, checkpoint, below,
                  not_or_right(U32.is_ne(p, t), Nat.is_eq(1n+committed,
                    checkpoint),
                    and_left(Bool.not(Bool.or(U32.is_ne(p, t),
                      Nat.is_eq(1n+committed, checkpoint))),
                      Spec.passes(more, rest, others, stops, 1n+committed,
                        budget, checkpoint), tail))))

def lt_add_zero(passed: Nat, -bound: Nat,
    less: {Nat.is_lt(Nat.add(passed, 0n), bound) == True{} : Bool})
  -> {Nat.is_lt(passed, bound) == True{} : Bool}:
  %add_zero(passed) : {Nat.is_lt(_, bound) == True{} : Bool}
  less

def explains_bounds(+count: Nat, +flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat,
    explained: {Spec.explains(count, flag, targets, proposals, stops, budget,
      checkpoint) == True{} : Bool})
  -> {Nat.is_le(count, List.length(&2, U32, targets)) == True{} : Bool} &
    {Nat.is_le(count, 1n+List.length(&2, U32, proposals)) == True{} : Bool}:
  match count:
    case 0n:
      Empty.absurd({Nat.is_le(0n, List.length(&2, U32, targets)) == True{}
        : Bool} & {Nat.is_le(0n, 1n+List.length(&2, U32, proposals)) ==
        True{} : Bool}, false_true(explained))
    case 1n+passed:
      +halting = and_right(
        Spec.passes(passed, targets, proposals, stops, 0n, budget, checkpoint),
        Spec.halts(passed, targets, proposals, stops, 0n, budget, checkpoint,
          flag), explained)
      (lt_succ_le(passed, List.length(&2, U32, targets),
        halts_length(passed, targets, proposals, stops, 0n, budget,
          checkpoint, flag, halting)),
       halts_proposals(passed, targets, proposals, stops, 0n, budget,
         checkpoint, flag, halting))

def explains_budget(+count: Nat, +flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat,
    explained: {Spec.explains(count, flag, targets, proposals, stops, budget,
      checkpoint) == True{} : Bool},
    positive: {Nat.is_lt(0n, budget) == True{} : Bool})
  -> {Nat.is_le(count, budget) == True{} : Bool}:
  match count:
    case 0n:
      Empty.absurd({Nat.is_le(0n, budget) == True{} : Bool},
        false_true(explained))
    case 1n+passed:
      match passed:
        case 0n:
          lt_succ_le(0n, budget, positive)
        case 1n+more:
          lt_succ_le(1n+more, budget,
            lt_add_zero(1n+more, budget,
              passes_budget(more, targets, proposals, stops, 0n, budget,
                checkpoint,
                and_left(Spec.passes(1n+more, targets, proposals, stops, 0n,
                  budget, checkpoint), Spec.halts(1n+more, targets, proposals,
                  stops, 0n, budget, checkpoint, flag), explained))))

def explains_checkpoint(+count: Nat, +flag: Bool, +targets: List<&2, U32>,
    +proposals: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat,
    explained: {Spec.explains(count, flag, targets, proposals, stops, budget,
      checkpoint) == True{} : Bool},
    positive: {Nat.is_lt(0n, checkpoint) == True{} : Bool})
  -> {Nat.is_le(count, checkpoint) == True{} : Bool}:
  match count:
    case 0n:
      Empty.absurd({Nat.is_le(0n, checkpoint) == True{} : Bool},
        false_true(explained))
    case 1n+passed:
      lt_succ_le(passed, checkpoint,
        lt_add_zero(passed, checkpoint,
          passes_checkpoint(passed, targets, proposals, stops, 0n, budget,
            checkpoint,
            and_left(Spec.passes(passed, targets, proposals, stops, 0n, budget,
              checkpoint), Spec.halts(passed, targets, proposals, stops, 0n,
              budget, checkpoint, flag), explained), positive)))

def Laws.accept_bounds(targets, proposals, stops, budget, checkpoint, shaped):
  explains_bounds(
    Spec.count(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    Spec.eos(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    targets, proposals, stops, budget, checkpoint,
    Laws.accept_explained(targets, proposals, stops, budget, checkpoint,
      shaped))

def Laws.accept_budget(targets, proposals, stops, budget, checkpoint, shaped,
    positive):
  explains_budget(
    Spec.count(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    Spec.eos(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    targets, proposals, stops, budget, checkpoint,
    Laws.accept_explained(targets, proposals, stops, budget, checkpoint,
      shaped), positive)

def Laws.accept_checkpoint(targets, proposals, stops, budget, checkpoint,
    shaped, positive):
  explains_checkpoint(
    Spec.count(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    Spec.eos(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    targets, proposals, stops, budget, checkpoint,
    Laws.accept_explained(targets, proposals, stops, budget, checkpoint,
      shaped), positive)

# The register lists have k + 1 targets for k proposals for every k: take
# stops at eight targets and seven proposals together.
def shaped_take(+k: Nat, -t0: U32, -t1: U32, -t2: U32, -t3: U32, -t4: U32,
    -t5: U32, -t6: U32, -t7: U32, -p0: U32, -p1: U32, -p2: U32, -p3: U32,
    -p4: U32, -p5: U32, -p6: U32)
  -> {List.length(&2, U32, List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7],
      1n+k)) ==
    1n+List.length(&2, U32, List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k))
    : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          {==}
        case 1n+k2:
          match k2:
            case 0n:
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  {==}
                case 1n+k4:
                  match k4:
                    case 0n:
                      {==}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          {==}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              {==}
                            case 1n+k7:
                              {==}

def Laws.leaf_explained(k, valid, budget, checkpoint, ns, s0, s1, s2, s3, t0,
    t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6):
  %Equal.sym(Spec.Verdict,
    Impl.accept(k, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4,
      t5, t6, t7, p0, p1, p2, p3, p4, p5, p6),
    Spec.accept(List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
      List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
      List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint),
    Laws.leaf_refinement(k, valid, budget, checkpoint, ns, s0, s1, s2, s3, t0,
      t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6)) :
    {Spec.explains(Spec.count(_), Spec.eos(_),
      List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
      List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
      List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint) == True{}
      : Bool}
  Laws.accept_explained(
    List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
    List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
    List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint,
    shaped_take(k, t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5,
      p6))

def Laws.leaf_maximal(passed, k, valid, budget, checkpoint, ns, s0, s1, s2, s3,
    t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6, passing):
  %Equal.sym(Spec.Verdict,
    Impl.accept(k, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4,
      t5, t6, t7, p0, p1, p2, p3, p4, p5, p6),
    Spec.accept(List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
      List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
      List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint),
    Laws.leaf_refinement(k, valid, budget, checkpoint, ns, s0, s1, s2, s3, t0,
      t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6)) :
    {Nat.is_lt(passed, Spec.count(_)) == True{} : Bool}
  Laws.accept_maximal(passed,
    List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
    List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
    List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint,
    shaped_take(k, t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5,
      p6), passing)
