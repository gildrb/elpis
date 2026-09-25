# Proofs of ext 8204's deferred phase-1 publish laws (mlp_m16_defer_laws.bend) about the Bend model
# mlp_m16_defer.bend. Structural evidence only: no unsafe definitions, axioms, holes or foreign proof
# code; the ext 8201 counter facts come from the proven mlp_m16_sched laws, the ext 8202 embedding
# from the proven tail_m16_sched law. Every def precedes its uses.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_proof.bend as PP
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_sched_laws.bend as MLaws
import ./mlp_m16_sched_proof.bend as MP
import ./tail_m16_sched.bend as Tail
import ./tail_m16_sched_spec.bend as TSpec
import ./tail_m16_sched_laws.bend as TLaws
import ./tail_m16_sched_proof.bend as TP
import ./mlp_m16_defer.bend as Impl
import ./mlp_m16_defer_spec.bend as Spec
import ./mlp_m16_defer_laws.bend as Laws

# ==== (1) projections ====

def sy_work(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>)
  -> {Spec.syncs(rest) == Spec.syncs(Impl.tag_work(evs, rest)) : List<&2, MSpec.Ev>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      sy_work(more, rest)

def sy_sync(+evs: List<&2, MSpec.Ev>)
  -> {Spec.syncs(Impl.tag_sync(evs, Nil{})) == evs : List<&2, MSpec.Ev>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      %sy_sync(more)
        : {ev <> Spec.syncs(Impl.tag_sync(more, Nil{})) == ev <> _ : List<&2, MSpec.Ev>}
      {==}

def sy_sync_sym(+evs: List<&2, MSpec.Ev>)
  -> {evs == Spec.syncs(Impl.tag_sync(evs, Nil{})) : List<&2, MSpec.Ev>}:
  Equal.sym(List<&2, MSpec.Ev>, Spec.syncs(Impl.tag_sync(evs, Nil{})), evs, sy_sync(evs))

def wk_work(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>,
    +h: {Spec.works(rest) == Nil{} : List<&2, PSpec.Ev>})
  -> {Spec.works(Impl.tag_work(evs, rest)) == evs : List<&2, PSpec.Ev>}:
  match evs:
    case Nil{}:
      h
    case ev <> more:
      %wk_work(more, rest, h)
        : {ev <> Spec.works(Impl.tag_work(more, rest)) == ev <> _ : List<&2, PSpec.Ev>}
      {==}

def wk_sync(+evs: List<&2, MSpec.Ev>, +rest: List<&2, Spec.Ev>)
  -> {Spec.works(Impl.tag_sync(evs, rest)) == Spec.works(rest) : List<&2, PSpec.Ev>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      wk_sync(more, rest)

def Laws.defer_syncs(G, H, I, b):
  +ML = Impl.mainloop1(G, H, I, b)
  +EV = Mlp.events(G, H, I, b)
  +R = {Impl.tag_sync(EV, Nil{}) : List<&2, Spec.Ev>}
  %sy_work(ML, R) : {_ == EV : List<&2, MSpec.Ev>}
  sy_sync(EV)

def Laws.defer_works(G, H, I, b):
  +ML = Impl.mainloop1(G, H, I, b)
  +EV = Mlp.events(G, H, I, b)
  wk_work(ML, Impl.tag_sync(EV, Nil{}), wk_sync(EV, Nil{}))

# The per-flush order: its counter events are sigs1 of the main loop over the tail's events ...
def eg_sy(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>)
  -> {Mlp.sigs1(evs, Spec.syncs(rest)) == Spec.syncs(Impl.eager.go(evs, rest)) : List<&2, MSpec.Ev>}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          eg_sy(more, rest)
        case PSpec.Flush{g}:
          %eg_sy(more, rest)
            : {MSpec.Sig{MSpec.C1{g}, 8n, 0n} <> Mlp.sigs1(more, Spec.syncs(rest)) ==
              MSpec.Sig{MSpec.C1{g}, 8n, 0n} <> _ : List<&2, MSpec.Ev>}
          {==}

# ... and its main-loop events are the main loop.
def eg_wk(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>,
    +h: {Spec.works(rest) == Nil{} : List<&2, PSpec.Ev>})
  -> {Spec.works(Impl.eager.go(evs, rest)) == evs : List<&2, PSpec.Ev>}:
  match evs:
    case Nil{}:
      h
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          %eg_wk(more, rest, h)
            : {PSpec.Tile{g, it} <> Spec.works(Impl.eager.go(more, rest)) ==
              PSpec.Tile{g, it} <> _ : List<&2, PSpec.Ev>}
          {==}
        case PSpec.Flush{g}:
          %eg_wk(more, rest, h)
            : {PSpec.Flush{g} <> Spec.works(Impl.eager.go(more, rest)) ==
              PSpec.Flush{g} <> _ : List<&2, PSpec.Ev>}
          {==}

def Laws.eager_same_events(G, H, I, b):
  +ML = Impl.mainloop1(G, H, I, b)
  +F = Mlp.finish(Mlp.pairs(I), Mlp.fin_pair(G, H, I, b), Mlp.waits2(Mlp.waits(G, H, I, b)))
  +R = {Impl.tag_sync(F, Nil{}) : List<&2, Spec.Ev>}
  (%eg_sy(ML, R) : {_ == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>}
    %sy_sync_sym(F) : {Mlp.sigs1(ML, _) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>}
    {==},
    eg_wk(ML, R, wk_sync(F, Nil{})))

# ==== (2) publish after flush ====

# The flushed groups after a main-loop prefix, onto `seen`.
def acc(+evs: List<&2, PSpec.Ev>, +seen: List<&2, Nat>) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      seen
    case ev <> more:
      acc(more, Spec.note(ev, seen))

# Every flushed group of the list is in `seen`.
def covers(+evs: List<&2, PSpec.Ev>, +seen: List<&2, Nat>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          covers(more, seen)
        case PSpec.Flush{g}:
          Bool.and(MSpec.member(seen, g), covers(more, seen))

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def member_self(+g: Nat, +seen: List<&2, Nat>) -> {MSpec.member(g <> seen, g) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(g, g), True{}, PP.ar_eq_refl(g))
    : {Bool.or(_, MSpec.member(seen, g)) == True{} : Bool}
  {==}

def member_cons(+g: Nat, +seen: List<&2, Nat>, +x: Nat, h: {MSpec.member(seen, x) == True{} : Bool})
  -> {MSpec.member(g <> seen, x) == True{} : Bool}:
  %Equal.sym(Bool, MSpec.member(seen, x), True{}, h)
    : {Bool.or(Nat.is_eq(g, x), _) == True{} : Bool}
  or_true_r(Nat.is_eq(g, x))

# acc only grows `seen`.
def acc_mono(+evs: List<&2, PSpec.Ev>, +seen: List<&2, Nat>, +x: Nat,
    h: {MSpec.member(seen, x) == True{} : Bool})
  -> {MSpec.member(acc(evs, seen), x) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          acc_mono(more, seen, x, h)
        case PSpec.Flush{g}:
          acc_mono(more, g <> seen, x, member_cons(g, seen, x, h))

# The flushes of a list are covered by the groups it accumulates.
def acc_covers(+evs: List<&2, PSpec.Ev>, +seen: List<&2, Nat>)
  -> {covers(evs, acc(evs, seen)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          acc_covers(more, seen)
        case PSpec.Flush{g}:
          PP.ar_and_intro(MSpec.member(acc(more, g <> seen), g), covers(more, acc(more, g <> seen)),
            acc_mono(more, g <> seen, g, member_self(g, seen)),
            acc_covers(more, g <> seen))

# Through the main-loop prefix of the deferred program, `seen` becomes acc.
def pw_work(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +seen: List<&2, Nat>)
  -> {Spec.pub_after_flush(rest, acc(evs, seen)) ==
    Spec.pub_after_flush(Impl.tag_work(evs, rest), seen) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      pw_work(more, rest, Spec.note(ev, seen))

# The phase-1 signals of sigs1 are all allowed once their groups are covered.
def pw_sigs(+evs: List<&2, PSpec.Ev>, +f: List<&2, MSpec.Ev>, +seen: List<&2, Nat>,
    +h: {covers(evs, seen) == True{} : Bool})
  -> {Spec.pub_after_flush(Impl.tag_sync(f, Nil{}), seen) ==
    Spec.pub_after_flush(Impl.tag_sync(Mlp.sigs1(evs, f), Nil{}), seen) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          pw_sigs(more, f, seen, h)
        case PSpec.Flush{g}:
          +hm = PP.ar_and_l(MSpec.member(seen, g), covers(more, seen), h)
          +hc = PP.ar_and_r(MSpec.member(seen, g), covers(more, seen), h)
          %Equal.sym(Bool, MSpec.member(seen, g), True{}, hm)
            : {Spec.pub_after_flush(Impl.tag_sync(f, Nil{}), seen) ==
              Bool.and(_, Spec.pub_after_flush(Impl.tag_sync(Mlp.sigs1(more, f), Nil{}), seen)) : Bool}
          pw_sigs(more, f, seen, hc)

# The phase-2 waits never constrain.
def pw_waits(+ws: List<&2, Nat>, +seen: List<&2, Nat>)
  -> {Spec.pub_after_flush(Impl.tag_sync(Mlp.waits2(ws), Nil{}), seen) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case p <> rest:
      pw_waits(rest, seen)

# Nor does the finish (cnt1 waits, cnt2 signal).
def pw_finish(+np: Nat, +p: Nat, +ws: List<&2, Nat>, +seen: List<&2, Nat>)
  -> {Spec.pub_after_flush(Impl.tag_sync(Mlp.finish(np, p, Mlp.waits2(ws)), Nil{}), seen) == True{}
    : Bool}:
  pw_waits(ws, seen)

def Laws.defer_pub_after_flush(G, H, I, b):
  +ML = Impl.mainloop1(G, H, I, b)
  +np = Mlp.pairs(I)
  +p = Mlp.fin_pair(G, H, I, b)
  +ws = Mlp.waits(G, H, I, b)
  +F = Mlp.finish(np, p, Mlp.waits2(ws))
  +S = acc(ML, Nil{})
  %pw_work(ML, Impl.tag_sync(Mlp.sigs1(ML, F), Nil{}), Nil{}) : {_ == True{} : Bool}
  %pw_sigs(ML, F, S, acc_covers(ML, Nil{})) : {_ == True{} : Bool}
  pw_finish(np, p, ws, S)

# The per-flush order: each Sig{C1{g}} directly follows Flush{g}.
def pw_eager(+evs: List<&2, PSpec.Ev>, +rest: List<&2, Spec.Ev>, +seen: List<&2, Nat>)
  -> {Spec.pub_after_flush(rest, acc(evs, seen)) ==
    Spec.pub_after_flush(Impl.eager.go(evs, rest), seen) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          pw_eager(more, rest, seen)
        case PSpec.Flush{g}:
          %Equal.sym(Bool, MSpec.member(g <> seen, g), True{}, member_self(g, seen))
            : {Spec.pub_after_flush(rest, acc(more, g <> seen)) ==
              Bool.and(_, Spec.pub_after_flush(Impl.eager.go(more, rest), g <> seen)) : Bool}
          pw_eager(more, rest, g <> seen)

def Laws.eager_pub_after_flush(G, H, I, b):
  +ML = Impl.mainloop1(G, H, I, b)
  +np = Mlp.pairs(I)
  +p = Mlp.fin_pair(G, H, I, b)
  +ws = Mlp.waits(G, H, I, b)
  +F = Mlp.finish(np, p, Mlp.waits2(ws))
  %pw_eager(ML, Impl.tag_sync(F, Nil{}), Nil{}) : {_ == True{} : Bool}
  pw_finish(np, p, ws, acc(ML, Nil{}))

# ==== (3) levels, through the projection ====

def dsym(+G: Nat, +H: Nat, +I: Nat, +b: Nat)
  -> {Mlp.events(G, H, I, b) == Spec.syncs(Impl.events(G, H, I, b)) : List<&2, MSpec.Ev>}:
  Equal.sym(List<&2, MSpec.Ev>, Spec.syncs(Impl.events(G, H, I, b)), Mlp.events(G, H, I, b),
    Laws.defer_syncs(G, H, I, b))

def Laws.defer_levels(G, H, I, b, d, c):
  +gl = MLaws.gate_level(c)
  (%dsym(G, H, I, b) : {MSpec.ordered(_, 0n) == True{} : Bool}
    MLaws.events_ordered(G, H, I, b),
    %dsym(G, H, I, d) : {MSpec.sigs_below(_, c, gl) == True{} : Bool}
    PP.ard_fst({MSpec.sigs_below(Mlp.events(G, H, I, d), c, gl) == True{} : Bool},
      {MSpec.waits_from(Mlp.events(G, H, I, b), c, gl) == True{} : Bool},
      MLaws.signals_before_waits(G, H, I, b, d, c)),
    %dsym(G, H, I, b) : {MSpec.waits_from(_, c, gl) == True{} : Bool}
    PP.ard_snd({MSpec.sigs_below(Mlp.events(G, H, I, d), c, gl) == True{} : Bool},
      {MSpec.waits_from(Mlp.events(G, H, I, b), c, gl) == True{} : Bool},
      MLaws.signals_before_waits(G, H, I, b, d, c)))

# ==== (4) grid totals equal 8201's ====

def sig_same(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: MSpec.Ctr)
  -> {MLaws.sig_total(G, H, I, n, c) == Laws.sig_total(G, H, I, n, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      %sig_same(G, H, I, b, c)
        : {Nat.add(MLaws.sig_total(G, H, I, b, c), MSpec.sig_amount(Mlp.events(G, H, I, b), c)) ==
          Nat.add(_, MSpec.sig_amount(Spec.syncs(Impl.events(G, H, I, b)), c)) : Nat}
      %dsym(G, H, I, b)
        : {Nat.add(MLaws.sig_total(G, H, I, b, c), MSpec.sig_amount(Mlp.events(G, H, I, b), c)) ==
          Nat.add(MLaws.sig_total(G, H, I, b, c), MSpec.sig_amount(_, c)) : Nat}
      {==}

def wait_same(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: MSpec.Ctr)
  -> {MLaws.wait_total(G, H, I, n, c) == Laws.wait_total(G, H, I, n, c) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+b:
      %wait_same(G, H, I, b, c)
        : {Nat.add(MLaws.wait_total(G, H, I, b, c), MSpec.wait_amount(Mlp.events(G, H, I, b), c)) ==
          Nat.add(_, MSpec.wait_amount(Spec.syncs(Impl.events(G, H, I, b)), c)) : Nat}
      %dsym(G, H, I, b)
        : {Nat.add(MLaws.wait_total(G, H, I, b, c), MSpec.wait_amount(Mlp.events(G, H, I, b), c)) ==
          Nat.add(MLaws.wait_total(G, H, I, b, c), MSpec.wait_amount(_, c)) : Nat}
      {==}

def Laws.defer_gate_signals(G, H, I, p, grid, shaped, fits, pair):
  %sig_same(G, H, I, G, MSpec.C1{p}) : {_ == Mlp.exp_gate(G, H, I, p) : Nat}
  MLaws.gate_signals(G, H, I, p, grid, shaped, fits, pair)

def Laws.defer_up_signals(G, H, I, p, grid, shaped, fits, pair):
  %sig_same(G, H, I, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) : {_ == Mlp.exp_up(G, H, I, p) : Nat}
  MLaws.up_signals(G, H, I, p, grid, shaped, fits, pair)

def Laws.defer_finish_signals(G, H, I, p):
  %sig_same(G, H, I, G, MSpec.C2{p}) : {_ == Mlp.exp2(G, H, I, p) : Nat}
  MLaws.finish_signals(G, H, I, p)

def Laws.defer_gate_waiters(G, H, I, p, pair):
  %wait_same(G, H, I, G, MSpec.C1{p}) : {_ == Mlp.wait1(G, H, I, p) : Nat}
  MLaws.gate_waiters(G, H, I, p, pair)

def Laws.defer_up_waiters(G, H, I, p, shaped, groups):
  %wait_same(G, H, I, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) : {_ == Mlp.wait1(G, H, I, p) : Nat}
  MLaws.up_waiters(G, H, I, p, shaped, groups)

def Laws.defer_pair_waiters(G, H, I, p):
  %wait_same(G, H, I, G, MSpec.C2{p}) : {_ == Mlp.wait2(G, H, I, p) : Nat}
  MLaws.pair_waiters(G, H, I, p)

# ==== (5) the layer tail ====

def Laws.tail_defer_syncs(G, A, H, I, m, b):
  Equal.trans(List<&2, MSpec.Ev>, TSpec.syncs(Tail.events(G, A, H, I, m, b)), Mlp.events(G, H, I, b),
    Spec.syncs(Impl.events(G, H, I, b)), TLaws.embeds_8201(G, A, H, I, m, b), dsym(G, H, I, b))
