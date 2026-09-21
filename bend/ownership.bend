# Total ownership transitions over unbounded identities and counters.
# Structural zero tests avoid summing counters; the independent reference
# instead specifies quiescence by a zero total. This module imports its data
# vocabulary only: no Spec executable function is called.
# Not connected to CUDA: authenticated generations, aliases and completion
# observations are obligations, not values available in native metadata.
import Base
import ./ownership_spec.bend as Spec

def counts(ledger: Spec.Ledger) -> Spec.Counts:
  Spec.Ledger{page, generation, owner, dummy, activity} = ledger
  activity

def reference_count(ledger: Spec.Ledger) -> Nat:
  Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
  shared

def reader_count(ledger: Spec.Ledger) -> Nat:
  Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, active, writers}} = ledger
  active

def writer_count(ledger: Spec.Ledger) -> Nat:
  Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, active}} = ledger
  active

def quiet(activity: Spec.Counts) -> Bool:
  match activity:
    case Spec.Counts{0n, 0n, 0n}:
      True{}
    case _:
      False{}

def nonzero(page: Nat) -> Bool:
  match page:
    case 0n:
      False{}
    case 1n+p:
      True{}

def ordinary(ledger: Spec.Ledger) -> Bool:
  Spec.Ledger{page, generation, owner, dummy, activity} = ledger
  Bool.and(nonzero(page), Bool.not(dummy))

def same(left: Spec.Lease, right: Spec.Lease) -> Bool:
  Spec.Lease{lp, lg, lo} = left
  Spec.Lease{rp, rg, ro} = right
  Bool.and(Nat.is_eq(lp, rp), Bool.and(Nat.is_eq(lg, rg), Nat.is_eq(lo, ro)))

def access(+ledger: Spec.Ledger, request: Spec.Request) -> Bool:
  match ledger request:
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity} Spec.Present{lease}:
      Bool.and(ordinary(ledger), same(Spec.Lease{page, generation, identity}, lease))
    case _ _:
      False{}

def vacant(ledger: Spec.Ledger) -> Bool:
  match ledger:
    case Spec.Ledger{page, generation, None{}, dummy, activity}:
      Bool.and(Bool.and(nonzero(page), Bool.not(dummy)), quiet(activity))
    case _:
      False{}

def fresh(request: Spec.Request) -> Bool:
  match request:
    case Spec.Missing{}:
      True{}
    case _:
      False{}

def permitted(action: Spec.Action, +ledger: Spec.Ledger, request: Spec.Request) -> Bool:
  match action:
    case Spec.Allocate{identity}:
      Bool.and(vacant(ledger), fresh(request))
    case Spec.Reserve{identity}:
      Bool.and(vacant(ledger), fresh(request))
    case Spec.Release{}:
      Bool.and(quiet(counts(ledger)), access(ledger, request))
    case Spec.Share{}:
      Bool.and(Nat.is_eq(writer_count(ledger), 0n), access(ledger, request))
    case Spec.Unshare{}:
      Bool.and(nonzero(reference_count(ledger)), access(ledger, request))
    case Spec.StartRead{}:
      Bool.and(Nat.is_eq(writer_count(ledger), 0n), access(ledger, request))
    case Spec.FinishRead{}:
      Bool.and(nonzero(reader_count(ledger)), access(ledger, request))
    case Spec.StartWrite{}:
      Bool.and(quiet(counts(ledger)), access(ledger, request))
    case Spec.FinishWrite{}:
      Bool.and(nonzero(writer_count(ledger)), access(ledger, request))

# Saturating predecessor is unreachable on an admitted decrement at zero.
def candidate(action: Spec.Action, ledger: Spec.Ledger) -> Spec.Ledger:
  match action:
    case Spec.Allocate{identity}:
      Spec.Ledger{page, generation, owner, dummy, activity} = ledger
      Spec.Ledger{page, 1n+generation, Some{identity}, False{}, Spec.Counts{0n, 0n, 0n}}
    case Spec.Reserve{identity}:
      Spec.Ledger{page, generation, owner, dummy, activity} = ledger
      Spec.Ledger{page, 1n+generation, Some{identity}, True{}, Spec.Counts{0n, 0n, 0n}}
    case Spec.Release{}:
      Spec.Ledger{page, generation, owner, dummy, activity} = ledger
      Spec.Ledger{page, generation, None{}, False{}, Spec.Counts{0n, 0n, 0n}}
    case Spec.Share{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{1n+shared, readers, writers}}
    case Spec.Unshare{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{Nat.sub(shared, 1n), readers, writers}}
    case Spec.StartRead{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, 1n+readers, writers}}
    case Spec.FinishRead{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, Nat.sub(readers, 1n), writers}}
    case Spec.StartWrite{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, 1n+writers}}
    case Spec.FinishWrite{}:
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}} = ledger
      Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, Nat.sub(writers, 1n)}}

def choose(valid: Bool, action: Spec.Action, ledger: Spec.Ledger) -> Maybe<&2, Spec.Ledger>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{candidate(action, ledger)}

def transition(+action: Spec.Action, +ledger: Spec.Ledger, request: Spec.Request) -> Maybe<&2, Spec.Ledger>:
  choose(permitted(action, ledger, request), action, ledger)

# Every finish must authenticate actual matching completion. A launch return,
# status mirror or epoch does not establish these propositions. Native has no
# generation-bearing leases or per-page reader/reference counters today.
def disjoint(token: Spec.Token) -> Bool:
  match token:
    case Spec.Conflict{}:
      False{}
    case _:
      True{}

def consistent(tokens: List<&2, Spec.Token>) -> Bool:
  match tokens:
    case Nil{}:
      True{}
    case token <> rest:
      Bool.and(disjoint(token), consistent(rest))

def immutable(tokens: List<&2, Spec.Token>) -> Bool:
  match tokens:
    case Nil{}:
      True{}
    case Spec.Committed{} <> rest:
      immutable(rest)
    case Spec.Hole{} <> rest:
      immutable(rest)
    case _:
      False{}

def complete(width: Nat, tokens: List<&2, Spec.Token>, +sealed: Bool) -> Bool:
  match width tokens:
    case 0n Nil{}:
      True{}
    case 1n+p Spec.Committed{} <> rest:
      complete(p, rest, sealed)
    case 1n+p Spec.Provisional{} <> rest:
      Bool.and(Bool.not(sealed), complete(p, rest, sealed))
    case _ _:
      False{}

def invalidate(representation: Spec.Representation) -> Spec.Representation:
  match representation:
    case Spec.Preview{slot}:
      Spec.Raw{slot}
    case other:
      other

def has_preview(representation: Spec.Representation) -> Bool:
  match representation:
    case Spec.Preview{slot}:
      True{}
    case _:
      False{}

def discard(tokens: List<&2, Spec.Token>) -> List<&2, Spec.Token>:
  match tokens:
    case Nil{}:
      Nil{}
    case Spec.Provisional{} <> rest:
      Spec.Hole{} <> discard(rest)
    case other <> rest:
      other <> discard(rest)

def token_edit(edit: Spec.Edit, token: Spec.Token) -> Maybe<&2, Spec.Token>:
  match edit token:
    case Spec.Stage{offset} Spec.Hole{}:
      Some{Spec.Provisional{}}
    case Spec.Stage{offset} Spec.Provisional{}:
      Some{Spec.Provisional{}}
    case Spec.Commit{offset} Spec.Provisional{}:
      Some{Spec.Committed{}}
    case _ _:
      None{}

def prepend(updated: Maybe<&2, List<&2, Spec.Token>>, token: Spec.Token) -> Maybe<&2, List<&2, Spec.Token>>:
  match updated:
    case None{}:
      None{}
    case Some{tokens}:
      Some{token <> tokens}

def replace_head(updated: Maybe<&2, Spec.Token>, rest: List<&2, Spec.Token>) -> Maybe<&2, List<&2, Spec.Token>>:
  match updated:
    case None{}:
      None{}
    case Some{token}:
      Some{token <> rest}

def replace(edit: Spec.Edit, offset: Nat, tokens: List<&2, Spec.Token>) -> Maybe<&2, List<&2, Spec.Token>>:
  match offset tokens:
    case 0n token <> rest:
      replace_head(token_edit(edit, token), rest)
    case 1n+p token <> rest:
      prepend(replace(edit, p, rest), token)
    case _ Nil{}:
      None{}

def editing(+ledger: Spec.Ledger, request: Spec.Request) -> Bool:
  match ledger:
    case Spec.Ledger{page, generation, owner, dummy, Spec.Counts{0n, 0n, 1n+w}}:
      Bool.and(Nat.is_eq(w, 0n), access(ledger, request))
    case _:
      False{}

def edited_tokens(edit: Spec.Edit, tokens: List<&2, Spec.Token>) -> Maybe<&2, List<&2, Spec.Token>>:
  match edit:
    case Spec.Stage{+offset}:
      replace(Spec.Stage{offset}, offset, tokens)
    case Spec.Commit{+offset}:
      replace(Spec.Commit{offset}, offset, tokens)
    case Spec.Discard{}:
      Some{discard(tokens)}
    case _:
      Some{tokens}

def choose_rep(valid: Bool, representation: Spec.Representation) -> Maybe<&2, Spec.Representation>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{representation}

def raw_representation(edit: Spec.Edit, +width: Nat, sink: Bool, slot: Nat,
    tokens: List<&2, Spec.Token>) -> Maybe<&2, Spec.Representation>:
  match edit:
    case Spec.PackPreview{}:
      choose_rep(Bool.and(nonzero(width), Bool.and(Bool.not(sink), complete(width, tokens, False{}))), Spec.Preview{slot})
    case Spec.Seal{}:
      choose_rep(Bool.and(nonzero(width), Bool.and(Bool.not(sink), complete(width, tokens, True{}))), Spec.Sealed{})
    case _:
      Some{Spec.Raw{slot}}

def representation_step(old: Spec.Representation, edit: Spec.Edit, width: Nat, sink: Bool,
    tokens: List<&2, Spec.Token>) -> Maybe<&2, Spec.Representation>:
  match old edit:
    case Spec.Raw{slot} operation:
      raw_representation(operation, width, sink, slot, tokens)
    case Spec.Preview{slot} Spec.Commit{offset}:
      # Spec.Commit changes classification, not bytes; native may reuse preview.
      Some{Spec.Preview{slot}}
    case Spec.Preview{slot} operation:
      raw_representation(operation, width, sink, slot, tokens)
    case _ _:
      None{}

def content_rep(next: Maybe<&2, Spec.Representation>, ledger: Spec.Ledger, sink: Bool,
    tokens: List<&2, Spec.Token>) -> Maybe<&2, Spec.Page>:
  match next:
    case None{}:
      None{}
    case Some{representation}:
      Some{Spec.Page{ledger, sink, representation, tokens}}

def content_tokens(updated: Maybe<&2, List<&2, Spec.Token>>, edit: Spec.Edit, width: Nat,
    page: Spec.Page) -> Maybe<&2, Spec.Page>:
  match updated:
    case None{}:
      None{}
    case Some{+tokens}:
      Spec.Page{ledger, +sink, old, previous} = page
      content_rep(representation_step(old, edit, width, sink, tokens), ledger, sink, tokens)

def content_gate(valid: Bool, +edit: Spec.Edit, width: Nat, +page: Spec.Page) -> Maybe<&2, Spec.Page>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Spec.Page{ledger, sink, old, tokens} = page
      content_tokens(edited_tokens(edit, tokens), edit, width, page)

def within_edit(edit: Spec.Edit, width: Nat) -> Bool:
  match edit:
    case Spec.Stage{offset}:
      Nat.is_lt(offset, width)
    case Spec.Commit{offset}:
      Nat.is_lt(offset, width)
    case _:
      True{}

# None never supplies an updated state: rejection is not native rollback.
# Admitted atomic edits require successful scatter/pack completion and zero
# sticky status as external premises. The writer ledger blocks exposure/reuse
# until a separately authenticated Spec.FinishWrite; it is not native instrumentation.
def content(+edit: Spec.Edit, +width: Nat, +page: Spec.Page, request: Spec.Request) -> Maybe<&2, Spec.Page>:
  Spec.Page{+ledger, sink, old, +tokens} = page
  content_gate(Bool.and(editing(ledger, request), Bool.and(consistent(tokens), within_edit(edit, width))), edit, width, page)

def page_candidate(action: Spec.Action, next: Spec.Ledger, page: Spec.Page) -> Spec.Page:
  match action:
    case Spec.Allocate{owner}:
      Spec.Page{next, False{}, Spec.Vacant{}, Nil{}}
    case Spec.Reserve{owner}:
      Spec.Page{next, True{}, Spec.Vacant{}, Nil{}}
    case Spec.Release{}:
      Spec.Page{next, False{}, Spec.Vacant{}, Nil{}}
    case Spec.StartWrite{}:
      Spec.Page{old, sink, representation, tokens} = page
      Spec.Page{next, sink, invalidate(representation), tokens}
    case _:
      Spec.Page{old, sink, representation, tokens} = page
      Spec.Page{next, sink, representation, tokens}

def page_permission(action: Spec.Action, tokens: List<&2, Spec.Token>) -> Bool:
  match action:
    case Spec.Share{}:
      immutable(tokens)
    case _:
      True{}

def page_result(next: Maybe<&2, Spec.Ledger>, action: Spec.Action, page: Spec.Page) -> Maybe<&2, Spec.Page>:
  match next:
    case None{}:
      None{}
    case Some{ledger}:
      Some{page_candidate(action, ledger, page)}

def page_gate(valid: Bool, +action: Spec.Action, +page: Spec.Page, request: Spec.Request) -> Maybe<&2, Spec.Page>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Spec.Page{ledger, sink, representation, tokens} = page
      page_result(transition(action, ledger, request), action, page)

def page_transition(+action: Spec.Action, +page: Spec.Page, request: Spec.Request) -> Maybe<&2, Spec.Page>:
  Spec.Page{ledger, sink, representation, tokens} = page
  page_gate(page_permission(action, tokens), action, page, request)

# Claim/release are local slot transitions; caller must supply a fresh unique
# forward binding. Global slot uniqueness is NOT established by a local claim.
def claim(slot: Spec.Slot, lease: Spec.Lease) -> Maybe<&2, Spec.Slot>:
  match slot lease:
    case Spec.Slot{index, None{}, 0n, 0n} Spec.Lease{1n+p, generation, identity}:
      Some{Spec.Slot{index, Some{Spec.Lease{1n+p, generation, identity}}, 0n, 0n}}
    case _ _:
      None{}

def choose_slot(valid: Bool, index: Nat) -> Maybe<&2, Spec.Slot>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{Spec.Slot{index, None{}, 0n, 0n}}

def unbind(slot: Spec.Slot, +ledger: Spec.Ledger, request: Spec.Request) -> Maybe<&2, Spec.Slot>:
  match slot ledger:
    case Spec.Slot{index, Some{lease}, readers, writers} Spec.Ledger{page, generation, Some{identity}, dummy, activity}:
      choose_slot(Bool.and(quiet(activity), Bool.and(access(ledger, request),
        Bool.and(same(lease, Spec.Lease{page, generation, identity}),
          Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index)
    case _ _:
      None{}

def link(page: Spec.Page, slot: Spec.Slot) -> Bool:
  match page slot:
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Raw{forward}, tokens} Spec.Slot{index, Some{lease}, readers, writers}:
      Bool.and(Nat.is_eq(forward, index), same(lease, Spec.Lease{physical, generation, identity}))
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Preview{forward}, tokens} Spec.Slot{index, Some{lease}, readers, writers}:
      Bool.and(Nat.is_eq(forward, index), same(lease, Spec.Lease{physical, generation, identity}))
    case _ _:
      False{}

def address(width: Nat, page: Nat, offset: Nat) -> Spec.TokenAddress:
  Spec.TokenAddress{Nat.add(Nat.mul(page, width), offset)}

def address_bound(+base: Nat, width: Nat, offset: Nat) -> Bool:
  Nat.is_lt(Nat.add(base, offset), Nat.add(base, width))

# Sampling req_to_token at width*j alone is insufficient. This checks every
# token offset in a logical page. Different request rows may legally alias.
def row(width: Nat, +base: Nat, +offset: Nat, locations: List<&2, Nat>) -> Bool:
  match width locations:
    case 0n Nil{}:
      True{}
    case 1n+p location <> rest:
      Bool.and(Nat.is_eq(location, Nat.add(base, offset)), row(p, base, 1n+offset, rest))
    case _ _:
      False{}

def bind_result(valid: Bool, +ledger: Spec.Ledger, sink: Bool, +index: Nat,
    width: Nat, lease: Spec.Lease) -> Maybe<&2, Spec.Binding>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{Spec.Binding{Spec.Page{ledger, sink, Spec.Raw{index}, List.replicate(Spec.Token, width, Spec.Hole{})},
        Spec.Slot{index, Some{lease}, 0n, 0n}}}

def bind(+page: Spec.Page, slot: Spec.Slot, +width: Nat, request: Spec.Request) -> Maybe<&2, Spec.Binding>:
  match page slot:
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, Nil{}} Spec.Slot{index, None{}, 0n, 0n}:
      +ledger = {Spec.Ledger{physical, generation, Some{identity}, dummy, activity} : Spec.Ledger}
      bind_result(Bool.and(nonzero(width), Bool.and(quiet(activity), access(ledger, request))),
        ledger, sink, index, width, Spec.Lease{physical, generation, identity})
    case _ _:
      None{}

# Build the complete physical-token row; this is not a byte-address generator.
def locations(width: Nat, +base: Nat, +offset: Nat) -> List<&2, Nat>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.add(base, offset) <> locations(p, base, 1n+offset)
