# Independent local ownership/lifetime reference; no implementation imports.
# Source: patches/kvarn-candidate.patch (_prepare_write, _commit_prefix,
# _discard_provisional, _plan_complete_tiles, _publish_complete_tiles,
# KVarNPool.release_pages); kvarn-reserved-accounting.patch (retained dummy).
# Native release checks range/duplicates/dummy, NOT the generations, references
# or completion counters below. _free_slot_epoch is NOT a page generation.
# These observations are explicit refinement premises, currently uninstrumented.
# One ledger is one physical allocation. Aliases add references, not pages.
# Owner identifies an allocation, not one request. Global free-list uniqueness
# and slot-map bijection need array refinement beyond this local transition.
import Base

type Lease is Data:
  Lease{page: Nat, generation: Nat, owner: Nat}

type Request is Data:
  Missing{}
  Bad{}
  Cancelled{}
  Present{lease: Lease}

type Counts is Data:
  Counts{references: Nat, readers: Nat, writers: Nat}

type Ledger is Data:
  Ledger{page: Nat, generation: Nat, owner: Maybe<&2, Nat>, dummy: Bool, counts: Counts}

type Action is Data:
  Allocate{owner: Nat}
  Reserve{owner: Nat}
  Release{}
  Share{}
  Unshare{}
  StartRead{}
  FinishRead{}
  StartWrite{}
  FinishWrite{}

# Bad requests preserve malformed signed input; only the exact native -1
# sentinel maps to None. Conflict preserves both mask bits being true.
# Holes are not a prefix: max written offset+1 does not imply completeness.
type Token is Data:
  Hole{}
  Provisional{}
  Committed{}
  Conflict{}

type Representation is Data:
  Vacant{}
  Raw{slot: Nat}
  Preview{slot: Nat}
  Sealed{}
  Broken{}

type Page is Data:
  Page{ledger: Ledger, sink: Bool, representation: Representation, tokens: List<&2, Token>}

type Edit is Data:
  Stage{offset: Nat}
  Commit{offset: Nat}
  Discard{}
  PackPreview{}
  Seal{}

type Slot is Data:
  Slot{index: Nat, owner: Maybe<&2, Lease>, readers: Nat, writers: Nat}

type Binding is Data:
  Binding{page: Page, slot: Slot}

# Width comes from existing geometry (128 in the admitted plan). There is no
# second tile-layout specification. Physical token indices are NOT byte or
# raw scalar-element offsets. Pool P includes zero; allocator capacity is P-1.
type TokenAddress is Data:
  TokenAddress{index: Nat}

type ByteAddress is Data:
  ByteAddress{index: Nat}

def counts(ledger: Ledger) -> Counts:
  Ledger{page, generation, owner, dummy, activity} = ledger
  activity

def reference_count(ledger: Ledger) -> Nat:
  Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
  shared

def reader_count(ledger: Ledger) -> Nat:
  Ledger{page, generation, owner, dummy, Counts{shared, active, writers}} = ledger
  active

def writer_count(ledger: Ledger) -> Nat:
  Ledger{page, generation, owner, dummy, Counts{shared, readers, active}} = ledger
  active

def quiet(activity: Counts) -> Bool:
  Counts{shared, readers, writers} = activity
  Nat.is_eq(Nat.add(shared, Nat.add(readers, writers)), 0n)

def nonzero(page: Nat) -> Bool:
  Nat.is_lt(0n, page)

def ordinary(ledger: Ledger) -> Bool:
  Ledger{page, generation, owner, dummy, activity} = ledger
  Bool.and(nonzero(page), Bool.not(dummy))

def same(left: Lease, right: Lease) -> Bool:
  Lease{lp, lg, lo} = left
  Lease{rp, rg, ro} = right
  Bool.and(Nat.is_eq(lp, rp), Bool.and(Nat.is_eq(lg, rg), Nat.is_eq(lo, ro)))

def access(+ledger: Ledger, request: Request) -> Bool:
  match ledger request:
    case Ledger{page, generation, Some{identity}, dummy, activity} Present{lease}:
      Bool.and(ordinary(ledger), same(Lease{page, generation, identity}, lease))
    case _ _:
      False{}

def vacant(ledger: Ledger) -> Bool:
  match ledger:
    case Ledger{page, generation, None{}, dummy, activity}:
      Bool.and(Bool.and(nonzero(page), Bool.not(dummy)), quiet(activity))
    case _:
      False{}

def fresh(request: Request) -> Bool:
  match request:
    case Missing{}:
      True{}
    case _:
      False{}

def permitted(action: Action, +ledger: Ledger, request: Request) -> Bool:
  match action:
    case Allocate{identity}:
      Bool.and(vacant(ledger), fresh(request))
    case Reserve{identity}:
      Bool.and(vacant(ledger), fresh(request))
    case Release{}:
      Bool.and(quiet(counts(ledger)), access(ledger, request))
    case Share{}:
      Bool.and(Nat.is_eq(writer_count(ledger), 0n), access(ledger, request))
    case Unshare{}:
      Bool.and(nonzero(reference_count(ledger)), access(ledger, request))
    case StartRead{}:
      Bool.and(Nat.is_eq(writer_count(ledger), 0n), access(ledger, request))
    case FinishRead{}:
      Bool.and(nonzero(reader_count(ledger)), access(ledger, request))
    case StartWrite{}:
      Bool.and(quiet(counts(ledger)), access(ledger, request))
    case FinishWrite{}:
      Bool.and(nonzero(writer_count(ledger)), access(ledger, request))

# Saturating predecessor is unreachable on an admitted decrement at zero.
def candidate(action: Action, ledger: Ledger) -> Ledger:
  match action:
    case Allocate{identity}:
      Ledger{page, generation, owner, dummy, activity} = ledger
      Ledger{page, 1n+generation, Some{identity}, False{}, Counts{0n, 0n, 0n}}
    case Reserve{identity}:
      Ledger{page, generation, owner, dummy, activity} = ledger
      Ledger{page, 1n+generation, Some{identity}, True{}, Counts{0n, 0n, 0n}}
    case Release{}:
      Ledger{page, generation, owner, dummy, activity} = ledger
      Ledger{page, generation, None{}, False{}, Counts{0n, 0n, 0n}}
    case Share{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{1n+shared, readers, writers}}
    case Unshare{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{Nat.sub(shared, 1n), readers, writers}}
    case StartRead{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{shared, 1n+readers, writers}}
    case FinishRead{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{shared, Nat.sub(readers, 1n), writers}}
    case StartWrite{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{shared, readers, 1n+writers}}
    case FinishWrite{}:
      Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
      Ledger{page, generation, owner, dummy, Counts{shared, readers, Nat.sub(writers, 1n)}}

def choose(valid: Bool, action: Action, ledger: Ledger) -> Maybe<&2, Ledger>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{candidate(action, ledger)}

def transition(+action: Action, +ledger: Ledger, request: Request) -> Maybe<&2, Ledger>:
  choose(permitted(action, ledger, request), action, ledger)

# Every finish must authenticate actual matching completion. A launch return,
# status mirror or epoch does not establish these propositions. Native has no
# generation-bearing leases or per-page reader/reference counters today.
def Quiescent(ledger: Ledger) -> Type:
  Ledger{page, generation, owner, dummy, Counts{shared, readers, writers}} = ledger
  {shared == 0n : Nat} & {readers == 0n : Nat} & {writers == 0n : Nat}

def observed_counts(ledger: Ledger, shared: Nat, readers: Nat, writers: Nat) -> Type:
  {counts(ledger) == Counts{shared, readers, writers} : Counts}

def disjoint(token: Token) -> Bool:
  match token:
    case Conflict{}:
      False{}
    case _:
      True{}

def consistent(tokens: List<&2, Token>) -> Bool:
  match tokens:
    case Nil{}:
      True{}
    case token <> rest:
      Bool.and(disjoint(token), consistent(rest))

def immutable(tokens: List<&2, Token>) -> Bool:
  match tokens:
    case Nil{}:
      True{}
    case Committed{} <> rest:
      immutable(rest)
    case Hole{} <> rest:
      immutable(rest)
    case _:
      False{}

def complete(width: Nat, tokens: List<&2, Token>, +sealed: Bool) -> Bool:
  match width tokens:
    case 0n Nil{}:
      True{}
    case 1n+p Committed{} <> rest:
      complete(p, rest, sealed)
    case 1n+p Provisional{} <> rest:
      Bool.and(Bool.not(sealed), complete(p, rest, sealed))
    case _ _:
      False{}

def invalidate(representation: Representation) -> Representation:
  match representation:
    case Preview{slot}:
      Raw{slot}
    case other:
      other

def has_preview(representation: Representation) -> Bool:
  match representation:
    case Preview{slot}:
      True{}
    case _:
      False{}

def discard(tokens: List<&2, Token>) -> List<&2, Token>:
  match tokens:
    case Nil{}:
      Nil{}
    case Provisional{} <> rest:
      Hole{} <> discard(rest)
    case other <> rest:
      other <> discard(rest)

def token_edit(edit: Edit, token: Token) -> Maybe<&2, Token>:
  match edit token:
    case Stage{offset} Hole{}:
      Some{Provisional{}}
    case Stage{offset} Provisional{}:
      Some{Provisional{}}
    case Commit{offset} Provisional{}:
      Some{Committed{}}
    case _ _:
      None{}

def prepend(updated: Maybe<&2, List<&2, Token>>, token: Token) -> Maybe<&2, List<&2, Token>>:
  match updated:
    case None{}:
      None{}
    case Some{tokens}:
      Some{token <> tokens}

def replace_head(updated: Maybe<&2, Token>, rest: List<&2, Token>) -> Maybe<&2, List<&2, Token>>:
  match updated:
    case None{}:
      None{}
    case Some{token}:
      Some{token <> rest}

def replace(edit: Edit, offset: Nat, tokens: List<&2, Token>) -> Maybe<&2, List<&2, Token>>:
  match offset tokens:
    case 0n token <> rest:
      replace_head(token_edit(edit, token), rest)
    case 1n+p token <> rest:
      prepend(replace(edit, p, rest), token)
    case _ Nil{}:
      None{}

def editing(+ledger: Ledger, request: Request) -> Bool:
  match ledger:
    case Ledger{page, generation, owner, dummy, Counts{0n, 0n, 1n+w}}:
      Bool.and(Nat.is_eq(w, 0n), access(ledger, request))
    case _:
      False{}

def edited_tokens(edit: Edit, tokens: List<&2, Token>) -> Maybe<&2, List<&2, Token>>:
  match edit:
    case Stage{+offset}:
      replace(Stage{offset}, offset, tokens)
    case Commit{+offset}:
      replace(Commit{offset}, offset, tokens)
    case Discard{}:
      Some{discard(tokens)}
    case _:
      Some{tokens}

def choose_rep(valid: Bool, representation: Representation) -> Maybe<&2, Representation>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{representation}

def raw_representation(edit: Edit, +width: Nat, sink: Bool, slot: Nat,
    tokens: List<&2, Token>) -> Maybe<&2, Representation>:
  match edit:
    case PackPreview{}:
      choose_rep(Bool.and(nonzero(width), Bool.and(Bool.not(sink), complete(width, tokens, False{}))), Preview{slot})
    case Seal{}:
      choose_rep(Bool.and(nonzero(width), Bool.and(Bool.not(sink), complete(width, tokens, True{}))), Sealed{})
    case _:
      Some{Raw{slot}}

def representation_step(old: Representation, edit: Edit, width: Nat, sink: Bool,
    tokens: List<&2, Token>) -> Maybe<&2, Representation>:
  match old edit:
    case Raw{slot} operation:
      raw_representation(operation, width, sink, slot, tokens)
    case Preview{slot} Commit{offset}:
      # Commit changes classification, not bytes; native may reuse preview.
      Some{Preview{slot}}
    case Preview{slot} operation:
      raw_representation(operation, width, sink, slot, tokens)
    case _ _:
      None{}

def content_rep(next: Maybe<&2, Representation>, ledger: Ledger, sink: Bool,
    tokens: List<&2, Token>) -> Maybe<&2, Page>:
  match next:
    case None{}:
      None{}
    case Some{representation}:
      Some{Page{ledger, sink, representation, tokens}}

def content_tokens(updated: Maybe<&2, List<&2, Token>>, edit: Edit, width: Nat,
    page: Page) -> Maybe<&2, Page>:
  match updated:
    case None{}:
      None{}
    case Some{+tokens}:
      Page{ledger, +sink, old, previous} = page
      content_rep(representation_step(old, edit, width, sink, tokens), ledger, sink, tokens)

def content_gate(valid: Bool, +edit: Edit, width: Nat, +page: Page) -> Maybe<&2, Page>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Page{ledger, sink, old, tokens} = page
      content_tokens(edited_tokens(edit, tokens), edit, width, page)

def within_edit(edit: Edit, width: Nat) -> Bool:
  match edit:
    case Stage{offset}:
      Nat.is_lt(offset, width)
    case Commit{offset}:
      Nat.is_lt(offset, width)
    case _:
      True{}

# None never supplies an updated state: rejection is not native rollback.
# Admitted atomic edits require successful scatter/pack completion and zero
# sticky status as external premises. The writer ledger blocks exposure/reuse
# until a separately authenticated FinishWrite; it is not native instrumentation.
def content(+edit: Edit, +width: Nat, +page: Page, request: Request) -> Maybe<&2, Page>:
  Page{+ledger, sink, old, +tokens} = page
  content_gate(Bool.and(editing(ledger, request), Bool.and(consistent(tokens), within_edit(edit, width))), edit, width, page)

def page_candidate(action: Action, next: Ledger, page: Page) -> Page:
  match action:
    case Allocate{owner}:
      Page{next, False{}, Vacant{}, Nil{}}
    case Reserve{owner}:
      Page{next, True{}, Vacant{}, Nil{}}
    case Release{}:
      Page{next, False{}, Vacant{}, Nil{}}
    case StartWrite{}:
      Page{old, sink, representation, tokens} = page
      Page{next, sink, invalidate(representation), tokens}
    case _:
      Page{old, sink, representation, tokens} = page
      Page{next, sink, representation, tokens}

def page_permission(action: Action, tokens: List<&2, Token>) -> Bool:
  match action:
    case Share{}:
      immutable(tokens)
    case _:
      True{}

def page_result(next: Maybe<&2, Ledger>, action: Action, page: Page) -> Maybe<&2, Page>:
  match next:
    case None{}:
      None{}
    case Some{ledger}:
      Some{page_candidate(action, ledger, page)}

def page_gate(valid: Bool, +action: Action, +page: Page, request: Request) -> Maybe<&2, Page>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Page{ledger, sink, representation, tokens} = page
      page_result(transition(action, ledger, request), action, page)

def page_transition(+action: Action, +page: Page, request: Request) -> Maybe<&2, Page>:
  Page{ledger, sink, representation, tokens} = page
  page_gate(page_permission(action, tokens), action, page, request)

# Claim/release are local slot transitions; caller must supply a fresh unique
# forward binding. Global slot uniqueness is NOT established by a local claim.
def claim(slot: Slot, lease: Lease) -> Maybe<&2, Slot>:
  match slot lease:
    case Slot{index, None{}, 0n, 0n} Lease{1n+p, generation, identity}:
      Some{Slot{index, Some{Lease{1n+p, generation, identity}}, 0n, 0n}}
    case _ _:
      None{}

def choose_slot(valid: Bool, index: Nat) -> Maybe<&2, Slot>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{Slot{index, None{}, 0n, 0n}}

def unbind(slot: Slot, +ledger: Ledger, request: Request) -> Maybe<&2, Slot>:
  match slot ledger:
    case Slot{index, Some{lease}, readers, writers} Ledger{page, generation, Some{identity}, dummy, activity}:
      choose_slot(Bool.and(quiet(activity), Bool.and(access(ledger, request),
        Bool.and(same(lease, Lease{page, generation, identity}),
          Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index)
    case _ _:
      None{}

def link(page: Page, slot: Slot) -> Bool:
  match page slot:
    case Page{Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Raw{forward}, tokens} Slot{index, Some{lease}, readers, writers}:
      Bool.and(Nat.is_eq(forward, index), same(lease, Lease{physical, generation, identity}))
    case Page{Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Preview{forward}, tokens} Slot{index, Some{lease}, readers, writers}:
      Bool.and(Nat.is_eq(forward, index), same(lease, Lease{physical, generation, identity}))
    case _ _:
      False{}

def address(width: Nat, page: Nat, offset: Nat) -> TokenAddress:
  TokenAddress{Nat.add(Nat.mul(page, width), offset)}

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

def bind_result(valid: Bool, +ledger: Ledger, sink: Bool, +index: Nat,
    width: Nat, lease: Lease) -> Maybe<&2, Binding>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{Binding{Page{ledger, sink, Raw{index}, List.replicate(Token, width, Hole{})},
        Slot{index, Some{lease}, 0n, 0n}}}

def bind(+page: Page, slot: Slot, +width: Nat, request: Request) -> Maybe<&2, Binding>:
  match page slot:
    case Page{Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Vacant{}, Nil{}} Slot{index, None{}, 0n, 0n}:
      +ledger = {Ledger{physical, generation, Some{identity}, dummy, activity} : Ledger}
      bind_result(Bool.and(nonzero(width), Bool.and(quiet(activity), access(ledger, request))),
        ledger, sink, index, width, Lease{physical, generation, identity})
    case _ _:
      None{}

# Safety of rejected results is not a successful-state witness: progress laws
# separately exhibit Some states. None leaves the caller's old state intact.
def safe_tokens(result: Maybe<&2, List<&2, Token>>) -> Bool:
  match result:
    case None{}:
      True{}
    case Some{tokens}:
      consistent(tokens)

# Native upper bounds, integer widths and completion/frontier authentication
# are separate from these Nat functions. For production correspondence one
# needs 0<page<P, slot<S, offset<128, exact signed sentinel decoding, exact
# masks and the global forward/reverse owner relation. Caller-held tensor and
# graph/workspace leases must outlive all joined users. No native observation
# in the current sources certifies these generations/counts/frontiers.
