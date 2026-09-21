# Laws concern the total abstract transitions, not native GPU refinement.
# Identities, generations and counts are unbounded; no sampled histories or
# finite machine-word truncation substitute for universal lifetime claims.
import Base
import ./ownership_spec.bend as Spec
import ./ownership.bend as Impl

law transition_reference:
  for +action: Spec.Action
  for +ledger: Spec.Ledger
  for +request: Spec.Request
  {Impl.transition(action, ledger, request) == Spec.transition(action, ledger, request) : Maybe<&2, Spec.Ledger>}

law content_reference:
  for +edit: Spec.Edit
  for +width: Nat
  for +page: Spec.Page
  for +request: Spec.Request
  {Impl.content(edit, width, page, request) == Spec.content(edit, width, page, request) : Maybe<&2, Spec.Page>}

law page_reference:
  for +action: Spec.Action
  for +page: Spec.Page
  for +request: Spec.Request
  {Impl.page_transition(action, page, request) == Spec.page_transition(action, page, request) : Maybe<&2, Spec.Page>}

law bind_reference:
  for +page: Spec.Page
  for +slot: Spec.Slot
  for +width: Nat
  for +request: Spec.Request
  {Impl.bind(page, slot, width, request) == Spec.bind(page, slot, width, request) : Maybe<&2, Spec.Binding>}

law unbind_reference:
  for +slot: Spec.Slot
  for +ledger: Spec.Ledger
  for +request: Spec.Request
  {Impl.unbind(slot, ledger, request) == Spec.unbind(slot, ledger, request) : Maybe<&2, Spec.Slot>}

law release_references:
  for page: Nat
  for generation: Nat
  for owner: Maybe<&2, Nat>
  for dummy: Bool
  for shared: Nat
  for readers: Nat
  for writers: Nat
  for request: Spec.Request
  {Impl.transition(Spec.Release{}, Spec.Ledger{page, generation, owner, dummy,
    Spec.Counts{1n+shared, readers, writers}}, request) == None{} : Maybe<&2, Spec.Ledger>}

law release_readers:
  for page: Nat
  for generation: Nat
  for owner: Maybe<&2, Nat>
  for dummy: Bool
  for shared: Nat
  for readers: Nat
  for writers: Nat
  for request: Spec.Request
  {Impl.transition(Spec.Release{}, Spec.Ledger{page, generation, owner, dummy,
    Spec.Counts{shared, 1n+readers, writers}}, request) == None{} : Maybe<&2, Spec.Ledger>}

law release_writers:
  for page: Nat
  for generation: Nat
  for owner: Maybe<&2, Nat>
  for dummy: Bool
  for shared: Nat
  for readers: Nat
  for writers: Nat
  for request: Spec.Request
  {Impl.transition(Spec.Release{}, Spec.Ledger{page, generation, owner, dummy,
    Spec.Counts{shared, readers, 1n+writers}}, request) == None{} : Maybe<&2, Spec.Ledger>}

law dummy_never_reclaimed:
  for +page: Nat
  for +generation: Nat
  for +owner: Maybe<&2, Nat>
  for +activity: Spec.Counts
  for +request: Spec.Request
  {Impl.transition(Spec.Release{}, Spec.Ledger{page, generation, owner, True{}, activity}, request) == None{} : Maybe<&2, Spec.Ledger>}

law zero_never_accessible:
  for generation: Nat
  for owner: Maybe<&2, Nat>
  for dummy: Bool
  for activity: Spec.Counts
  for request: Spec.Request
  {Impl.access(Spec.Ledger{0n, generation, owner, dummy, activity}, request) == False{} : Bool}

law stale_generation_rejected:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for +dummy: Bool
  for +activity: Spec.Counts
  for +old_page: Nat
  for +old_generation: Nat
  for +old_owner: Nat
  for stale: {Nat.is_eq(generation, old_generation) == False{} : Bool}
  {Impl.access(Spec.Ledger{page, generation, Some{owner}, dummy, activity},
    Spec.Present{Spec.Lease{old_page, old_generation, old_owner}}) == False{} : Bool}

law missing_cancelled_invalid:
  for +ledger: Spec.Ledger
  {Impl.access(ledger, Spec.Missing{}) == False{} : Bool} &
  {Impl.access(ledger, Spec.Cancelled{}) == False{} : Bool} &
  {Impl.access(ledger, Spec.Bad{}) == False{} : Bool}

law allocate_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.transition(Spec.Allocate{owner}, Spec.Ledger{1n+page, generation, None{}, False{},
    Spec.Counts{0n, 0n, 0n}}, Spec.Missing{}) == Some{Spec.Ledger{1n+page, 1n+generation,
      Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}}} : Maybe<&2, Spec.Ledger>}

law reserve_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.transition(Spec.Reserve{owner}, Spec.Ledger{1n+page, generation, None{}, False{},
    Spec.Counts{0n, 0n, 0n}}, Spec.Missing{}) == Some{Spec.Ledger{1n+page, 1n+generation,
      Some{owner}, True{}, Spec.Counts{0n, 0n, 0n}}} : Maybe<&2, Spec.Ledger>}

law release_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.transition(Spec.Release{}, Spec.Ledger{1n+page, generation, Some{owner}, False{},
    Spec.Counts{0n, 0n, 0n}}, Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
      Some{Spec.Ledger{1n+page, generation, None{}, False{}, Spec.Counts{0n, 0n, 0n}}} : Maybe<&2, Spec.Ledger>}

# ABA prevention is about the generation, even when page and owner are reused.
law reuse_rejects_old_lease:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for activity: Spec.Counts
  {Impl.access(Spec.Ledger{1n+page, 1n+generation, Some{owner}, False{}, activity},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}) == False{} : Bool}

law shared_readonly:
  for page: Nat
  for generation: Nat
  for owner: Maybe<&2, Nat>
  for dummy: Bool
  for shared: Nat
  for readers: Nat
  for writers: Nat
  for request: Spec.Request
  {Impl.transition(Spec.StartWrite{}, Spec.Ledger{page, generation, owner, dummy,
    Spec.Counts{1n+shared, readers, writers}}, request) == None{} : Maybe<&2, Spec.Ledger>}

law read_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for +shared: Nat
  for +readers: Nat
  {Impl.transition(Spec.StartRead{}, Spec.Ledger{1n+page, generation, Some{owner}, False{},
    Spec.Counts{shared, readers, 0n}}, Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
      Some{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{shared, 1n+readers, 0n}}} : Maybe<&2, Spec.Ledger>}

law write_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.transition(Spec.StartWrite{}, Spec.Ledger{1n+page, generation, Some{owner}, False{},
    Spec.Counts{0n, 0n, 0n}}, Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
      Some{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}}} : Maybe<&2, Spec.Ledger>}

# Actual reported zeros imply safety only with this independent exactness
# premise. No function here reads native refcounts or authenticates events.
law observed_release_progress:
  for +ledger: Spec.Ledger
  for +request: Spec.Request
  for exact: Spec.observed_counts(ledger, 0n, 0n, 0n)
  for authorized: {Impl.access(ledger, request) == True{} : Bool}
  {Impl.transition(Spec.Release{}, ledger, request) == Some{Spec.candidate(Spec.Release{}, ledger)} : Maybe<&2, Spec.Ledger>}

law bind_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for +slot: Nat
  for +width: Nat
  for +sink: Bool
  {Impl.bind(Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    sink, Spec.Vacant{}, Nil{}}, Spec.Slot{slot, None{}, 0n, 0n}, 1n+width,
      Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
    Some{Spec.Binding{Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
      sink, Spec.Raw{slot}, List.replicate(Spec.Token, 1n+width, Spec.Hole{})},
      Spec.Slot{slot, Some{Spec.Lease{1n+page, generation, owner}}, 0n, 0n}}} : Maybe<&2, Spec.Binding>}

law slot_owned_not_reused:
  for index: Nat
  for old: Spec.Lease
  for readers: Nat
  for writers: Nat
  for next: Spec.Lease
  {Impl.claim(Spec.Slot{index, Some{old}, readers, writers}, next) == None{} : Maybe<&2, Spec.Slot>}

law slot_reader_blocks_unbind:
  for index: Nat
  for +owner: Maybe<&2, Spec.Lease>
  for +readers: Nat
  for +writers: Nat
  for +ledger: Spec.Ledger
  for +request: Spec.Request
  {Impl.unbind(Spec.Slot{index, owner, 1n+readers, writers}, ledger, request) == None{} : Maybe<&2, Spec.Slot>}

law slot_writer_blocks_unbind:
  for +index: Nat
  for +owner: Maybe<&2, Spec.Lease>
  for +readers: Nat
  for +writers: Nat
  for +ledger: Spec.Ledger
  for +request: Spec.Request
  {Impl.unbind(Spec.Slot{index, owner, readers, 1n+writers}, ledger, request) == None{} : Maybe<&2, Spec.Slot>}

law invalidate_preview:
  for representation: Spec.Representation
  {Spec.has_preview(Impl.invalidate(representation)) == False{} : Bool}

law discard_preserves_disjointness:
  for +tokens: List<&2, Spec.Token>
  {Spec.consistent(Impl.discard(tokens)) == Spec.consistent(tokens) : Bool}

law committed_not_overwritten:
  for offset: Nat
  {Impl.token_edit(Spec.Stage{offset}, Spec.Committed{}) == None{} : Maybe<&2, Spec.Token>}

law provisional_commit_progress:
  for offset: Nat
  {Impl.token_edit(Spec.Commit{offset}, Spec.Provisional{}) == Some{Spec.Committed{}} : Maybe<&2, Spec.Token>}

law discard_invalidates_preview:
  for slot: Nat
  for width: Nat
  for sink: Bool
  for tokens: List<&2, Spec.Token>
  {Impl.representation_step(Spec.Preview{slot}, Spec.Discard{}, width, sink, tokens) == Some{Spec.Raw{slot}} : Maybe<&2, Spec.Representation>}

law provisional_never_sealed:
  for slot: Nat
  for width: Nat
  for sink: Bool
  for tokens: List<&2, Spec.Token>
  {Impl.representation_step(Spec.Raw{slot}, Spec.Seal{}, width, sink,
    Spec.Provisional{} <> tokens) == None{} : Maybe<&2, Spec.Representation>}

law sink_never_sealed:
  for slot: Nat
  for width: Nat
  for tokens: List<&2, Spec.Token>
  {Impl.representation_step(Spec.Raw{slot}, Spec.Seal{}, width, True{}, tokens) == None{} : Maybe<&2, Spec.Representation>}

law seal_progress:
  for +slot: Nat
  for +width: Nat
  for +tokens: List<&2, Spec.Token>
  for full: {Impl.complete(1n+width, tokens, True{}) == True{} : Bool}
  {Impl.representation_step(Spec.Preview{slot}, Spec.Seal{}, 1n+width, False{}, tokens) ==
    Some{Spec.Sealed{}} : Maybe<&2, Spec.Representation>} &
  {Spec.has_preview(Spec.Sealed{}) == False{} : Bool}

law address_reference:
  for +width: Nat
  for +page: Nat
  for +offset: Nat
  {Impl.address(width, page, offset) == Spec.address(width, page, offset) : Spec.TokenAddress}

law address_within_page:
  for +base: Nat
  for +width: Nat
  for +offset: Nat
  for bounded: {Nat.is_lt(offset, width) == True{} : Bool}
  {Spec.address_bound(base, width, offset) == True{} : Bool}

law claim_reference:
  for +slot: Spec.Slot
  for +lease: Spec.Lease
  {Impl.claim(slot, lease) == Spec.claim(slot, lease) : Maybe<&2, Spec.Slot>}

law slot_claim_progress:
  for +index: Nat
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.claim(Spec.Slot{index, None{}, 0n, 0n}, Spec.Lease{1n+page, generation, owner}) ==
    Some{Spec.Slot{index, Some{Spec.Lease{1n+page, generation, owner}}, 0n, 0n}} : Maybe<&2, Spec.Slot>}

law slot_release_progress:
  for +index: Nat
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  {Impl.unbind(Spec.Slot{index, Some{Spec.Lease{1n+page, generation, owner}}, 0n, 0n},
    Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
    Some{Spec.Slot{index, None{}, 0n, 0n}} : Maybe<&2, Spec.Slot>}

law bound_link:
  for +index: Nat
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for activity: Spec.Counts
  for sink: Bool
  for tokens: List<&2, Spec.Token>
  {Spec.link(Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, activity},
    sink, Spec.Raw{index}, tokens}, Spec.Slot{index, Some{Spec.Lease{1n+page, generation, owner}}, 0n, 0n}) == True{} : Bool}

law cancelled_allocation_rejected:
  for +owner: Nat
  for +ledger: Spec.Ledger
  {Impl.transition(Spec.Allocate{owner}, ledger, Spec.Cancelled{}) == None{} : Maybe<&2, Spec.Ledger>}

law replace_preserves_disjointness:
  for +edit: Spec.Edit
  for +offset: Nat
  for +tokens: List<&2, Spec.Token>
  for valid: {Spec.consistent(tokens) == True{} : Bool}
  {Spec.safe_tokens(Impl.replace(edit, offset, tokens)) == True{} : Bool}

law stage_progress:
  for +page: Nat
  for +generation: Nat
  for +owner: Nat
  for +slot: Nat
  for +width: Nat
  for +sink: Bool
  for +rest: List<&2, Spec.Token>
  for valid: {Impl.consistent(rest) == True{} : Bool}
  {Impl.content(Spec.Stage{0n}, 1n+width, Spec.Page{Spec.Ledger{1n+page, generation, Some{owner},
    False{}, Spec.Counts{0n, 0n, 1n}}, sink, Spec.Preview{slot}, Spec.Hole{} <> rest},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}) ==
    Some{Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}},
      sink, Spec.Raw{slot}, Spec.Provisional{} <> rest}} : Maybe<&2, Spec.Page>}

# This successful seal witness has no assumed complete-mask oracle: induction
# constructs an arbitrary nonempty fully committed page.
law committed_page_seals:
  for +slot: Nat
  for +width: Nat
  {Impl.representation_step(Spec.Preview{slot}, Spec.Seal{}, 1n+width, False{},
    List.replicate(Spec.Token, 1n+width, Spec.Committed{})) == Some{Spec.Sealed{}} : Maybe<&2, Spec.Representation>}

law exact_logical_row:
  for +width: Nat
  for +base: Nat
  for +offset: Nat
  {Spec.row(width, base, offset, Impl.locations(width, base, offset)) == True{} : Bool}
