# Structural proofs over arbitrary Nat identities/counters and finite lists.
# No native state is observed here; source/refinement premises are in Spec.
import Base
import ./ownership_spec.bend as Spec
import ./ownership.bend as Impl
import ./ownership_laws.bend as Laws

def and_false(value: Bool) -> {Bool.and(value, False{}) == False{} : Bool}:
  match value:
    case False{}:
      {==}
    case True{}:
      {==}

def and3_false(a: Bool, b: Bool, c: Bool)
  -> {Bool.and(a, Bool.and(b, Bool.and(c, False{}))) == False{} : Bool}:
  match a b c:
    case False{} _ _:
      {==}
    case True{} False{} _:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def eq_self(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_self(p)

def successor_not_old(+n: Nat) -> {Nat.is_eq(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      successor_not_old(p)

def nonzero_reference(+n: Nat) -> {Impl.nonzero(n) == Spec.nonzero(n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def quiet_reference(+activity: Spec.Counts) -> {Impl.quiet(activity) == Spec.quiet(activity) : Bool}:
  match activity:
    case Spec.Counts{0n, 0n, 0n}:
      {==}
    case Spec.Counts{0n, 0n, 1n+w}:
      {==}
    case Spec.Counts{0n, 1n+r, w}:
      {==}
    case Spec.Counts{1n+s, r, w}:
      {==}

def ordinary_reference(+ledger: Spec.Ledger) -> {Impl.ordinary(ledger) == Spec.ordinary(ledger) : Bool}:
  match ledger:
    case Spec.Ledger{page, generation, owner, dummy, activity}:
      %nonzero_reference(page) : {Impl.ordinary(ledger) == Bool.and(_, Bool.not(dummy)) : Bool}
      {==}

def same_reference(+left: Spec.Lease, +right: Spec.Lease)
  -> {Impl.same(left, right) == Spec.same(left, right) : Bool}:
  match left right:
    case Spec.Lease{lp, lg, lo} Spec.Lease{rp, rg, ro}:
      {==}

def access_reference(+ledger: Spec.Ledger, +request: Spec.Request)
  -> {Impl.access(ledger, request) == Spec.access(ledger, request) : Bool}:
  match ledger request:
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity} Spec.Present{lease}:
      %ordinary_reference(ledger) : {Impl.access(ledger, request) ==
        Bool.and(_, Spec.same(Spec.Lease{page, generation, identity}, lease)) : Bool}
      %same_reference(Spec.Lease{page, generation, identity}, lease) :
        {Impl.access(ledger, request) == Bool.and(Impl.ordinary(ledger), _) : Bool}
      {==}
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity} Spec.Missing{}:
      {==}
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity} Spec.Bad{}:
      {==}
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity} Spec.Cancelled{}:
      {==}
    case Spec.Ledger{page, generation, None{}, dummy, activity} _:
      {==}

def vacant_reference(+ledger: Spec.Ledger) -> {Impl.vacant(ledger) == Spec.vacant(ledger) : Bool}:
  match ledger:
    case Spec.Ledger{page, generation, None{}, dummy, activity}:
      %nonzero_reference(page) : {Impl.vacant(ledger) == Bool.and(Bool.and(_, Bool.not(dummy)), Spec.quiet(activity)) : Bool}
      %quiet_reference(activity) : {Impl.vacant(ledger) == Bool.and(Bool.and(Impl.nonzero(page), Bool.not(dummy)), _) : Bool}
      {==}
    case Spec.Ledger{page, generation, Some{identity}, dummy, activity}:
      {==}

def fresh_reference(+request: Spec.Request) -> {Impl.fresh(request) == Spec.fresh(request) : Bool}:
  match request:
    case Spec.Missing{}:
      {==}
    case Spec.Bad{}:
      {==}
    case Spec.Cancelled{}:
      {==}
    case Spec.Present{lease}:
      {==}

def permission_reference(+action: Spec.Action, +ledger: Spec.Ledger, +request: Spec.Request)
  -> {Impl.permitted(action, ledger, request) == Spec.permitted(action, ledger, request) : Bool}:
  match action ledger:
    case Spec.Allocate{identity} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %vacant_reference(ledger) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.fresh(request)) : Bool}
      %fresh_reference(request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.vacant(ledger), _) : Bool}
      {==}
    case Spec.Reserve{identity} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %vacant_reference(ledger) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.fresh(request)) : Bool}
      %fresh_reference(request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.vacant(ledger), _) : Bool}
      {==}
    case Spec.Release{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %quiet_reference(Impl.counts(ledger)) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.access(ledger, request)) : Bool}
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.quiet(Impl.counts(ledger)), _) : Bool}
      {==}
    case Spec.Share{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Nat.is_eq(Impl.writer_count(ledger), 0n), _) : Bool}
      {==}
    case Spec.Unshare{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %nonzero_reference(Impl.reference_count(ledger)) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.access(ledger, request)) : Bool}
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.nonzero(Impl.reference_count(ledger)), _) : Bool}
      {==}
    case Spec.StartRead{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Nat.is_eq(Impl.writer_count(ledger), 0n), _) : Bool}
      {==}
    case Spec.FinishRead{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %nonzero_reference(Impl.reader_count(ledger)) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.access(ledger, request)) : Bool}
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.nonzero(Impl.reader_count(ledger)), _) : Bool}
      {==}
    case Spec.StartWrite{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %quiet_reference(Impl.counts(ledger)) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.access(ledger, request)) : Bool}
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.quiet(Impl.counts(ledger)), _) : Bool}
      {==}
    case Spec.FinishWrite{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      %nonzero_reference(Impl.writer_count(ledger)) : {Impl.permitted(action, ledger, request) == Bool.and(_, Spec.access(ledger, request)) : Bool}
      %access_reference(ledger, request) : {Impl.permitted(action, ledger, request) == Bool.and(Impl.nonzero(Impl.writer_count(ledger)), _) : Bool}
      {==}

def candidate_reference(+action: Spec.Action, +ledger: Spec.Ledger)
  -> {Impl.candidate(action, ledger) == Spec.candidate(action, ledger) : Spec.Ledger}:
  match action ledger:
    case Spec.Allocate{identity} Spec.Ledger{page, generation, owner, dummy, activity}:
      {==}
    case Spec.Reserve{identity} Spec.Ledger{page, generation, owner, dummy, activity}:
      {==}
    case Spec.Release{} Spec.Ledger{page, generation, owner, dummy, activity}:
      {==}
    case Spec.Share{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}
    case Spec.Unshare{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}
    case Spec.StartRead{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}
    case Spec.FinishRead{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}
    case Spec.StartWrite{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}
    case Spec.FinishWrite{} Spec.Ledger{page, generation, owner, dummy, Spec.Counts{shared, readers, writers}}:
      {==}

def choose_reference(+valid: Bool, +action: Spec.Action, +ledger: Spec.Ledger)
  -> {Impl.choose(valid, action, ledger) == Spec.choose(valid, action, ledger) : Maybe<&2, Spec.Ledger>}:
  match valid:
    case False{}:
      {==}
    case True{}:
      %candidate_reference(action, ledger) : {Impl.choose(valid, action, ledger) == Some{_} : Maybe<&2, Spec.Ledger>}
      {==}

def Laws.transition_reference(action, ledger, request):
  %permission_reference(action, ledger, request) : {Impl.transition(action, ledger, request) == Spec.choose(_, action, ledger) : Maybe<&2, Spec.Ledger>}
  choose_reference(Impl.permitted(action, ledger, request), action, ledger)

def complete_reference(+width: Nat, +tokens: List<&2, Spec.Token>, +sealed: Bool)
  -> {Impl.complete(width, tokens, sealed) == Spec.complete(width, tokens, sealed) : Bool}:
  match width tokens:
    case 0n Nil{}:
      {==}
    case 1n+p Spec.Committed{} <> rest:
      complete_reference(p, rest, sealed)
    case 1n+p Spec.Provisional{} <> rest:
      %complete_reference(p, rest, sealed) : {Impl.complete(width, tokens, sealed) == Bool.and(Bool.not(sealed), _) : Bool}
      {==}
    case 0n token <> rest:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Spec.Hole{} <> rest:
      {==}
    case 1n+p Spec.Conflict{} <> rest:
      {==}

def immutable_reference(+tokens: List<&2, Spec.Token>)
  -> {Impl.immutable(tokens) == Spec.immutable(tokens) : Bool}:
  match tokens:
    case Nil{}:
      {==}
    case Spec.Committed{} <> rest:
      immutable_reference(rest)
    case Spec.Hole{} <> rest:
      immutable_reference(rest)
    case Spec.Provisional{} <> rest:
      {==}
    case Spec.Conflict{} <> rest:
      {==}

def disjoint_reference(+token: Spec.Token) -> {Impl.disjoint(token) == Spec.disjoint(token) : Bool}:
  match token:
    case Spec.Hole{}:
      {==}
    case Spec.Provisional{}:
      {==}
    case Spec.Committed{}:
      {==}
    case Spec.Conflict{}:
      {==}

def consistent_reference(+tokens: List<&2, Spec.Token>)
  -> {Impl.consistent(tokens) == Spec.consistent(tokens) : Bool}:
  match tokens:
    case Nil{}:
      {==}
    case token <> rest:
      %consistent_reference(rest) : {Impl.consistent(tokens) == Bool.and(Spec.disjoint(token), _) : Bool}
      %disjoint_reference(token) : {Impl.consistent(tokens) == Bool.and(_, Impl.consistent(rest)) : Bool}
      {==}

def discard_reference(+tokens: List<&2, Spec.Token>)
  -> {Impl.discard(tokens) == Spec.discard(tokens) : List<&2, Spec.Token>}:
  match tokens:
    case Nil{}:
      {==}
    case Spec.Provisional{} <> rest:
      %discard_reference(rest) : {Impl.discard(tokens) == Spec.Hole{} <> _ : List<&2, Spec.Token>}
      {==}
    case Spec.Hole{} <> rest:
      %discard_reference(rest) : {Impl.discard(tokens) == Spec.Hole{} <> _ : List<&2, Spec.Token>}
      {==}
    case Spec.Committed{} <> rest:
      %discard_reference(rest) : {Impl.discard(tokens) == Spec.Committed{} <> _ : List<&2, Spec.Token>}
      {==}
    case Spec.Conflict{} <> rest:
      %discard_reference(rest) : {Impl.discard(tokens) == Spec.Conflict{} <> _ : List<&2, Spec.Token>}
      {==}

def token_edit_reference(+edit: Spec.Edit, +token: Spec.Token)
  -> {Impl.token_edit(edit, token) == Spec.token_edit(edit, token) : Maybe<&2, Spec.Token>}:
  match edit token:
    case Spec.Stage{offset} Spec.Hole{}:
      {==}
    case Spec.Stage{offset} Spec.Provisional{}:
      {==}
    case Spec.Stage{offset} Spec.Committed{}:
      {==}
    case Spec.Stage{offset} Spec.Conflict{}:
      {==}
    case Spec.Commit{offset} Spec.Hole{}:
      {==}
    case Spec.Commit{offset} Spec.Provisional{}:
      {==}
    case Spec.Commit{offset} Spec.Committed{}:
      {==}
    case Spec.Commit{offset} Spec.Conflict{}:
      {==}
    case Spec.Discard{} _:
      {==}
    case Spec.PackPreview{} _:
      {==}
    case Spec.Seal{} _:
      {==}

def replace_head_reference(+updated: Maybe<&2, Spec.Token>, +rest: List<&2, Spec.Token>)
  -> {Impl.replace_head(updated, rest) == Spec.replace_head(updated, rest) : Maybe<&2, List<&2, Spec.Token>>}:
  match updated:
    case None{}:
      {==}
    case Some{token}:
      {==}

def prepend_reference(+updated: Maybe<&2, List<&2, Spec.Token>>, +token: Spec.Token)
  -> {Impl.prepend(updated, token) == Spec.prepend(updated, token) : Maybe<&2, List<&2, Spec.Token>>}:
  match updated:
    case None{}:
      {==}
    case Some{tokens}:
      {==}

def replace_reference(+edit: Spec.Edit, +offset: Nat, +tokens: List<&2, Spec.Token>)
  -> {Impl.replace(edit, offset, tokens) == Spec.replace(edit, offset, tokens) : Maybe<&2, List<&2, Spec.Token>>}:
  match offset tokens:
    case 0n token <> rest:
      %token_edit_reference(edit, token) : {Impl.replace(edit, offset, tokens) == Spec.replace_head(_, rest) : Maybe<&2, List<&2, Spec.Token>>}
      replace_head_reference(Impl.token_edit(edit, token), rest)
    case 1n+p token <> rest:
      %replace_reference(edit, p, rest) : {Impl.replace(edit, offset, tokens) == Spec.prepend(_, token) : Maybe<&2, List<&2, Spec.Token>>}
      prepend_reference(Impl.replace(edit, p, rest), token)
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}

def edited_reference(+edit: Spec.Edit, +tokens: List<&2, Spec.Token>)
  -> {Impl.edited_tokens(edit, tokens) == Spec.edited_tokens(edit, tokens) : Maybe<&2, List<&2, Spec.Token>>}:
  match edit:
    case Spec.Stage{offset}:
      replace_reference(edit, offset, tokens)
    case Spec.Commit{offset}:
      replace_reference(edit, offset, tokens)
    case Spec.Discard{}:
      %discard_reference(tokens) : {Impl.edited_tokens(edit, tokens) == Some{_} : Maybe<&2, List<&2, Spec.Token>>}
      {==}
    case Spec.PackPreview{}:
      {==}
    case Spec.Seal{}:
      {==}

def choose_rep_reference(+valid: Bool, +representation: Spec.Representation)
  -> {Impl.choose_rep(valid, representation) == Spec.choose_rep(valid, representation) : Maybe<&2, Spec.Representation>}:
  match valid:
    case False{}:
      {==}
    case True{}:
      {==}

def raw_reference(+edit: Spec.Edit, +width: Nat, +sink: Bool, +slot: Nat, +tokens: List<&2, Spec.Token>)
  -> {Impl.raw_representation(edit, width, sink, slot, tokens) == Spec.raw_representation(edit, width, sink, slot, tokens) : Maybe<&2, Spec.Representation>}:
  match edit:
    case Spec.PackPreview{}:
      %nonzero_reference(width) : {Impl.raw_representation(edit, width, sink, slot, tokens) ==
        Spec.choose_rep(Bool.and(_, Bool.and(Bool.not(sink), Spec.complete(width, tokens, False{}))), Spec.Preview{slot}) : Maybe<&2, Spec.Representation>}
      %complete_reference(width, tokens, False{}) : {Impl.raw_representation(edit, width, sink, slot, tokens) ==
        Spec.choose_rep(Bool.and(Impl.nonzero(width), Bool.and(Bool.not(sink), _)), Spec.Preview{slot}) : Maybe<&2, Spec.Representation>}
      choose_rep_reference(Bool.and(Impl.nonzero(width), Bool.and(Bool.not(sink), Impl.complete(width, tokens, False{}))), Spec.Preview{slot})
    case Spec.Seal{}:
      %nonzero_reference(width) : {Impl.raw_representation(edit, width, sink, slot, tokens) ==
        Spec.choose_rep(Bool.and(_, Bool.and(Bool.not(sink), Spec.complete(width, tokens, True{}))), Spec.Sealed{}) : Maybe<&2, Spec.Representation>}
      %complete_reference(width, tokens, True{}) : {Impl.raw_representation(edit, width, sink, slot, tokens) ==
        Spec.choose_rep(Bool.and(Impl.nonzero(width), Bool.and(Bool.not(sink), _)), Spec.Sealed{}) : Maybe<&2, Spec.Representation>}
      choose_rep_reference(Bool.and(Impl.nonzero(width), Bool.and(Bool.not(sink), Impl.complete(width, tokens, True{}))), Spec.Sealed{})
    case Spec.Stage{offset}:
      {==}
    case Spec.Commit{offset}:
      {==}
    case Spec.Discard{}:
      {==}

def representation_reference(+old: Spec.Representation, +edit: Spec.Edit, +width: Nat,
    +sink: Bool, +tokens: List<&2, Spec.Token>)
  -> {Impl.representation_step(old, edit, width, sink, tokens) == Spec.representation_step(old, edit, width, sink, tokens) : Maybe<&2, Spec.Representation>}:
  match old edit:
    case Spec.Raw{slot} operation:
      raw_reference(operation, width, sink, slot, tokens)
    case Spec.Preview{slot} Spec.Commit{offset}:
      {==}
    case Spec.Preview{slot} Spec.Stage{offset}:
      raw_reference(edit, width, sink, slot, tokens)
    case Spec.Preview{slot} Spec.Discard{}:
      raw_reference(edit, width, sink, slot, tokens)
    case Spec.Preview{slot} Spec.PackPreview{}:
      raw_reference(edit, width, sink, slot, tokens)
    case Spec.Preview{slot} Spec.Seal{}:
      raw_reference(edit, width, sink, slot, tokens)
    case Spec.Vacant{} _:
      {==}
    case Spec.Sealed{} _:
      {==}
    case Spec.Broken{} _:
      {==}

def editing_reference(+ledger: Spec.Ledger, +request: Spec.Request)
  -> {Impl.editing(ledger, request) == Spec.editing(ledger, request) : Bool}:
  match ledger:
    case Spec.Ledger{page, generation, owner, dummy, Spec.Counts{0n, 0n, 1n+w}}:
      %access_reference(ledger, request) : {Impl.editing(ledger, request) == Bool.and(Nat.is_eq(w, 0n), _) : Bool}
      {==}
    case Spec.Ledger{page, generation, owner, dummy, Spec.Counts{0n, 0n, 0n}}:
      {==}
    case Spec.Ledger{page, generation, owner, dummy, Spec.Counts{0n, 1n+r, w}}:
      {==}
    case Spec.Ledger{page, generation, owner, dummy, Spec.Counts{1n+s, r, w}}:
      {==}

def content_rep_reference(+next: Maybe<&2, Spec.Representation>, +ledger: Spec.Ledger, +sink: Bool,
    +tokens: List<&2, Spec.Token>)
  -> {Impl.content_rep(next, ledger, sink, tokens) == Spec.content_rep(next, ledger, sink, tokens) : Maybe<&2, Spec.Page>}:
  match next:
    case None{}:
      {==}
    case Some{representation}:
      {==}

def content_tokens_reference(+updated: Maybe<&2, List<&2, Spec.Token>>, +edit: Spec.Edit,
    +width: Nat, +page: Spec.Page)
  -> {Impl.content_tokens(updated, edit, width, page) == Spec.content_tokens(updated, edit, width, page) : Maybe<&2, Spec.Page>}:
  match updated page:
    case None{} _:
      {==}
    case Some{tokens} Spec.Page{ledger, sink, old, previous}:
      %representation_reference(old, edit, width, sink, tokens) : {Impl.content_tokens(updated, edit, width, page) ==
        Spec.content_rep(_, ledger, sink, tokens) : Maybe<&2, Spec.Page>}
      content_rep_reference(Impl.representation_step(old, edit, width, sink, tokens), ledger, sink, tokens)

def content_gate_reference(+valid: Bool, +edit: Spec.Edit, +width: Nat, +page: Spec.Page)
  -> {Impl.content_gate(valid, edit, width, page) == Spec.content_gate(valid, edit, width, page) : Maybe<&2, Spec.Page>}:
  match valid page:
    case False{} _:
      {==}
    case True{} Spec.Page{ledger, sink, old, tokens}:
      %edited_reference(edit, tokens) : {Impl.content_gate(valid, edit, width, page) == Spec.content_tokens(_, edit, width, page) : Maybe<&2, Spec.Page>}
      content_tokens_reference(Impl.edited_tokens(edit, tokens), edit, width, page)

def within_reference(+edit: Spec.Edit, +width: Nat)
  -> {Impl.within_edit(edit, width) == Spec.within_edit(edit, width) : Bool}:
  match edit:
    case Spec.Stage{offset}:
      {==}
    case Spec.Commit{offset}:
      {==}
    case Spec.Discard{}:
      {==}
    case Spec.PackPreview{}:
      {==}
    case Spec.Seal{}:
      {==}

def Laws.content_reference(edit, width, page, request):
  match page:
    case Spec.Page{ledger, sink, old, tokens}:
      %editing_reference(ledger, request) : {Impl.content(edit, width, page, request) ==
        Spec.content_gate(Bool.and(_, Bool.and(Spec.consistent(tokens), Spec.within_edit(edit, width))), edit, width, page) : Maybe<&2, Spec.Page>}
      %consistent_reference(tokens) : {Impl.content(edit, width, page, request) ==
        Spec.content_gate(Bool.and(Impl.editing(ledger, request), Bool.and(_, Spec.within_edit(edit, width))), edit, width, page) : Maybe<&2, Spec.Page>}
      %within_reference(edit, width) : {Impl.content(edit, width, page, request) ==
        Spec.content_gate(Bool.and(Impl.editing(ledger, request), Bool.and(Impl.consistent(tokens), _)), edit, width, page) : Maybe<&2, Spec.Page>}
      content_gate_reference(Bool.and(Impl.editing(ledger, request), Bool.and(Impl.consistent(tokens), Impl.within_edit(edit, width))), edit, width, page)

def page_permission_reference(+action: Spec.Action, +tokens: List<&2, Spec.Token>)
  -> {Impl.page_permission(action, tokens) == Spec.page_permission(action, tokens) : Bool}:
  match action:
    case Spec.Share{}:
      immutable_reference(tokens)
    case Spec.Allocate{owner}:
      {==}
    case Spec.Reserve{owner}:
      {==}
    case Spec.Release{}:
      {==}
    case Spec.Unshare{}:
      {==}
    case Spec.StartRead{}:
      {==}
    case Spec.FinishRead{}:
      {==}
    case Spec.StartWrite{}:
      {==}
    case Spec.FinishWrite{}:
      {==}

def invalidate_reference(+representation: Spec.Representation)
  -> {Impl.invalidate(representation) == Spec.invalidate(representation) : Spec.Representation}:
  match representation:
    case Spec.Vacant{}:
      {==}
    case Spec.Raw{slot}:
      {==}
    case Spec.Preview{slot}:
      {==}
    case Spec.Sealed{}:
      {==}
    case Spec.Broken{}:
      {==}

def page_candidate_reference(+action: Spec.Action, +next: Spec.Ledger, +page: Spec.Page)
  -> {Impl.page_candidate(action, next, page) == Spec.page_candidate(action, next, page) : Spec.Page}:
  match action page:
    case Spec.Allocate{owner} _:
      {==}
    case Spec.Reserve{owner} _:
      {==}
    case Spec.Release{} _:
      {==}
    case Spec.StartWrite{} Spec.Page{old, sink, representation, tokens}:
      %invalidate_reference(representation) : {Impl.page_candidate(action, next, page) == Spec.Page{next, sink, _, tokens} : Spec.Page}
      {==}
    case Spec.Share{} Spec.Page{old, sink, representation, tokens}:
      {==}
    case Spec.Unshare{} Spec.Page{old, sink, representation, tokens}:
      {==}
    case Spec.StartRead{} Spec.Page{old, sink, representation, tokens}:
      {==}
    case Spec.FinishRead{} Spec.Page{old, sink, representation, tokens}:
      {==}
    case Spec.FinishWrite{} Spec.Page{old, sink, representation, tokens}:
      {==}

def page_result_reference(+next: Maybe<&2, Spec.Ledger>, +action: Spec.Action, +page: Spec.Page)
  -> {Impl.page_result(next, action, page) == Spec.page_result(next, action, page) : Maybe<&2, Spec.Page>}:
  match next:
    case None{}:
      {==}
    case Some{ledger}:
      %page_candidate_reference(action, ledger, page) : {Impl.page_result(next, action, page) == Some{_} : Maybe<&2, Spec.Page>}
      {==}

def page_gate_reference(+valid: Bool, +action: Spec.Action, +page: Spec.Page, +request: Spec.Request)
  -> {Impl.page_gate(valid, action, page, request) == Spec.page_gate(valid, action, page, request) : Maybe<&2, Spec.Page>}:
  match valid page:
    case False{} _:
      {==}
    case True{} Spec.Page{ledger, sink, representation, tokens}:
      %Laws.transition_reference(action, ledger, request) : {Impl.page_gate(valid, action, page, request) == Spec.page_result(_, action, page) : Maybe<&2, Spec.Page>}
      page_result_reference(Impl.transition(action, ledger, request), action, page)

def Laws.page_reference(action, page, request):
  match page:
    case Spec.Page{ledger, sink, representation, tokens}:
      %page_permission_reference(action, tokens) : {Impl.page_transition(action, page, request) == Spec.page_gate(_, action, page, request) : Maybe<&2, Spec.Page>}
      page_gate_reference(Impl.page_permission(action, tokens), action, page, request)

def bind_result_reference(+valid: Bool, +ledger: Spec.Ledger, +sink: Bool, +index: Nat,
    +width: Nat, +lease: Spec.Lease)
  -> {Impl.bind_result(valid, ledger, sink, index, width, lease) == Spec.bind_result(valid, ledger, sink, index, width, lease) : Maybe<&2, Spec.Binding>}:
  match valid:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.bind_reference(page, slot, width, request):
  match page slot:
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, Nil{}} Spec.Slot{index, None{}, 0n, 0n}:
      +ledger = {Spec.Ledger{physical, generation, Some{identity}, dummy, activity} : Spec.Ledger}
      %nonzero_reference(width) : {Impl.bind(page, slot, width, request) == Spec.bind_result(Bool.and(_, Bool.and(Spec.quiet(activity), Spec.access(ledger, request))), ledger, sink, index, width, Spec.Lease{physical, generation, identity}) : Maybe<&2, Spec.Binding>}
      %quiet_reference(activity) : {Impl.bind(page, slot, width, request) == Spec.bind_result(Bool.and(Impl.nonzero(width), Bool.and(_, Spec.access(ledger, request))), ledger, sink, index, width, Spec.Lease{physical, generation, identity}) : Maybe<&2, Spec.Binding>}
      %access_reference(ledger, request) : {Impl.bind(page, slot, width, request) == Spec.bind_result(Bool.and(Impl.nonzero(width), Bool.and(Impl.quiet(activity), _)), ledger, sink, index, width, Spec.Lease{physical, generation, identity}) : Maybe<&2, Spec.Binding>}
      bind_result_reference(Bool.and(Impl.nonzero(width), Bool.and(Impl.quiet(activity), Impl.access(ledger, request))),
        ledger, sink, index, width, Spec.Lease{physical, generation, identity})
    case Spec.Page{Spec.Ledger{physical, generation, None{}, dummy, activity}, sink, representation, tokens} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Raw{index}, tokens} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Preview{index}, tokens} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Sealed{}, tokens} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Broken{}, tokens} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, token <> rest} _:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, Nil{}} Spec.Slot{index, Some{lease}, readers, writers}:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, Nil{}} Spec.Slot{index, None{}, 1n+r, writers}:
      {==}
    case Spec.Page{Spec.Ledger{physical, generation, Some{identity}, dummy, activity}, sink, Spec.Vacant{}, Nil{}} Spec.Slot{index, None{}, 0n, 1n+w}:
      {==}

def choose_slot_reference(+valid: Bool, +index: Nat)
  -> {Impl.choose_slot(valid, index) == Spec.choose_slot(valid, index) : Maybe<&2, Spec.Slot>}:
  match valid:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.unbind_reference(slot, ledger, request):
  match slot ledger:
    case Spec.Slot{index, Some{lease}, readers, writers} Spec.Ledger{page, generation, Some{identity}, dummy, activity}:
      %quiet_reference(activity) : {Impl.unbind(slot, ledger, request) == Spec.choose_slot(Bool.and(_, Bool.and(Spec.access(ledger, request), Bool.and(Spec.same(lease, Spec.Lease{page, generation, identity}), Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index) : Maybe<&2, Spec.Slot>}
      %access_reference(ledger, request) : {Impl.unbind(slot, ledger, request) == Spec.choose_slot(Bool.and(Impl.quiet(activity), Bool.and(_, Bool.and(Spec.same(lease, Spec.Lease{page, generation, identity}), Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index) : Maybe<&2, Spec.Slot>}
      %same_reference(lease, Spec.Lease{page, generation, identity}) : {Impl.unbind(slot, ledger, request) == Spec.choose_slot(Bool.and(Impl.quiet(activity), Bool.and(Impl.access(ledger, request), Bool.and(_, Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index) : Maybe<&2, Spec.Slot>}
      choose_slot_reference(Bool.and(Impl.quiet(activity), Bool.and(Impl.access(ledger, request), Bool.and(Impl.same(lease, Spec.Lease{page, generation, identity}), Bool.and(Nat.is_eq(readers, 0n), Nat.is_eq(writers, 0n))))), index)
    case Spec.Slot{index, None{}, readers, writers} _:
      {==}
    case Spec.Slot{index, Some{lease}, readers, writers} Spec.Ledger{page, generation, None{}, dummy, activity}:
      {==}

def Laws.release_references(page, generation, owner, dummy, shared, readers, writers, request):
  {==}

def Laws.release_readers(page, generation, owner, dummy, shared, readers, writers, request):
  match shared:
    case 0n:
      {==}
    case 1n+s:
      {==}

def Laws.release_writers(page, generation, owner, dummy, shared, readers, writers, request):
  match shared readers:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+s _:
      {==}

def dummy_access(+page: Nat, +generation: Nat, +owner: Maybe<&2, Nat>,
    +activity: Spec.Counts, +request: Spec.Request)
  -> {Impl.access(Spec.Ledger{page, generation, owner, True{}, activity}, request) == False{} : Bool}:
  match owner request:
    case Some{identity} Spec.Present{lease}:
      %Equal.sym(Bool, Bool.and(Impl.nonzero(page), False{}), False{}, and_false(Impl.nonzero(page))) :
        {Bool.and(_, Impl.same(Spec.Lease{page, generation, identity}, lease)) == False{} : Bool}
      {==}
    case Some{identity} Spec.Missing{}:
      {==}
    case Some{identity} Spec.Bad{}:
      {==}
    case Some{identity} Spec.Cancelled{}:
      {==}
    case None{} _:
      {==}

def release_denied(+ledger: Spec.Ledger, +request: Spec.Request,
    denied: {Impl.access(ledger, request) == False{} : Bool})
  -> {Impl.transition(Spec.Release{}, ledger, request) == None{} : Maybe<&2, Spec.Ledger>}:
  %Equal.sym(Bool, Impl.access(ledger, request), False{}, denied) :
    {Impl.choose(Bool.and(Impl.quiet(Impl.counts(ledger)), _), Spec.Release{}, ledger) == None{} : Maybe<&2, Spec.Ledger>}
  Equal.cong(Bool, Maybe<&2, Spec.Ledger>, valid => Impl.choose(valid, Spec.Release{}, ledger),
    Bool.and(Impl.quiet(Impl.counts(ledger)), False{}), False{}, and_false(Impl.quiet(Impl.counts(ledger))))

def Laws.dummy_never_reclaimed(page, generation, owner, activity, request):
  release_denied(Spec.Ledger{page, generation, owner, True{}, activity}, request,
    dummy_access(page, generation, owner, activity, request))

def Laws.zero_never_accessible(generation, owner, dummy, activity, request):
  match owner request:
    case Some{identity} Spec.Present{lease}:
      {==}
    case Some{identity} Spec.Missing{}:
      {==}
    case Some{identity} Spec.Bad{}:
      {==}
    case Some{identity} Spec.Cancelled{}:
      {==}
    case None{} _:
      {==}

def Laws.stale_generation_rejected(page, generation, owner, dummy, activity, old_page, old_generation, old_owner, stale):
  %Equal.sym(Bool, Nat.is_eq(generation, old_generation), False{}, stale) :
    {Bool.and(Impl.ordinary(Spec.Ledger{page, generation, Some{owner}, dummy, activity}),
      Bool.and(Nat.is_eq(page, old_page), Bool.and(_, Nat.is_eq(owner, old_owner)))) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(Nat.is_eq(page, old_page), False{}), False{}, and_false(Nat.is_eq(page, old_page))) :
    {Bool.and(Impl.ordinary(Spec.Ledger{page, generation, Some{owner}, dummy, activity}), _) == False{} : Bool}
  and_false(Impl.ordinary(Spec.Ledger{page, generation, Some{owner}, dummy, activity}))

def Laws.missing_cancelled_invalid(ledger):
  match ledger:
    case Spec.Ledger{page, generation, owner, dummy, activity}:
      match owner:
        case None{}:
          ({==}, {==}, {==})
        case Some{identity}:
          ({==}, {==}, {==})

def same_self(+page: Nat, +generation: Nat, +owner: Nat)
  -> {Impl.same(Spec.Lease{page, generation, owner}, Spec.Lease{page, generation, owner}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(page, page), True{}, eq_self(page)) :
    {Bool.and(_, Bool.and(Nat.is_eq(generation, generation), Nat.is_eq(owner, owner))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(generation, generation), True{}, eq_self(generation)) :
    {Bool.and(_, Nat.is_eq(owner, owner)) == True{} : Bool}
  eq_self(owner)

def access_self(+page: Nat, +generation: Nat, +owner: Nat, activity: Spec.Counts)
  -> {Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, activity},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}) == True{} : Bool}:
  same_self(1n+page, generation, owner)

def Laws.allocate_progress(page, generation, owner):
  {==}

def Laws.reserve_progress(page, generation, owner):
  {==}

def Laws.release_progress(page, generation, owner):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{0n, 0n, 0n})) :
    {Impl.choose(_, Spec.Release{}, Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}}) ==
      Some{Spec.Ledger{1n+page, generation, None{}, False{}, Spec.Counts{0n, 0n, 0n}}} : Maybe<&2, Spec.Ledger>}
  {==}

def Laws.reuse_rejects_old_lease(page, generation, owner, activity):
  Laws.stale_generation_rejected(1n+page, 1n+generation, owner, False{}, activity,
    1n+page, generation, owner, successor_not_old(generation))

def Laws.shared_readonly(page, generation, owner, dummy, shared, readers, writers, request):
  {==}

def Laws.read_progress(page, generation, owner, shared, readers):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{shared, readers, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{shared, readers, 0n})) :
    {Impl.choose(_, Spec.StartRead{}, Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{shared, readers, 0n}}) ==
      Some{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{shared, 1n+readers, 0n}}} : Maybe<&2, Spec.Ledger>}
  {==}

def Laws.write_progress(page, generation, owner):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{0n, 0n, 0n})) :
    {Impl.choose(_, Spec.StartWrite{}, Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}}) ==
      Some{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}}} : Maybe<&2, Spec.Ledger>}
  {==}

def Laws.observed_release_progress(ledger, request, exact, authorized):
  match ledger:
    case Spec.Ledger{page, generation, owner, dummy, activity}:
      %Equal.sym(Spec.Counts, Impl.counts(ledger), Spec.Counts{0n, 0n, 0n}, exact) :
        {Impl.choose(Bool.and(Impl.quiet(_), Impl.access(ledger, request)), Spec.Release{}, ledger) == Some{Spec.candidate(Spec.Release{}, ledger)} : Maybe<&2, Spec.Ledger>}
      %Equal.sym(Bool, Impl.access(ledger, request), True{}, authorized) :
        {Impl.choose(_, Spec.Release{}, ledger) == Some{Spec.candidate(Spec.Release{}, ledger)} : Maybe<&2, Spec.Ledger>}
      {==}

def Laws.bind_progress(page, generation, owner, slot, width, sink):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{0n, 0n, 0n})) :
    {Impl.bind_result(_, Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}}, sink, slot,
      1n+width, Spec.Lease{1n+page, generation, owner}) == Some{Spec.Binding{Spec.Page{Spec.Ledger{1n+page, generation,
        Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}}, sink, Spec.Raw{slot}, List.replicate(Spec.Token, 1n+width, Spec.Hole{})},
          Spec.Slot{slot, Some{Spec.Lease{1n+page, generation, owner}}, 0n, 0n}}} : Maybe<&2, Spec.Binding>}
  {==}

def Laws.slot_owned_not_reused(index, old, readers, writers, next):
  {==}

def Laws.slot_reader_blocks_unbind(index, owner, readers, writers, ledger, request):
  match owner ledger:
    case Some{lease} Spec.Ledger{page, generation, Some{identity}, dummy, activity}:
      Equal.cong(Bool, Maybe<&2, Spec.Slot>, valid => Impl.choose_slot(valid, index),
        Bool.and(Impl.quiet(activity), Bool.and(Impl.access(ledger, request), Bool.and(Impl.same(lease, Spec.Lease{page, generation, identity}), False{}))),
        False{}, and3_false(Impl.quiet(activity), Impl.access(ledger, request), Impl.same(lease, Spec.Lease{page, generation, identity})))
    case None{} _:
      {==}
    case Some{lease} Spec.Ledger{page, generation, None{}, dummy, activity}:
      {==}

def Laws.slot_writer_blocks_unbind(index, owner, readers, writers, ledger, request):
  match owner ledger:
    case Some{lease} Spec.Ledger{page, generation, Some{identity}, dummy, activity}:
      %Equal.sym(Bool, Bool.and(Nat.is_eq(readers, 0n), False{}), False{}, and_false(Nat.is_eq(readers, 0n))) :
        {Impl.choose_slot(Bool.and(Impl.quiet(activity), Bool.and(Impl.access(ledger, request), Bool.and(Impl.same(lease, Spec.Lease{page, generation, identity}), _))), index) == None{} : Maybe<&2, Spec.Slot>}
      Equal.cong(Bool, Maybe<&2, Spec.Slot>, valid => Impl.choose_slot(valid, index),
        Bool.and(Impl.quiet(activity), Bool.and(Impl.access(ledger, request), Bool.and(Impl.same(lease, Spec.Lease{page, generation, identity}), False{}))),
        False{}, and3_false(Impl.quiet(activity), Impl.access(ledger, request), Impl.same(lease, Spec.Lease{page, generation, identity})))
    case None{} _:
      {==}
    case Some{lease} Spec.Ledger{page, generation, None{}, dummy, activity}:
      {==}

def Laws.invalidate_preview(representation):
  match representation:
    case Spec.Vacant{}:
      {==}
    case Spec.Raw{slot}:
      {==}
    case Spec.Preview{slot}:
      {==}
    case Spec.Sealed{}:
      {==}
    case Spec.Broken{}:
      {==}

def Laws.discard_preserves_disjointness(tokens):
  match tokens:
    case Nil{}:
      {==}
    case Spec.Hole{} <> rest:
      Laws.discard_preserves_disjointness(rest)
    case Spec.Provisional{} <> rest:
      Laws.discard_preserves_disjointness(rest)
    case Spec.Committed{} <> rest:
      Laws.discard_preserves_disjointness(rest)
    case Spec.Conflict{} <> rest:
      {==}

def Laws.committed_not_overwritten(offset):
  {==}

def Laws.provisional_commit_progress(offset):
  {==}

def Laws.discard_invalidates_preview(slot, width, sink, tokens):
  {==}

def Laws.provisional_never_sealed(slot, width, sink, tokens):
  match width:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Bool, Maybe<&2, Spec.Representation>, valid => Impl.choose_rep(valid, Spec.Sealed{}),
        Bool.and(Bool.not(sink), False{}), False{}, and_false(Bool.not(sink)))

def Laws.sink_never_sealed(slot, width, tokens):
  Equal.cong(Bool, Maybe<&2, Spec.Representation>, valid => Impl.choose_rep(valid, Spec.Sealed{}),
    Bool.and(Impl.nonzero(width), False{}), False{}, and_false(Impl.nonzero(width)))

def Laws.seal_progress(slot, width, tokens, full):
  %Equal.sym(Bool, Impl.complete(1n+width, tokens, True{}), True{}, full) :
    {Impl.choose_rep(_, Spec.Sealed{}) == Some{Spec.Sealed{}} : Maybe<&2, Spec.Representation>} &
    {Spec.has_preview(Spec.Sealed{}) == False{} : Bool}
  ({==}, {==})

def Laws.address_reference(width, page, offset):
  {==}

def add_lt(+base: Nat, +offset: Nat, +width: Nat)
  -> {Nat.is_lt(Nat.add(base, offset), Nat.add(base, width)) == Nat.is_lt(offset, width) : Bool}:
  match base:
    case 0n:
      {==}
    case 1n+p:
      add_lt(p, offset, width)

def Laws.address_within_page(base, width, offset, bounded):
  Equal.trans(Bool, Spec.address_bound(base, width, offset), Nat.is_lt(offset, width), True{},
    add_lt(base, offset, width), bounded)

def Laws.claim_reference(slot, lease):
  match slot lease:
    case Spec.Slot{index, None{}, 0n, 0n} Spec.Lease{1n+p, generation, owner}:
      {==}
    case Spec.Slot{index, None{}, 0n, 0n} Spec.Lease{0n, generation, owner}:
      {==}
    case Spec.Slot{index, None{}, 0n, 1n+w} _:
      {==}
    case Spec.Slot{index, None{}, 1n+r, writers} _:
      {==}
    case Spec.Slot{index, Some{old}, readers, writers} _:
      {==}

def Laws.slot_claim_progress(index, page, generation, owner):
  {==}

def Laws.slot_release_progress(index, page, generation, owner):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 0n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{0n, 0n, 0n})) :
    {Impl.choose_slot(Bool.and(_, Bool.and(Impl.same(Spec.Lease{1n+page, generation, owner}, Spec.Lease{1n+page, generation, owner}), True{})), index) ==
      Some{Spec.Slot{index, None{}, 0n, 0n}} : Maybe<&2, Spec.Slot>}
  %Equal.sym(Bool, Impl.same(Spec.Lease{1n+page, generation, owner}, Spec.Lease{1n+page, generation, owner}), True{}, same_self(1n+page, generation, owner)) :
    {Impl.choose_slot(Bool.and(_, True{}), index) == Some{Spec.Slot{index, None{}, 0n, 0n}} : Maybe<&2, Spec.Slot>}
  {==}

def Laws.bound_link(index, page, generation, owner, activity, sink, tokens):
  %Equal.sym(Bool, Nat.is_eq(index, index), True{}, eq_self(index)) :
    {Bool.and(_, Spec.same(Spec.Lease{1n+page, generation, owner}, Spec.Lease{1n+page, generation, owner})) == True{} : Bool}
  same_self(1n+page, generation, owner)

def Laws.cancelled_allocation_rejected(owner, ledger):
  Equal.cong(Bool, Maybe<&2, Spec.Ledger>, valid => Impl.choose(valid, Spec.Allocate{owner}, ledger),
    Bool.and(Impl.vacant(ledger), False{}), False{}, and_false(Impl.vacant(ledger)))

def Truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

def false_not_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : Truth(_)
  Unit{}

def and_right(+a: Bool, +b: Bool, valid: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({b == True{} : Bool}, false_not_true(valid))
    case True{}:
      valid

def and_parts(+a: Bool, +b: Bool, valid: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, false_not_true(valid))
    case True{}:
      ({==}, valid)

def head_safe(edit: Spec.Edit, token: Spec.Token, +rest: List<&2, Spec.Token>,
    valid: {Spec.consistent(rest) == True{} : Bool})
  -> {Spec.safe_tokens(Impl.replace_head(Impl.token_edit(edit, token), rest)) == True{} : Bool}:
  match edit token:
    case Spec.Stage{offset} Spec.Hole{}:
      valid
    case Spec.Stage{offset} Spec.Provisional{}:
      valid
    case Spec.Commit{offset} Spec.Provisional{}:
      valid
    case Spec.Stage{offset} Spec.Committed{}:
      {==}
    case Spec.Stage{offset} Spec.Conflict{}:
      {==}
    case Spec.Commit{offset} Spec.Hole{}:
      {==}
    case Spec.Commit{offset} Spec.Committed{}:
      {==}
    case Spec.Commit{offset} Spec.Conflict{}:
      {==}
    case Spec.Discard{} _:
      {==}
    case Spec.PackPreview{} _:
      {==}
    case Spec.Seal{} _:
      {==}

def prepend_safe(+updated: Maybe<&2, List<&2, Spec.Token>>, +token: Spec.Token,
    head: {Spec.disjoint(token) == True{} : Bool},
    tail: {Spec.safe_tokens(updated) == True{} : Bool})
  -> {Spec.safe_tokens(Impl.prepend(updated, token)) == True{} : Bool}:
  match updated:
    case None{}:
      {==}
    case Some{tokens}:
      %Equal.sym(Bool, Spec.disjoint(token), True{}, head) :
        {Bool.and(_, Spec.consistent(tokens)) == True{} : Bool}
      tail

def prepend_proved(+updated: Maybe<&2, List<&2, Spec.Token>>, +token: Spec.Token,
    +rest: List<&2, Spec.Token>,
    pieces: {Spec.disjoint(token) == True{} : Bool} & {Spec.consistent(rest) == True{} : Bool},
    continuation: {Spec.consistent(rest) == True{} : Bool} -> {Spec.safe_tokens(updated) == True{} : Bool})
  -> {Spec.safe_tokens(Impl.prepend(updated, token)) == True{} : Bool}:
  (head, tail) = pieces
  prepend_safe(updated, token, head, continuation(tail))

def Laws.replace_preserves_disjointness(edit, offset, tokens, valid):
  match offset tokens:
    case 0n token <> rest:
      head_safe(edit, token, rest, and_right(Spec.disjoint(token), Spec.consistent(rest), valid))
    case 1n+p token <> rest:
      prepend_proved(Impl.replace(edit, p, rest), token, rest,
        and_parts(Spec.disjoint(token), Spec.consistent(rest), valid),
        tail => Laws.replace_preserves_disjointness(edit, p, rest, tail))
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}

def Laws.stage_progress(page, generation, owner, slot, width, sink, rest, valid):
  %Equal.sym(Bool, Impl.access(Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}},
    Spec.Present{Spec.Lease{1n+page, generation, owner}}), True{}, access_self(page, generation, owner, Spec.Counts{0n, 0n, 1n})) :
    {Impl.content_gate(Bool.and(_, Bool.and(Impl.consistent(rest), True{})), Spec.Stage{0n}, 1n+width,
      Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}}, sink,
        Spec.Preview{slot}, Spec.Hole{} <> rest}) == Some{Spec.Page{Spec.Ledger{1n+page, generation, Some{owner},
          False{}, Spec.Counts{0n, 0n, 1n}}, sink, Spec.Raw{slot}, Spec.Provisional{} <> rest}} : Maybe<&2, Spec.Page>}
  %Equal.sym(Bool, Impl.consistent(rest), True{}, valid) :
    {Impl.content_gate(Bool.and(_, True{}), Spec.Stage{0n}, 1n+width,
      Spec.Page{Spec.Ledger{1n+page, generation, Some{owner}, False{}, Spec.Counts{0n, 0n, 1n}}, sink,
        Spec.Preview{slot}, Spec.Hole{} <> rest}) == Some{Spec.Page{Spec.Ledger{1n+page, generation, Some{owner},
          False{}, Spec.Counts{0n, 0n, 1n}}, sink, Spec.Raw{slot}, Spec.Provisional{} <> rest}} : Maybe<&2, Spec.Page>}
  {==}

def committed_complete(+width: Nat)
  -> {Impl.complete(width, List.replicate(Spec.Token, width, Spec.Committed{}), True{}) == True{} : Bool}:
  match width:
    case 0n:
      {==}
    case 1n+p:
      committed_complete(p)

def Laws.committed_page_seals(slot, width):
  %Equal.sym(Bool, Impl.complete(1n+width, List.replicate(Spec.Token, 1n+width, Spec.Committed{}), True{}),
    True{}, committed_complete(1n+width)) :
    {Impl.choose_rep(_, Spec.Sealed{}) == Some{Spec.Sealed{}} : Maybe<&2, Spec.Representation>}
  {==}

def Laws.exact_logical_row(width, base, offset):
  match width:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, Nat.is_eq(Nat.add(base, offset), Nat.add(base, offset)), True{}, eq_self(Nat.add(base, offset))) :
        {Bool.and(_, Spec.row(p, base, 1n+offset, Impl.locations(p, base, 1n+offset))) == True{} : Bool}
      Laws.exact_logical_row(p, base, 1n+offset)
