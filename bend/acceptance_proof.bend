# Live structural proof terms. No unsafe definitions, axioms or foreign proof
# code. Only the fixed 128-mask domain is specialized; reducer safety is general.
import Base
import ./acceptance.bend as Acceptance
import ./acceptance_spec.bend as Spec
import ./acceptance_laws.bend as Laws
import ./spec.bend as Sequence
import ./ACCEPT.bend as Wire

# A summary acts on a hypothetical continuation count. Stopped summaries never
# consult it; this interpretation proves concatenation without trusting combine.
def resume(summary: Acceptance.Summary, continuation: Nat) -> Nat:
  match summary:
    case Acceptance.Full{length}:
      Nat.add(length, continuation)
    case Acceptance.Stopped{accepted}:
      accepted

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_assoc(n: Nat, -m: Nat, -k: Nat)
  -> {Nat.add(Nat.add(n, m), k) == Nat.add(n, Nat.add(m, k)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, m, k) : {1n+Nat.add(Nat.add(p, m), k) == 1n+_ : Nat}
      {==}

def resume_zero(summary: Acceptance.Summary)
  -> {resume(summary, 0n) == Acceptance.count(summary) : Nat}:
  match summary:
    case Acceptance.Full{length}:
      add_zero(length)
    case Acceptance.Stopped{accepted}:
      {==}

def combine_resume(left: Acceptance.Summary, right: Acceptance.Summary, continuation: Nat)
  -> {resume(Acceptance.combine(left, right), continuation) ==
    resume(left, resume(right, continuation)) : Nat}:
  match left:
    case Acceptance.Stopped{accepted}:
      {==}
    case Acceptance.Full{length}:
      match right:
        case Acceptance.Full{next}:
          add_assoc(length, next, continuation)
        case Acceptance.Stopped{accepted}:
          {==}

# Sequential concatenation, proved on arbitrary finite Boolean lists.
def scan_append(+left: List<&2, Bool>, +right: List<&2, Bool>, +continuation: Nat)
  -> {Spec.scan(left, Spec.scan(right, continuation)) ==
    Spec.scan(List.append(&2, Bool, left, right), continuation) : Nat}:
  match left:
    case Nil{}:
      {==}
    case False{} <> rest:
      {==}
    case True{} <> rest:
      %scan_append(rest, right, continuation) :
        {1n+Spec.scan(rest, Spec.scan(right, continuation)) ==
          1n+_ : Nat}
      {==}

# Both subtree induction hypotheses stay live. Their combination explains the
# exact parallel implementation, not an independently enumerated answer table.
def resume_tree(+tree: Acceptance.Tree, +continuation: Nat)
  -> {resume(Acceptance.summarize(tree), continuation) ==
    Spec.scan(Spec.flatten(tree), continuation) : Nat}:
  match tree:
    case Acceptance.Empty{}:
      {==}
    case Acceptance.Bit{equal}:
      match equal:
        case False{}:
          {==}
        case True{}:
          {==}
    case Acceptance.Fork{left, right}:
      %scan_append(Spec.flatten(left), Spec.flatten(right), continuation) :
        {resume(Acceptance.combine(Acceptance.summarize(left), Acceptance.summarize(right)), continuation) == _ : Nat}
      %resume_tree(left, Spec.scan(Spec.flatten(right), continuation)) :
        {resume(Acceptance.combine(Acceptance.summarize(left), Acceptance.summarize(right)), continuation) == _ : Nat}
      %resume_tree(right, continuation) :
        {resume(Acceptance.combine(Acceptance.summarize(left), Acceptance.summarize(right)), continuation) ==
          resume(Acceptance.summarize(left), _) : Nat}
      combine_resume(Acceptance.summarize(left), Acceptance.summarize(right), continuation)

def Laws.tree_semantics(tree):
  %resume_zero(Acceptance.summarize(tree)) :
    {_ == Spec.prefix(Spec.flatten(tree)) : Nat}
  resume_tree(tree, 0n)

def prefix_bound(+bits: List<&2, Bool>)
  -> {Nat.is_le(Spec.prefix(bits), List.length(&2, Bool, bits)) == True{} : Bool}:
  match bits:
    case Nil{}:
      {==}
    case False{} <> rest:
      {==}
    case True{} <> rest:
      prefix_bound(rest)

def Laws.tree_bound(tree):
  %Equal.sym(Nat, Acceptance.accepted(tree), Spec.prefix(Spec.flatten(tree)),
    Laws.tree_semantics(tree)) :
    {Nat.is_le(_, List.length(&2, Bool, Spec.flatten(tree))) == True{} : Bool}
  prefix_bound(Spec.flatten(tree))

# An arbitrary suffix disappears at the first false, after exactly n trues.
def repeat_stop(n: Nat, +suffix: List<&2, Bool>)
  -> {Spec.prefix(List.append(&2, Bool, List.replicate(Bool, n, True{}),
    False{} <> suffix)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %repeat_stop(p, suffix) :
        {1n+Spec.prefix(List.append(&2, Bool, List.replicate(Bool, p, True{}),
          False{} <> suffix)) == 1n+_ : Nat}
      {==}

def Laws.first_mismatch(tree, n, suffix, layout):
  %repeat_stop(n, suffix) : {Acceptance.accepted(tree) == _ : Nat}
  %layout : {Acceptance.accepted(tree) == Spec.prefix(_) : Nat}
  Laws.tree_semantics(tree)

def Laws.seven_semantics(b0, b1, b2, b3, b4, b5, b6):
  Laws.tree_semantics(Acceptance.seven(b0, b1, b2, b3, b4, b5, b6))

def Laws.mask_inputs(mask):
  {==}

def Laws.mask_semantics(mask):
  %Laws.mask_inputs(mask) : {Acceptance.accept_mask(mask) == Spec.prefix(_) : Nat}
  Laws.tree_semantics(Acceptance.mask_tree(mask))

def Laws.native_bound(mask):
  %Equal.sym(Nat, Acceptance.accept_mask(mask), Spec.prefix(Spec.bits(7n, mask)),
    Laws.mask_semantics(mask)) : {Nat.is_le(_, 7n) == True{} : Bool}
  prefix_bound(Spec.bits(7n, mask))

# Range.tree's balanced traversal normalizes to precisely these 128 consecutive
# masks. This proves order/domain, not acceptance by a closed answer literal.
def Laws.emitter_domain():
  {==}

def decisions_seq(n: Nat, +start: Nat)
  -> {Acceptance.decisions(Sequence.seq(n, start)) == Spec.table(n, start) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Laws.mask_semantics(start) :
        {Acceptance.accept_mask(start) <> Acceptance.decisions(Sequence.seq(p, 1n+start)) ==
          _ <> Spec.table(p, 1n+start) : List<&2, Nat>}
      %decisions_seq(p, 1n+start) :
        {Acceptance.accept_mask(start) <> Acceptance.decisions(Sequence.seq(p, 1n+start)) ==
          Acceptance.accept_mask(start) <> _ : List<&2, Nat>}
      {==}

def Laws.emitter_values():
  %Equal.sym(List<&2, Nat>, Acceptance.masks(), Sequence.seq(128n, 0n),
    Laws.emitter_domain()) :
    {Acceptance.decisions(_) == Spec.table(128n, 0n) : List<&2, Nat>}
  decisions_seq(128n, 0n)

def table_length(n: Nat, start: Nat)
  -> {List.length(&2, Nat, Spec.table(n, start)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %table_length(p, 1n+start) :
        {1n+List.length(&2, Nat, Spec.table(p, 1n+start)) == 1n+_ : Nat}
      {==}

def Laws.emitter_count():
  %Equal.sym(List<&2, Nat>, Acceptance.values(), Spec.table(128n, 0n),
    Laws.emitter_values()) : {List.length(&2, Nat, _) == 128n : Nat}
  table_length(128n, 0n)

def Laws.rows_semantics(values):
  match values:
    case Nil{}:
      {==}
    case value <> rest:
      %Laws.rows_semantics(rest) :
        {Nat.show(value) ++ "\n" ++ Wire.rows(rest) ==
          Nat.show(value) ++ "\n" ++ _ : String}
      {==}

def Laws.acceptance_wire():
  %Laws.rows_semantics(Spec.table(128n, 0n)) :
    {Wire.protocol() == "QWEN_DFLASH_ACCEPT_V1\n7\n128\n" ++ _ ++
      "END_QWEN_DFLASH_ACCEPT" : String}
  %Laws.emitter_values() :
    {Wire.protocol() == "QWEN_DFLASH_ACCEPT_V1\n7\n128\n" ++ Wire.rows(_) ++
      "END_QWEN_DFLASH_ACCEPT" : String}
  {==}
