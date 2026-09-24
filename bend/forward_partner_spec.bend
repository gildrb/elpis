# Proof-only selected 32x256 forward model. Reuse the established coordinate
# maps, XOR interpretation and ordered Expr helpers, NOT inverse permission.
import Base
import ./inverse_partner_spec.bend as Transport
import ./attention_schedule_spec.bend as Attention

def forward_partner_stages(head256: Bool, rows32: Bool) -> Nat:
  match head256 rows32:
    case True{} True{}:
      3n
    case _ _:
      0n

def row(+index: Nat) -> Nat:
  forward_partner_stages(Transport.bit(index), Transport.bit(Nat.div(index, 2n)))

def Action(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Empty
        case 1n+q:
          match q:
            case 0n:
              Empty
            case 1n+r:
              match r:
                case 0n:
                  Unit
                case 1n+s:
                  Empty

# This is exactly the native loop's bit < FORWARD_PARTNER_STAGES condition.
# False is the ORIGINAL XOR gather, not a different transport certificate.
def permute(stage: Nat, stages: Nat) -> Bool:
  Nat.is_lt(stage, stages)

def partner(permute: Bool, +stage: Nat, +lane: Nat) -> Nat:
  Bool.pick(Nat, permute, Transport.selected_partner(stage, lane),
    Transport.reference_partner(stage, lane))

def read_row(permute: Bool, stage: Nat, +row: Nat, lane: Nat) -> Nat:
  Bool.pick(Nat, permute,
    Transport.coordinate_row(Transport.transport(Transport.reshape(stage, row, lane))), row)

def native_count(head256: Bool) -> Nat:
  Bool.pick(Nat, head256, 8n, 7n)

def trace(count: Nat, +stages: Nat) -> List<&2, Bool>:
  match count:
    case 0n:
      Nil{}
    case 1n++p:
      List.append(&2, Bool, trace(p, stages), [permute(p, stages)])

# Prefix p+1 reads BOTH operands from prefix p. The mask and both ordered
# branches are the original Where(low, Add(current,partner), Sub(partner,current)).
# Missing inputs remain None; no implicit zero or invented initial expression.
def scheduled(count: Nat, +stages: Nat, +values: List<&2, Attention.Expr>, +lane: Nat)
    -> Maybe<&2, Attention.Expr>:
  match count:
    case 0n:
      Transport.lookup(values, lane)
    case 1n++p:
      Transport.lift(Transport.reference_low(p, lane), scheduled(p, stages, values, lane),
        scheduled(p, stages, values, partner(permute(p, stages), p, lane)))

# Only NEW certificate: first three partners stay in the same group of eight
# logical columns. This is a source-layout property, NOT register allocation,
# warp routing, absence of shuffles or any compiler/hardware guarantee.
def local_check(+stage: Nat, +lane: Nat) -> Bool:
  Nat.is_eq(Nat.div(Transport.selected_partner(stage, lane), 8n), Nat.div(lane, 8n))

def local_checks(count: Nat, +start: Nat, +stage: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(local_check(stage, start), local_checks(p, 1n+start, stage))

# Explicit forward-loop context: sanitized are the actual lane expressions
# AFTER the unchanged native query_ok select, not Ref{input, RotatedQuery{}}.
# Their construction (load/F32/isfinite/reduction/select and atomics) is an
# unchanged external source boundary. All masks, guard observations and sticky
# status remain identities; we do not manufacture a new arithmetic constructor.
type Context is Data:
  Context{input: Attention.Input, sanitized: List<&2, Attention.Expr>,
    load_mask: Attention.Expr, query_mask: Attention.Expr, row_mask: Attention.Expr,
    raw_any: Bool, packed_any: Bool, status: Attention.Expr}

def entering(context: Context) -> List<&2, Attention.Expr>:
  match context:
    case Context{input, sanitized, load_mask, query_mask, row_mask, raw_any, packed_any, status}:
      sanitized

def input(context: Context) -> Attention.Input:
  match context:
    case Context{input, sanitized, load_mask, query_mask, row_mask, raw_any, packed_any, status}:
      input

type Query is Data:
  Query{context: Context, raw: Attention.Expr, rotated: Attention.Expr}

def finish(+context: Context, original: Attention.Expr, result: Attention.Expr) -> Query:
  Query{context, Attention.F16{original},
    Attention.F16{Attention.Mul{result, Attention.Ref{input(context), Attention.Normalize{}}}}}

def finish_result(context: Context, original: Maybe<&2, Attention.Expr>, result: Maybe<&2, Attention.Expr>)
    -> Maybe<&2, Query>:
  match original result:
    case Some{original} Some{result}:
      Some{finish(context, original, result)}
    case _ _:
      None{}

def QueryPresent(query: Maybe<&2, Query>) -> Type:
  match query:
    case None{}:
      Empty
    case Some{value}:
      Unit

# The exact same sanitized entering lane supplies raw F16 in both endpoints.
# No law equates the attention model's opaque RotatedQuery leaf to this tree.
def reference_query(prefix: Nat, +context: Context, +lane: Nat) -> Maybe<&2, Query>:
  finish_result(context, Transport.lookup(entering(context), lane),
    Transport.reference(prefix, entering(context), lane))
