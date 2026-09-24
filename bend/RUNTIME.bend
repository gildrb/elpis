# Startup CPU table wire, not per-step subprocess execution. Original Bend
# IO.print supplies the sole final newline after END_QWEN_RUNTIME_CONTROL.
import Base
import ./transaction.bend as Transaction
import ./marlin_pipeline.bend as MarlinPipeline
import ./attention_schedule.bend as AttentionSchedule
import ./inverse_partner.bend as InversePartner
import ./forward_partner.bend as ForwardPartner

def rows(values: List<&2, Nat>) -> String:
  match values:
    case Nil{}:
      ""
    case value <> rest:
      Nat.show(value) ++ "\n" ++ rows(rest)

def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V7\nFREE_MIRROR\n8\n" ++
    rows(Transaction.free_table(3n, False{}, False{}, False{})) ++
    "STATUS\n8\n" ++
    rows(Transaction.status_table(3n, False{}, False{}, False{})) ++
    "MARLIN_EIGHT_STAGE\n8\n" ++
    rows(MarlinPipeline.table(3n, False{}, False{}, False{})) ++
    "MARLIN_SCALE_REFRESH\n8\n" ++
    rows(MarlinPipeline.scale_refresh_table(8n, 0n)) ++
    "PACKED_LATE_VALUE\n4\n" ++
    rows(AttentionSchedule.table(2n, False{}, False{})) ++
    "PACKED_INVERSE_PARTNER\n4\n" ++
    rows(InversePartner.table(2n, False{}, False{})) ++
    "PACKED_FORWARD_PARTNER_STAGES\n4\n" ++
    rows(ForwardPartner.table(2n, False{}, False{})) ++
    "MARLIN_SELECTED_SHARED_BYTES\n1\n" ++
    Nat.show(MarlinPipeline.selected_shared_bytes()) ++ "\n" ++
    "END_QWEN_RUNTIME_CONTROL"

def main() -> IO(Unit):
  IO.print(protocol())
