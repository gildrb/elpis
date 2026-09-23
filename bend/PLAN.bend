# Standalone CPU startup program. Exactly one print, once at startup.
# Base IO.print adds the final newline. No runtime proof or per-token process.
import Base
import ./control.bend as Control

def rows(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      Nat.show(h) ++ "\n" ++ rows(t)

def render(plan: Control.Plan) -> String:
  match plan:
    case Control.Plan{fields, free_pages}:
      "QWEN_KVARN_PLAN_V2\n" ++ rows(fields) ++ "FREE_PAGES\n" ++
        rows(free_pages) ++ "END_QWEN_KVARN_PLAN"

def accepted(result: Maybe<&2, Control.Plan>) -> String:
  match result:
    case None{}:
      "QWEN_KVARN_PLAN_ERROR"
    case Some{plan}:
      render(plan)

def protocol() -> String:
  accepted(Control.plan(262144n, 263168n, 128n))

def main() -> IO(Unit):
  IO.print(protocol())
