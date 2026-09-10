import Parser.Regex
import Parser.AutomatonRuntime

namespace Parser

/-- The state language is a proof-only annotation, erased from the runtime.
The generated finite tables are checked by kernel reduction. -/
structure CertifiedDFA (α : Type) [DecidableEq α] where
  State : Type
  start : State
  next : State → α → State
  final : State → Bool
  language : State → RE α
  next_correct : ∀ s c, (language s).step c = language (next s c)
  final_correct : ∀ s, final s = (language s).nullable

namespace CertifiedDFA

def run [DecidableEq α] (d : CertifiedDFA α) (s : d.State) (xs : List α) : Bool :=
  runDFA d.next d.final s xs

theorem run_correct [DecidableEq α] (d : CertifiedDFA α) (s : d.State) (xs : List α) :
    d.run s xs = true ↔ (d.language s).Accepts xs := by
  induction xs generalizing s with
  | nil => rw [run, runDFA, d.final_correct]; exact RegularExpression.nullable_correct _
  | cons c cs ih =>
    change d.run (d.next s c) cs = true ↔ _
    rw [ih, ← d.next_correct]
    exact RegularExpression.step_correct _ _ _

end CertifiedDFA
end Parser
