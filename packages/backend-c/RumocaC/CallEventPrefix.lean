import RumocaC.CallEventChoices
import RumocaCore.Transition.Events.Prefix

/-! Determined call prefixes retain their event trace while leaving the
continuation free to choose, fail or diverge. -/
noncomputable section
namespace Rumoca.CCalls.Events
variable {E : Type} [interface : CInterface]
open CMemory

theorem internal_path (program : Program E)
    (path : Transition.Reaches (fun s t => internalNext program s = some t) s t) :
    Transition.Events.Prefix (machine program) s [] t := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next (Step.internal first) (internal_unique program first) ih

theorem external_path (program : Program E) (found : program.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (executed : fn.execute values before events result after)
    (unique : ∀ trace value heap, fn.execute values before trace value heap →
      trace = events ∧ value = result ∧ heap = after) (stack : Typed.Continuation) :
    Transition.Events.Prefix (machine program) (.calling name args before stack) events
      (.returning result after stack) := by
  simpa only [List.append_nil] using Transition.Events.Prefix.next
    (m := machine program) (Step.external found converted executed) (fun trace state step => by
      obtain ⟨value, heap, operation, rfl⟩ := (external_step_iff program found converted).mp step
      obtain ⟨rfl, rfl, rfl⟩ := unique _ _ _ operation
      exact ⟨rfl, rfl⟩) (.refl _)

end Rumoca.CCalls.Events
