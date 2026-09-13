import RumocaC.CallEventChoices
import RumocaCore.Transition.Events.SilentChoices

/-! Compose silent external choices with arbitrary caller observations. This
supports standard-library routines whose legal return values need not be
unique but whose caller continuations have the same observable behavior. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CMemory
variable [interface : CInterface]

theorem external_silent_equivalence (program : Program E)
    (found : program.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (available : ∃ value after, fn.execute values heap [] value after)
    (silent : ∀ events value after, fn.execute values heap events value after → events = [])
    (equivalent : ∀ value after, fn.execute values heap [] value after →
      ∀ behavior, (machine program).Behaves (.returning value after stack) behavior ↔
        (machine program).Behaves target behavior)
    (behavior) :
    (machine program).Behaves (.calling name args heap stack) behavior ↔
      (machine program).Behaves target behavior := by
  apply (machine program).silent_choices_behaviors
  · obtain ⟨value, after, executed⟩ := available
    exact ⟨_, Step.external found converted executed⟩
  · intro events state step
    obtain ⟨value, after, executed, rfl⟩ := (external_step_iff program found converted).mp step
    exact silent events value after executed
  · intro state step observed
    obtain ⟨value, after, executed, rfl⟩ := (external_step_iff program found converted).mp step
    exact equivalent value after executed observed

end Rumoca.CCalls.Events
