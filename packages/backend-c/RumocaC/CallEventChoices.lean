import RumocaC.CallEvents
import RumocaCore.Transition.Events.Choices

/-! Complete observations across internal prefixes and external choices.
The caller supplies a proved continuation for every represented outcome. -/
noncomputable section
namespace Rumoca.CCalls.Events
variable {E : Type}
variable [interface : CInterface]
open CMemory

/-- No restriction is placed on events or choices after the internal prefix. -/
theorem internal_prefix_behaviors (program : Program E)
    (path : Transition.Reaches (fun s t => internalNext program s = some t) s t)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (machine program).Behaves s behavior ↔ (machine program).Behaves t behavior := by
  induction path with
  | refl => rfl
  | next first rest ih =>
      exact ((machine program).silent_step_behaviors (.internal first)
        (internal_unique program first) behavior).trans ih

theorem external_step_iff (program : Program E)
    (found : program.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values) :
    Step program (.calling name args heap stack) events target ↔
      ∃ value after, fn.execute values heap events value after ∧
        target = .returning value after stack := by
  constructor
  · intro step
    cases step with
    | internal next =>
        rw [external_entry_exclusive program found] at next
        contradiction
    | external found' converted' executed =>
        have same := Option.some.inj (found'.symm.trans found)
        cases same
        have sameArgs := Option.some.inj (converted'.symm.trans converted)
        cases sameArgs
        exact ⟨_, _, executed, rfl⟩
  · rintro ⟨value, after, executed, rfl⟩
    exact .external found converted executed

/-- All returning foreign choices followed by a proved silent continuation.
No callback outcome or local determinacy is supplied as a premise. -/
theorem external_choices_behaviors (program : Program E)
    (found : program.externals name = some fn)
    (converted : convertedArguments fn.signature.parameters args = some values)
    (resultOf : Value → Heap → CBody.Result)
    (finished : ∀ events value after, fn.execute values heap events value after →
      Transition.Events.Forced (machine program) (.returning value after stack) [] (resultOf value after))
    (behavior : Transition.Events.Observation E CBody.Result) :
    (machine program).Behaves (.calling name args heap stack) behavior ↔
      (∃ events value after, fn.execute values heap events value after ∧
        behavior = .terminates events (resultOf value after)) ∨
      ((∀ events value after, ¬ fn.execute values heap events value after) ∧ behavior = .wrong []) := by
  have completes : ∀ events target, Step program (.calling name args heap stack) events target →
      ∃ result, Transition.Events.Forced (machine program) target [] result := by
    intro events target step
    obtain ⟨value, after, executed, rfl⟩ := (external_step_iff program found converted).mp step
    exact ⟨resultOf value after, finished events value after executed⟩
  rw [(machine program).terminal_choices_behaviors _ rfl completes behavior]
  constructor
  · rintro (⟨events, target, result, step, forced, observed⟩ | ⟨stuck, observed⟩)
    · obtain ⟨value, after, executed, rfl⟩ := (external_step_iff program found converted).mp step
      have same := ((finished events value after executed).behaviors (.terminates [] result)).mp
        ((forced.behaviors (.terminates [] result)).mpr rfl)
      have resultSame := (Transition.Events.Observation.terminates.inj same).2
      exact Or.inl ⟨events, value, after, executed, resultSame ▸ observed⟩
    · refine Or.inr ⟨?_, observed⟩
      intro events value after executed
      exact stuck events _ (.external found converted executed)
  · rintro (⟨events, value, after, executed, observed⟩ | ⟨missing, observed⟩)
    · exact Or.inl ⟨events, _, resultOf value after, .external found converted executed,
        finished events value after executed, observed⟩
    · refine Or.inr ⟨?_, observed⟩
      intro events target step
      obtain ⟨value, after, executed, _⟩ := (external_step_iff program found converted).mp step
      exact missing events value after executed

end Rumoca.CCalls.Events
