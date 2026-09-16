import RumocaC.InitializationCompletion

namespace Rumoca.CCalls.InitializationRegion
open CTree CMemory CBody.Footprint
variable [interface : CInterface] {E : Type}

/-- A protected initializer cannot get stuck before root completion. The
successor is the actual internal C step, with a strictly smaller control count. -/
theorem complete_next_ready (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (active : ¬ ∃ result, state = .halted result) :
    ∃ after, Events.internalNext program state = some after ∧
      CompleteReady region env types resultExpr resultType expected returned after ∧
      remaining after + 1 = remaining state ∧
      Set.EqOn (CReadOnly.typedHeap after) (CReadOnly.typedHeap state) regionᶜ := by
  rcases ready with ready | ⟨heap, rfl, _⟩
  · by_cases exited : Concurrent.Exit .done state
    · obtain ⟨value, heap, rfl⟩ := exited
      obtain ⟨identity, agreement⟩ := ready.exit
      subst value
      refine ⟨.halted ⟨returned, heap⟩, ?_, .inr ⟨heap, rfl, agreement⟩, rfl, fun _ _ => rfl⟩
      simp [Events.internalNext, Typed.nextWith, Typed.resume]
    · obtain ⟨after, enabled, next, decreases, frame⟩ := next_ready program resultFree cast ready exited
      exact ⟨after, enabled, .inl next, decreases, frame⟩
  · exact False.elim (active ⟨_, rfl⟩)

theorem complete_step_decreases (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (step : Events.Step program state events after) :
    remaining after + 1 = remaining state := by
  have active : ¬ ∃ result, state = .halted result := by
    rintro ⟨result, rfl⟩
    cases step with
    | internal next => simp [Events.internalNext, Typed.nextWith] at next
  obtain ⟨next, enabled, _, decreases, _⟩ := complete_next_ready program resultFree cast ready active
  obtain ⟨_, rfl⟩ := Events.internal_unique program enabled events after step
  exact decreases

/-- The actual initializer step retains every cell outside its write region.
This lets a second initializer's frame be derived from its own C execution. -/
theorem complete_step_frame (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (step : Events.Step program state events after) :
    Set.EqOn (CReadOnly.typedHeap after) (CReadOnly.typedHeap state) regionᶜ := by
  have active : ¬ ∃ result, state = .halted result := by
    rintro ⟨result, rfl⟩
    cases step with
    | internal next => simp [Events.internalNext, Typed.nextWith] at next
  obtain ⟨next, enabled, _, _, frame⟩ := complete_next_ready program resultFree cast ready active
  obtain ⟨_, rfl⟩ := Events.internal_unique program enabled events after step
  exact frame

/-- Zero remaining own steps is exactly actual root completion for a ready
initializer. This gives a stopping criterion without a successful-run premise. -/
theorem CompleteReady.zero_iff_halted
    (ready : CompleteReady region env types resultExpr resultType expected returned state) :
    remaining state = 0 ↔ ∃ result, state = .halted result := by
  rcases ready with ready | ⟨heap, rfl, _⟩
  · cases ready <;> simp [remaining]
  · simp [remaining]

end Rumoca.CCalls.InitializationRegion
