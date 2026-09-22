import RumocaC.InitializationRegion

namespace Rumoca.CCalls.InitializationRegion
open CTree CMemory CBody.Footprint
variable [interface : CInterface] {E : Type}

/-- A public function may consume its root return and become halted. Its
private result remains protected until the host observes that completion. -/
def CompleteReady (region : Set Address) (env : CBody.Locals) (types : CLoops.Types)
    (resultExpr : Expr) (resultType : String) (expected : CBody.Result)
    (returned : Value) (state : Typed.State) : Prop :=
  Ready region env types resultExpr resultType expected returned .done state ∨
    ∃ heap, state = .halted ⟨returned, heap⟩ ∧ Set.EqOn expected.heap heap region

theorem CompleteReady.withHeap
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (frame : Set.EqOn (CReadOnly.typedHeap state) heap region) :
    CompleteReady region env types resultExpr resultType expected returned (Concurrent.withHeap state heap) := by
  rcases ready with ready | ⟨previous, rfl, agreement⟩
  · exact .inl (ready.withHeap frame)
  · exact .inr ⟨heap, rfl, agreement.trans frame⟩

theorem CompleteReady.halted
    (ready : CompleteReady region env types resultExpr resultType expected returned (.halted result)) :
    result.value = returned ∧ Set.EqOn expected.heap result.heap region := by
  rcases ready with ready | ⟨heap, same, agreement⟩
  · cases ready
  · cases Typed.State.halted.inj same
    exact ⟨rfl, agreement⟩

theorem complete_step_ready (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : CompleteReady region env types resultExpr resultType expected returned state)
    (step : Events.Step program state events after) :
    events = [] ∧ CompleteReady region env types resultExpr resultType expected returned after := by
  rcases ready with ready | ⟨heap, rfl, agreement⟩
  · by_cases exited : Concurrent.Exit .done state
    · obtain ⟨value, heap, rfl⟩ := exited
      obtain ⟨identity, agreement⟩ := ready.exit
      subst value
      have next : Events.internalNext program (.returning returned heap .done) =
          some (.halted ⟨returned, heap⟩) := by
        simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions, Typed.resumeWith]
      obtain ⟨silent, rfl⟩ := Events.internal_unique program next events after step
      exact ⟨silent, .inr ⟨heap, rfl, agreement⟩⟩
    · obtain ⟨silent, next⟩ := step_ready program resultFree cast ready exited step
      exact ⟨silent, .inl next⟩
  · cases step with
    | internal next => simp [Events.internalNextWith, Typed.nextWithExpressions] at next

end Rumoca.CCalls.InitializationRegion
