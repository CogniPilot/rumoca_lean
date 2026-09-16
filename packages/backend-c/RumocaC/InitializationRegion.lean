import RumocaC.AssignmentFootprint
import RumocaC.CallHeapIntervals
import RumocaC.CallIntervalTrace

/-! Interference-aware execution of a certified store block and its return.
The reference heap evolves through actual typed stores; the live shared heap
agrees only inside the protected region. No shared scheduler is replaced. -/
noncomputable section
namespace Rumoca.CCalls.InitializationRegion
open CTree CMemory CBody.Footprint CLoops.Footprint
variable [interface : CInterface] {E : Type}

inductive Ready (region : Set Address) (env : CBody.Locals) (types : CLoops.Types)
    (resultExpr : Expr) (resultType : String) (expected : CBody.Result)
    (returned : Value) (stack : Typed.Continuation) : Typed.State → Prop where
  | running (pending : List Stmt) (reference heap : Heap)
      (writes : ∀ stmt ∈ pending, AssignsWithin env region stmt)
      (finishes : CLoops.run (pending.length + 1)
        (.running (pending ++ [.ret (some resultExpr)]) env types reference) = some (.returned expected))
      (agreement : Set.EqOn reference heap region) :
      Ready region env types resultExpr resultType expected returned stack
        (.body (.running (pending ++ [.ret (some resultExpr)]) env types heap) resultType stack)
  | finishing (heap : Heap) (agreement : Set.EqOn expected.heap heap region) :
      Ready region env types resultExpr resultType expected returned stack
        (.body (.returned ⟨expected.value, heap⟩) resultType stack)
  | returning (heap : Heap) (agreement : Set.EqOn expected.heap heap region) :
      Ready region env types resultExpr resultType expected returned stack
        (.returning returned heap stack)

theorem Ready.withHeap
    (ready : Ready region env types resultExpr resultType expected returned stack state)
    (frame : Set.EqOn (CReadOnly.typedHeap state) heap region) :
    Ready region env types resultExpr resultType expected returned stack (Concurrent.withHeap state heap) := by
  cases ready with
  | running pending reference current writes finishes agreement =>
    exact .running pending reference heap writes finishes (agreement.trans frame)
  | finishing current agreement => exact .finishing heap (agreement.trans frame)
  | returning current agreement => exact .returning heap (agreement.trans frame)

theorem Ready.exit
    (ready : Ready region env types resultExpr resultType expected returned stack
      (.returning value heap stack)) : value = returned ∧ Set.EqOn expected.heap heap region := by
  cases ready with
  | returning heap agreement => exact ⟨rfl, agreement⟩

/-- Remaining own C steps for a store block, body return and root return.
The measure comes from the actual saved control, not an execution annotation. -/
def remaining : Typed.State → Nat
  | .body (.running code _ _ _) _ _ => code.length + 2
  | .body (.returned _) _ _ => 2
  | .returning _ _ _ => 1
  | _ => 0

omit interface in
theorem remaining_withHeap (state : Typed.State) (heap : Heap) :
    remaining (Concurrent.withHeap state heap) = remaining state := by
  cases state with
  | body state => cases state <;> rfl
  | calling | kernel | returning | halted => rfl

/-- The certified reference run enables the next actual internal C step.
Each such step reduces a control-derived remaining-step count. -/
theorem next_ready (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : Ready region env types resultExpr resultType expected returned stack state)
    (active : ¬ Concurrent.Exit stack state) :
    ∃ after, Events.internalNext program state = some after ∧
      Ready region env types resultExpr resultType expected returned stack after ∧
      remaining after + 1 = remaining state ∧
      Set.EqOn (CReadOnly.typedHeap after) (CReadOnly.typedHeap state) regionᶜ := by
  cases ready with
  | running pending reference heap writes finishes agreement =>
    cases pending with
    | nil =>
      have next : CLoops.next (.running [.ret (some resultExpr)] env types reference) =
          some (.returned expected) := by simpa [CLoops.run] using finishes
      cases evaluated : CLoops.eval env types reference resultExpr with
      | none => simp [CLoops.next, evaluated] at next
      | some value =>
        have same : CLoops.State.returned ⟨value, reference⟩ = .returned expected := by
          simpa [CLoops.next, evaluated] using next
        cases CLoops.State.returned.inj same
        have actual : CLoops.next (.running [.ret (some resultExpr)] env types heap) =
            some (.returned ⟨value, heap⟩) := by
          simp only [CLoops.next, ← loop_heap_free resultFree env types reference heap, evaluated]
          rfl
        exact ⟨_, Events.body_step program actual resultType stack, .finishing heap agreement, rfl, fun _ _ => rfl⟩
    | cons stmt rest =>
      have head := writes stmt (by simp)
      have tail : ∀ stmt ∈ rest, AssignsWithin env region stmt :=
        fun stmt member => writes stmt (by simp [member])
      cases stmt <;> simp only [AssignsWithin] at head
      case assign target value =>
        obtain ⟨addressFree, valueFree, inside⟩ := head
        change (CLoops.next (.running ((.assign target value :: rest) ++ [.ret (some resultExpr)])
          env types reference)).bind (CLoops.run (rest.length + 1)) = some (.returned expected) at finishes
        obtain ⟨next, nextStep, restRun⟩ := Option.bind_eq_some_iff.mp finishes
        obtain ⟨nextReference, nextHeap, rfl, actual, agreed, frame⟩ :=
          assignment_region addressFree valueFree (inside reference) agreement nextStep
        exact ⟨_, Events.body_step program actual resultType stack,
          .running rest nextReference nextHeap tail restRun agreed,
          by simp [remaining], frame⟩
  | finishing heap agreement =>
    have next : Events.internalNext program
        (.body (.returned ⟨expected.value, heap⟩) resultType stack) =
        some (.returning returned heap stack) := by
      simp [Events.internalNext, Typed.nextWith, cast]
    exact ⟨_, next, .returning heap agreement, rfl, fun _ _ => rfl⟩
  | returning heap agreement => exact False.elim (active ⟨returned, heap, rfl⟩)


/-- Every actual own step agrees with the enabled reference step, including
its empty event trace. Unused nondeterministic foreign bindings cannot add a
second transition to this ordinary store block. -/
theorem step_ready (program : Events.Program E)
    (resultFree : heapFreeValue resultExpr = true)
    (cast : returnCast resultType expected.value = some returned)
    (ready : Ready region env types resultExpr resultType expected returned stack state)
    (active : ¬ Concurrent.Exit stack state)
    (step : Events.Step program state events after) :
    events = [] ∧ Ready region env types resultExpr resultType expected returned stack after := by
  obtain ⟨next, enabled, nextReady, _⟩ := next_ready program resultFree cast ready active
  obtain ⟨silent, rfl⟩ := Events.internal_unique program enabled events after step
  exact ⟨silent, nextReady⟩

end Rumoca.CCalls.InitializationRegion
