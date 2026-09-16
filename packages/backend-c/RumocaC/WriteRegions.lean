import RumocaC.WriteFootprint
import RumocaC.ConcurrentCalls

noncomputable section
namespace Rumoca.CWriteFootprint
open CTree CMemory CCalls
variable [CInterface] {E : Type} {region : Set Address}

/-- Computed internal writes exclude the protected region. This is a
destination obligation, not an assumed equality of before/after heaps. -/
def Avoids (region : Set Address) (state : Typed.State) : Prop :=
  ∀ address, current state = some address → address ∉ region

/-- Only the current external call needs a separate memory-effect contract.
Internal calls and saved return destinations use the proved write footprint. -/
def ForeignFrame (region : Set Address) (program : Events.Program E) : Typed.State → Prop
  | .calling name args before _ =>
      ∀ fn values events result after,
        program.externals name = some fn →
        Events.convertedArguments fn.signature.parameters args = some values →
        fn.execute values before events result after → Set.EqOn before after region
  | _ => True

theorem internal_region (confined : Avoids region state)
    (step : Events.internalNext program state = some following) :
    Set.EqOn (CReadOnly.typedHeap state) (CReadOnly.typedHeap following) region := by
  intro query inside
  exact (internal_frame step (fun selected => confined query selected inside)).symm

theorem event_region (confined : Avoids region state)
    (foreign : ForeignFrame region program state)
    (step : Events.Step program state events following) :
    Set.EqOn (CReadOnly.typedHeap state) (CReadOnly.typedHeap following) region := by
  cases step with
  | internal actual => exact internal_region confined actual
  | external found converted executed => exact foreign _ _ _ _ _ found converted executed

/-- The same frame applies to the selected thread with the current shared
heap. It does not use the erased heap in its suspended control. -/
theorem concurrent_region
    (confined : ∀ saved, before.threads thread = some saved →
      Avoids region (Concurrent.withHeap saved before.heap))
    (foreign : ∀ saved, before.threads thread = some saved →
      ForeignFrame region program (Concurrent.withHeap saved before.heap))
    (step : Concurrent.Step program before thread events after) :
    Set.EqOn before.heap after.heap region := by
  cases step with
  | run found executed =>
    simpa only [Concurrent.heap_withHeap] using
      event_region (confined _ found) (foreign _ found) executed

end Rumoca.CWriteFootprint
