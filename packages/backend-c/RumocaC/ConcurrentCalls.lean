import RumocaC.CallEvents

/-! An interleaving semantics for host-supplied concurrent C invocations. There
is one shared object heap; saved controls contain no private heap snapshot.
Each selected transition is an actual transition of the existing typed call
machine. This is not an OS scheduler or a native C11 memory-model refinement;
race freedom and the selected atomic bindings require separate contracts. -/
noncomputable section
namespace Rumoca.CCalls.Concurrent
open CTree CMemory

def withHeap : Typed.State → Heap → Typed.State
  | .body (.running code locals types _) resultType stack, heap =>
      .body (.running code locals types heap) resultType stack
  | .body (.returned result) resultType stack, heap =>
      .body (.returned ⟨result.value, heap⟩) resultType stack
  | .calling name args _ stack, heap => .calling name args heap stack
  | .kernel state _ stack, heap => .kernel state heap stack
  | .returning value _ stack, heap => .returning value heap stack
  | .halted result, heap => .halted ⟨result.value, heap⟩

theorem heap_withHeap (state : Typed.State) (heap : Heap) : CReadOnly.typedHeap (withHeap state heap) = heap := by
  cases state with
  | body state => cases state <;> rfl
  | calling | kernel | returning | halted => rfl

theorem withHeap_twice (state : Typed.State) (first second : Heap) :
    withHeap (withHeap state first) second = withHeap state second := by
  cases state with
  | body state => cases state <;> rfl
  | calling | kernel | returning | halted => rfl

theorem withHeap_original (state : Typed.State) : withHeap state (CReadOnly.typedHeap state) = state := by
  cases state with
  | body state => cases state <;> rfl
  | calling | kernel | returning | halted => rfl

def control (state : Typed.State) : Typed.State := withHeap state (fun _ => none)

theorem control_resume (state : Typed.State) (heap : Heap) : withHeap (control state) heap = withHeap state heap :=
  withHeap_twice state _ heap

structure State where
  heap : Heap
  threads : Nat → Option Typed.State

def update (threads : Nat → Option Typed.State) (thread : Nat) (state : Typed.State) : Nat → Option Typed.State :=
  fun other => if other = thread then some (control state) else threads other

variable [interface : CInterface]

inductive Step (program : Events.Program E) : State → Nat → List E → State → Prop where
  | run {before : State} {thread : Nat} {saved result : Typed.State} {events : List E}
      (found : before.threads thread = some saved)
      (executed : Events.Step program (withHeap saved before.heap) events result) :
      Step program before thread events ⟨CReadOnly.typedHeap result, update before.threads thread result⟩

theorem other_thread (step : Step program before thread events after) (different : other ≠ thread) :
    after.threads other = before.threads other := by
  cases step
  simp [update, different]

/-- The selected thread sees the latest shared memory, even when its control
was last saved before another thread changed the heap. -/
theorem resumes_result (step : Step program before thread events after) :
    ∃ next, after.heap = CReadOnly.typedHeap next ∧
      after.threads thread = some (control next) ∧ withHeap (control next) after.heap = next := by
  cases step with
  | @run saved result found executed =>
    exact ⟨result, rfl, by simp [update], by rw [control_resume, withHeap_original]⟩

theorem step_readonly (step : Step program before thread events after) :
    CReadOnly.Preserves before.heap after.heap := by
  cases step with
  | run found executed =>
    simpa only [heap_withHeap] using Events.step_preserves executed

theorem reaches_readonly
    (path : Transition.Reaches (fun before after => ∃ thread events, Step program before thread events after) before after) :
    CReadOnly.Preserves before.heap after.heap := by
  induction path with
  | refl => exact .refl _
  | next first rest ih =>
    obtain ⟨thread, events, step⟩ := first
    exact (step_readonly step).trans ih

end Rumoca.CCalls.Concurrent
