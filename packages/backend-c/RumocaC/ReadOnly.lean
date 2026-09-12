import RumocaC.TypedCalls

/-! Every reachable prefix of the existing body, loop and typed call machines
preserves all previously present read-only cells. This does not allocate
objects or model foreign callbacks; it protects supplied immutable storage. -/

noncomputable section
namespace Rumoca.CReadOnly
open CTree CMemory

def Preserves (before after : Heap) : Prop :=
  ∀ p c, before p = some c → c.writable = false → after p = some c

theorem Preserves.refl (heap : Heap) : Preserves heap heap :=
  fun _ _ found _ => found

theorem Preserves.trans (first : Preserves a b) (second : Preserves b c) : Preserves a c :=
  fun p cell found readonly => second p cell (first p cell found readonly) readonly

theorem store_preserves (h : store heap address value = some out) : Preserves heap out := by
  intro p c hp hw
  by_cases same : p = address
  · subst address
    rw [store_readonly heap p value c hp hw] at h
    contradiction
  · rw [store_frame _ _ _ _ h _ same, hp]

theorem Preserves.load_eq (preserved : Preserves before after)
    (found : before p = some cell) (readonly : cell.writable = false) :
    load after p = load before p := by
  simp only [load, found, preserved p cell found readonly]

def bodyHeap : CBody.State → Heap
  | .running _ _ heap => heap
  | .returned result => result.heap

variable [interface : CInterface]

theorem body_next (step : CBody.next s = some t) : Preserves (bodyHeap s) (bodyHeap t) := by
  unfold CBody.next at step
  split at step
  all_goals try simp_all only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff]
  all_goals
    aesop (add safe forward store_preserves)
      (add safe apply Preserves.refl)
      (add simp bodyHeap)

theorem body_reaches (steps : Transition.Reaches CBody.machine.step s t) :
    Preserves (bodyHeap s) (bodyHeap t) := by
  induction steps with
  | refl => exact .refl _
  | next step rest ih => exact (body_next step).trans ih

def loopHeap : CLoops.State → Heap
  | .running _ _ _ heap => heap
  | .returned result => result.heap

theorem loop_next (step : CLoops.next s = some t) : Preserves (loopHeap s) (loopHeap t) := by
  unfold CLoops.next at step
  split at step
  all_goals
    aesop (add safe forward store_preserves)
      (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, loopHeap])

theorem loop_reaches (steps : Transition.Reaches CLoops.machine.step s t) :
    Preserves (loopHeap s) (loopHeap t) := by
  induction steps with
  | refl => exact .refl _
  | next step rest ih => exact (loop_next step).trans ih

def typedHeap : CCalls.Typed.State → Heap
  | .body state _ _ => loopHeap state
  | .calling _ _ heap _ | .kernel _ heap _ | .returning _ heap _ => heap
  | .halted result => result.heap

theorem enter_preserves (step : CCalls.Typed.enterCall s resultType stack = some t) :
    Preserves (loopHeap s) (typedHeap t) := by
  unfold CCalls.Typed.enterCall at step
  split at step
  all_goals
    aesop (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, loopHeap, typedHeap])

theorem resume_preserves (step : CCalls.Typed.resume value heap stack = some t) :
    Preserves heap (typedHeap t) := by
  unfold CCalls.Typed.resume at step
  split at step
  all_goals
    aesop (add safe forward store_preserves)
      (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, loopHeap, typedHeap])

/-- Read-only preservation of the shared scheduler depends only on the same
property of its call-entry handler. Foreign effects are checked separately. -/
theorem typed_nextWith
    (enter : CLoops.State → String → CCalls.Typed.Continuation → Option CCalls.Typed.State)
    (preserved : ∀ s resultType stack t, enter s resultType stack = some t →
      Preserves (loopHeap s) (typedHeap t))
    (step : CCalls.Typed.nextWith enter program s = some t) :
    Preserves (typedHeap s) (typedHeap t) := by
  unfold CCalls.Typed.nextWith at step
  split at step
  all_goals
    aesop (add safe forward [loop_next, preserved, resume_preserves])
      (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, loopHeap, typedHeap])

theorem typed_next (step : CCalls.Typed.next program s = some t) :
    Preserves (typedHeap s) (typedHeap t) :=
  typed_nextWith CCalls.Typed.enterCall (fun _ _ _ _ next => enter_preserves next) step

theorem typed_reaches (steps : Transition.Reaches (CCalls.Typed.machine program).step s t) :
    Preserves (typedHeap s) (typedHeap t) := by
  induction steps with
  | refl => exact .refl _
  | next step rest ih => exact (typed_next step).trans ih

theorem typed_load (steps : Transition.Reaches (CCalls.Typed.machine program).step s t)
    (found : typedHeap s p = some cell) (readonly : cell.writable = false) :
    load (typedHeap t) p = load (typedHeap s) p :=
  (typed_reaches steps).load_eq found readonly

end Rumoca.CReadOnly
