import RumocaC.CallEvents

/-! Reusable lifting of a heap relation through internal C execution. The only
object mutation in this machine is the existing checked cell store. Foreign
calls must supply separate effects; the lifting does not assume their safety. -/
noncomputable section
namespace Rumoca.CStoreInvariant
open CTree CMemory

structure Stable (R : Heap → Heap → Prop) : Prop where
  refl : ∀ heap, R heap heap
  store : ∀ before address value after, CMemory.store before address value = some after → R before after

variable {R : Heap → Heap → Prop} (stable : Stable R) [interface : CInterface]
include stable

theorem body_next (step : CBody.next s = some t) :
    R (CReadOnly.bodyHeap s) (CReadOnly.bodyHeap t) := by
  have store_rule := stable.store
  have refl_rule := stable.refl
  unfold CBody.next at step
  split at step
  all_goals try simp_all only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff]
  all_goals
    aesop (add safe forward store_rule) (add safe apply refl_rule) (add simp CReadOnly.bodyHeap)

theorem loop_next (step : CLoops.next s = some t) :
    R (CReadOnly.loopHeap s) (CReadOnly.loopHeap t) := by
  have store_rule := stable.store
  have refl_rule := stable.refl
  unfold CLoops.next at step
  split at step
  all_goals
    aesop (add safe forward store_rule) (add safe apply refl_rule)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, CReadOnly.loopHeap])

theorem resume (step : CCalls.Typed.resume value heap stack = some t) : R heap (CReadOnly.typedHeap t) := by
  have store_rule := stable.store
  have refl_rule := stable.refl
  unfold CCalls.Typed.resume at step
  split at step
  all_goals
    aesop (add safe forward store_rule) (add safe apply refl_rule)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

set_option maxHeartbeats 800000 in
theorem nextWith
    (enter : CLoops.State → String → CCalls.Typed.Continuation → Option CCalls.Typed.State)
    (entry : ∀ s resultType stack t, enter s resultType stack = some t →
      R (CReadOnly.loopHeap s) (CReadOnly.typedHeap t))
    (step : CCalls.Typed.nextWith enter program s = some t) :
    R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  have loops : ∀ s t, CLoops.next s = some t → R (CReadOnly.loopHeap s) (CReadOnly.loopHeap t) :=
    fun _ _ step => loop_next stable step
  have resumed : ∀ value heap stack t, CCalls.Typed.resume value heap stack = some t →
      R heap (CReadOnly.typedHeap t) := fun _ _ _ _ step => resume stable step
  have refl_rule := stable.refl
  unfold CCalls.Typed.nextWith at step
  split at step
  all_goals
    aesop (add safe forward [loops, entry, resumed])
      (add safe apply refl_rule)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem event_entry (program : CCalls.Events.Program E)
    (step : CCalls.Events.enterCall program s resultType stack = some t) :
    R (CReadOnly.loopHeap s) (CReadOnly.typedHeap t) := by
  have refl_rule := stable.refl
  unfold CCalls.Events.enterCall at step
  split at step
  all_goals
    aesop (add safe apply refl_rule)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem internal_next (program : CCalls.Events.Program E)
    (step : CCalls.Events.internalNext program s = some t) :
    R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  nextWith stable (CCalls.Events.enterCall program)
    (fun _ _ _ _ next => event_entry stable program next) step

end Rumoca.CStoreInvariant
