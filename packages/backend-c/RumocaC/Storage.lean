import RumocaC.CallEvents

/-! Execution preserves the set, types and permissions of supplied object
cells. This is stronger than absence of heap-library names, but still a
theorem of the authored C fragment. Unsupported operations can be stuck;
actual-program termination/refinement is required alongside this invariant.
Native stack bounds, layout and foreign effects are separate obligations. -/
noncomputable section
namespace Rumoca.CStorage
open CTree CMemory

def description (cell : Option Cell) : Option (CType × Bool) :=
  cell.map fun c => (c.type, c.writable)

def Preserves (before after : Heap) : Prop :=
  ∀ p, description (after p) = description (before p)

theorem Preserves.refl (heap : Heap) : Preserves heap heap := fun _ => rfl

theorem Preserves.trans (first : Preserves a b) (second : Preserves b c) : Preserves a c :=
  fun p => (second p).trans (first p)

theorem store_preserves (stored : store heap address value = some out) : Preserves heap out := by
  unfold store at stored
  cases found : heap address with
  | none => simp [found] at stored
  | some cell =>
    simp only [found, bind, Option.bind] at stored
    split at stored
    · contradiction
    · cases cast : convert cell.type value with
      | none => simp [cast] at stored
      | some value =>
        simp only [cast, pure, Option.some.injEq] at stored
        subst out
        intro p
        by_cases same : p = address
        · subst p
          simp [replace_at, found, description]
        · rw [replace_other _ _ _ _ same]

theorem Preserves.absent (preserved : Preserves before after) : after p = none ↔ before p = none := by
  have same := preserved p
  cases hb : before p <;> cases ha : after p <;> simp_all [description]

variable [interface : CInterface]

theorem body_next (step : CBody.next s = some t) :
    Preserves (CReadOnly.bodyHeap s) (CReadOnly.bodyHeap t) := by
  unfold CBody.next at step
  split at step
  all_goals try simp_all only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff]
  all_goals
    aesop (add safe forward store_preserves)
      (add safe apply Preserves.refl) (add simp CReadOnly.bodyHeap)

theorem loop_next (step : CLoops.next s = some t) :
    Preserves (CReadOnly.loopHeap s) (CReadOnly.loopHeap t) := by
  unfold CLoops.next at step
  split at step
  all_goals
    aesop (add safe forward store_preserves) (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, CReadOnly.loopHeap])

theorem resume_preserves (step : CCalls.Typed.resume value heap stack = some t) :
    Preserves heap (CReadOnly.typedHeap t) := by
  unfold CCalls.Typed.resume at step
  split at step
  all_goals
    aesop (add safe forward store_preserves) (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem typed_nextWith
    (enter : CLoops.State → String → CCalls.Typed.Continuation → Option CCalls.Typed.State)
    (preserved : ∀ s resultType stack t, enter s resultType stack = some t →
      Preserves (CReadOnly.loopHeap s) (CReadOnly.typedHeap t))
    (step : CCalls.Typed.nextWith enter program s = some t) :
    Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  unfold CCalls.Typed.nextWith at step
  split at step
  all_goals
    aesop (add safe forward [loop_next, preserved, resume_preserves])
      (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem event_enter_preserves (program : CCalls.Events.Program E)
    (step : CCalls.Events.enterCall program s resultType stack = some t) :
    Preserves (CReadOnly.loopHeap s) (CReadOnly.typedHeap t) := by
  unfold CCalls.Events.enterCall at step
  split at step
  all_goals
    aesop (add safe apply Preserves.refl)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, CReadOnly.typedHeap])

theorem internal_next (program : CCalls.Events.Program E)
    (step : CCalls.Events.internalNext program s = some t) :
    Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) :=
  typed_nextWith (CCalls.Events.enterCall program)
    (fun _ _ _ _ next => event_enter_preserves program next) step

theorem internal_reaches (program : CCalls.Events.Program E)
    (path : Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t) s t) :
    Preserves (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) := by
  induction path with
  | refl => exact .refl _
  | next step _ ih => exact (internal_next program step).trans ih

/-- No internal execution can create or remove an object cell. Reads/writes
still require the separately proved type, value and ownership preconditions. -/
theorem internal_no_new_cells (program : CCalls.Events.Program E)
    (path : Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t) s t)
    (absent : CReadOnly.typedHeap s p = none) : CReadOnly.typedHeap t p = none :=
  (internal_reaches program path).absent.mpr absent
end Rumoca.CStorage
