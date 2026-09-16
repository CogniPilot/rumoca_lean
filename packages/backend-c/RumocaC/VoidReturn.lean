import RumocaC.InvocationContinuation

/-! A root void-return suffix is independent of all shared memory. In
particular, a resource released by the preceding call may already be reused. -/
namespace Rumoca.CCalls.VoidReturn
open CTree CMemory

inductive Ready (env : CBody.Locals) (types : CLoops.Types) : Typed.State → Prop where
  | resumed (heap : Heap) : Ready env types
      (.returning .void heap (.caller .discard [.ret none] env types "void" .done))
  | returning (heap : Heap) : Ready env types
      (.body (.running [.ret none] env types heap) "void" .done)
  | returned (heap : Heap) : Ready env types
      (.body (.returned ⟨.void, heap⟩) "void" .done)
  | done (heap : Heap) : Ready env types (.returning .void heap .done)
  | halted (heap : Heap) : Ready env types (.halted ⟨.void, heap⟩)

theorem Ready.withHeap (ready : Ready env types state) (heap : Heap) :
    Ready env types (Concurrent.withHeap state heap) := by
  cases ready with
  | resumed => exact .resumed heap
  | returning => exact .returning heap
  | returned => exact .returned heap
  | done => exact .done heap
  | halted => exact .halted heap

theorem Ready.halted_value (ready : Ready env types (.halted result)) :
    result.value = .void := by cases ready; rfl

def remaining : Typed.State → Nat
  | .returning _ _ (.caller ..) => 4
  | .body (.running ..) _ _ => 3
  | .body (.returned _) _ _ => 2
  | .returning _ _ .done => 1
  | _ => 0

theorem Ready.zero_iff_halted (ready : Ready env types state) :
    remaining state = 0 ↔ ∃ result, state = .halted result := by
  cases ready <;> simp [remaining]

variable [CInterface] {E : Type}

/-- Each nonfinal state has an actual silent successor and one fewer own
steps to completion. No condition on any heap cell is required. -/
theorem next_ready (program : Events.Program E) (ready : Ready env types state)
    (active : ¬ ∃ result, state = .halted result) :
    ∃ after, Events.internalNext program state = some after ∧ Ready env types after ∧
      remaining after + 1 = remaining state ∧
      CReadOnly.typedHeap after = CReadOnly.typedHeap state := by
  cases ready with
  | resumed heap => exact ⟨_, rfl, .returning heap, rfl, rfl⟩
  | returning heap => exact ⟨_, rfl, .returned heap, rfl, rfl⟩
  | returned heap => exact ⟨_, rfl, .done heap, rfl, rfl⟩
  | done heap => exact ⟨_, rfl, .halted heap, rfl, rfl⟩
  | halted heap => exact False.elim (active ⟨_, rfl⟩)

/-- Every actual step follows the suffix, emits no event and preserves the
whole current shared heap, including storage already reused by another call. -/
theorem step_ready (program : Events.Program E) (ready : Ready env types state)
    (step : Events.Step program state events after) :
    events = [] ∧ Ready env types after ∧ remaining after + 1 = remaining state ∧
      CReadOnly.typedHeap after = CReadOnly.typedHeap state := by
  have active : ¬ ∃ result, state = .halted result := by
    rintro ⟨result, rfl⟩
    cases step with
    | internal next => simp [Events.internalNext, Typed.nextWith] at next
  obtain ⟨next, enabled, following, decreases, unchanged⟩ := next_ready program ready active
  obtain ⟨rfl, rfl⟩ := Events.internal_unique program enabled events after step
  exact ⟨rfl, following, decreases, unchanged⟩

/-- The original invocation retains its return suffix under arbitrary admitted
host actions and other-thread effects. No metadata or private-region frame is
imposed after the resource has been released. -/
theorem history_ready (program : Events.Program E) (policy : Host.Policy)
    (issued : serial < before.ledger.next)
    (ready : Host.Recording.Selected (Ready env types) tracked serial before)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after) :
    serial < after.ledger.next ∧ Host.Recording.Selected (Ready env types) tracked serial after :=
  Host.Recording.selected_history program policy (Ready env types)
    (fun _ h heap => h.withHeap heap)
    (fun _ _ _ h step => (step_ready program h step).2.1) issued ready path

theorem observed_void (program : Events.Program E) (policy : Host.Policy)
    (issued : serial < before.ledger.next)
    (ready : Host.Recording.Selected (Ready env types) tracked serial before)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after)
    (active : after.ledger.active tracked = some call) (origin : call.serial = serial)
    (completed : Host.Step program policy after.runtime tracked (.complete value) following) :
    value = .void ∧ following.heap = after.runtime.heap := by
  have ready := (history_ready program policy issued ready path).2
  obtain ⟨⟨result, halted, identity⟩, followingEq⟩ := Host.complete_iff.mp completed
  exact ⟨identity.symm.trans (ready call _ active origin halted).halted_value,
    by rw [followingEq]⟩

end Rumoca.CCalls.VoidReturn
