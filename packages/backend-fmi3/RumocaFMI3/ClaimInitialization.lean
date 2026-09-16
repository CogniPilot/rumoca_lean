import RumocaFMI3.StaticFactoryReservation
import RumocaFMI3.InstanceInitializationRegion
import RumocaC.AtomicClaimProgress
import RumocaC.InitializationProgress

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CBody CCalls CCalls.InitializationRegion
open CAtomicScan.ConcurrentInvariant

def caller (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types) :
    Typed.Continuation :=
  .caller (.declare "size_t" "slot") (guard :: initializeInstance model kind) env types "fmi3Instance" .done

def initializedLocals (env : Locals) (base : Address) (slot : Nat) : Locals :=
  CBody.bind (reservedLocals env slot) "m" (.pointer (some (base.index slot)))

def initializedTypes (types : CLoops.Types) : CLoops.Types :=
  CLoops.bindType (reservedTypes types) "m" .pointer

variable [interface : CInterface] {E : Type}

/-- The successful atomic continuation keeps the literal factory caller,
then crosses the actual capacity guard and address selection before entering
the prepared initializer. Its reference heap is protected only in this record. -/
inductive Ready (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (base flags : Address) (capacity slot : Nat) (environment logger : Option Address) (logging : Bool)
    (reference : Heap) : Typed.State → Prop where
  | scan (control : ClaimedReady flags capacity slot (caller model kind env types) state)
      (agreement : Set.EqOn reference (CReadOnly.typedHeap state) {q | (base.index slot).InRecord q}) :
      Ready model kind env types base flags capacity slot environment logger logging reference state
  | guard (heap : Heap) (agreement : Set.EqOn reference heap {q | (base.index slot).InRecord q}) :
      Ready model kind env types base flags capacity slot environment logger logging reference
        (.body (.running (StaticFactory.guard :: initializeInstance model kind) (reservedLocals env slot)
          (reservedTypes types) heap) "fmi3Instance" .done)
  | select (heap : Heap) (agreement : Set.EqOn reference heap {q | (base.index slot).InRecord q}) :
      Ready model kind env types base flags capacity slot environment logger logging reference
        (.body (.running (initializeInstance model kind) (reservedLocals env slot)
          (reservedTypes types) heap) "fmi3Instance" .done)
  | initializing (control : CompleteReady {q | (base.index slot).InRecord q}
      (initializedLocals env base slot) (initializedTypes types)
      (.cast "fmi3Instance" (.id "m")) "fmi3Instance"
      ⟨.pointer (some (base.index slot)), InstanceSlot.finalHeap reference (base.index slot) slot kind environment logger logging⟩
      (.pointer (some (base.index slot))) state) :
      Ready model kind env types base flags capacity slot environment logger logging reference state

theorem Ready.withHeap
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference state)
    (frame : Set.EqOn (CReadOnly.typedHeap state) heap {q | (base.index slot).InRecord q}) :
    Ready model kind env types base flags capacity slot environment logger logging reference (Concurrent.withHeap state heap) := by
  cases ready with
  | scan control agreement =>
    exact .scan (control.withHeap heap) (by simpa only [Concurrent.heap_withHeap] using agreement.trans frame)
  | guard old agreement => exact .guard heap (agreement.trans frame)
  | select old agreement => exact .select heap (agreement.trans frame)
  | initializing control => exact .initializing (control.withHeap frame)

theorem Ready.halted
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference (.halted result)) :
    result.value = .pointer (some (base.index slot)) ∧
      Set.EqOn (InstanceSlot.finalHeap reference (base.index slot) slot kind environment logger logging)
        result.heap {q | (base.index slot).InRecord q} := by
  cases ready with
  | scan control agreement => cases control
  | initializing control => exact control.halted

/-- Actual C execution, including the helper return and both factory prefix
steps, derives initializer entry. A successful initialization or reached entry
is not an additional premise. -/
theorem step_with_frame (program : Events.Program E)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : InstanceSlot.Storage reference (base.index slot))
    (inside : slot < capacity) (bounded : slot < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference before)
    (step : Events.Step program before events after) :
    events = [] ∧ Ready model kind env types base flags capacity slot environment logger logging reference after ∧
      Set.EqOn (CReadOnly.typedHeap after) (CReadOnly.typedHeap before) {q | (base.index slot).InRecord q}ᶜ := by
  cases ready with
  | scan control agreement =>
    by_cases exited : Concurrent.Exit (caller model kind env types) before
    · obtain ⟨value, heap, rfl⟩ := exited
      have identity := control.exit_value
      subst value
      obtain ⟨silent, rfl⟩ := Events.internal_unique program
        (reserve_resume program model kind env types heap slot .done scope.slotFresh size bounded) events after step
      exact ⟨silent, .guard heap agreement, fun _ _ => rfl⟩
    · obtain ⟨silent, controlNext⟩ := claimed_step program size bounded control exited step
      have heapSame := claimed_step_heap program size bounded control exited step
      exact ⟨silent, .scan controlNext (by rw [heapSame]; exact agreement), by rw [heapSame]; intro _ _; rfl⟩
  | guard heap agreement =>
    have selected : resolve (reservedLocals env slot) "slot" = some (.integer slot) := by
      simp [reservedLocals, resolve, CBody.bind]
    have count : resolve (reservedLocals env slot) "rumoca_instance_capacity" = some (.integer capacity) := by
      simpa [reservedLocals, resolve, CBody.bind] using scope.count
    have next := guard_step (reservedLocals env slot) (reservedTypes types) heap slot capacity
      (initializeInstance model kind) selected count
    simp only [Nat.ne_of_lt inside, ↓reduceIte, List.nil_append] at next
    obtain ⟨silent, rfl⟩ := Events.internal_unique program (Events.body_step program next "fmi3Instance" .done)
      events after step
    exact ⟨silent, .select heap agreement, fun _ _ => rfl⟩
  | select heap agreement =>
    have selected : resolve (reservedLocals env slot) "slot" = some (.integer slot) := by
      simp [reservedLocals, resolve, CBody.bind]
    have instances : resolve (reservedLocals env slot) "rumoca_instances" = some (.pointer (some base)) := by
      simpa [reservedLocals, resolve, CBody.bind] using scope.instances
    have fresh : reservedLocals env slot "m" = none := by
      simpa [reservedLocals, CBody.bind] using scope.instanceFresh
    have next := select_step (reservedLocals env slot) (reservedTypes types) heap base slot
      (InstanceSlot.code model kind) instances selected fresh pointer
    obtain ⟨silent, rfl⟩ := Events.internal_unique program (Events.body_step program next "fmi3Instance" .done)
      events after step
    have bindings := selected_bindings (reservedLocals env slot) (base.index slot) environment logger logging
      (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
      (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
      (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
    have seed := InstanceSlot.initialization_ready model kind (initializedLocals env base slot)
      (initializedTypes types) reference (base.index slot) slot environment logger logging storage bindings
      (by simp [initializedLocals, reservedLocals, resolve, CBody.bind]) bounded double handle
    exact ⟨silent, .initializing (seed.withHeap agreement), fun _ _ => rfl⟩
  | initializing control =>
    have cast : returnCast "fmi3Instance" (.pointer (some (base.index slot))) =
        some (.pointer (some (base.index slot))) := by
      simp [returnCast, CBody.cast, handle, convert]
    obtain ⟨silent, next⟩ := complete_step_ready program rfl cast control step
    exact ⟨silent, .initializing next, complete_step_frame program rfl cast control step⟩


theorem step_ready (program : Events.Program E)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : InstanceSlot.Storage reference (base.index slot))
    (inside : slot < capacity) (bounded : slot < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference before)
    (step : Events.Step program before events after) :
    events = [] ∧ Ready model kind env types base flags capacity slot environment logger logging reference after := by
  obtain ⟨silent, next, _⟩ := step_with_frame program scope storage inside bounded size pointer double handle ready step
  exact ⟨silent, next⟩

/-- Every own step after a successful claim preserves any distinct instance
record, including helper return, guard and pointer selection. This discharges
the private frame for concurrent factory continuations from their actual C. -/
theorem step_other_instance (program : Events.Program E)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : InstanceSlot.Storage reference (base.index slot))
    (inside : slot < capacity) (bounded : slot < 2^64) (different : slot ≠ other)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (ready : Ready model kind env types base flags capacity slot environment logger logging reference before)
    (step : Events.Step program before events after) :
    Set.EqOn (CReadOnly.typedHeap before) (CReadOnly.typedHeap after) {q | (base.index other).InRecord q} := by
  have frame := (step_with_frame program scope storage inside bounded size pointer double handle ready step).2.2
  intro query belongs
  exact (frame (fun own => Address.records_separate base slot other different own belongs rfl)).symm

end Rumoca.FMI3.StaticFactory.ClaimInitialization
