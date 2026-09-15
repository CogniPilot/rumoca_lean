import RumocaC.AtomicScanEntryInvariant
import RumocaC.AtomicArguments

namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn)

/-- After observing a free slot, the actual scan cannot attempt another
exchange. The selected index stays in its control until the caller resumes. -/
inductive ClaimedReady (flags : Address) (count k : Nat) (stack : Typed.Continuation) : Typed.State → Prop where
  | resume (previous : Bool) (heap : Heap) : ClaimedReady flags count k stack
      (.returning (CAtomicBoolean.value false) heap
        (.caller (.assign (.id "busy")) tail (locals flags count k previous) types "size_t" stack))
  | selected (heap : Heap) : ClaimedReady flags count k stack
      (.body (.running tail (locals flags count k false) types heap) "size_t" stack)
  | returnIndex (heap : Heap) : ClaimedReady flags count k stack
      (.body (.running
        [.ret (some (.id "k")), CAtomicScan.advance, CAtomicScan.scan, .ret (some (.id "count"))]
        (locals flags count k false) types heap) "size_t" stack)
  | returned (heap : Heap) : ClaimedReady flags count k stack
      (.body (.returned ⟨.integer k, heap⟩) "size_t" stack)
  | done (heap : Heap) : ClaimedReady flags count k stack (.returning (.integer k) heap stack)

theorem ClaimedReady.withHeap (ready : ClaimedReady flags count k stack state) (heap : Heap) :
    ClaimedReady flags count k stack (Concurrent.withHeap state heap) := by
  cases ready with
  | resume previous => exact .resume previous heap
  | selected => exact .selected heap
  | returnIndex => exact .returnIndex heap
  | returned => exact .returned heap
  | done => exact .done heap

theorem ClaimedReady.no_call (ready : ClaimedReady flags count k stack (.calling name args heap later)) : False := by
  cases ready

theorem ClaimedReady.exit_value (ready : ClaimedReady flags count k stack (.returning value heap stack)) :
    value = .integer k := by
  cases ready
  rfl

variable [interface : CInterface] {E : Type}

private theorem claimed_known_step (program : Events.Program E)
    (known : Events.internalNext program before = some target)
    (ready : ClaimedReady flags count k stack target)
    (step : Events.Step program before events after) :
    events = [] ∧ ClaimedReady flags count k stack after := by
  obtain ⟨rfl, rfl⟩ := Events.internal_unique program known _ _ step
  exact ⟨rfl, ready⟩

/-- Every remaining own step is silent and keeps the first successful index.
No restriction on intervening shared-heap contents is needed for this control fact. -/
theorem claimed_step (program : Events.Program E)
    (size : interface.types "size_t" = some .size)
    (bounded : k < 2 ^ 64)
    (ready : ClaimedReady flags count k stack before) (active : ¬ Exit stack before)
    (step : Events.Step program before events after) :
    events = [] ∧ ClaimedReady flags count k stack after := by
  cases ready with
  | resume previous heap =>
    exact claimed_known_step program
      (attempt_resume program flags count k previous false heap tail "size_t" stack)
      (.selected heap) step
  | selected heap =>
    exact claimed_known_step program (Events.body_step program
      (selected_step flags count k false heap _) "size_t" stack) (.returnIndex heap) step
  | returnIndex heap =>
    exact claimed_known_step program (Events.body_step program
      (return_body (locals flags count k false) heap "k" k _ (by simp [locals, CBody.bind]))
      "size_t" stack) (.returned heap) step
  | returned heap =>
    exact claimed_known_step program (size_returned program heap k stack size (by omega)) (.done heap) step
  | done heap => exact False.elim (active ⟨_, _, rfl⟩)

/-- At an actual exchange reached by the scan, the raw operation determines
the observed bit, exact trace and the successful continuation. Success is
not an annotation added to the scheduler. -/
theorem scan_exchange (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (ready : FullReady flags count stack (.calling "atomic_exchange" args heap later))
    (step : Events.Step program (.calling "atomic_exchange" args heap later) events after) :
    ∃ k : Nat, ∃ observed : Bool, ∃ nextHeap : Heap,
      k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] ∧
      CAtomicBoolean.exchange heap (flags.index k) true = some (observed, nextHeap) ∧
      events = [tag (.exchange (flags.index k) observed true)] ∧
      after = .returning (CAtomicBoolean.value observed) nextHeap later ∧
      (observed = false → ClaimedReady flags count k stack after) := by
  generalize nameEq : ("atomic_exchange" : String) = name at ready
  cases ready with
  | entry => simp [function] at nameEq
  | loop ready =>
    cases ready with
    | atomic k bounded previous heap =>
      cases step with
      | internal moved =>
        rw [Events.external_entry_exclusive program bound] at moved
        contradiction
      | external found converted executed =>
        cases Option.some.inj (found.symm.trans bound)
        obtain ⟨address, observed, addressEq, operation, trace, rfl⟩ :=
          CAtomicBoolean.Calls.exchange_from_arguments tag boolean pointer converted executed
        have same : address = flags.index k := by simpa using addressEq.symm
        subst address
        exact ⟨k, observed, _, bounded, rfl, operation, trace, rfl,
          fun success => by cases success; exact .resume previous _⟩

end Rumoca.CAtomicScan.ConcurrentInvariant
