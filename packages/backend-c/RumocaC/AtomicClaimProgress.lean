import RumocaC.AtomicScanClaim

namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit)
variable [interface : CInterface] {E : Type}

/-- After success, the scan's next actual internal step is enabled and keeps
the entire shared heap. Its continuation performs only local control work. -/
theorem claimed_next (program : Events.Program E)
    (size : interface.types "size_t" = some .size) (bounded : k < 2^64)
    (ready : ClaimedReady flags count k stack before) (active : ¬ Exit stack before) :
    ∃ after, Events.internalNext program before = some after ∧
      ClaimedReady flags count k stack after ∧ CReadOnly.typedHeap after = CReadOnly.typedHeap before := by
  cases ready with
  | resume previous heap =>
    exact ⟨_, attempt_resume program flags count k previous false heap tail "size_t" stack,
      .selected heap, rfl⟩
  | selected heap =>
    exact ⟨_, Events.body_step program (selected_step flags count k false heap _) "size_t" stack,
      .returnIndex heap, rfl⟩
  | returnIndex heap =>
    exact ⟨_, Events.body_step program
      (return_body (locals flags count k false) heap "k" k _ (by simp [locals, CBody.bind]))
      "size_t" stack, .returned heap, rfl⟩
  | returned heap =>
    exact ⟨_, size_returned program heap k stack size (by omega), .done heap, rfl⟩
  | done heap => exact False.elim (active ⟨_, _, rfl⟩)

theorem claimed_step_heap (program : Events.Program E)
    (size : interface.types "size_t" = some .size) (bounded : k < 2^64)
    (ready : ClaimedReady flags count k stack before) (active : ¬ Exit stack before)
    (step : Events.Step program before events after) :
    CReadOnly.typedHeap after = CReadOnly.typedHeap before := by
  obtain ⟨next, enabled, _, heap⟩ := claimed_next program size bounded ready active
  obtain ⟨_, rfl⟩ := Events.internal_unique program enabled events after step
  exact heap

end Rumoca.CAtomicScan.ConcurrentInvariant
