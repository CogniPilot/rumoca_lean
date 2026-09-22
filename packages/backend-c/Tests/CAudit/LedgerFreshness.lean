import RumocaC.InvocationLedger
import ProofAudit.Audit

namespace Rumoca.CCalls.Host.Recording
open CMemory

/-- For every counter value, alignment can coexist with an active descriptor
at that value. Recording a new invocation then repeats its serial. This is a
counterexample to deriving freshness from alignment, not a production feature. -/
theorem alignment_allows_reissued_serial (serial : Nat) (heap : Heap) :
    ∃ (runtime : Concurrent.State) (ledger : Ledger),
      Aligned runtime ledger ∧ runtime.threads 0 = none ∧ ¬ Fresh ledger ∧
      (advance ledger 0 (.invoke "new" [] : Action Unit)).active 0 =
        some ⟨serial, "new", []⟩ ∧
      (advance ledger 0 (.invoke "new" [] : Action Unit)).active 1 =
        some ⟨serial, "old", []⟩ := by
  let runtime : Concurrent.State :=
    ⟨heap, fun thread => if thread = 0 then none else some (.halted ⟨.void, heap⟩)⟩
  let ledger : Ledger :=
    ⟨serial, fun thread => if thread = 0 then none else some ⟨serial, "old", []⟩⟩
  refine ⟨runtime, ledger, ?_, rfl, ?_, ?_, ?_⟩
  · intro thread
    by_cases zero : thread = 0 <;> simp [runtime, ledger, zero]
  · intro fresh
    have impossible := fresh 1 ⟨serial, "old", []⟩ (by simp [ledger])
    exact Nat.lt_irrefl serial impossible
  · simp [advance, bind, ledger]
  · simp [advance, bind, ledger]

#audit axioms alignment_allows_reissued_serial

end Rumoca.CCalls.Host.Recording
