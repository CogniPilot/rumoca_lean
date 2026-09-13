import RumocaFMI3.ModelAdvance
import Rumoca.FMI3AdapterProofs
import Rumoca.FMI3InitializationSemantics

/-! Actual adapter evidence for the numerical helper and its initialized
source trajectory. Public communication-step policy is a separate contract. -/

noncomputable section
namespace Rumoca.FMI3
open CMemory CTree StaticFactory

/-- Numerical error is measured at the executed solver duration. This does
not identify that duration with a separately rounded communication clock. -/
theorem ModelAdvance.source_error (model : Solve.Model source)
    (heap : Heap) (p : Address) (x start : Binary64.Value) (n : Nat)
    (initialized : InitializationCalls.SourceInitialized source heap p start trajectory)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩) :
    |Binary64.value (model.run x n) - trajectory (Binary64.value start + (n : ℝ))| ≤ (n : ℝ) := by
  have represented : StateProofs.Represents heap p ⟨x⟩ := by
    simp [StateProofs.Represents, load, stored, convert, Value.finite]
  have same := InitializationCalls.source_initialized_unique initialized represented
  rw [same, Initialization.trajectory, model.run_correct]
  convert Binary64.run_error x n using 1
  congr 1
  ring

/-- Derive the actual helper's fragment, tokenization, definition bindings,
complete execution and source error from the existing adapter certificate.
Public step admission, outputs and communication-time histories are separate. -/
theorem adapter_model_advance (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      (∃ before after, adapter = before ++ Runtime.helpers[2].render ++ after) ∧
      Printer.FunctionTokenization RuntimePrinter.typedefs Runtime.helpers[2].render Runtime.helpers[2] ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (x : Binary64.Value) (n : CStatements.Counter),
        heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩ →
        let after := StateProofs.written heap (StateProofs.stateAddress p)
          (Binary64.toBits (a.solve.run x n.val)).val
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling "model_advance" [.pointer (some (p.member "model")), .integer n.val] heap .done) behavior ↔
          behavior = .terminates [] ⟨.void, after⟩) ∧
        after (StateProofs.stateAddress p) =
          some ⟨.float64, true, some (.finite (a.solve.run x n.val))⟩ ∧
        (∀ query, query ≠ StateProofs.stateAddress p → after query = heap query) ∧
        (∀ start trajectory, InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
          |Binary64.value (a.solve.run x n.val) - trajectory (Binary64.value start + (n.val : ℝ))| ≤
            (n.val : ℝ)) := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, derivative, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  have member : Runtime.helpers[2] ∈ Runtime.helpers := by simp [Runtime.helpers]
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_helper a.solve.prepareFMI3
    signatures Runtime.helpers[2] member
  refine ⟨signatures, pool, made, printed, ⟨before, after, printed ▸ located⟩,
    (Printer.function_denotes (RuntimePrinter.helpers_printable _ member)).tokenization, ?_⟩
  intro E objects firstBlock
  letI : CInterface := executionInterface objects (pool.addresses firstBlock)
  intro program actual heap p x n stored
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ModelAdvance.prepared_behaviors a.solve.prepareFMI3 signatures derivative.numerical.fresh
      objects (pool.addresses firstBlock) program actual heap (p.member "model") x n stored
  · simp [StateProofs.written, Value.finite]
  · intro query other
    exact StateProofs.written_frame heap _ query _ other
  · intro start trajectory initialized
    exact ModelAdvance.source_error a.solve heap p x start n.val initialized stored

end Rumoca.FMI3
end
