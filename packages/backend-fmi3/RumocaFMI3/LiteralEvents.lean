import RumocaFMI3.LiteralPreparation
import RumocaC.LiteralEventPool

/-! The actual FMI function collection discharges the structural premises of
eventful literal lowering. No particular foreign outcome is assumed. -/
noncomputable section
namespace Rumoca.FMI3.LiteralPreparation
open CTree CMemory CLiteral

theorem event_lowering_behaviors (m : Solve.FMI3Model source) (sigs : List Signature)
    {pool : Pool (excluded ++ (functions m sigs).flatMap functionNames)}
    (made : prepare m sigs = some pool) (firstBlock : Nat)
    (original : @CCalls.Events.Program (pool.interface cInterface firstBlock) E)
    (same : @CCalls.Events.Program.internal (pool.interface cInterface firstBlock) E original = program m sigs)
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (∀ fn ∈ functions m sigs, functionTexts (Lowering.function pool.symbols fn) = []) ∧
    ((@CCalls.Events.machine E (pool.namedInterface cInterface firstBlock)
        (pool.eventProgram cInterface firstBlock original)).Behaves (.calling name args heap .done) behavior ↔
      (@CCalls.Events.machine E (pool.interface cInterface firstBlock) original).Behaves
        (.calling name args heap .done) behavior) := by
  refine ⟨pool_complete m sigs made, ?_⟩
  apply pool.event_invocation_behaviors cInterface firstBlock (header_fresh m sigs pool) original
  · rw [same]
    exact collected_names_cover (functions m sigs) (program m sigs) (program_covered m sigs)
  · intro functionName fn found
    rw [same] at found
    exact functions_calls m sigs fn (program_covered m sigs functionName fn found)

/-- All functions in the prepared table lose their literal syntax, and every
complete call retains exactly its eventful behaviors. The same foreign
relations and symbolic function addresses are used on both sides. -/
def EventPreparedContract (m : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (excluded ++ (functions m sigs).flatMap functionNames)) : Prop :=
  (∀ fn ∈ functions m sigs, functionTexts (Lowering.function pool.symbols fn) = []) ∧
  ∀ (E : Type) (firstBlock : Nat)
    (original : @CCalls.Events.Program (pool.interface cInterface firstBlock) E),
    @CCalls.Events.Program.internal (pool.interface cInterface firstBlock) E original = program m sigs →
    ∀ (name : String) (args : List Value) (heap : Heap)
      (behavior : Transition.Events.Observation E CBody.Result),
      (@CCalls.Events.machine E (pool.namedInterface cInterface firstBlock)
        (pool.eventProgram cInterface firstBlock original)).Behaves (.calling name args heap .done) behavior ↔
      (@CCalls.Events.machine E (pool.interface cInterface firstBlock) original).Behaves
        (.calling name args heap .done) behavior

/-- Successful preparation supplies the pass contract for the actual table.
Preparation success is a separate required artifact-checker obligation. -/
def EventContract (m : Solve.FMI3Model source) (sigs : List Signature) : Prop :=
  ∀ pool, prepare m sigs = some pool → EventPreparedContract m sigs pool

theorem event_contract (m : Solve.FMI3Model source) (sigs : List Signature) :
    EventContract m sigs := by
  intro pool made
  refine ⟨pool_complete m sigs made, ?_⟩
  intro E firstBlock original same name args heap behavior
  exact (event_lowering_behaviors m sigs made firstBlock original same name args heap behavior).2

end Rumoca.FMI3.LiteralPreparation
