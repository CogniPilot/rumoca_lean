import RumocaC.TensorSquareRhsTotal
import RumocaC.TensorSquareTable

/-! RHS source and linked-table outcomes, not merely arithmetic helper outcomes.
ArtifactContract binds the RHS fragment and ordinary Solve lowering.
LinkedArtifactContract additionally ties all executed table entries to their
actual surrounding file bytes. Callers supply storage and target header
correspondence, not a finite-result premise. -/
noncomputable section
namespace Rumoca.CTensor.SquareRhsTotal
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering ProgramFixture AddressedIVP

def StorageContract (definitions : CLoops.Calls.Definitions) : Prop :=
  ∀ [interface : CInterface], HeaderTypes interface →
  ∀ {shape : Tensor.Shape} (heap : Heap) (addresses : String → Address) (state input : Values shape),
  shape.volume < 2 ^ 64 → Reads heap (addresses "x") state → Reads heap (addresses "u") input →
  Writable heap (addresses "dx") shape.volume →
  (∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
    (addresses "dx").index i ≠ (addresses name).index j) →
  let final := finalHeap heap (addresses "dx") input
  EncodedTensor.ReadsBits final (addresses "dx") (Numerical.encode (Numerical.multiply input input)) ∧
  Writable final (addresses "dx") shape.volume ∧
  (∀ q, (∀ i < shape.volume, q ≠ (addresses "dx").index i) → final q = heap q) ∧
  (EncodedTensor.AllFinite final (addresses "dx") shape ↔
    ∃ result, Finite.Executes (IVPEntry.kernel shape).derivative (ArrayProfile.environment state input) result) ∧
  (Numerical.allFiniteBits (Numerical.encode (Numerical.multiply input input)) = false ↔
    ∃ i : Fin shape.volume, Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i]) ∧
  (∀ result, Finite.Executes (IVPEntry.kernel shape).derivative (ArrayProfile.environment state input) result →
    final = TensorView.written heap (addresses "dx") result shape.volume) ∧
  (∀ behavior, (CLoops.Calls.machine definitions).Behaves
    (.calling (IVPEntry.plan shape).derivative.function.name
      (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape)) heap .done)
    behavior ↔ behavior = .terminates final) ∧
  (∀ (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects)
    (p : CCalls.Program), CCalls.Typed.Extends definitions p →
    CContextMachine.CallResult (CContextMachine.declared declarations objects) p
      (IVPEntry.plan shape).derivative.function.name
      (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape)) heap final)

theorem storage_correct (definitions : CLoops.Calls.Definitions)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : ∀ shape, definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree)
    (free : CContextMachine.FieldFree.DefinitionsFree definitions) : StorageContract definitions := by
  intro interface header shape heap addresses state input bounded readState readInput writeOutput separate
  exact ⟨reads heap (addresses "dx") input, writable heap (addresses "dx") input,
    frame heap (addresses "dx") input, finite_execution heap (addresses "dx") state input,
    detects_overflow input, finite_heap heap (addresses "dx") state input,
    call_correct definitions header helper (found shape) heap addresses state input bounded
      readState readInput writeOutput separate,
    fun declarations objects p linked => call_context definitions header helper (found shape)
      heap addresses state input bounded readState readInput writeOutput separate declarations objects p linked free⟩

theorem closed_free : CContextMachine.FieldFree.DefinitionsFree TensorKernel.definitions := by
  intro name fn found
  have member := (CCalls.TreeTable.lookup_some TensorKernel.functions name fn found).1
  have all : TensorKernel.functions.all (fun f => CDeclaredMembers.FieldFree.body f.body) = true := rfl
  exact List.all_eq_true.mp all fn member

theorem closed_storage : StorageContract TensorKernel.definitions :=
  storage_correct TensorKernel.definitions (TensorKernel.binary_defined .mul (Or.inr rfl))
    TensorKernel.derivative_defined closed_free

def ArtifactContract (actual : String) : Prop :=
  actual = IVPEntry.sources.derivative ∧
  (∀ shape, (IVPEntry.plan shape).derivative.ContractFor actual) ∧
  StorageContract TensorKernel.definitions

theorem artifact_correct (actual : String) (printed : actual = IVPEntry.sources.derivative) :
    ArtifactContract actual := by
  refine ⟨printed, ?_, closed_storage⟩
  intro shape
  rw [printed]
  exact (IVPEntry.plan shape).derivative.correct_for (IVPEntry.plan_valid shape).2.1

/-- All executed definitions are rendered in this actual file in table order.
The owning artifact fixes the prefix/suffix (headers and interface methods)
and retains their own contracts; this is not a parser for arbitrary C text. -/
def LinkedArtifactContract (actual : String) (functions : List Function) (preamble postlude : String) : Prop :=
  actual = preamble ++ String.join (functions.map Function.render) ++ postlude ∧
  StorageContract (CCalls.TreeTable.treeDefinitions functions)

theorem linked_artifact_correct (actual : String) (functions : List Function) (preamble postlude : String)
    (printed : actual = preamble ++ String.join (functions.map Function.render) ++ postlude)
    (storage : StorageContract (CCalls.TreeTable.treeDefinitions functions)) :
    LinkedArtifactContract actual functions preamble postlude := ⟨printed, storage⟩

end Rumoca.CTensor.SquareRhsTotal
