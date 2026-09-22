import RumocaC.TensorSquareRhsTotalContract
import RumocaEFMI.TensorNumericalFieldFree

/-! Total encoded RHS outcomes on the actual eFMI numerical/runtime tables.
All lookup, field-free and target-header premises are discharged here. This is
the prepared RHS call, not a whole DoStep or a numerical error-status policy. -/
noncomputable section
namespace Rumoca.EFMI.ContextRhsTotal
open CMemory CMemory.TensorView CTensor CTensor.ProgramFixture Solve.Tensor
open TensorNumericalLinkage

theorem storage : SquareRhsTotal.StorageContract definitions :=
  SquareRhsTotal.storage_correct definitions (binary_defined .mul (Or.inr rfl))
    derivative_defined TensorNumericalFieldFree.definition_body

def CallContract : Prop :=
  ∀ (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects)
    (unusedKernel : CSyntax.Program) {shape : Tensor.Shape}
    (heap : Heap) (addresses : String → Address) (state input : Values shape),
    shape.volume < 2 ^ 64 → Reads heap (addresses "x") state → Reads heap (addresses "u") input →
    Writable heap (addresses "dx") shape.volume →
    (∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j) →
    letI : CInterface := NumericalInterface.interface
    CContextMachine.CallResult (CContextMachine.declared declarations objects) (program unusedKernel)
      (IVPEntry.plan shape).derivative.function.name
      (Lowering.Arguments.values (IVPEntry.plan shape).derivative.function.parameters
        (AddressedIVP.args addresses shape)) heap (SquareRhsTotal.finalHeap heap (addresses "dx") input)

theorem call_correct : CallContract := by
  intro declarations objects unusedKernel shape heap addresses state input bounded readState readInput
    writable separate
  letI : CInterface := NumericalInterface.interface
  exact SquareRhsTotal.call_context definitions NumericalInterface.binary_header
    (binary_defined .mul (Or.inr rfl)) (derivative_defined shape) heap addresses state input
    bounded readState readInput writable separate declarations objects (program unusedKernel)
    (numerical_in_actual unusedKernel) TensorNumericalFieldFree.definition_body

end Rumoca.EFMI.ContextRhsTotal
