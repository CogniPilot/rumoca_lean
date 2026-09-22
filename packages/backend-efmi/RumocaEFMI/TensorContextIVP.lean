import RumocaC.AddressedIVP
import RumocaC.ContextCallResult
import RumocaEFMI.TensorNumericalFieldFree

/-! Actual eFMI initial/RHS tables, on the declaration-aware machine. All helper
lookup/header/field-free premises are discharged; storage and finite RHS remain. -/
noncomputable section
namespace Rumoca.EFMI.ContextIVP
open CMemory CMemory.TensorView CTensor CTensor.ProgramFixture Solve.Tensor
open TensorNumericalLinkage

theorem initial (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (unusedKernel : CSyntax.Program)
    (heap : Heap) (addresses : String → Address) (shape : Tensor.Shape)
    (bounded : shape.volume < 2 ^ 64) (writable : Writable heap (addresses "x") shape.volume) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, Reads finalHeap (addresses "x")
        ((IVPEntry.kernel shape).problem.initial Finite.ops Binary64.positiveZero Binary64.one) ∧
      Writable finalHeap (addresses "x") shape.volume ∧
      (∀ q, (∀ i < shape.volume, q ≠ (addresses "x").index i) → finalHeap q = heap q) ∧
      CContextMachine.CallResult (CContextMachine.declared declarations objects)
        (program unusedKernel) (IVPEntry.plan shape).initial.function.name
        (Lowering.Arguments.values (IVPEntry.plan shape).initial.function.parameters
          (AddressedIVP.args addresses shape)) heap finalHeap := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, reads, writes, frame, ran⟩ :=
    AddressedIVP.initial_call definitions (initial_library_numerical shape)
      (initial_defined shape) heap addresses bounded writable
  exact ⟨finalHeap, reads, writes, frame,
    CContextMachine.loop_call_result_context declarations objects (program unusedKernel)
      definitions (numerical_in_actual unusedKernel) TensorNumericalFieldFree.definition_body
      ((ran _).2 rfl)⟩

theorem derivative (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (unusedKernel : CSyntax.Program)
    (heap : Heap) (addresses : String → Address) (state input result : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (addresses "x") state) (readsInput : Reads heap (addresses "u") input)
    (writable : Writable heap (addresses "dx") shape.volume)
    (separate : ∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j)
    (executed : Finite.Executes (IVPEntry.kernel shape).derivative
      (ArrayProfile.environment state input) result) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, Reads finalHeap (addresses "dx") result ∧
      Writable finalHeap (addresses "dx") shape.volume ∧
      (∀ q, (∀ i < shape.volume, q ≠ (addresses "dx").index i) → finalHeap q = heap q) ∧
      CContextMachine.CallResult (CContextMachine.declared declarations objects)
        (program unusedKernel) (IVPEntry.plan shape).derivative.function.name
        (Lowering.Arguments.values (IVPEntry.plan shape).derivative.function.parameters
          (AddressedIVP.args addresses shape)) heap finalHeap := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, reads, writes, frame, ran⟩ :=
    AddressedIVP.derivative_call definitions (derivative_library_numerical shape)
      (derivative_defined shape) heap addresses state input result bounded
      readsState readsInput writable separate executed
  exact ⟨finalHeap, reads, writes, frame,
    CContextMachine.loop_call_result_context declarations objects (program unusedKernel)
      definitions (numerical_in_actual unusedKernel) TensorNumericalFieldFree.definition_body
      ((ran _).2 rfl)⟩

end Rumoca.EFMI.ContextIVP
