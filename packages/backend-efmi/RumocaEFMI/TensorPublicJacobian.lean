import RumocaEFMI.TensorPublicRHS
import RumocaC.DiagonalWritable
import RumocaEFMI.TensorContextJacobian

noncomputable section
namespace Rumoca.EFMI.PublicJacobian
open CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

theorem storage_after (storage : Storage objects heap base input)
    (result : Values inputShape) :
    Storage objects (Diagonal.resultHeap heap (base.member jacobianVar.name) result) base input := by
  have frame := Diagonal.result_frame heap (base.member jacobianVar.name) result
  refine ⟨storage.object, ?_, ?_, Diagonal.result_writable _ _ _, ?_, ?_⟩
  · exact storage.inputCells.framed (PublicRHS.member_preserved frame (by decide +kernel))
  · exact writable_framed storage.square (PublicRHS.member_preserved frame (by decide +kernel))
  · apply storage.clock.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show clockName ≠ jacobianVar.name by decide +kernel) 0
  · apply storage.status.framed
    simpa only [Address.index_zero] using PublicRHS.member_preserved frame
      (show statusName ≠ jacobianVar.name by decide +kernel) 0

/-- Reuse the actual numerical library in any enclosing table that preserves
its definitions; unrelated public methods need not agree. -/
theorem helper_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (objects : Objects) (heap : Heap) (base : Address) (input rhs result : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    letI : CInterface := NumericalInterface.interface
    let finalHeap := Diagonal.resultHeap heap (base.member jacobianVar.name) result
    Storage objects finalHeap base input ∧
    Finite.Executes (ArrayProfile.squareJacobianProgram inputShape).coefficients
      (ArrayProfile.environment input input) result ∧
    CallResult (expressions objects) p "rumoca_square_jacobian_diag"
      [.pointer (some (base.member inputVar.name)), .pointer (some (base.member jacobianVar.name)),
        .integer inputVar.volume, .integer jacobianVar.volume] heap finalHeap ∧
    Reads finalHeap (base.member jacobianVar.name)
      ((ArrayProfile.squareJacobianProgram inputShape).eval Finite.ops Binary64.positiveZero Binary64.one
        (ArrayProfile.environment input input)) ∧
    SquareJacobianObservation.Observes finalHeap (base.member jacobianVar.name) input input ∧
    (∀ q, (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
      finalHeap q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  have separate : Diagonal.Separate (base.member jacobianVar.name) (base.member inputVar.name) inputShape :=
    fun i _ j _ => Address.fields_separate base jacobianVar.name inputVar.name (by decide +kernel) i j
  obtain ⟨ran, matrixReads, observes, frame⟩ := JacobianObservation.helper_observations
    (base.member inputVar.name) (base.member jacobianVar.name) input input result heap
    separate storage.input_reads adds storage.jacobian (by decide +kernel)
  have contextual := loop_call_result_context TensorArrayMembers.declarations objects p
    definitions linked TensorNumericalFieldFree.definition_body ((ran _).2 rfl)
  exact ⟨PublicJacobian.storage_after storage result,
    SquareJacobianExact.coefficients_from_rhs input input rhs result executed adds,
    contextual, (SquareJacobianExact.matrix_equal input input result adds) ▸ matrixReads,
    observes, frame⟩

theorem helper (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (input rhs result : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite result[i])) :
    letI : CInterface := NumericalInterface.interface
    let finalHeap := Diagonal.resultHeap heap (base.member jacobianVar.name) result
    Storage objects finalHeap base input ∧
    Finite.Executes (ArrayProfile.squareJacobianProgram inputShape).coefficients
      (ArrayProfile.environment input input) result ∧
    CContextMachine.CallResult (TensorContextCalls.expressions objects) (program unusedKernel)
      "rumoca_square_jacobian_diag"
      [.pointer (some (base.member inputVar.name)), .pointer (some (base.member jacobianVar.name)),
        .integer inputVar.volume, .integer jacobianVar.volume] heap finalHeap ∧
    Reads finalHeap (base.member jacobianVar.name)
      ((ArrayProfile.squareJacobianProgram inputShape).eval Finite.ops Binary64.positiveZero Binary64.one
        (ArrayProfile.environment input input)) ∧
    SquareJacobianObservation.Observes finalHeap (base.member jacobianVar.name) input input ∧
    (∀ q, (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
      finalHeap q = heap q) :=
  helper_in (program unusedKernel) (numerical_in_actual unusedKernel)
    objects heap base input rhs result storage executed adds

end Rumoca.EFMI.PublicJacobian
