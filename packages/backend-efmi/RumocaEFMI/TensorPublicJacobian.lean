import RumocaEFMI.TensorPublicRHS
import RumocaC.DiagonalWritable
import RumocaEFMI.TensorContextJacobian

noncomputable section
namespace Rumoca.EFMI.PublicJacobian
open CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage

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
      finalHeap q = heap q) := by
  letI : CInterface := NumericalInterface.interface
  have separate : Diagonal.Separate (base.member jacobianVar.name) (base.member inputVar.name) inputShape :=
    fun i _ j _ => Address.fields_separate base jacobianVar.name inputVar.name (by decide +kernel) i j
  obtain ⟨ad, ran, reads, observes, frame⟩ := ContextJacobian.helper_exact
    TensorArrayMembers.declarations objects unusedKernel (base.member inputVar.name)
    (base.member jacobianVar.name) input input rhs result heap executed separate storage.input_reads
    adds storage.jacobian (by decide +kernel)
  exact ⟨storage_after storage result, ad, ran, reads, observes, frame⟩

end Rumoca.EFMI.PublicJacobian
