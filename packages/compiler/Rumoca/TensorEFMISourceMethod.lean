import RumocaEFMI.TensorMethodEntry
import Rumoca.TensorEFMISourceObservation

/-! Source-owned whole DoStep composition, still a conditional scratch product.
No new producer-supplied statement is accepted as an artifact certificate. -/
noncomputable section
namespace Rumoca.ArrayProfile.StateIrrelevant
open Rumoca.Tensor Solve.Tensor CMemory.TensorView

theorem rhs (state other input result : Values shape) :
    Finite.Executes (squareProgram shape) (environment state input) result ↔
      Finite.Executes (squareProgram shape) (environment other input) result := by
  rw [square_finite_correct, square_finite_correct]

theorem coefficients (state other input result : Values shape) :
    Finite.Executes (squareJacobianProgram shape).coefficients (environment state input) result ↔
      Finite.Executes (squareJacobianProgram shape).coefficients (environment other input) result := by
  rw [ADExact.coefficients_executes_iff, ADExact.coefficients_executes_iff]

theorem matrix (state other input : Values shape) :
    (squareJacobianProgram shape).eval Finite.ops Binary64.positiveZero Binary64.one
      (environment state input) =
    (squareJacobianProgram shape).eval Finite.ops Binary64.positiveZero Binary64.one
      (environment other input) := rfl

theorem observes (heap : CMemory.Heap) (output : CMemory.Address) (state other input : Values shape) :
    CTensor.SquareJacobianObservation.Observes heap output state input ↔
      CTensor.SquareJacobianObservation.Observes heap output other input := by
  simp only [CTensor.SquareJacobianObservation.Observes,
    CTensor.SquareJacobianObservation.mathematical_eq]

end Rumoca.ArrayProfile.StateIrrelevant

namespace Rumoca.EFMI.SourceMethod
open ArrayProfile Rumoca.Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open TensorProduction TensorNumericalLinkage

/-- One source artifact determines the input labels, built-in denotation,
prepared derivative and diagonal, and exact actual C text. Full ordinary
method execution and both numerical/source observations share ONE final heap.
The source state may differ arbitrarily from the input, as in the source IR;
the actual C helper's ignored state argument need not point at that source state. -/
theorem doStep (a : TensorArtifact source)
    (contract : TensorProductionContract a algorithm c) (unusedKernel : CSyntax.Program)
    (values : String → Values stateShape) (objects : CDeclaredMembers.Objects)
    (heap : Heap) (base : Address) (rhs result : Values stateShape)
    (storage : TensorPublicStorage.Storage objects heap base
      (values a.prepared.parsed.parsed.ast.header.input))
    (rhsExecuted : Finite.Executes a.prepared.kernel.derivative
      (environment (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input)) rhs)
    (adds : ∀ i : Fin stateShape.volume,
      Binary64.Adds (values a.prepared.parsed.parsed.ast.header.input)[i]
        (values a.prepared.parsed.parsed.ast.header.input)[i] (.finite result[i])) :
    letI : CInterface := NumericalInterface.interface
    SourceObservation.SourceMatrix a values ∧
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
    ∃ diagonal : DiagonalProgram [stateShape, stateShape] stateShape,
      a.prepared.kernel.diagonal = some diagonal ∧
      ∃ finalHeap,
        ContextDoStep.Outcome objects heap finalHeap base
          (values a.prepared.parsed.parsed.ast.header.input) rhs result ∧
        Finite.Executes diagonal.coefficients
          (environment (values a.prepared.parsed.parsed.ast.header.state)
            (values a.prepared.parsed.parsed.ast.header.input)) result ∧
        Reads finalHeap (base.member jacobianVar.name)
          (diagonal.eval Finite.ops Binary64.positiveZero Binary64.one
            (environment (values a.prepared.parsed.parsed.ast.header.state)
              (values a.prepared.parsed.parsed.ast.header.input))) ∧
        SquareJacobianObservation.Observes finalHeap (base.member jacobianVar.name)
          (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input) ∧
        (∀ stack, Transition.Reaches
          (CContextMachine.machine (TensorContextCalls.expressions objects) (program unusedKernel)).step
          (.calling doStepName [.pointer (some base)] heap stack)
          (.returning (.integer 0) finalHeap stack)) ∧
        ∀ behavior,
          (CContextMachine.machine (TensorContextCalls.expressions objects) (program unusedKernel)).Behaves
            (.calling doStepName [.pointer (some base)] heap .done) behavior ↔
            behavior = .terminates ⟨.integer 0, finalHeap⟩ := by
  letI : CInterface := NumericalInterface.interface
  have index := JacobianObservation.prepared_index a contract
  have squareRHS := rhsExecuted
  rw [index] at squareRHS
  have inputRHS := (StateIrrelevant.rhs
    (values a.prepared.parsed.parsed.ast.header.state)
    (values a.prepared.parsed.parsed.ast.header.input)
    (values a.prepared.parsed.parsed.ast.header.input) rhs).1 squareRHS
  obtain ⟨finalHeap, outcome, ran, behaviors⟩ := ContextMethod.doStep unusedKernel objects heap base
    (values a.prepared.parsed.parsed.ast.header.input) rhs result storage inputRHS adds
  refine ⟨SourceObservation.source_matrix a contract values, JacobianObservation.actual_trees a contract,
    squareJacobianProgram stateShape, ?_, finalHeap, outcome, ?_, ?_, ?_, ran, behaviors⟩
  · rw [index]; rfl
  · exact (StateIrrelevant.coefficients _ _ _ _).1 outcome.derivative
  · exact (StateIrrelevant.matrix _ _ _).symm ▸ outcome.jacobian
  · exact (StateIrrelevant.observes _ _ _ _ _).1 outcome.mathematical

end Rumoca.EFMI.SourceMethod
