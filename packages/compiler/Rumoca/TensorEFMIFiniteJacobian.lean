import Rumoca.TensorEFMISourceMethod
import RumocaCore.Array.ADFiniteSquare

/-! Whole source-bound DoStep from finite RHS execution alone. The exact
Jacobian coefficient vector is derived, not supplied by an external premise.
The same final heap carries execution, source observations and encoded values. -/
noncomputable section
namespace Rumoca.EFMI.SourceMethod
open ArrayProfile Rumoca.Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open TensorProduction TensorNumericalLinkage

/-- Mandatory actual-byte contract for the existing square/Jacobian profile.
This does not admit overflowing squares or prove native C compilation. -/
def FiniteDoStep (a : TensorArtifact source) (c : String) : Prop :=
  ∀ (unusedKernel : CSyntax.Program) (values : String → Values stateShape)
    (objects : CDeclaredMembers.Objects) (heap : Heap) (base : Address)
    (rhs : Values stateShape),
    TensorPublicStorage.Storage objects heap base
      (values a.prepared.parsed.parsed.ast.header.input) →
    Finite.Executes a.prepared.kernel.derivative
      (environment (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input)) rhs →
    letI : CInterface := NumericalInterface.interface
    let result := (squareJacobianProgram stateShape).coefficients.eval Finite.ops
      Binary64.positiveZero Binary64.one
      (environment (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input))
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
            behavior = .terminates ⟨.integer 0, finalHeap⟩

theorem finiteDoStep (a : TensorArtifact source)
    (contract : TensorProductionContract a algorithm c) : FiniteDoStep a c := by
  intro unusedKernel values objects heap base rhs storage rhsExecuted
  have squareRHS := rhsExecuted
  rw [JacobianObservation.prepared_index a contract] at squareRHS
  exact doStep a contract unusedKernel values objects heap base rhs _ storage rhsExecuted
    (ADExact.coefficient_adds_from_finite_rhs
      (values a.prepared.parsed.parsed.ast.header.state)
      (values a.prepared.parsed.parsed.ast.header.input) rhs squareRHS)

end Rumoca.EFMI.SourceMethod
