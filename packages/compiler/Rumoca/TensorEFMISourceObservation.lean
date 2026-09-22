import Rumoca.TensorEFMISourceJacobian
import RumocaEFMI.TensorJacobianExact

/-! Scratch artifact-own source observation, not whole-method execution. -/
noncomputable section
namespace Rumoca.EFMI.SourceObservation
open ArrayProfile Rumoca.Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open CTensor.SquareJacobianObservation

/-- The SAME artifact's stored lowering proof and parsed Algorithm denotation
exclude the driven-only source body. No extra pinned-AST assumption is supplied. -/
theorem source_jacobian_body (a : TensorArtifact input)
    (contract : TensorProductionContract a algorithm c) :
    ∃ output derivative rhs assigned call,
      a.prepared.parsed.parsed.ast.body = .jacobian output derivative rhs assigned call := by
  have index := JacobianObservation.prepared_index a contract
  let dae := ArrayProfile.DAE.lower
    (ArrayProfile.Flat.lower a.prepared.parsed.parsed.ast a.prepared.resolved)
  have checked := Solved.lower_checked dae
  rw [← a.prepared.kernel_lowered, index] at checked
  cases body : a.prepared.parsed.parsed.ast.body with
  | jacobian output derivative rhs assigned call => exact ⟨_, _, _, _, _, rfl⟩
  | driven derivative rhs =>
    have absent : dae.jacobian = none := by
      simp only [dae, ArrayProfile.DAE.lower, ArrayProfile.Flat.lower, body,
        ArrayProfile.Flat.jacobianFor, Option.map_none]
    obtain ⟨rhsProgram, initial, diagonal, _, _, hj, assembled⟩ :=
      Solved.lower_fields dae _ checked
    have shape : diagonal = some (squareJacobianProgram stateShape) :=
      (congrArg Solve.PointwiseIVP.diagonal assembled).symm
    rw [absent] at hj
    have missing : diagonal = none := (Option.some.inj hj).symm
    rw [missing] at shape
    cases shape

/-- Source labels, parsed built-in and mathematical Jacobian are tied to this
artifact's AST and fixed source shape, not an independently supplied model. -/
def SourceMatrix (a : TensorArtifact input)
    (values : String → Values stateShape) : Prop :=
  ∃ output derivative rhs assigned call,
    a.prepared.parsed.parsed.ast.body = .jacobian output derivative rhs assigned call ∧
    assigned = output ∧
    call.Denotes (fun name i => Binary64.value (values name)[i])
      (mathematical (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input))

theorem source_matrix (a : TensorArtifact input)
    (contract : TensorProductionContract a algorithm c) (values : String → Values stateShape) :
    SourceMatrix a values := by
  obtain ⟨output, derivative, rhs, assigned, call, body⟩ := source_jacobian_body a contract
  have resolved := a.prepared.resolved
  obtain ⟨_, _, _, _, components⟩ := resolved
  rw [body] at components
  refine ⟨output, derivative, rhs, assigned, call, body, components.2.2.2.2.2.1, ?_⟩
  exact JacobianObservation.source_builtin a.prepared.parsed.parsed.ast a.prepared.resolved body values

/-- Fixed-shape, artifact-own helper product. Actual byte/table identity,
source builtin, stored prepared diagonal, finite execution, exact matrix Reads
and real derivative observation all use the same source/value/heap witnesses.
No public-method argument evaluation or sequencing is asserted. -/
theorem artifact_helper (a : TensorArtifact source)
    (contract : TensorProductionContract a algorithm c) (unusedKernel : CSyntax.Program)
    (values : String → Values stateShape) (input output : Address)
    (rhs result : Values stateShape) (heap : Heap)
    (rhsExecuted : Finite.Executes a.prepared.kernel.derivative
      (environment (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input)) rhs)
    (separate : Diagonal.Separate output input stateShape)
    (reads : Reads heap input (values a.prepared.parsed.parsed.ast.header.input))
    (adds : ∀ i : Fin stateShape.volume,
      Binary64.Adds (values a.prepared.parsed.parsed.ast.header.input)[i]
        (values a.prepared.parsed.parsed.ast.header.input)[i] (.finite result[i]))
    (writable : Writable heap output jacobianShape.volume) :
    letI : CInterface := TensorNumericalLinkage.NumericalInterface.interface
    SourceMatrix a values ∧
    c = "#include <stddef.h>\n#include <stdint.h>\n" ++
      String.join (TensorNumericalLinkage.numericalFunctions.map CTree.Function.render) ++
      TensorProduction.header ++ String.join (TensorProduction.functions.map CTree.Function.render) ∧
    ∃ diagonal : DiagonalProgram [stateShape, stateShape] stateShape,
      a.prepared.kernel.diagonal = some diagonal ∧
      Finite.Executes diagonal.coefficients
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) result ∧
      CCalls.Typed.CallResult (TensorNumericalLinkage.program unusedKernel)
        SquareDiagonal.function.signature.name (Diagonal.argumentValues input output stateShape)
        heap (Diagonal.resultHeap heap output result) ∧
      Reads (Diagonal.resultHeap heap output result) output
        (diagonal.eval Finite.ops Binary64.positiveZero Binary64.one
          (environment (values a.prepared.parsed.parsed.ast.header.state)
            (values a.prepared.parsed.parsed.ast.header.input))) ∧
      Observes (Diagonal.resultHeap heap output result) output
        (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input) ∧
      (∀ q, (∀ i < jacobianShape.volume, q ≠ output.index i) →
        Diagonal.resultHeap heap output result q = heap q) := by
  letI : CInterface := TensorNumericalLinkage.NumericalInterface.interface
  have index := JacobianObservation.prepared_index a contract
  have squareRHS := rhsExecuted
  rw [index] at squareRHS
  obtain ⟨executed, ran, matrixReads, observes, frame⟩ :=
    JacobianExact.typed_helper_exact unusedKernel input output
      (values a.prepared.parsed.parsed.ast.header.state)
      (values a.prepared.parsed.parsed.ast.header.input) rhs result heap squareRHS
      separate reads adds writable (by decide +kernel)
  refine ⟨source_matrix a contract values, JacobianObservation.actual_trees a contract,
    squareJacobianProgram stateShape, ?_, executed, ran, matrixReads, observes, frame⟩
  rw [index]
  rfl

end Rumoca.EFMI.SourceObservation
