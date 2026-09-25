import Rumoca.TensorEFMISourceMethod
import RumocaCore.Array.ADFiniteSquare

/-! Whole source-bound DoStep for every represented finite input. Exactly two
outcomes exist: every product and every sum of the input finite, with finite
RHS execution, the exact Jacobian coefficients and the ordinary return on one
final heap; otherwise a real overflow witness, the `OVERFLOW` status and every
other cell unchanged. The finite-RHS form is derived from it. -/
noncomputable section
namespace Rumoca.EFMI.SourceMethod
open ArrayProfile Rumoca.Tensor CMemory CMemory.TensorView CTensor Solve.Tensor
open TensorProduction TensorNumericalLinkage

/-- The ordinary DoStep result for a finite RHS `rhs`: the source-bound Jacobian,
the bytes and one public call returning zero, all on the same final heap. -/
def FiniteCall (a : TensorArtifact source) (c : String) (unusedKernel : CSyntax.Program)
    (values : String → Values stateShape) (objects : CDeclaredMembers.Objects)
    (heap : Heap) (base : Address) (rhs : Values stateShape) : Prop :=
  letI : CInterface := NumericalInterface.interface
  let result := (squareJacobianProgram stateShape).coefficients.eval Finite.ops
    Binary64.positiveZero Binary64.one
    (environment (values a.prepared.parsed.parsed.ast.header.state)
      (values a.prepared.parsed.parsed.ast.header.input))
  SourceObservation.SourceMatrix a values ∧
  c = TensorProduction.includes ++
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

/-- A coordinate whose square reaches the overflow threshold, or whose sum
reaches either threshold. -/
def OverflowWitness (input : Values stateShape) : Prop :=
  ∃ i : Fin stateShape.volume,
    Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i] ∨
      Binary64.value input[i] + Binary64.value input[i] ≤ -Binary64.overflowValue ∨
      Binary64.overflowValue ≤ Binary64.value input[i] + Binary64.value input[i]

/-- Mandatory actual-byte contract of the square/Jacobian DoStep: for every
represented finite input, either the prepared RHS executes, every coefficient
sum is finite and the ordinary result holds, or an overflow witness exists and
the public call returns the `OVERFLOW` encoding with only the status changed. -/
def DoStepOutcomes (a : TensorArtifact source) (c : String) : Prop :=
  ∀ (unusedKernel : CSyntax.Program) (values : String → Values stateShape)
    (objects : CDeclaredMembers.Objects) (heap : Heap) (base : Address),
    TensorPublicStorage.Storage objects heap base
      (values a.prepared.parsed.parsed.ast.header.input) →
    (∃ rhs, Finite.Executes a.prepared.kernel.derivative
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) rhs ∧
      (∀ i : Fin stateShape.volume,
        Binary64.Adds (values a.prepared.parsed.parsed.ast.header.input)[i]
          (values a.prepared.parsed.parsed.ast.header.input)[i]
          (.finite ((squareJacobianProgram stateShape).coefficients.eval Finite.ops
            Binary64.positiveZero Binary64.one
            (environment (values a.prepared.parsed.parsed.ast.header.state)
              (values a.prepared.parsed.parsed.ast.header.input)))[i])) ∧
      FiniteCall a c unusedKernel values objects heap base rhs) ∨
    (OverflowWitness (values a.prepared.parsed.parsed.ast.header.input) ∧
      ContextDoStep.OverflowOutcome objects heap
        (TensorPublicStorage.raised (TensorPublicStorage.cleared heap base) base) base
        (values a.prepared.parsed.parsed.ast.header.input) ∧
      ContextMethod.Returns (program unusedKernel) objects doStepName heap
        (TensorPublicStorage.raised (TensorPublicStorage.cleared heap base) base) base overflowStatus)

theorem coefficients_state (state input : Values stateShape) :
    (squareJacobianProgram stateShape).coefficients.eval Finite.ops Binary64.positiveZero Binary64.one
      (environment state input) = ContextDoStep.coefficients input := by
  apply Tensor.Value.ext
  intro i hi
  exact (ADExact.coefficients_eval_get state input ⟨i, hi⟩).trans
    (ADExact.coefficients_eval_get input input ⟨i, hi⟩).symm

theorem doStepOutcomes (a : TensorArtifact source)
    (contract : TensorProductionContract a algorithm c) : DoStepOutcomes a c := by
  intro unusedKernel values objects heap base storage
  have index := JacobianObservation.prepared_index a contract
  rcases ContextMethod.doStep_outcomes_in (program unusedKernel) (numerical_in_actual unusedKernel)
      (method_defined unusedKernel doStepFunction (by simp [TensorProduction.functions]))
      objects heap base (values a.prepared.parsed.parsed.ast.header.input) storage with
    ⟨_, sums, rhs, _, executed, _, _⟩ | ⟨failed, outcome, returned⟩
  · have sourceRan : Finite.Executes a.prepared.kernel.derivative
        (environment (values a.prepared.parsed.parsed.ast.header.state)
          (values a.prepared.parsed.parsed.ast.header.input)) rhs := by
      rw [index]
      exact (StateIrrelevant.rhs _ _ _ rhs).2 executed
    have adds := ContextDoStep.sum_adds _ sums
    rw [← coefficients_state (values a.prepared.parsed.parsed.ast.header.state)] at adds
    exact Or.inl ⟨rhs, sourceRan, adds, doStep a contract unusedKernel values objects heap base rhs _
      storage sourceRan adds⟩
  · refine Or.inr ⟨?_, outcome, returned⟩
    rcases failed with products | sums
    · obtain ⟨i, above⟩ := (ProductPreflight.square_overflow _).mp products
      exact ⟨i, Or.inl above⟩
    · obtain ⟨i, outside⟩ := (SumPreflight.result_overflow _ _).mp sums
      exact ⟨i, Or.inr outside⟩

/-- The finite-RHS contract, derived: a finite RHS excludes the overflow
outcome, since its square is finite and so is its doubling. -/
def FiniteDoStep (a : TensorArtifact source) (c : String) : Prop :=
  ∀ (unusedKernel : CSyntax.Program) (values : String → Values stateShape)
    (objects : CDeclaredMembers.Objects) (heap : Heap) (base : Address)
    (rhs : Values stateShape),
    TensorPublicStorage.Storage objects heap base
      (values a.prepared.parsed.parsed.ast.header.input) →
    Finite.Executes a.prepared.kernel.derivative
      (environment (values a.prepared.parsed.parsed.ast.header.state)
        (values a.prepared.parsed.parsed.ast.header.input)) rhs →
    FiniteCall a c unusedKernel values objects heap base rhs

theorem finiteDoStep (a : TensorArtifact source)
    (contract : TensorProductionContract a algorithm c) : FiniteDoStep a c := by
  intro unusedKernel values objects heap base rhs storage rhsExecuted
  have squareRHS := rhsExecuted
  rw [JacobianObservation.prepared_index a contract] at squareRHS
  rcases doStepOutcomes a contract unusedKernel values objects heap base storage with
    ⟨other, otherRan, _, call⟩ | ⟨⟨i, witness⟩, _, _⟩
  · rw [JacobianObservation.prepared_index a contract] at otherRan
    have same := Finite.execution_unique otherRan squareRHS
    subst same
    exact call
  · exfalso
    have adds := ADExact.coefficient_adds_from_finite_rhs
      (values a.prepared.parsed.parsed.ast.header.state)
      (values a.prepared.parsed.parsed.ast.header.input) rhs squareRHS i
    have inputRHS := (StateIrrelevant.rhs _
      (values a.prepared.parsed.parsed.ast.header.input) _ rhs).1 squareRHS
    have products := (ArrayProfile.square_detection_finite_execution _ _).mpr ⟨rhs, inputRHS⟩
    rcases witness with square | low | high
    · have failed := (ArrayProfile.square_detection_overflow _).mpr ⟨i, square⟩
      rw [products] at failed
      cases failed
    · have positive := Binary64.overflowValue_pos
      have bound := adds.1
      linarith
    · have bound := adds.2.1
      linarith

end Rumoca.EFMI.SourceMethod
