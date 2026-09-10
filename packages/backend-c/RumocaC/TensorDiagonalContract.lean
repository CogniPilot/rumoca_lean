import RumocaC.TensorDiagonalCalls
import RumocaC.TensorDiagonalSyntax

/-! Actual text, all call behaviors and the prepared Solve diagonal result.
The coefficient producer's finite execution, storage validity and external
definition/header bindings are explicit. Allocation, native linkage and FMI
lifecycle composition are separate obligations. -/
noncomputable section
namespace Rumoca.CTensor.Diagonal
open CMemory CMemory.TensorView Rumoca.Tensor Solve.Tensor

def ExecutionContract : Prop :=
  ∀ (interface : CInterface) (shape : Shape) (values : Values shape) (input output : Address)
    (heap : Heap) (definitions : CLoops.Calls.Definitions),
    CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
    definitions function.signature.name = some function →
    definitions Fill.function.signature.name = some Fill.function →
    Reads heap input values → Writable heap output (matrixShape shape.volume shape.volume).volume →
    Separate output input shape → (matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    Reads (resultHeap heap output values) output (matrix values) ∧
      (∀ q, (∀ i < (matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
        resultHeap heap output values q = heap q) ∧
      ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
        (.calling function.signature.name (argumentValues input output shape) heap .done) behavior ↔
        behavior = .terminates (resultHeap heap output values)

def SolveContract : Prop :=
  ∀ (interface : CInterface) (Γ : List Shape) (shape : Shape) (p : DiagonalProgram Γ shape)
    (env : Env Binary64.Value Γ) (values : Values shape) (input output : Address)
    (heap : Heap) (definitions : CLoops.Calls.Definitions),
    CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
    definitions function.signature.name = some function →
    definitions Fill.function.signature.name = some Fill.function →
    Finite.Executes p.coefficients env values → Reads heap input values →
    Writable heap output (matrixShape shape.volume shape.volume).volume → Separate output input shape →
    (matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    Reads (resultHeap heap output values) output (p.eval Finite.ops Binary64.positiveZero Binary64.one env) ∧
      ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
        (.calling function.signature.name (argumentValues input output shape) heap .done) behavior ↔
        behavior = .terminates (resultHeap heap output values)

theorem execution_correct : ExecutionContract := by
  intro interface shape values input output heap definitions header fillHeader found fillDefined
    reads writable separate bounded
  letI : CInterface := interface
  exact ⟨result_reads _ _ _, result_frame _ _ _,
    helper_call_correct definitions input output values heap found fillDefined header fillHeader
      separate reads writable bounded⟩

theorem solve_correct : SolveContract := by
  intro interface context shape program env values input output heap definitions header fillHeader
    found fillDefined executed reads writable separate bounded
  obtain ⟨readResult, _, behavior⟩ := execution_correct interface shape values input output heap
    definitions header fillHeader found fillDefined reads writable separate bounded
  obtain ⟨_, exactValues⟩ := Finite.executes_sound executed
  refine ⟨?_, behavior⟩
  have matrixEq := (congrArg matrix exactValues).trans (solve_matrix program env)
  rw [matrixEq] at readResult
  exact readResult

def ArtifactContract (source : String) : Prop := Syntax.Denotes source ∧ ExecutionContract ∧ SolveContract

theorem artifact_correct (source : String) (printed : source = function.render) : ArtifactContract source :=
  ⟨printed ▸ Syntax.render_denotes, execution_correct, solve_correct⟩

end Rumoca.CTensor.Diagonal
