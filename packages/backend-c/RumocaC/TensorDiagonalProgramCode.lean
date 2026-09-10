import RumocaC.TensorProgramCode
import RumocaC.TensorDiagonalCode
import RumocaCore.Solve.Tensor.Diagonal

/-! A prepared coefficient program followed by its explicit matrix output. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor
def emitDiagonal (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) : Product p.shape :=
  let coefficients := emit p.coefficients plan layout
  ⟨coefficients.code ++ [Diagonal.invoke coefficients.result.pointer output.pointer coefficients.result.count output.count],
    output⟩

theorem emitDiagonal_code_count (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients)
    (layout : Layout Γ) (output : Buffer p.shape) :
    (emitDiagonal p plan layout output).code.length + 1 = p.nodeCount := by
  simpa only [emitDiagonal, List.length_append, List.length_singleton, DiagonalProgram.nodeCount]
    using congrArg (· + 1) (emit_code_count p.coefficients plan layout)

end Rumoca.CTensor.Lowering
