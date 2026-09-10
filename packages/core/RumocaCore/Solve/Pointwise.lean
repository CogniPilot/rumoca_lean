import RumocaCore.Solve.IVP
import RumocaCore.Solve.Tensor.Diagonal

/-! Prepared executable data for one state tensor and one equally shaped
input tensor. The state is observed directly; an optional diagonal tensor
observation is already lowered to its coefficient program and materializer.
This root contains no source names, resolution or differentiation decisions. -/
namespace Rumoca.Solve
open Rumoca.Tensor Solve.Tensor

structure PointwiseIVP (shape : Shape) where
  initialProgram : Program [] shape
  derivative : Program [shape, shape] shape
  diagonal : Option (DiagonalProgram [shape, shape] shape)
  deriving Repr

def PointwiseIVP.problem (p : PointwiseIVP shape) : IVP where
  stateShape := shape
  inputShape := shape
  outputShape := shape
  initialProgram := p.initialProgram
  derivative := p.derivative
  output := .ret .here

end Rumoca.Solve
