import RumocaCore.Solve.Tensor

/-! Backend-independent executable initial-value problems. FMI lifecycle and
solver policy are consumers of this representation, not part of its meaning.
There is one tensor per role in the initial profile; each retains its shape. -/
namespace Rumoca.Solve
open Rumoca.Tensor Solve.Tensor

structure IVP where
  stateShape : Shape
  inputShape : Shape
  outputShape : Shape
  initialProgram : Program [] stateShape
  derivative : Program [stateShape, inputShape] stateShape
  output : Program [stateShape, inputShape] outputShape
  deriving Repr

def IVP.environment (m : IVP) (state : Value α m.stateShape)
    (input : Value α m.inputShape) : Env α [m.stateShape, m.inputShape] :=
  Env.push state (Env.push input Env.empty)

def IVP.initial (m : IVP) (ops : ScalarOps α) (zero one : α) : Value α m.stateShape :=
  m.initialProgram.eval ops zero one Env.empty

def IVP.rhs (m : IVP) (ops : ScalarOps α) (zero one : α) (state : Value α m.stateShape)
    (input : Value α m.inputShape) : Value α m.stateShape :=
  m.derivative.eval ops zero one (m.environment state input)

def IVP.outputs (m : IVP) (ops : ScalarOps α) (zero one : α) (state : Value α m.stateShape)
    (input : Value α m.inputShape) : Value α m.outputShape :=
  m.output.eval ops zero one (m.environment state input)

end Rumoca.Solve
