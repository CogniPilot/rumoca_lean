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

/-- The initial admitted equation, generalized in representation only to a
tensor shape. This does not add Modelica array syntax or a tensor solver. -/
def drivenIVP (shape : Shape) : IVP where
  stateShape := shape
  inputShape := shape
  outputShape := shape
  initialProgram := fill shape .zero
  derivative := .ret (.there .here)
  output := .ret .here

theorem driven_initial (shape : Shape) (ops : ScalarOps α) (zero one : α) :
    (drivenIVP shape).initial ops zero one = Value.fill shape zero := rfl

theorem driven_rhs (shape : Shape) (ops : ScalarOps α) (zero one : α) (state input : Value α shape) :
    (drivenIVP shape).rhs ops zero one state input = input := rfl

theorem driven_outputs (shape : Shape) (ops : ScalarOps α) (zero one : α) (state input : Value α shape) :
    (drivenIVP shape).outputs ops zero one state input = state := rfl

/-- IR size is independent of tensor volume: no per-element instructions. -/
theorem driven_compact (shape : Shape) :
    (drivenIVP shape).initialProgram.nodeCount + (drivenIVP shape).derivative.nodeCount +
      (drivenIVP shape).output.nodeCount = 4 := rfl

end Rumoca.Solve
