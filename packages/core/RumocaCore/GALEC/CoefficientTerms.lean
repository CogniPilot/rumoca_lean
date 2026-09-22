import RumocaCore.GALEC.Statements
import RumocaCore.GALEC.CoefficientRealization

/-! Reify a previously certified immutable-input coefficient expression into
ordinary typed scalar reads and operators. This translation performs no AD,
name resolution, arithmetic rewriting or tensor-element enumeration. -/
namespace Rumoca.GALEC.Coefficients
open Rumoca.Tensor Rumoca.Solve.Tensor

def ScalarExpr.toTerm (ref : Ref inputs shape) (indices : Subscripts bounds shape.dimensions) :
    ScalarExpr → ScalarTerm inputs outputs bounds
  | .input => .input ref indices
  | .literal value => .literal value
  | .binary op left right => .binary op (left.toTerm ref indices) (right.toTerm ref indices)

theorem ScalarExpr.toTerm_eval (expression : ScalarExpr) (ref : Ref inputs shape)
    (indices : Subscripts bounds shape.dimensions) (ops : ScalarOps α) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (iterators : IteratorEnv bounds) :
    (expression.toTerm ref indices).eval ops zero one input state iterators =
      expression.eval ops zero one (input ref)[Coordinate.index (indices.eval iterators)] := by
  induction expression with
  | input => rfl
  | literal value => rfl
  | binary op left right ihl ihr => simp only [toTerm, ScalarTerm.eval, eval, ihl, ihr]

noncomputable section

theorem ScalarExpr.toTerm_executes (expression : ScalarExpr) (ref : Ref inputs shape)
    (indices : Subscripts bounds shape.dimensions) (input : Env Binary64.Value inputs)
    (state : Env Binary64.Value outputs) (iterators : IteratorEnv bounds) (result : Binary64.Value) :
    (expression.toTerm ref indices).Evaluates Finite.Result Binary64.positiveZero Binary64.one
      input state iterators result ↔
    expression.Executes (input ref)[Coordinate.index (indices.eval iterators)] result := by
  induction expression generalizing result with
  | input =>
    constructor
    · intro h; cases h; exact .input
    · intro h; cases h; exact .input ref indices
  | literal value =>
    constructor
    · intro h; cases h; exact .literal value
    · intro h; cases h; exact .literal value
  | binary op left right ihl ihr =>
    constructor
    · intro h
      cases h with
      | binary hl hr step => exact .binary ((ihl _).mp hl) ((ihr _).mp hr) step
    · intro h
      cases h with
      | binary hl hr step => exact .binary ((ihl _).mpr hl) ((ihr _).mpr hr) step

theorem ScalarExpr.assignment_executes (expression : ScalarExpr)
    (source : Ref inputs sourceShape) (sourceIndices : Subscripts bounds sourceShape.dimensions)
    (target : Ref outputs targetShape) (targetIndices : Subscripts bounds targetShape.dimensions)
    (input : Env Binary64.Value inputs) (before after : Env Binary64.Value outputs)
    (iterators : IteratorEnv bounds) :
    (Statement.assign target targetIndices (expression.toTerm source sourceIndices)).Executes
      Finite.Result Binary64.positiveZero Binary64.one input iterators before after ↔
    ∃ tensor, expression.Writes (input source)[Coordinate.index (sourceIndices.eval iterators)]
      (Coordinate.index (targetIndices.eval iterators)) (before target) tensor ∧
      Env.Updates before target tensor after := by
  simp only [Statement.Executes, toTerm_executes, Writes]
  constructor
  · rintro ⟨result, tensor, evaluated, written, frame⟩
    exact ⟨tensor, ⟨result, evaluated, written⟩, frame⟩
  · rintro ⟨tensor, ⟨result, evaluated, written⟩, frame⟩
    exact ⟨result, tensor, evaluated, written, frame⟩

end
end Rumoca.GALEC.Coefficients
