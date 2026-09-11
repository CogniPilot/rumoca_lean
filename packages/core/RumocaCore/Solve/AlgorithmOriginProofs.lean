import RumocaCore.Solve.AlgorithmProofs

namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor
open _root_.Parser.Provenance (Table)
variable {Site Rule : Type} {table : Table Site Rule}

/-- The same actual lowering preserves both expression meaning and exact
operation/use provenance, universally over tensor shapes and scalar operations. -/
theorem compileExpr_value_and_origins {expr : GALEC.Expr shape}
    (origins : GALEC.Expr.Origins table expr) (command : Origin table)
    (zero one : α) (add : α → α → α) (state : Value α shape) :
    (compileExpr expr).eval zero one add (Solve.Tensor.Env.push state Solve.Tensor.Env.empty) =
      expr.eval zero one add state ∧
    (compileExprOrigins origins command).events =
      expressionEvents origins ++ [.ret command origins.root] :=
  ⟨compileExpr_correct expr zero one add state, compileExprOrigins_events origins command⟩


/-- One composed guarantee for the actual prepared model: lifecycle evaluation
and every operation/operand origin come from the same GALEC product. -/
theorem Model.lowering_preserves (model : Model source) (zero one : α)
    (add : α → α → α) (method : GALEC.Method) (state : Value α scalar) :
    model.block.execute zero one add method state =
      model.origin.block.execute zero one add method state ∧
    (model.lowered ▸ model.origins).startup.events =
      bodyEvents model.origin.originTrace.startup model.origin.originTrace.stateDeclaration ∧
    (model.lowered ▸ model.origins).recalibrate.events =
      bodyEvents model.origin.originTrace.recalibrate model.origin.originTrace.stateDeclaration ∧
    (model.lowered ▸ model.origins).doStep.events =
      bodyEvents model.origin.originTrace.doStep model.origin.originTrace.stateDeclaration ∧
    (model.lowered ▸ model.origins).period.events =
      expressionEvents model.origin.originTrace.periodValue ++
        [.ret model.origin.originTrace.periodAssignment model.origin.originTrace.periodValue.root] := by
  constructor
  · rw [model.lowered]
    exact lower_correct model.origin.block zero one add method state
  · rw [model.origins_lowered]
    exact lowerOrigins_events model.origin.originTrace

end Rumoca.Solve.Algorithm
