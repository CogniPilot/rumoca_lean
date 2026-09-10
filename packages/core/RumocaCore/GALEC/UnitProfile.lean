import RumocaCore.Solve.AlgorithmProofs

/-! The admitted sampled block's state includes its immutable sampling-period
constant. These method semantics are distinct from the environment's lifecycle
protocol: calls on one instance must be serialized and Startup precedes use. -/
namespace Rumoca.GALEC.UnitProfile
open Rumoca.Tensor

structure State (α : Type) where
  x : Value α scalar
  samplePeriod : Value α scalar
  deriving Repr, BEq, DecidableEq

def execute (block : GALEC.Block scalar) (zero one : α) (add : α → α → α)
    (method : Method) (state : State α) : State α :=
  ⟨block.execute zero one add method state.x,
   match method with
   | .startup => block.startupPeriod.eval zero one add state.samplePeriod
   | _ => state.samplePeriod⟩

def solveExecute (block : Solve.Algorithm.Block scalar) (zero one : α) (add : α → α → α)
    (method : Method) (state : State α) : State α :=
  ⟨block.execute zero one add method state.x,
   match method with
   | .startup => block.startupPeriod.eval zero one add
       (Solve.Tensor.Env.push state.samplePeriod Solve.Tensor.Env.empty)
   | _ => state.samplePeriod⟩

theorem lower_correct (block : GALEC.Block scalar) (zero one : α) (add : α → α → α)
    (method : Method) (state : State α) :
    solveExecute (Solve.Algorithm.lower block) zero one add method state =
      execute block zero one add method state := by
  simp only [solveExecute, execute, Solve.Algorithm.lower_correct]
  cases method <;> simp only [Solve.Algorithm.lower, Solve.Algorithm.compileExpr_correct]

theorem startup_initializes (zero one : α) (add : α → α → α) (state : State α) :
    execute unitBlock zero one add .startup state =
      ⟨Value.fill scalar zero, Value.fill scalar one⟩ := rfl

theorem clock_preserved (zero one : α) (add : α → α → α)
    (method : Method) (state : State α) (h : state.samplePeriod = Value.fill scalar one) :
    (execute unitBlock zero one add method state).samplePeriod = Value.fill scalar one := by
  cases method <;> simp [execute, unitBlock, Expr.eval, h]

end Rumoca.GALEC.UnitProfile
