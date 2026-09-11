import RumocaCore.IR
import RumocaC.Tree

/-! Shared C emission consumes the already selected Solve initial value. -/
namespace Rumoca.CInitialization
open CTree

def value (model : Solve.Model source) : Expr :=
  .cast "double" (.nat model.initial.initial)

def statement (model : Solve.Model source) (target : Expr) : Stmt :=
  .assign target (value model)

end Rumoca.CInitialization
