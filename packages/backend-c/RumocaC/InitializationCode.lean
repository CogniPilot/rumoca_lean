import RumocaCore.IR
import RumocaC.Tree
import RumocaC.Origins
import RumocaC.InitializationOrigins
import RumocaC.StatementOrigins

/-! Shared C emission consumes the already selected Solve initial value. -/
namespace Rumoca.CInitialization
open CTree

def value (model : Solve.Model source) : Expr :=
  .cast "double" (.nat model.initial.initial)

/-- The generated operation owns its complete expression annotations. Pure C
syntax is a projection of this checked emission, not a second unannotated API. -/
structure Emission (model : Solve.Model source) (target : Expr) where
  origins : Origins model
  targetOrigins : Expr.Origins origins.table target
  target_checked : targetOrigins.Every (fun origin => origin = origins.target)
  valueOrigins : Expr.Origins origins.table (value model)
  value_checked : valueOrigins = .cast origins.conversion origins.conversion (.nat origins.literal)

def Emission.statement (_ : Emission model target) : Stmt := .assign target (value model)

def Emission.statementOrigins (emission : Emission model target) :
    Stmt.Origins emission.origins.table emission.statement :=
  .assign emission.origins.write emission.targetOrigins emission.valueOrigins

def emit (model : Solve.Model source) (target : Expr) : Emission model target :=
  let origins := OriginLowering.lower model
  ⟨origins, Expr.Origins.uniform origins.target target,
    Expr.Origins.uniform_every origins.target (fun origin => origin = origins.target) rfl target,
    .cast origins.conversion origins.conversion (.nat origins.literal), rfl⟩

end Rumoca.CInitialization
