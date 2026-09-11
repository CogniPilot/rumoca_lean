import RumocaCore.Solve.AlgorithmSyntax
import RumocaCore.GALEC.Origins

/-! Exact operation and operand origins through tensor register lowering. -/
namespace Rumoca.Solve.Algorithm
open Rumoca.Tensor
open Rumoca.Solve.Tensor (Ref)
open _root_.Parser.Provenance (Table)

variable {Site Rule : Type} {table : Table Site Rule}
abbrev Origin (table : Table Site Rule) := _root_.Parser.Provenance.Ref table

/-- Operation and operand occurrences remain distinct even when two operands
read the same register. Register types still retain complete tensor shapes. -/
inductive Program.Origins (table : Table Site Rule) : Program Γ shape → Type where
  | ret (command value : Origin table) : Origins table (.ret reference)
  | fill (operation : Origin table) (next : Origins table program) :
      Origins table (.fill literal program)
  | add (operation left right : Origin table) (next : Origins table program) :
      Origins table (.add lhs rhs program)

/-- This metadata construction follows the existing CPS lowering. The value
origin passed to the continuation describes this use of the result register. -/
def lowerExprOrigins {expr : GALEC.Expr shape}
    (origins : GALEC.Expr.Origins table expr) (state : Ref Γ shape)
    (k : {Δ : List Shape} → Ren Γ Δ → Ref Δ shape → Program Δ result)
    (continuation : {Δ : List Shape} → (ren : Ren Γ Δ) → (ref : Ref Δ shape) →
      Origin table → Program.Origins table (k ren ref)) :
    Program.Origins table (lowerExpr expr state k) :=
  match origins with
  | .state origin => continuation (fun r => r) state origin
  | .zero origin => .fill origin (continuation (fun r => .there r) .here origin)
  | .one origin => .fill origin (continuation (fun r => .there r) .here origin)
  | .add operation left right =>
    lowerExprOrigins left state _ fun ren _lhs leftOrigin =>
      lowerExprOrigins right (ren state) _ fun ren' _rhs rightOrigin =>
        .add operation leftOrigin rightOrigin
          (continuation (fun r => .there (ren' (ren r))) .here operation)

def compileExprOrigins (origins : GALEC.Expr.Origins table expr) (command : Origin table) :
    Program.Origins table (compileExpr expr) :=
  lowerExprOrigins origins .here _ (fun _ _ value => .ret command value)

/-- Independent provenance observations record the exact operation and operand
origins. Tensor extents never enter this operation-level observation. -/
inductive OriginEvent (table : Table Site Rule) where
  | fill (operation : Origin table)
  | add (operation left right : Origin table)
  | ret (command value : Origin table)

def Program.Origins.events : Program.Origins table program → List (OriginEvent table)
  | .ret command value => [.ret command value]
  | .fill operation next => .fill operation :: next.events
  | .add operation left right next => .add operation left right :: next.events

def expressionEvents : GALEC.Expr.Origins table expr → List (OriginEvent table)
  | .state _ => []
  | .zero literal => [.fill literal]
  | .one literal => [.fill literal]
  | .add operation left right => expressionEvents left ++ expressionEvents right ++
      [.add operation left.root right.root]

/-- Exact operation/operand lineage through arbitrary CPS contexts. Repeated
state reads are observed separately when their results are consumed. -/
theorem lowerExprOrigins_events {expr : GALEC.Expr shape}
    (origins : GALEC.Expr.Origins table expr) (state : Ref Γ shape)
    (k : {Δ : List Shape} → Ren Γ Δ → Ref Δ shape → Program Δ result)
    (continuation : {Δ : List Shape} → (ren : Ren Γ Δ) → (ref : Ref Δ shape) →
      Origin table → Program.Origins table (k ren ref))
    (suffix : List (OriginEvent table))
    (hk : ∀ {Δ} (ren : Ren Γ Δ) (ref : Ref Δ shape),
      (continuation ren ref origins.root).events = suffix) :
    (lowerExprOrigins origins state k continuation).events = expressionEvents origins ++ suffix := by
  induction origins generalizing Γ suffix with
  | state reference => exact hk (fun r => r) state
  | zero literal =>
      change OriginEvent.fill literal :: (continuation (fun r => .there r) .here literal).events = _
      exact congrArg (OriginEvent.fill literal :: ·) (hk (fun r => .there r) .here)
  | one literal =>
      change OriginEvent.fill literal :: (continuation (fun r => .there r) .here literal).events = _
      exact congrArg (OriginEvent.fill literal :: ·) (hk (fun r => .there r) .here)
  | add operation left right ihLeft ihRight =>
      calc
        _ = expressionEvents left ++ (expressionEvents right ++
            (OriginEvent.add operation left.root right.root :: suffix)) := by
          change (lowerExprOrigins left state _ _).events = _
          apply ihLeft
          intro Δ ren lhs
          apply ihRight
          intro Δ' ren' rhs
          change OriginEvent.add operation left.root right.root ::
            (continuation (fun r => .there (ren' (ren r))) .here operation).events = _
          exact congrArg (OriginEvent.add operation left.root right.root :: ·)
            (hk (fun r => .there (ren' (ren r))) .here)
        _ = _ := by simp only [expressionEvents, List.append_assoc, List.singleton_append]

theorem compileExprOrigins_events (origins : GALEC.Expr.Origins table expr)
    (command : Origin table) :
    (compileExprOrigins origins command).events =
      expressionEvents origins ++ [.ret command origins.root] := by
  apply lowerExprOrigins_events
  intro Δ ren ref
  rfl

def compileBodyOrigins {body : Option (GALEC.Expr shape)}
    (origins : GALEC.BodyOrigins table body) (state : Origin table) :
    Program.Origins table (compileBody body) :=
  match origins with
  | .empty method => .ret method state
  | .assign _ assignment _ value => compileExprOrigins value assignment

def bodyEvents : GALEC.BodyOrigins table body → Origin table → List (OriginEvent table)
  | .empty method, state => [.ret method state]
  | .assign _ assignment _ value, _ => expressionEvents value ++ [.ret assignment value.root]

theorem compileBodyOrigins_events (origins : GALEC.BodyOrigins table body)
    (state : Origin table) :
    (compileBodyOrigins origins state).events = bodyEvents origins state := by
  cases origins with
  | empty method => rfl
  | assign method assignment target value => exact compileExprOrigins_events value assignment

/-- Root and destination occurrences stay explicit alongside the program
traces. In particular, an assignment's target is not inferred from a value's
origin or discarded when the expression becomes a return instruction. -/
structure Block.Origins (table : Table Site Rule) (block : Block shape) where
  model : Origin table
  stateDeclaration : Origin table
  startupMethod : Origin table
  startupTarget : Origin table
  startup : Program.Origins table block.startup
  recalibrateMethod : Origin table
  recalibrateTarget : Origin table
  recalibrate : Program.Origins table block.recalibrate
  doStepMethod : Origin table
  doStepTarget : Origin table
  doStep : Program.Origins table block.doStep
  periodDeclaration : Origin table
  periodTarget : Origin table
  period : Program.Origins table block.startupPeriod

private def methodOrigin : GALEC.BodyOrigins table body → Origin table
  | .empty method => method
  | .assign method _ _ _ => method

private def targetOrigin : GALEC.BodyOrigins table body → Origin table → Origin table
  | .empty _, state => state
  | .assign _ _ target _, _ => target

def lowerOrigins (origins : GALEC.Block.Origins table block) : Block.Origins table (lower block) where
  model := origins.model
  stateDeclaration := origins.stateDeclaration
  startupMethod := methodOrigin origins.startup
  startupTarget := targetOrigin origins.startup origins.stateDeclaration
  startup := compileBodyOrigins origins.startup origins.stateDeclaration
  recalibrateMethod := methodOrigin origins.recalibrate
  recalibrateTarget := targetOrigin origins.recalibrate origins.stateDeclaration
  recalibrate := compileBodyOrigins origins.recalibrate origins.stateDeclaration
  doStepMethod := methodOrigin origins.doStep
  doStepTarget := targetOrigin origins.doStep origins.stateDeclaration
  doStep := compileBodyOrigins origins.doStep origins.stateDeclaration
  periodDeclaration := origins.periodDeclaration
  periodTarget := origins.periodTarget
  period := compileExprOrigins origins.periodValue origins.periodAssignment

theorem lowerOrigins_events (origins : GALEC.Block.Origins table block) :
    (lowerOrigins origins).startup.events = bodyEvents origins.startup origins.stateDeclaration ∧
    (lowerOrigins origins).recalibrate.events = bodyEvents origins.recalibrate origins.stateDeclaration ∧
    (lowerOrigins origins).doStep.events = bodyEvents origins.doStep origins.stateDeclaration ∧
    (lowerOrigins origins).period.events = expressionEvents origins.periodValue ++
      [.ret origins.periodAssignment origins.periodValue.root] :=
  ⟨compileBodyOrigins_events origins.startup origins.stateDeclaration,
    compileBodyOrigins_events origins.recalibrate origins.stateDeclaration,
    compileBodyOrigins_events origins.doStep origins.stateDeclaration,
    compileExprOrigins_events origins.periodValue origins.periodAssignment⟩

end Rumoca.Solve.Algorithm
