import Parser.LALR.EBNFActions
import Lean

/-! Proof-producing infrastructure, not an action interpreter or parser.
Only syntax-directed `Denotes` constructors and checked reflexivity are used.
The depth bound limits candidate construction, not the certified proposition.
No action result is evaluated by native code or imported as a proof. -/
namespace Parser.LALR.Frontend.StructuralActions.Certificate
open Lean Meta Elab Tactic

private def constructorFor (action value : Expr) : MetaM Name := do
  let a ← whnf action
  let v ← whnf value
  match a.getAppFn.constName! with
  | ``Action.empty => return ``Denotes.empty
  | ``Action.terminal => return ``Denotes.terminal
  | ``Action.seq => return ``Denotes.seq
  | ``Action.ref => return ``Denotes.ref
  | ``Action.map => return ``Denotes.map
  | ``Action.alt =>
    match v.getAppFn.constName! with
    | ``Structure.Value.altLeft => return ``Denotes.altLeft
    | ``Structure.Value.altRight => return ``Denotes.altRight
    | _ => throwError "action certificate: expected an alternative node"
  | ``Action.optional =>
    match v.getAppFn.constName! with
    | ``Structure.Value.optionalEmpty => return ``Denotes.optionalEmpty
    | ``Structure.Value.optionalSome => return ``Denotes.optionalSome
    | _ => throwError "action certificate: expected an optional node"
  | ``Action.many =>
    match v.getAppFn.constName! with
    | ``Structure.Value.manyEmpty => return ``Denotes.manyEmpty
    | ``Structure.Value.manyCons => return ``Denotes.manyCons
    | _ => throwError "action certificate: expected a repetition node"
  | _ => throwError "action certificate: action does not expose a constructor"

private def solve : Nat → MVarId → MetaM Unit
  | 0, _ => throwError "action certificate: construction depth exhausted"
  | fuel + 1, goal => goal.withContext do
    if ← goal.isAssigned then return
    let target ← instantiateMVars (← goal.getType)
    if target.isAppOf ``Eq then
      goal.refl
    else if target.isAppOf ``Denotes then
      let args := target.getAppArgs
      let constructor ← constructorFor args[args.size - 3]! args[args.size - 2]!
      let children ← goal.applyConst constructor
      -- In particular the rule-lookup equality is solved before its body.
      -- Other metavariables are inferred by these proof subgoals.
      for child in children do
        unless ← child.isAssigned do
          if ← isProp (← child.getType) then solve fuel child
      for child in children do
        unless ← child.isAssigned do
          throwError "action certificate: unresolved constructor parameter {child}"
    else
      throwError "action certificate: unsupported proof obligation {target}"

/-- Construct a proof of the supplied `Denotes` proposition. Infer the semantic
result from the constructors first, then check it against the requested result.
The caller must submit the returned term to the kernel, as with any tactic.
Failure (including a depth or definitional-equality limit) proves nothing. -/
def build (target : Expr) (depth : Nat := 4096) : MetaM Expr := do
  let target ← instantiateMVars target
  unless target.isAppOf ``Denotes do
    throwError "action certificate: expected a Denotes goal"
  let args := target.getAppArgs
  let expected := args[args.size - 1]!
  let result ← mkFreshExprMVar (← inferType expected)
  let inferredType := mkAppN target.getAppFn (args.set! (args.size - 1) result)
  let proof ← mkFreshExprMVar inferredType
  solve depth proof.mvarId!
  let proof ← instantiateMVars proof
  unless ← isDefEq (← inferType proof) target do
    throwError "action certificate: constructed result differs from requested result"
  let proof ← instantiateMVars proof
  if proof.hasMVar then
    throwError "action certificate: unresolved proof metavariables"
  return proof

/-- Syntax-directed certificates only; this tactic never unfolds `run`. -/
elab "action_certificate" : tactic => do
  let goal ← getMainGoal
  let proof ← goal.withContext <| build (← goal.getType)
  goal.assign proof
  replaceMainGoal []

end Parser.LALR.Frontend.StructuralActions.Certificate
