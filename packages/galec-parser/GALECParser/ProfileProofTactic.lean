import Parser.LALR.ActionWords
import Mathlib.Tactic.CasesM

/-! Proof elaboration only: expose one inductive Words layer, then eliminate
its logical witnesses and typed lookup equality. The generated proofs are
kernel checked. This is neither a runtime parser nor a finite action engine. -/
open Lean Meta Elab Tactic

namespace Rumoca.GALEC.ProfileProofTactic

private def lookupEquality (ty : Expr) : MetaM Bool := do
  unless ty.isAppOfArity ``Eq 3 do return false
  let type ← whnf ty.getAppArgs[0]!
  unless type.isAppOfArity ``Option 1 do return false
  let action ← whnf type.getAppArgs[0]!
  return action.isAppOf ``Parser.LALR.Frontend.StructuralActions.Action

private partial def unpack (goal : MVarId) : MetaM (List MVarId) :=
  withTransparency .all do goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← whnf decl.type
      let head := ty.getAppFn
      if head.isConstOf ``Parser.LALR.Frontend.StructuralActions.Words then
        let proof ← mkAppM
          ``Parser.LALR.Frontend.StructuralActions.Words.step #[decl.toExpr]
        let (_, next) ← goal.note decl.userName proof
        let next ← next.clear decl.fvarId
        return ← unpack next
      if head.isConstOf ``Exists || head.isConstOf ``And || head.isConstOf ``Or ||
          head.isConstOf ``Prod || (← lookupEquality ty) then
        let branches ← goal.cases decl.fvarId
        let mut result := []
        for branch in branches do
          result := result ++ (← unpack branch.mvarId)
        return result
    return [goal]

elab "unpack_direct_words" : tactic => liftMetaTactic unpack

end Rumoca.GALEC.ProfileProofTactic

