import Parser.LALR.EBNFStructure
import Parser.LALR.Grammar
import Lean

/-! Quotation of generic token, grammar and tree values as kernel terms, and
equation declarations proved by kernel reflexivity. Certificate generators use
these to state natively proposed data; quotation gives no semantic authority,
and every stated equation is checked by the kernel. -/
namespace Parser.Quotation
open Lean Elab Command

deriving instance ToExpr for Parser.Token
deriving instance ToExpr for Parser.Symbol
deriving instance ToExpr for Parser.EBNF.Expr
deriving instance ToExpr for Parser.LALR.Tree
deriving instance ToExpr for Parser.LALR.Frontend.Structure.Value

/-- Add `name : α := value` as a closed definition of the quoted value. -/
def quoteDefinition {α : Type} [ToExpr α] (name : Name) (value : α) : CommandElabM Unit :=
  liftTermElabM do
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := toTypeExpr α
      value := toExpr value
      hints := .abbrev
      safety := .safe })

/-- Add the theorem `name : type` proved by `Eq.refl right`, so the kernel
checks the equation. Only the three standard foundational axioms, carried by
referenced definitions, are admitted in the result. -/
def checkEquation (name : Name) (type : TSyntax `term) (right : TSyntax `term) :
    CommandElabM Unit := do
  liftTermElabM do
    let type ← Term.elabType type
    let right ← Term.elabTerm right none
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    let proof ← Meta.mkEqRefl (← instantiateMVars right)
    addDecl (.thmDecl { name, levelParams := [], type, value := proof })
  for dependency in ← collectAxioms name do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "invalid equation certificate {name}: {dependency}"

end Parser.Quotation
