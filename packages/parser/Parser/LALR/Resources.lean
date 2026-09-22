import Parser.LALR.Generator
import Parser.LALR.Progress

/-! Candidate resource annotations for the generic parser. This search is
separate from its correctness conditions. Emitted artifacts must still prove
both validators about their actual grammar, tables, edges and coefficients. -/
namespace Parser.LALR.Resources

structure Candidate where
  budget : Fuel.Budget
  credits : Progress.Credits
  deriving Repr

/-- Propose state credits for a fixed budget; success still requires both
independent grammar and edge validators. -/
private def creditsFor (g : Grammar) (tables : Tables) (edges : List Edge)
    (budget : Fuel.Budget) : Option Progress.Credits := Id.run do
  let mut credits : Progress.Credits := ⟨Array.replicate tables.actions.size 0, 0⟩
  for _ in [:tables.actions.size + 1] do
    for edge in edges do
      let required := ((credits.get edge.source : Int) - budget.weight edge.symbol).toNat
      let old := credits.get edge.target
      credits := { credits with states := credits.states.setIfInBounds edge.target (max old required) }
    credits := { credits with ceiling := credits.states.foldl max 0 }
    if Fuel.validate g budget && Progress.validate tables edges budget credits then
      return some credits
  return none

/-- Preserve the legacy nonnegative resource search first. On failure, retry
signed grammar AND state credits at every larger token allowance: freezing
grammar credits cannot repair a bad all-nonterminal state-edge cycle.
Bounded failure is a preprocessing error, never syntax rejection or a proof
that no certificate exists. No search-completeness claim is made. -/
def generate (g : Grammar) (tables : Tables) (edges : List Edge)
    (attempts : Nat := 20) : Except String Candidate := do
  if !g.wellFormed then throw "ill-formed grammar for fuel budget"
  if let .ok initial := generateBudget g attempts then
    let mut budget := initial
    for _ in [:attempts] do
      if let some credits := creditsFor g tables edges budget then
        return ⟨budget, credits⟩
      budget := { budget with perToken := budget.perToken * 2 }
  let mut perToken := 1
  for _ in [:attempts] do
    if let some budget := generateSignedBudgetAt g perToken then
      if let some credits := creditsFor g tables edges budget then
        return ⟨budget, credits⟩
    perToken := perToken * 2
  throw "total parsing resource search exhausted its bound"

end Parser.LALR.Resources
