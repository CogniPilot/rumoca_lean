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

/-- Relax state-credit inequalities, increasing the token allowance when a
cycle cannot be paid for. Bounded search failure is an explicit preprocessing
error; it is never interpreted as a syntax rejection. -/
def generate (g : Grammar) (tables : Tables) (edges : List Edge)
    (attempts : Nat := 20) : Except String Candidate := do
  let mut budget ← generateBudget g attempts
  for _ in [:attempts] do
    let mut credits : Progress.Credits := ⟨Array.replicate tables.actions.size 0, 0⟩
    for _ in [:tables.actions.size + 1] do
      for edge in edges do
        let required := ((credits.get edge.source : Int) - budget.weight edge.symbol).toNat
        let old := credits.get edge.target
        credits := { credits with states := credits.states.setIfInBounds edge.target (max old required) }
      credits := { credits with ceiling := credits.states.foldl max 0 }
      if Fuel.validate g budget && Progress.validate tables edges budget credits then
        return ⟨budget, credits⟩
    budget := { budget with perToken := budget.perToken * 2 }
  throw "total parsing resource search exhausted its bound"

end Parser.LALR.Resources
