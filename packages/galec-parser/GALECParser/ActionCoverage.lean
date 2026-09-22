import GALECParser.StructuralActions

namespace Rumoca.GALEC.Structural
open _root_.Parser LALR.Frontend

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Exhaustive over the authored grammar, not a selection of example trees. -/
theorem covered : StructuralActions.Covers Generated.sourceGrammar rules := by
  intro name e member
  simp only [Generated.sourceGrammar, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h | h
  all_goals
    obtain ⟨rfl, rfl⟩ := h
    simp [rules, program, scalarBlock, tensorBlock, startup, recalibrate, doStep,
      tensorDoStep, product, reference, lit, ident,
      StructuralActions.Action.expr, StructuralActions.Action.WellFormed]

/-- No rule-table entry can execute an unauthored body. -/
theorem licensed : StructuralActions.Licensed Generated.sourceGrammar rules := by
  intro name a found
  unfold rules at found
  split at found <;> try contradiction
  all_goals
    cases Option.some.inj found
    simp [program, scalarBlock, tensorBlock, startup, recalibrate,
      doStep, tensorDoStep, product, reference, lit, ident, Generated.sourceGrammar,
      StructuralActions.Action.expr, StructuralActions.Action.WellFormed]

theorem program_total {v : Structure.Value Token}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "program") :
    ∃ ast, StructuralActions.Denotes rules Token.symbol (.ref "program") v ast :=
  StructuralActions.total covered (.ref "program") v trivial valid shape

theorem program_domain (v : Structure.Value Token) :
    (∃ ast, StructuralActions.run rules Token.symbol (.ref "program") v = some ast) ↔
      Structure.Valid Generated.sourceGrammar Token.symbol v ∧ v.expr = .ref "program" :=
  StructuralActions.domain covered licensed (.ref "program") trivial v

theorem program_correct (v : Structure.Value Token) (ast : AST.Block) :
    StructuralActions.run rules Token.symbol (.ref "program") v = some ast ↔
      StructuralActions.Denotes rules Token.symbol (.ref "program") v ast :=
  StructuralActions.run_iff (rules := rules) (classify := Token.symbol) (.ref "program") v ast

end Rumoca.GALEC.Structural

