import GALECParser.StructuralActions

namespace Rumoca.GALEC.Structural
open _root_.Parser LALR.Frontend

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Each well-formedness check sees only one rule body. The grammar equality
below erases semantic maps once; coverage and licensing never simplify inside
the AST-building functions or repeatedly expand every action definition. -/

local macro "well_formed " name:ident : tactic =>
  `(tactic| (simp only [$name:ident, lit, ident, StructuralActions.Action.WellFormed]; decide))

private theorem block_wellFormed : block.WellFormed := by well_formed block
private theorem declaration_wellFormed : declaration.WellFormed := by well_formed declaration
private theorem direction_wellFormed : direction.WellFormed := by well_formed direction
private theorem primitiveType_wellFormed : primitiveType.WellFormed := by well_formed primitiveType
private theorem method_wellFormed : method.WellFormed := by well_formed method
private theorem statement_wellFormed : statement.WellFormed := by
  change (True ∧ True) ∧ (Symbol.literal ";" ≠ .literal "")
  decide
private theorem singleAssignment_wellFormed : singleAssignment.WellFormed := by
  well_formed singleAssignment
private theorem forLoop_wellFormed : forLoop.WellFormed := by well_formed forLoop
private theorem reference_wellFormed : reference.WellFormed := ⟨trivial, trivial⟩
private theorem localReference_wellFormed : localReference.WellFormed := True.intro
private theorem stateReference_wellFormed : stateReference.WellFormed := by
  well_formed stateReference
private theorem componentReference_wellFormed : componentReference.WellFormed := by
  well_formed componentReference
private theorem expressionList_wellFormed : expressionList.WellFormed := by
  well_formed expressionList
private theorem expression_wellFormed : expression.WellFormed := by well_formed expression
private theorem additiveOperator_wellFormed : additiveOperator.WellFormed := by
  well_formed additiveOperator
private theorem term_wellFormed : term.WellFormed := by well_formed term
private theorem multiplicativeOperator_wellFormed : multiplicativeOperator.WellFormed := by
  well_formed multiplicativeOperator
private theorem primary_wellFormed : primary.WellFormed := by
  change True ∧ ((Symbol.literal "(" ≠ .literal "" ∧ True ∧ Symbol.literal ")" ≠ .literal "") ∧
    True ∧ True)
  decide
private theorem functionCall_wellFormed : functionCall.WellFormed := by well_formed functionCall
private theorem dimensionQuery_wellFormed : dimensionQuery.WellFormed := by
  well_formed dimensionQuery

private theorem grammar_actions : Generated.sourceGrammar =
    [("block", block.expr),
     ("declaration", declaration.expr),
     ("direction", direction.expr),
     ("primitive_type", primitiveType.expr),
     ("method", method.expr),
     ("statement", statement.expr),
     ("single_assignment", singleAssignment.expr),
     ("for_loop", forLoop.expr),
     ("reference", reference.expr),
     ("local_reference", localReference.expr),
     ("state_reference", stateReference.expr),
     ("component_reference", componentReference.expr),
     ("expression_list", expressionList.expr),
     ("expression", expression.expr),
     ("additive_operator", additiveOperator.expr),
     ("term", term.expr),
     ("multiplicative_operator", multiplicativeOperator.expr),
     ("primary", primary.expr),
     ("function_call", functionCall.expr),
     ("dimension_query", dimensionQuery.expr)] := rfl

/-- Exhaustive over the authored grammar, not a selection of example trees. -/
theorem covered : StructuralActions.Covers Generated.sourceGrammar rules := by
  intro name e member
  rw [grammar_actions] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact ⟨block, rfl, rfl, block_wellFormed⟩
  · exact ⟨declaration, rfl, rfl, declaration_wellFormed⟩
  · exact ⟨direction, rfl, rfl, direction_wellFormed⟩
  · exact ⟨primitiveType, rfl, rfl, primitiveType_wellFormed⟩
  · exact ⟨method, rfl, rfl, method_wellFormed⟩
  · exact ⟨statement, rfl, rfl, statement_wellFormed⟩
  · exact ⟨singleAssignment, rfl, rfl, singleAssignment_wellFormed⟩
  · exact ⟨forLoop, rfl, rfl, forLoop_wellFormed⟩
  · exact ⟨reference, rfl, rfl, reference_wellFormed⟩
  · exact ⟨localReference, rfl, rfl, localReference_wellFormed⟩
  · exact ⟨stateReference, rfl, rfl, stateReference_wellFormed⟩
  · exact ⟨componentReference, rfl, rfl, componentReference_wellFormed⟩
  · exact ⟨expressionList, rfl, rfl, expressionList_wellFormed⟩
  · exact ⟨expression, rfl, rfl, expression_wellFormed⟩
  · exact ⟨additiveOperator, rfl, rfl, additiveOperator_wellFormed⟩
  · exact ⟨term, rfl, rfl, term_wellFormed⟩
  · exact ⟨multiplicativeOperator, rfl, rfl, multiplicativeOperator_wellFormed⟩
  · exact ⟨primary, rfl, rfl, primary_wellFormed⟩
  · exact ⟨functionCall, rfl, rfl, functionCall_wellFormed⟩
  · exact ⟨dimensionQuery, rfl, rfl, dimensionQuery_wellFormed⟩

local macro "listed" : tactic =>
  `(tactic| (rw [grammar_actions]; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)))

/-- No rule-table entry can execute an unauthored body. -/
theorem licensed : StructuralActions.Licensed Generated.sourceGrammar rules := by
  intro name a found
  unfold rules at found
  split at found <;> try contradiction
  all_goals cases Option.some.inj found
  · exact ⟨by listed, block_wellFormed⟩
  · exact ⟨by listed, declaration_wellFormed⟩
  · exact ⟨by listed, direction_wellFormed⟩
  · exact ⟨by listed, primitiveType_wellFormed⟩
  · exact ⟨by listed, method_wellFormed⟩
  · exact ⟨by listed, statement_wellFormed⟩
  · exact ⟨by listed, singleAssignment_wellFormed⟩
  · exact ⟨by listed, forLoop_wellFormed⟩
  · exact ⟨by listed, reference_wellFormed⟩
  · exact ⟨by listed, localReference_wellFormed⟩
  · exact ⟨by listed, stateReference_wellFormed⟩
  · exact ⟨by listed, componentReference_wellFormed⟩
  · exact ⟨by listed, expressionList_wellFormed⟩
  · exact ⟨by listed, expression_wellFormed⟩
  · exact ⟨by listed, additiveOperator_wellFormed⟩
  · exact ⟨by listed, term_wellFormed⟩
  · exact ⟨by listed, multiplicativeOperator_wellFormed⟩
  · exact ⟨by listed, primary_wellFormed⟩
  · exact ⟨by listed, functionCall_wellFormed⟩
  · exact ⟨by listed, dimensionQuery_wellFormed⟩

theorem block_total {v : Structure.Value Token}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "block") :
    ∃ ast, StructuralActions.Denotes rules Token.symbol (.ref "block") v ast :=
  StructuralActions.total covered (.ref "block") v trivial valid shape

theorem block_domain (v : Structure.Value Token) :
    (∃ ast, StructuralActions.run rules Token.symbol (.ref "block") v = some ast) ↔
      Structure.Valid Generated.sourceGrammar Token.symbol v ∧ v.expr = .ref "block" :=
  StructuralActions.domain covered licensed (.ref "block") trivial v

theorem block_correct (v : Structure.Value Token) (ast : AST.Block) :
    StructuralActions.run rules Token.symbol (.ref "block") v = some ast ↔
      StructuralActions.Denotes rules Token.symbol (.ref "block") v ast :=
  StructuralActions.run_iff (rules := rules) (classify := Token.symbol) (.ref "block") v ast

end Rumoca.GALEC.Structural
