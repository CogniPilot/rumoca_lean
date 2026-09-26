import ModelicaParser.StructuralActions
import ModelicaParser.Generated

namespace Rumoca.Modelica.Structural
open _root_.Parser LALR.Frontend

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Each well-formedness check sees only one rule body. The grammar equality
below erases semantic maps once; coverage and licensing never simplify inside
the AST-building functions or repeatedly expand every action definition. -/

local macro "well_formed " name:ident : tactic =>
  `(tactic| (simp only [$name:ident, lit, ident, string, partsTail, callee,
      StructuralActions.Action.WellFormed]; decide))

private theorem storedDefinition_wellFormed : storedDefinition.WellFormed := by
  well_formed storedDefinition
private theorem classDefinition_wellFormed : classDefinition.WellFormed := by
  well_formed classDefinition
private theorem classPrefixes_wellFormed : classPrefixes.WellFormed := by
  well_formed classPrefixes
private theorem classSpecifier_wellFormed : classSpecifier.WellFormed := trivial
private theorem longClassSpecifier_wellFormed : longClassSpecifier.WellFormed := by
  well_formed longClassSpecifier
private theorem composition_wellFormed : composition.WellFormed := by well_formed composition
private theorem elementList_wellFormed : elementList.WellFormed := by well_formed elementList
private theorem element_wellFormed : element.WellFormed := trivial
private theorem componentClause_wellFormed : componentClause.WellFormed := by
  well_formed componentClause
private theorem typePrefix_wellFormed : typePrefix.WellFormed := by well_formed typePrefix
private theorem typeSpecifier_wellFormed : typeSpecifier.WellFormed := trivial
private theorem componentList_wellFormed : componentList.WellFormed := by
  well_formed componentList
private theorem componentDeclaration_wellFormed : componentDeclaration.WellFormed := by
  well_formed componentDeclaration
private theorem conditionAttribute_wellFormed : conditionAttribute.WellFormed := by
  well_formed conditionAttribute
private theorem declaration_wellFormed : declaration.WellFormed := by well_formed declaration
private theorem modification_wellFormed : modification.WellFormed := by well_formed modification
private theorem modificationExpression_wellFormed : modificationExpression.WellFormed := trivial
private theorem classModification_wellFormed : classModification.WellFormed := by
  well_formed classModification
private theorem argumentList_wellFormed : argumentList.WellFormed := by well_formed argumentList
private theorem argument_wellFormed : argument.WellFormed := trivial
private theorem elementModificationOrReplaceable_wellFormed :
    elementModificationOrReplaceable.WellFormed := by
  well_formed elementModificationOrReplaceable
private theorem elementModification_wellFormed : elementModification.WellFormed := by
  well_formed elementModification
private theorem equationSection_wellFormed : equationSection.WellFormed := by
  well_formed equationSection
private theorem someEquation_wellFormed : someEquation.WellFormed := by well_formed someEquation
private theorem equationOrProcedure_wellFormed : equationOrProcedure.WellFormed := trivial
private theorem simpleEquation_wellFormed : simpleEquation.WellFormed := by
  well_formed simpleEquation
private theorem expression_wellFormed : expression.WellFormed := trivial
private theorem simpleExpression_wellFormed : simpleExpression.WellFormed := trivial
private theorem logicalExpression_wellFormed : logicalExpression.WellFormed := trivial
private theorem logicalTerm_wellFormed : logicalTerm.WellFormed := trivial
private theorem logicalFactor_wellFormed : logicalFactor.WellFormed := trivial
private theorem relation_wellFormed : relation.WellFormed := trivial
private theorem arithmeticExpression_wellFormed : arithmeticExpression.WellFormed := by
  well_formed arithmeticExpression
private theorem addOperator_wellFormed : addOperator.WellFormed := by well_formed addOperator
private theorem term_wellFormed : term.WellFormed := by well_formed term
private theorem mulOperator_wellFormed : mulOperator.WellFormed := by well_formed mulOperator
private theorem factor_wellFormed : factor.WellFormed := trivial
private theorem lit_wellFormed (text : String) (nonempty : text ≠ "") : (lit text).WellFormed :=
  fun same => nonempty (Symbol.literal.inj same)
private theorem ident_wellFormed : ident.WellFormed := fun same => nomatch same
private theorem string_wellFormed : string.WellFormed := fun same => nomatch same

local macro "literal" : term => `(lit_wellFormed _ (by decide))

private theorem primary_wellFormed : primary.WellFormed :=
  ⟨trivial, ⟨⟨trivial, literal⟩, trivial⟩, string_wellFormed, literal, literal, literal, trivial,
    literal⟩
private theorem name_wellFormed : name.WellFormed := by well_formed name
private theorem componentReference_wellFormed : componentReference.WellFormed :=
  ⟨⟨ident_wellFormed, trivial, literal, ident_wellFormed, trivial⟩,
    ⟨literal, ident_wellFormed, trivial, literal, ident_wellFormed, trivial⟩⟩
private theorem functionCallArgs_wellFormed : functionCallArgs.WellFormed := by
  well_formed functionCallArgs
private theorem functionArguments_wellFormed : functionArguments.WellFormed := by
  well_formed functionArguments
private theorem functionArgumentsNonFirst_wellFormed : functionArgumentsNonFirst.WellFormed := by
  well_formed functionArgumentsNonFirst
private theorem functionArgument_wellFormed : functionArgument.WellFormed := trivial
private theorem outputExpressionList_wellFormed : outputExpressionList.WellFormed := by
  well_formed outputExpressionList
private theorem arraySubscripts_wellFormed : arraySubscripts.WellFormed := by
  well_formed arraySubscripts
private theorem subscript_wellFormed : subscript.WellFormed := trivial
private theorem description_wellFormed : description.WellFormed := by well_formed description
private theorem descriptionString_wellFormed : descriptionString.WellFormed := by
  well_formed descriptionString
private theorem annotationClause_wellFormed : annotationClause.WellFormed := by
  well_formed annotationClause

private theorem grammar_actions : Generated.sourceGrammar =
    [("stored_definition", storedDefinition.expr),
     ("class_definition", classDefinition.expr),
     ("class_prefixes", classPrefixes.expr),
     ("class_specifier", classSpecifier.expr),
     ("long_class_specifier", longClassSpecifier.expr),
     ("composition", composition.expr),
     ("element_list", elementList.expr),
     ("element", element.expr),
     ("component_clause", componentClause.expr),
     ("type_prefix", typePrefix.expr),
     ("type_specifier", typeSpecifier.expr),
     ("component_list", componentList.expr),
     ("component_declaration", componentDeclaration.expr),
     ("condition_attribute", conditionAttribute.expr),
     ("declaration", declaration.expr),
     ("modification", modification.expr),
     ("modification_expression", modificationExpression.expr),
     ("class_modification", classModification.expr),
     ("argument_list", argumentList.expr),
     ("argument", argument.expr),
     ("element_modification_or_replaceable", elementModificationOrReplaceable.expr),
     ("element_modification", elementModification.expr),
     ("equation_section", equationSection.expr),
     ("some_equation", someEquation.expr),
     ("equation_or_procedure", equationOrProcedure.expr),
     ("simple_equation", simpleEquation.expr),
     ("expression", expression.expr),
     ("simple_expression", simpleExpression.expr),
     ("logical_expression", logicalExpression.expr),
     ("logical_term", logicalTerm.expr),
     ("logical_factor", logicalFactor.expr),
     ("relation", relation.expr),
     ("arithmetic_expression", arithmeticExpression.expr),
     ("add_operator", addOperator.expr),
     ("term", term.expr),
     ("mul_operator", mulOperator.expr),
     ("factor", factor.expr),
     ("primary", primary.expr),
     ("name", name.expr),
     ("component_reference", componentReference.expr),
     ("function_call_args", functionCallArgs.expr),
     ("function_arguments", functionArguments.expr),
     ("function_arguments_non_first", functionArgumentsNonFirst.expr),
     ("function_argument", functionArgument.expr),
     ("output_expression_list", outputExpressionList.expr),
     ("array_subscripts", arraySubscripts.expr),
     ("subscript", subscript.expr),
     ("description", description.expr),
     ("description_string", descriptionString.expr),
     ("annotation_clause", annotationClause.expr)] := rfl

/-- Exhaustive over the authored grammar, not a selection of example trees. -/
theorem covered : StructuralActions.Covers Generated.sourceGrammar rules := by
  intro name e member
  rw [grammar_actions] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact ⟨_, rfl, rfl, storedDefinition_wellFormed⟩
  · exact ⟨_, rfl, rfl, classDefinition_wellFormed⟩
  · exact ⟨_, rfl, rfl, classPrefixes_wellFormed⟩
  · exact ⟨_, rfl, rfl, classSpecifier_wellFormed⟩
  · exact ⟨_, rfl, rfl, longClassSpecifier_wellFormed⟩
  · exact ⟨_, rfl, rfl, composition_wellFormed⟩
  · exact ⟨_, rfl, rfl, elementList_wellFormed⟩
  · exact ⟨_, rfl, rfl, element_wellFormed⟩
  · exact ⟨_, rfl, rfl, componentClause_wellFormed⟩
  · exact ⟨_, rfl, rfl, typePrefix_wellFormed⟩
  · exact ⟨_, rfl, rfl, typeSpecifier_wellFormed⟩
  · exact ⟨_, rfl, rfl, componentList_wellFormed⟩
  · exact ⟨_, rfl, rfl, componentDeclaration_wellFormed⟩
  · exact ⟨_, rfl, rfl, conditionAttribute_wellFormed⟩
  · exact ⟨_, rfl, rfl, declaration_wellFormed⟩
  · exact ⟨_, rfl, rfl, modification_wellFormed⟩
  · exact ⟨_, rfl, rfl, modificationExpression_wellFormed⟩
  · exact ⟨_, rfl, rfl, classModification_wellFormed⟩
  · exact ⟨_, rfl, rfl, argumentList_wellFormed⟩
  · exact ⟨_, rfl, rfl, argument_wellFormed⟩
  · exact ⟨_, rfl, rfl, elementModificationOrReplaceable_wellFormed⟩
  · exact ⟨_, rfl, rfl, elementModification_wellFormed⟩
  · exact ⟨_, rfl, rfl, equationSection_wellFormed⟩
  · exact ⟨_, rfl, rfl, someEquation_wellFormed⟩
  · exact ⟨_, rfl, rfl, equationOrProcedure_wellFormed⟩
  · exact ⟨_, rfl, rfl, simpleEquation_wellFormed⟩
  · exact ⟨_, rfl, rfl, expression_wellFormed⟩
  · exact ⟨_, rfl, rfl, simpleExpression_wellFormed⟩
  · exact ⟨_, rfl, rfl, logicalExpression_wellFormed⟩
  · exact ⟨_, rfl, rfl, logicalTerm_wellFormed⟩
  · exact ⟨_, rfl, rfl, logicalFactor_wellFormed⟩
  · exact ⟨_, rfl, rfl, relation_wellFormed⟩
  · exact ⟨_, rfl, rfl, arithmeticExpression_wellFormed⟩
  · exact ⟨_, rfl, rfl, addOperator_wellFormed⟩
  · exact ⟨_, rfl, rfl, term_wellFormed⟩
  · exact ⟨_, rfl, rfl, mulOperator_wellFormed⟩
  · exact ⟨_, rfl, rfl, factor_wellFormed⟩
  · exact ⟨_, rfl, rfl, primary_wellFormed⟩
  · exact ⟨_, rfl, rfl, name_wellFormed⟩
  · exact ⟨_, rfl, rfl, componentReference_wellFormed⟩
  · exact ⟨_, rfl, rfl, functionCallArgs_wellFormed⟩
  · exact ⟨_, rfl, rfl, functionArguments_wellFormed⟩
  · exact ⟨_, rfl, rfl, functionArgumentsNonFirst_wellFormed⟩
  · exact ⟨_, rfl, rfl, functionArgument_wellFormed⟩
  · exact ⟨_, rfl, rfl, outputExpressionList_wellFormed⟩
  · exact ⟨_, rfl, rfl, arraySubscripts_wellFormed⟩
  · exact ⟨_, rfl, rfl, subscript_wellFormed⟩
  · exact ⟨_, rfl, rfl, description_wellFormed⟩
  · exact ⟨_, rfl, rfl, descriptionString_wellFormed⟩
  · exact ⟨_, rfl, rfl, annotationClause_wellFormed⟩

local macro "listed" : tactic =>
  `(tactic| (rw [grammar_actions]; repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)))

/-- No rule-table entry can execute an unauthored body. -/
theorem licensed : StructuralActions.Licensed Generated.sourceGrammar rules := by
  intro name a found
  unfold rules at found
  split at found <;> try contradiction
  all_goals cases Option.some.inj found
  · exact ⟨by listed, storedDefinition_wellFormed⟩
  · exact ⟨by listed, classDefinition_wellFormed⟩
  · exact ⟨by listed, classPrefixes_wellFormed⟩
  · exact ⟨by listed, classSpecifier_wellFormed⟩
  · exact ⟨by listed, longClassSpecifier_wellFormed⟩
  · exact ⟨by listed, composition_wellFormed⟩
  · exact ⟨by listed, elementList_wellFormed⟩
  · exact ⟨by listed, element_wellFormed⟩
  · exact ⟨by listed, componentClause_wellFormed⟩
  · exact ⟨by listed, typePrefix_wellFormed⟩
  · exact ⟨by listed, typeSpecifier_wellFormed⟩
  · exact ⟨by listed, componentList_wellFormed⟩
  · exact ⟨by listed, componentDeclaration_wellFormed⟩
  · exact ⟨by listed, conditionAttribute_wellFormed⟩
  · exact ⟨by listed, declaration_wellFormed⟩
  · exact ⟨by listed, modification_wellFormed⟩
  · exact ⟨by listed, modificationExpression_wellFormed⟩
  · exact ⟨by listed, classModification_wellFormed⟩
  · exact ⟨by listed, argumentList_wellFormed⟩
  · exact ⟨by listed, argument_wellFormed⟩
  · exact ⟨by listed, elementModificationOrReplaceable_wellFormed⟩
  · exact ⟨by listed, elementModification_wellFormed⟩
  · exact ⟨by listed, equationSection_wellFormed⟩
  · exact ⟨by listed, someEquation_wellFormed⟩
  · exact ⟨by listed, equationOrProcedure_wellFormed⟩
  · exact ⟨by listed, simpleEquation_wellFormed⟩
  · exact ⟨by listed, expression_wellFormed⟩
  · exact ⟨by listed, simpleExpression_wellFormed⟩
  · exact ⟨by listed, logicalExpression_wellFormed⟩
  · exact ⟨by listed, logicalTerm_wellFormed⟩
  · exact ⟨by listed, logicalFactor_wellFormed⟩
  · exact ⟨by listed, relation_wellFormed⟩
  · exact ⟨by listed, arithmeticExpression_wellFormed⟩
  · exact ⟨by listed, addOperator_wellFormed⟩
  · exact ⟨by listed, term_wellFormed⟩
  · exact ⟨by listed, mulOperator_wellFormed⟩
  · exact ⟨by listed, factor_wellFormed⟩
  · exact ⟨by listed, primary_wellFormed⟩
  · exact ⟨by listed, name_wellFormed⟩
  · exact ⟨by listed, componentReference_wellFormed⟩
  · exact ⟨by listed, functionCallArgs_wellFormed⟩
  · exact ⟨by listed, functionArguments_wellFormed⟩
  · exact ⟨by listed, functionArgumentsNonFirst_wellFormed⟩
  · exact ⟨by listed, functionArgument_wellFormed⟩
  · exact ⟨by listed, outputExpressionList_wellFormed⟩
  · exact ⟨by listed, arraySubscripts_wellFormed⟩
  · exact ⟨by listed, subscript_wellFormed⟩
  · exact ⟨by listed, description_wellFormed⟩
  · exact ⟨by listed, descriptionString_wellFormed⟩
  · exact ⟨by listed, annotationClause_wellFormed⟩

theorem storedDefinition_total {v : Structure.Value Token}
    (valid : Structure.Valid Generated.sourceGrammar Token.symbol v)
    (shape : v.expr = .ref "stored_definition") :
    ∃ ast, StructuralActions.Denotes rules Token.symbol (.ref "stored_definition") v ast :=
  StructuralActions.total covered (.ref "stored_definition") v trivial valid shape

theorem storedDefinition_domain (v : Structure.Value Token) :
    (∃ ast, StructuralActions.run rules Token.symbol (.ref "stored_definition") v = some ast) ↔
      Structure.Valid Generated.sourceGrammar Token.symbol v ∧ v.expr = .ref "stored_definition" :=
  StructuralActions.domain covered licensed (.ref "stored_definition") trivial v

theorem storedDefinition_correct (v : Structure.Value Token) (ast : AST.StoredDefinition) :
    StructuralActions.run rules Token.symbol (.ref "stored_definition") v = some ast ↔
      StructuralActions.Denotes rules Token.symbol (.ref "stored_definition") v ast :=
  StructuralActions.run_iff (rules := rules) (classify := Token.symbol) (.ref "stored_definition") v ast

end Rumoca.Modelica.Structural
