import Parser.LALR.ActionYield
import ModelicaParser.StructuralActions
import ModelicaParser.Print

/-! Every Modelica rule action yields its printer: the AST built from a parsed
tree prints back to exactly the parsed tokens. Each rule body is checked once,
against the printer of the rule's result, as coverage is. -/
namespace Rumoca.Modelica.Structural
open _root_.Parser LALR.Frontend StructuralActions

/-- The printer of each rule's result. -/
def printResult : (name : String) → Result name → List Token
  | "stored_definition" => Print.storedDefinition
  | "class_definition" => Print.classDefinition
  | "class_prefixes" | "add_operator" | "mul_operator" => fun token => [token]
  | "class_specifier" | "long_class_specifier" => Print.classSpecifier
  | "composition" => Print.composition
  | "element_list" => fun elements => elements.flatMap fun e => Print.element e ++ [.literal ";"]
  | "element" => Print.element
  | "component_clause" => Print.componentClause
  | "type_prefix" => Print.typePrefix
  | "type_specifier" | "name" => Print.name
  | "component_list" => Print.declarations
  | "component_declaration" | "declaration" => Print.declaration
  | "modification" => Print.modification
  | "class_modification" => fun arguments =>
      .literal "(" :: Print.argumentList arguments ++ [.literal ")"]
  | "argument_list" => Print.argumentList
  | "argument" | "element_modification_or_replaceable" => Print.argument
  | "element_modification" => Print.elementModification
  | "equation_section" => Print.equationSection
  | "some_equation" | "equation_or_procedure" | "simple_equation" => Print.equation
  | "modification_expression" | "expression" | "simple_expression" | "logical_expression"
    | "logical_term" | "logical_factor" | "relation" | "arithmetic_expression" | "term"
    | "factor" | "primary" | "function_argument" | "subscript" => Print.expr
  | "component_reference" => Print.reference
  | "function_call_args" => fun arguments => .literal "(" :: Print.exprs arguments ++ [.literal ")"]
  | "function_arguments" => Print.exprs
  | "function_arguments_non_first" => fun (first, rest) => Print.exprs (first :: rest)
  | "array_subscripts" => fun indices => .literal "[" :: Print.exprs indices ++ [.literal "]"]
  | "output_expression_list" => Print.outputs
  | _ => fun _ => []

local notation "Yields" => Action.Yields Token.symbol printResult

/-! ### Terminal and reference printers -/

private theorem literal_unique (s : String) (nonempty : s ≠ "") :
    ∀ x : Token, x.symbol = .literal s → x = .literal s := by
  intro x same
  cases x with
  | ident _ => cases same
  | number _ => cases same
  | string _ => cases same
  | comment _ => exact absurd (Symbol.literal.inj same).symm nonempty
  | literal t => cases same; rfl

private theorem fixed (s : String) (nonempty : s ≠ "" := by decide) :
    Yields (lit s) (fun _ => [.literal s]) :=
  Action.Yields.fixed (literal_unique s nonempty)

private theorem payload (s : Parser.Symbol) :
    Yields (.terminal s : Action Token) (fun x => [x]) := Action.Yields.terminal s

private theorem ref' (n : String) {p : Result n → List Token}
    (same : ∀ r, printResult n r = p r) : Yields (.ref n : Action (Result n)) p :=
  fun r => (same r).symm

/-- A reference printed by the printer its rule is checked against. -/
local macro "ref " n:str " as " p:term : term => `(ref' $n (p := $p) fun _ => rfl)

private def subscriptsPrinter (indices : List AST.Expr) : List Token :=
  .literal "[" :: Print.exprs indices ++ [.literal "]"]

private def argumentsPrinter (arguments : List AST.Expr) : List Token :=
  .literal "(" :: Print.exprs arguments ++ [.literal ")"]

private def elementsPrinter (elements : List AST.Element) : List Token :=
  elements.flatMap fun e => Print.element e ++ [.literal ";"]

/-! ### List and option normal forms -/

private theorem flatMap_fst {α β γ : Type} (xs : List (α × β)) (g : α → List γ) :
    (xs.map Prod.fst).flatMap g = xs.flatMap fun xy => g xy.1 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem flatMap_snd {α β γ : Type} (xs : List (α × β)) (g : β → List γ) :
    (xs.map Prod.snd).flatMap g = xs.flatMap fun xy => g xy.2 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem exprsTail_map (rest : List (Token × AST.Expr)) :
    Print.exprsTail (rest.map Prod.snd) =
      rest.flatMap fun xy => [.literal ","] ++ Print.expr xy.2 := by
  induction rest with
  | nil => rfl
  | cons head rest ih => simp [Print.exprsTail, ih]

private theorem output_optional (value : Option AST.Expr) :
    Print.output value = value.elim [] Print.expr := by
  cases value <;> rfl

private theorem outputsTail_map (rest : List (Token × Option AST.Expr)) :
    Print.outputsTail (rest.map Prod.snd) =
      rest.flatMap fun xy => [.literal ","] ++ xy.2.elim [] Print.expr := by
  induction rest with
  | nil => rfl
  | cons head rest ih => simp [Print.outputsTail, ih, output_optional]

private theorem argumentsTail_map (rest : List (Token × AST.Argument)) :
    Print.argumentsTail (rest.map Prod.snd) =
      rest.flatMap fun xy => [.literal ","] ++ Print.argument xy.2 := by
  induction rest with
  | nil => rfl
  | cons head rest ih => simp [Print.argumentsTail, ih]

private theorem subscripts_optional (indices : Option (List AST.Expr)) :
    Print.subscripts indices = indices.elim [] subscriptsPrinter := by
  cases indices <;> rfl

private theorem componentsTail_map (rest : List (Token × Token × Option (List AST.Expr))) :
    Print.componentsTail (rest.map fun (_, name, subscripts) => ⟨name, subscripts⟩) =
      rest.flatMap fun xy => [.literal "."] ++ ([xy.2.1] ++ xy.2.2.elim [] subscriptsPrinter) := by
  induction rest with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨_, name, subscripts⟩ := head
    simp [Print.componentsTail, Print.component, ih, subscripts_optional]

private theorem binding_map (value : Option (Token × AST.Expr)) :
    Print.binding (value.map Prod.snd) = value.elim [] fun xy => [.literal "="] ++ Print.expr xy.2 := by
  cases value <;> rfl

private theorem modification_optional (value : Option AST.Modification) :
    Print.optionalModification value = value.elim [] Print.modification := by
  cases value <;> rfl

private theorem following_exprs (first : AST.Expr)
    (rest : Option (Token × (AST.Expr × List AST.Expr))) :
    Print.exprs (first :: following rest) =
      Print.expr first ++ rest.elim [] fun xy =>
        [.literal ","] ++ Print.exprs (xy.2.1 :: xy.2.2) := by
  cases rest with
  | none => simp [following, Print.exprs, Print.exprsTail]
  | some value =>
    obtain ⟨_, next, more⟩ := value
    simp [following, Print.exprs, Print.exprsTail]

/-! ### One lemma per rule body -/

private theorem storedDefinition_yields : Yields storedDefinition Print.storedDefinition :=
  .map <| .congr (.many (.seq (ref "class_definition" as Print.classDefinition) (fixed ";")))
    fun classes => flatMap_fst classes _

private theorem classDefinition_yields : Yields classDefinition Print.classDefinition :=
  .map <| .congr (.seq (ref "class_prefixes" as fun t => [t])
    (ref "class_specifier" as Print.classSpecifier)) fun _ => rfl

private theorem longClassSpecifier_yields : Yields longClassSpecifier Print.classSpecifier :=
  .map <| .congr (.seq (payload .ident) (.seq (ref "composition" as Print.composition)
    (.seq (fixed "end") (payload .ident)))) fun ⟨name, body, _, endName⟩ => by
      simp [Print.classSpecifier]

private theorem composition_yields : Yields composition Print.composition :=
  .map <| .congr (.seq (ref "element_list" as elementsPrinter)
    (.many (ref "equation_section" as Print.equationSection))) fun _ => rfl

private theorem elementList_yields : Yields elementList elementsPrinter :=
  .map <| .congr (.many (.seq (ref "element" as Print.element) (fixed ";")))
    fun elements => flatMap_fst elements _

private theorem element_yields : Yields element Print.element :=
  .map <| .congr (ref "component_clause" as Print.componentClause) fun _ => rfl

private theorem componentClause_yields : Yields componentClause Print.componentClause :=
  .map <| .congr (.seq (ref "type_prefix" as Print.typePrefix)
    (.seq (ref "type_specifier" as Print.name)
      (.seq (.optional (ref "array_subscripts" as subscriptsPrinter))
        (ref "component_list" as Print.declarations))))
    fun ⟨typePrefix, typeName, subscripts, declarations⟩ => by
      simp [Print.componentClause, subscripts_optional]; rfl

private theorem typePrefix_yields : Yields typePrefix Print.typePrefix :=
  .congr (.optional (.alt (payload _) (payload _))) fun _ => rfl

private theorem componentList_yields : Yields componentList Print.declarations :=
  .map <| .congr (.seq (ref "component_declaration" as Print.declaration)
    (.many (.seq (fixed ",") (ref "component_declaration" as Print.declaration))))
    fun ⟨first, rest⟩ => by simp [Print.declarations, flatMap_snd]; rfl

private theorem declaration_yields : Yields declaration Print.declaration :=
  .map <| .congr (.seq (payload .ident) (.seq (.optional (ref "array_subscripts" as subscriptsPrinter))
    (.optional (ref "modification" as Print.modification))))
    fun ⟨name, subscripts, modification⟩ => by
      simp [Print.declaration, subscripts_optional, modification_optional]; rfl

private theorem modification_yields : Yields modification Print.modification :=
  .alt (.map <| .congr (.seq (ref "class_modification" as fun arguments =>
      .literal "(" :: Print.argumentList arguments ++ [.literal ")"])
      (.optional (.seq (fixed "=") (ref "modification_expression" as Print.expr))))
      fun ⟨arguments, value⟩ => by simp [Print.modification, binding_map]; rfl)
    (.map <| .congr (.seq (fixed "=") (ref "modification_expression" as Print.expr)) fun _ => rfl)

private theorem classModification_yields : Yields classModification fun arguments =>
    .literal "(" :: Print.argumentList arguments ++ [.literal ")"] :=
  .map <| .congr (.seq (fixed "(") (.seq (.optional (ref "argument_list" as Print.argumentList))
    (fixed ")"))) fun ⟨_, arguments, _⟩ => by cases arguments <;> simp [Print.argumentList]

private theorem argumentList_yields : Yields argumentList Print.argumentList :=
  .map <| .congr (.seq (ref "argument" as Print.argument)
    (.many (.seq (fixed ",") (ref "argument" as Print.argument))))
    fun ⟨first, rest⟩ => by simp [Print.argumentList, argumentsTail_map]; rfl

private theorem elementModificationOrReplaceable_yields :
    Yields elementModificationOrReplaceable Print.argument :=
  .map <| .congr (.seq (.optional (fixed "each"))
    (ref "element_modification" as Print.elementModification))
    fun ⟨each, target⟩ => by cases each <;> rfl

private theorem elementModification_yields : Yields elementModification Print.elementModification :=
  .map <| .congr (.seq (ref "name" as Print.name) (.optional (ref "modification" as Print.modification)))
    fun ⟨target, modification⟩ => by cases modification <;> simp [Print.elementModification,
      Print.optionalModification]

private theorem equationSection_yields : Yields equationSection Print.equationSection :=
  .map <| .congr (.seq (fixed "equation")
    (.many (.seq (ref "some_equation" as Print.equation) (fixed ";"))))
    fun ⟨_, equations⟩ => by simp [Print.equationSection, flatMap_fst]; rfl

private theorem simpleEquation_yields : Yields simpleEquation Print.equation :=
  .map <| .congr (.seq (ref "simple_expression" as Print.expr)
    (.seq (fixed "=") (ref "expression" as Print.expr))) fun _ => rfl

private theorem arithmeticExpression_yields : Yields arithmeticExpression Print.expr :=
  .alt (.map <| .congr (.seq (ref "term" as Print.expr)
      (.many (.seq (ref "add_operator" as fun t => [t]) (ref "term" as Print.expr))))
      fun ⟨first, rest⟩ => Print.expr_leftAssociate first rest)
    (.map <| .congr (.seq (ref "add_operator" as fun t => [t]) (.seq (ref "term" as Print.expr)
      (.many (.seq (ref "add_operator" as fun t => [t]) (ref "term" as Print.expr)))))
      fun ⟨sign, first, rest⟩ => by rw [Print.expr_leftAssociate]; rfl)

private theorem operator_yields (a b : String) : Yields (.alt (lit a) (lit b)) fun t => [t] :=
  .alt (payload _) (payload _)

private theorem term_yields : Yields term Print.expr :=
  .map <| .congr (.seq (ref "factor" as Print.expr)
    (.many (.seq (ref "mul_operator" as fun t => [t]) (ref "factor" as Print.expr))))
    fun ⟨first, rest⟩ => Print.expr_leftAssociate first rest

private theorem callee_yields : Yields callee Print.callee :=
  .alt (.map (ref "component_reference" as fun r => Print.callee (.reference r))) (.map (fixed "der"))

private theorem primary_yields : Yields primary Print.expr :=
  .alt (.map (ref "component_reference" as fun r => Print.expr (.reference r)))
    (.alt (.map <| .congr (.seq callee_yields (ref "function_call_args" as argumentsPrinter))
        fun ⟨_, _⟩ => by simp [Print.expr, argumentsPrinter])
      (.alt (.map (payload _))
        (.alt (.map (payload _))
          (.map <| .congr (.seq (fixed "(") (.seq (ref "output_expression_list" as Print.outputs)
            (fixed ")"))) fun _ => rfl))))

private theorem name_yields : Yields name Print.name :=
  .map <| .congr (.seq (payload .ident) (.many (.seq (fixed ".") (payload .ident))))
    fun ⟨first, rest⟩ => by simp [Print.name, flatMap_snd]

private theorem partsTail_yields : Yields partsTail fun rest =>
    rest.flatMap fun xy => [.literal "."] ++ ([xy.2.1] ++ xy.2.2.elim [] subscriptsPrinter) :=
  .many (.seq (fixed ".") (.seq (payload .ident)
    (.optional (ref "array_subscripts" as subscriptsPrinter))))

private theorem componentReference_yields : Yields componentReference Print.reference :=
  .alt (.map <| .congr (.seq (payload .ident)
      (.seq (.optional (ref "array_subscripts" as subscriptsPrinter)) partsTail_yields))
      fun ⟨first, subscripts, rest⟩ => by
        simp [Print.reference, Print.components, Print.component, referenceSyntax,
          componentsTail_map, subscripts_optional]; rfl)
    (.map <| .congr (.seq (fixed ".") (.seq (payload .ident)
      (.seq (.optional (ref "array_subscripts" as subscriptsPrinter)) partsTail_yields)))
      fun ⟨_, first, subscripts, rest⟩ => by
        simp [Print.reference, Print.components, Print.component, referenceSyntax,
          componentsTail_map, subscripts_optional]; rfl)

private theorem functionCallArgs_yields : Yields functionCallArgs argumentsPrinter :=
  .map <| .congr (.seq (fixed "(") (.seq (.optional (ref "function_arguments" as Print.exprs))
    (fixed ")"))) fun ⟨_, arguments, _⟩ => by cases arguments <;> rfl

private theorem functionArguments_yields : Yields functionArguments Print.exprs :=
  .map <| .congr (.seq (ref "expression" as Print.expr) (.optional (.seq (fixed ",")
    (ref "function_arguments_non_first" as fun (first, rest) => Print.exprs (first :: rest)))))
    fun ⟨first, rest⟩ => following_exprs first rest

private theorem functionArgumentsNonFirst_yields :
    Yields functionArgumentsNonFirst fun (first, rest) => Print.exprs (first :: rest) :=
  .map <| .congr (.seq (ref "function_argument" as Print.expr) (.optional (.seq (fixed ",")
    (ref "function_arguments_non_first" as fun (first, rest) => Print.exprs (first :: rest)))))
    fun ⟨first, rest⟩ => following_exprs first rest

private theorem outputExpressionList_yields : Yields outputExpressionList Print.outputs :=
  .map <| .congr (.seq (.optional (ref "expression" as Print.expr))
    (.many (.seq (fixed ",") (.optional (ref "expression" as Print.expr)))))
    fun ⟨first, rest⟩ => by simp [Print.outputs, output_optional, outputsTail_map]; rfl

private theorem arraySubscripts_yields : Yields arraySubscripts subscriptsPrinter :=
  .map <| .congr (.seq (fixed "[") (.seq (ref "subscript" as Print.expr)
    (.seq (.many (.seq (fixed ",") (ref "subscript" as Print.expr))) (fixed "]"))))
    fun ⟨_, first, rest, _⟩ => by simp [subscriptsPrinter, Print.exprs, exprsTail_map]; rfl

/-- A reference rule body yields the printer of the rule it names. -/
local macro "delegates " n:str : term =>
  `(.congr (ref' $n (p := printResult $n) fun _ => rfl) fun _ => rfl)

/-- Each rule body yields the printer of its rule. -/
theorem printed : Yield rules Token.symbol printResult := by
  intro rule action found
  unfold rules at found
  split at found <;> try contradiction
  all_goals cases Option.some.inj found
  · exact .congr storedDefinition_yields fun _ => rfl
  · exact .congr classDefinition_yields fun _ => rfl
  · exact .congr (payload _) fun _ => rfl
  · exact delegates "long_class_specifier"
  · exact .congr longClassSpecifier_yields fun _ => rfl
  · exact .congr composition_yields fun _ => rfl
  · exact .congr elementList_yields fun _ => rfl
  · exact .congr element_yields fun _ => rfl
  · exact .congr componentClause_yields fun _ => rfl
  · exact .congr typePrefix_yields fun _ => rfl
  · exact delegates "name"
  · exact .congr componentList_yields fun _ => rfl
  · exact delegates "declaration"
  · exact .congr declaration_yields fun _ => rfl
  · exact .congr modification_yields fun _ => rfl
  · exact delegates "expression"
  · exact .congr classModification_yields fun _ => rfl
  · exact .congr argumentList_yields fun _ => rfl
  · exact delegates "element_modification_or_replaceable"
  · exact .congr elementModificationOrReplaceable_yields fun _ => rfl
  · exact .congr elementModification_yields fun _ => rfl
  · exact .congr equationSection_yields fun _ => rfl
  · exact delegates "equation_or_procedure"
  · exact delegates "simple_equation"
  · exact .congr simpleEquation_yields fun _ => rfl
  · exact delegates "simple_expression"
  · exact delegates "logical_expression"
  · exact delegates "logical_term"
  · exact delegates "logical_factor"
  · exact delegates "relation"
  · exact delegates "arithmetic_expression"
  · exact .congr arithmeticExpression_yields fun _ => rfl
  · exact .congr (operator_yields "+" "-") fun _ => rfl
  · exact .congr term_yields fun _ => rfl
  · exact .congr (.alt (payload _) (operator_yields "/" ".*")) fun _ => rfl
  · exact delegates "primary"
  · exact .congr primary_yields fun _ => rfl
  · exact .congr name_yields fun _ => rfl
  · exact .congr componentReference_yields fun _ => rfl
  · exact .congr functionCallArgs_yields fun _ => rfl
  · exact .congr functionArguments_yields fun _ => rfl
  · exact .congr functionArgumentsNonFirst_yields fun _ => rfl
  · exact delegates "expression"
  · exact .congr outputExpressionList_yields fun _ => rfl
  · exact .congr arraySubscripts_yields fun _ => rfl
  · exact delegates "expression"

/-- The payloads of every value a rule denotes are its printed result. -/
theorem denotes_tokens {name : String} {v : Structure.Value Token} {result : Result name}
    (denotes : Denotes rules Token.symbol (.ref name) v result) :
    v.tokens = printResult name result :=
  Denotes.tokens printed denotes (Action.Yields.ref name)

end Rumoca.Modelica.Structural
