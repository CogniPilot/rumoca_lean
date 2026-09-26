import ModelicaParser.Generated

/-! Derivations in the independent EBNF language of the forms static semantics
admits: a model class, plain declarations `T n`, and equations whose sides are
names, derivative calls and signed names. Static semantics composes them into
the derivation of a whole admitted record, so the certified parser accepts its
tokens (`Structural.accepts_iff`). -/
namespace Rumoca.Modelica.Derivations
open _root_.Parser EBNF

local notation "D" => Derives Generated.sourceGrammar

private theorem cast {e : Expr} {w w' : List Symbol} (same : w = w') (d : D e w) : D e w' :=
  same ▸ d

private theorem terminal (s : Symbol) (nonempty : s ≠ .literal "" := by decide) : D (.terminal s) [s] :=
  .terminal nonempty

/-- Repetition of a derivable body. -/
theorem many {α : Type} {body : Expr} (f : α → List Symbol) :
    (xs : List α) → (∀ x ∈ xs, D body (f x)) → D (.many body) (xs.flatMap f)
  | [], _ => .manyEmpty
  | x :: xs, each =>
    .manyCons (each x (List.mem_cons_self ..)) (many f xs fun y member =>
      each y (List.mem_cons_of_mem _ member))

theorem componentReference_ident : D (.ref "component_reference") [.ident] :=
  (Generated.«rule_component_reference» _).mpr (.altLeft (cast (by simp)
    (.seq (terminal .ident) (.seq .optionalEmpty .manyEmpty))))

/-- An arithmetic expression is an expression. -/
theorem expression_of_arithmetic {w : List Symbol} (d : D (.ref "arithmetic_expression") w) :
    D (.ref "expression") w :=
  (Generated.«rule_expression» _).mpr <| (Generated.«rule_simple_expression» _).mpr <|
    (Generated.«rule_logical_expression» _).mpr <| (Generated.«rule_logical_term» _).mpr <|
      (Generated.«rule_logical_factor» _).mpr <| (Generated.«rule_relation» _).mpr d

theorem simpleExpression_of_arithmetic {w : List Symbol} (d : D (.ref "arithmetic_expression") w) :
    D (.ref "simple_expression") w :=
  (Generated.«rule_simple_expression» _).mpr <|
    (Generated.«rule_logical_expression» _).mpr <| (Generated.«rule_logical_term» _).mpr <|
      (Generated.«rule_logical_factor» _).mpr <| (Generated.«rule_relation» _).mpr d

/-- A primary is a term. -/
theorem term_of_primary {w : List Symbol} (d : D (.ref "primary") w) : D (.ref "term") w :=
  (Generated.«rule_term» _).mpr (cast (by simp) (.seq ((Generated.«rule_factor» _).mpr d) .manyEmpty))

/-- An unsigned term is an arithmetic expression. -/
theorem arithmetic_of_term {w : List Symbol} (d : D (.ref "term") w) :
    D (.ref "arithmetic_expression") w :=
  (Generated.«rule_arithmetic_expression» _).mpr (.altLeft (cast (by simp) (.seq d .manyEmpty)))

/-- A term with a leading sign is an arithmetic expression. -/
theorem arithmetic_signed {w : List Symbol} (sign : Symbol)
    (signed : sign = .literal "+" ∨ sign = .literal "-") (d : D (.ref "term") w) :
    D (.ref "arithmetic_expression") (sign :: w) := by
  have operator : D (.ref "add_operator") [sign] := by
    apply (Generated.«rule_add_operator» _).mpr
    rcases signed with rfl | rfl
    · exact .altLeft (terminal _)
    · exact .altRight (terminal _)
  exact (Generated.«rule_arithmetic_expression» _).mpr
    (.altRight (cast (by simp) (.seq operator (.seq d .manyEmpty))))

theorem primary_ident : D (.ref "primary") [.ident] :=
  (Generated.«rule_primary» _).mpr (.altLeft componentReference_ident)

/-- The arithmetic expression of one name. -/
theorem arithmetic_ident : D (.ref "arithmetic_expression") [.ident] :=
  arithmetic_of_term (term_of_primary primary_ident)

/-- `der ( n )`. -/
theorem primary_derivative :
    D (.ref "primary") [.literal "der", .literal "(", .ident, .literal ")"] := by
  have argument : D (.ref "function_arguments") [.ident] :=
    (Generated.«rule_function_arguments» _).mpr
      (cast (by simp) (.seq (expression_of_arithmetic arithmetic_ident) .optionalEmpty))
  have arguments : D (.ref "function_call_args") [.literal "(", .ident, .literal ")"] :=
    (Generated.«rule_function_call_args» _).mpr
      (cast (by simp) (.seq (terminal _) (.seq (.optionalSome argument) (terminal _))))
  exact (Generated.«rule_primary» _).mpr (.altRight (.altLeft
    (cast (by simp) (.seq (.altRight (terminal _)) arguments))))

/-- An equation `left = right`. -/
theorem someEquation {left right : List Symbol} (l : D (.ref "simple_expression") left)
    (r : D (.ref "expression") right) : D (.ref "some_equation") (left ++ .literal "=" :: right) :=
  (Generated.«rule_some_equation» _).mpr <| (Generated.«rule_equation_or_procedure» _).mpr <|
    (Generated.«rule_simple_equation» _).mpr (cast (by simp) (.seq l (.seq (terminal _) r)))

/-- The plain declaration `T n`. -/
theorem element_declaration : D (.ref "element") [.ident, .ident] := by
  have typePrefix : D (.ref "type_prefix") [] := (Generated.«rule_type_prefix» _).mpr .optionalEmpty
  have typeName : D (.ref "type_specifier") [.ident] :=
    (Generated.«rule_type_specifier» _).mpr ((Generated.«rule_name» _).mpr
      (cast (by simp) (.seq (terminal _) .manyEmpty)))
  have declaration : D (.ref "declaration") [.ident] :=
    (Generated.«rule_declaration» _).mpr
      (cast (by simp) (.seq (terminal _) (.seq .optionalEmpty .optionalEmpty)))
  have declared : D (.ref "component_list") [.ident] :=
    (Generated.«rule_component_list» _).mpr (cast (by simp)
      (.seq ((Generated.«rule_component_declaration» _).mpr declaration) .manyEmpty))
  exact (Generated.«rule_element» _).mpr ((Generated.«rule_component_clause» _).mpr
    (cast (by simp) (.seq typePrefix (.seq typeName (.seq .optionalEmpty declared)))))

/-- A class body of declarations and one equation section. -/
theorem composition {elements equations : List Symbol}
    (declared : D (.many (.seq (.ref "element") (.terminal (.literal ";")))) elements)
    (equated : D (.many (.seq (.ref "some_equation") (.terminal (.literal ";")))) equations) :
    D (.ref "composition") (elements ++ .literal "equation" :: equations) := by
  have section' : D (.ref "equation_section") (.literal "equation" :: equations) :=
    (Generated.«rule_equation_section» _).mpr (cast (by simp) (.seq (terminal _) equated))
  exact (Generated.«rule_composition» _).mpr (cast (by simp)
    (.seq ((Generated.«rule_element_list» _).mpr declared) (.manyCons section' .manyEmpty)))

/-- A stored definition of one model class. -/
theorem accepts_model {body : List Symbol} (composed : D (.ref "composition") body) :
    Accepts Generated.sourceGrammar
      (.literal "model" :: .ident :: body ++ [.literal "end", .ident, .literal ";"]) := by
  apply (Generated.start_rule _).mpr
  apply (Generated.«rule_stored_definition» _).mpr
  have specified : D (.ref "class_specifier") (.ident :: body ++ [.literal "end", .ident]) :=
    (Generated.«rule_class_specifier» _).mpr ((Generated.«rule_long_class_specifier» _).mpr
      (cast (by simp) (.seq (terminal _) (.seq composed (.seq (terminal _) (terminal _))))))
  have defined : D (.ref "class_definition") (.literal "model" :: .ident :: body ++
      [.literal "end", .ident]) :=
    (Generated.«rule_class_definition» _).mpr (cast (by simp)
      (.seq ((Generated.«rule_class_prefixes» _).mpr (terminal _)) specified))
  exact cast (by simp) (.manyCons (.seq defined (terminal _)) .manyEmpty)

end Rumoca.Modelica.Derivations
