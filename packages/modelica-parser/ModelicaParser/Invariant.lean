import Parser.LALR.ActionHolds
import ModelicaParser.StructuralParser

/-! Invariants of every parsed Modelica syntax tree: each retained token has
the lexical class of its grammar position (a name is an identifier or number
token, an operator one of its operator literals, a Boolean `false` or `true`),
and every list the grammar requires to be nonempty is. Each rule body is
checked once to establish the invariant of its rule, so every tree the
certified parser builds satisfies it. Static semantics uses the invariant to
read a tree back from its printed tokens. -/
namespace Rumoca.Modelica.Good
open _root_.Parser AST

/-- A token of identifier class: an identifier or a number. -/
def Named (t : Token) : Prop := t.symbol = .ident

/-- The binary operators of the grammar. -/
def operators : List Token :=
  [.literal "+", .literal "-", .literal "*", .literal "/", .literal ".*"]

mutual
  def expr : Expr → Prop
    | .reference ref => reference ref
    | .call function arguments => callee function ∧ exprs arguments
    | .boolean value => value = .literal "false" ∨ value = .literal "true"
    | .parens items => outputs items
    | .unary operator operand =>
        (operator = .literal "+" ∨ operator = .literal "-") ∧ expr operand
    | .binary operator left right => operator ∈ operators ∧ expr left ∧ expr right

  def callee : Callee → Prop
    | .reference ref => reference ref
    | .der => True

  def reference : ComponentReference → Prop
    | ⟨_, parts⟩ => parts ≠ [] ∧ components parts

  def components : List Part → Prop
    | [] => True
    | first :: rest => component first ∧ components rest

  def component : Part → Prop
    | ⟨name, indices⟩ => Named name ∧ subscripts indices

  def subscripts : Option (List Expr) → Prop
    | none => True
    | some indices => exprs indices

  def exprs : List Expr → Prop
    | [] => True
    | first :: rest => expr first ∧ exprs rest

  def outputs : List (Option Expr) → Prop
    | [] => True
    | first :: rest => output first ∧ outputs rest

  def output : Option Expr → Prop
    | none => True
    | some value => expr value
end

/-- A dotted name: one or more name tokens. -/
def name (n : Name) : Prop := n ≠ [] ∧ ∀ t ∈ n, Named t

/-- The STRING tokens of a description string. -/
def strings (ts : List Token) : Prop := ∀ t ∈ ts, t.symbol = .string

mutual
  def modification : Modification → Prop
    | .class arguments value => argumentList arguments ∧ binding value
    | .value value => expr value

  def binding : Option Expr → Prop
    | none => True
    | some value => expr value

  def argumentList : List Argument → Prop
    | [] => True
    | first :: rest => argument first ∧ argumentList rest

  def argument : Argument → Prop
    | ⟨_, target⟩ => elementModification target

  def elementModification : ElementModification → Prop
    | ⟨target, value, description⟩ => name target ∧ optionalModification value ∧ strings description

  def optionalModification : Option Modification → Prop
    | none => True
    | some value => modification value
end

def typePrefix (value : Option Token) : Prop :=
  ∀ t ∈ value, t = .literal "input" ∨ t = .literal "output"

def declaration (d : Declaration) : Prop :=
  Named d.name ∧ subscripts d.subscripts ∧ optionalModification d.modification

def description (d : Description) : Prop := strings d.strings ∧ ∀ a ∈ d.annotation, argumentList a

def componentDeclaration (c : ComponentDeclaration) : Prop :=
  declaration c.declaration ∧ (∀ e ∈ c.condition, expr e) ∧ description c.description

def declarations (ds : List ComponentDeclaration) : Prop := ds ≠ [] ∧ ∀ d ∈ ds, componentDeclaration d

def componentClause (c : ComponentClause) : Prop :=
  typePrefix c.typePrefix ∧ name c.typeName ∧ subscripts c.subscripts ∧ declarations c.declarations

def element : Element → Prop
  | .component clause => componentClause clause

def equation : Equation → Prop
  | .simple left right => expr left ∧ expr right

def someEquation (q : SomeEquation) : Prop := equation q.equation ∧ description q.description

def equationSection (s : EquationSection) : Prop := ∀ q ∈ s.equations, someEquation q

def composition (c : Composition) : Prop :=
  (∀ e ∈ c.elements, element e) ∧ (∀ s ∈ c.sections, equationSection s) ∧
    ∀ a ∈ c.annotation, argumentList a

def classSpecifier : ClassSpecifier → Prop
  | .long first description body last =>
    Named first ∧ strings description ∧ composition body ∧ Named last

def classDefinition (c : ClassDefinition) : Prop :=
  c.prefixes = .literal "model" ∧ classSpecifier c.specifier

def storedDefinition (d : StoredDefinition) : Prop := ∀ c ∈ d.classes, classDefinition c

/-! ### List forms -/

theorem exprs_iff (es : List Expr) : exprs es ↔ ∀ e ∈ es, expr e := by
  induction es with
  | nil => simp [exprs]
  | cons _ _ ih => simp [exprs, ih]

theorem outputs_iff (os : List (Option Expr)) : outputs os ↔ ∀ o ∈ os, ∀ e ∈ o, expr e := by
  induction os with
  | nil => simp [outputs]
  | cons first _ ih => cases first <;> simp [outputs, output, ih]

theorem components_iff (ps : List Part) : components ps ↔ ∀ p ∈ ps, component p := by
  induction ps with
  | nil => simp [components]
  | cons _ _ ih => simp [components, ih]

theorem argumentList_iff (as : List Argument) : argumentList as ↔ ∀ a ∈ as, argument a := by
  induction as with
  | nil => simp [argumentList]
  | cons _ _ ih => simp [argumentList, ih]

theorem leftAssociate (first : Expr) (rest : List (Token × Expr)) (valid : expr first)
    (following : ∀ x ∈ rest, x.1 ∈ operators ∧ expr x.2) : expr (AST.leftAssociate first rest) := by
  induction rest generalizing first with
  | nil => exact valid
  | cons head rest ih =>
    apply ih
    · have := following head (List.mem_cons_self ..)
      exact ⟨this.1, valid, this.2⟩
    · exact fun x member => following x (List.mem_cons_of_mem _ member)

/-! ### Rule invariants -/

/-- The invariant of each rule's result. -/
def invariant : (name : String) → Structural.Result name → Prop
  | "stored_definition" => storedDefinition
  | "class_definition" => classDefinition
  | "class_prefixes" => fun t => t = .literal "model"
  | "add_operator" => fun t => t = .literal "+" ∨ t = .literal "-"
  | "mul_operator" => fun t => t = .literal "*" ∨ t = .literal "/" ∨ t = .literal ".*"
  | "class_specifier" | "long_class_specifier" => classSpecifier
  | "composition" => composition
  | "element_list" => fun (elements : List Element) => ∀ e ∈ elements, element e
  | "element" => element
  | "component_clause" => componentClause
  | "type_prefix" => typePrefix
  | "type_specifier" | "name" => name
  | "component_list" => declarations
  | "component_declaration" => componentDeclaration
  | "declaration" => declaration
  | "modification" => modification
  | "class_modification" | "argument_list" | "annotation_clause" => argumentList
  | "argument" | "element_modification_or_replaceable" => argument
  | "element_modification" => elementModification
  | "equation_section" => equationSection
  | "some_equation" => someEquation
  | "equation_or_procedure" | "simple_equation" => equation
  | "modification_expression" | "condition_attribute" | "expression" | "simple_expression" | "logical_expression"
    | "logical_term" | "logical_factor" | "relation" | "arithmetic_expression" | "term"
    | "factor" | "primary" | "function_argument" | "subscript" => expr
  | "component_reference" => reference
  | "function_call_args" | "function_arguments" | "array_subscripts" => exprs
  | "function_arguments_non_first" => fun (pair : Expr × List Expr) => expr pair.1 ∧ exprs pair.2
  | "output_expression_list" => outputs
  | "description" => description
  | "description_string" => strings
  | _ => fun _ => True

open LALR.Frontend StructuralActions Structural

local notation "Holds" => Action.Holds Token.symbol invariant

/-- A token whose class is a nonempty literal is that literal. -/
theorem literal_of_symbol {t : Token} {s : String} (same : t.symbol = .literal s)
    (nonempty : s ≠ "" := by decide) : t = .literal s := by
  cases t with
  | ident _ | number _ | string _ => cases same
  | comment _ => exact absurd (Symbol.literal.inj same).symm nonempty
  | literal _ => cases same; rfl

private theorem following_exprs {first : Expr} {rest : Option (Token × (Expr × List Expr))}
    (valid : expr first) (more : ∀ x ∈ rest, Token.symbol x.1 = .literal "," ∧
      (expr x.2.1 ∧ exprs x.2.2)) : exprs (first :: following rest) := by
  cases rest with
  | none => exact ⟨valid, trivial⟩
  | some x => exact ⟨valid, (more x rfl).2.1, (more x rfl).2.2⟩

private theorem subscripts_of {o : Option (List Expr)} (h : ∀ x ∈ o, exprs x) : subscripts o := by
  cases o with
  | none => trivial
  | some x => exact h x rfl

private theorem optionalModification_of {o : Option Modification} (h : ∀ x ∈ o, modification x) :
    optionalModification o := by
  cases o with
  | none => trivial
  | some x => exact h x rfl

private theorem reference_of (global : Bool) {first : Token} {indices : Option (List Expr)}
    {rest : List (Token × Token × Option (List Expr))} (named : Named first)
    (indexed : ∀ x ∈ indices, exprs x)
    (tail : ∀ x ∈ rest, Token.symbol x.1 = .literal "." ∧ (Token.symbol x.2.1 = .ident ∧
      ∀ y ∈ x.2.2, exprs y)) :
    reference (referenceSyntax global first indices rest) := by
  refine ⟨List.cons_ne_nil _ _, (components_iff _).mpr ?_⟩
  intro p member
  simp only [List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨⟨_, name, indices'⟩, found, rfl⟩
  · exact ⟨named, subscripts_of indexed⟩
  · exact ⟨(tail _ found).2.1, subscripts_of (tail _ found).2.2⟩

/-! ### One lemma per rule body -/

private theorem storedDefinition_holds : ∀ x, Holds Structural.storedDefinition x → storedDefinition x := by
  rintro _ ⟨classes, rfl, h⟩ c member
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
  exact (h y hy).1

private theorem classDefinition_holds : ∀ x, Holds Structural.classDefinition x → classDefinition x := by
  rintro _ ⟨⟨_, _⟩, rfl, hp, hs⟩
  exact ⟨hp, hs⟩

private theorem classPrefixes_holds : ∀ x, Holds Structural.classPrefixes x → x = .literal "model" :=
  fun _ h => literal_of_symbol h

private theorem longClassSpecifier_holds :
    ∀ x, Holds Structural.longClassSpecifier x → classSpecifier x := by
  rintro _ ⟨⟨_, _, _, _, _⟩, rfl, hn, hs, hc, _, he⟩
  exact ⟨hn, hs, hc, he⟩

private theorem composition_holds : ∀ x, Holds Structural.composition x → composition x := by
  rintro _ ⟨⟨_, _, annotation⟩, rfl, hels, hsecs, ha⟩
  refine ⟨hels, hsecs, fun a member => ?_⟩
  cases annotation with
  | none => cases member
  | some x => cases member; exact (ha x rfl).1

private theorem elementList_holds :
    ∀ x, Holds Structural.elementList x → ∀ e ∈ x, element e := by
  rintro _ ⟨elements, rfl, h⟩ e member
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
  exact (h y hy).1

private theorem element_holds : ∀ x, Holds Structural.element x → element x := by
  rintro _ ⟨_, rfl, h⟩
  exact h

private theorem componentClause_holds :
    ∀ x, Holds Structural.componentClause x → componentClause x := by
  rintro _ ⟨⟨_, _, _, _⟩, rfl, htp, htn, hsubs, hds⟩
  exact ⟨htp, htn, subscripts_of hsubs, hds⟩

private theorem typePrefix_holds : ∀ x, Holds Structural.typePrefix x → typePrefix x := by
  intro o h t member
  rcases h t member with h | h
  · exact .inl (literal_of_symbol h)
  · exact .inr (literal_of_symbol h)

private theorem componentList_holds : ∀ x, Holds Structural.componentList x → declarations x := by
  rintro _ ⟨⟨first, rest⟩, rfl, hf, hr⟩
  refine ⟨List.cons_ne_nil _ _, fun d member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
    exact (hr y hy).2

private theorem componentDeclaration_holds :
    ∀ x, Holds Structural.componentDeclaration x → componentDeclaration x := by
  rintro _ ⟨⟨_, _, _⟩, rfl, hd, hc, hdesc⟩
  exact ⟨hd, hc, hdesc⟩

private theorem conditionAttribute_holds : ∀ x, Holds Structural.conditionAttribute x → expr x := by
  rintro _ ⟨⟨_, _⟩, rfl, _, he⟩
  exact he

private theorem declaration_holds : ∀ x, Holds Structural.declaration x → declaration x := by
  rintro _ ⟨⟨_, _, _⟩, rfl, hn, hs, hm⟩
  exact ⟨hn, subscripts_of hs, optionalModification_of hm⟩

private theorem modification_holds : ∀ x, Holds Structural.modification x → modification x := by
  rintro _ (⟨⟨_, value⟩, rfl, ha, hv⟩ | ⟨⟨_, _⟩, rfl, _, hv⟩)
  · refine ⟨ha, ?_⟩
    cases value with
    | none => trivial
    | some v => exact (hv v rfl).2
  · exact hv

private theorem classModification_holds :
    ∀ x, Holds Structural.classModification x → argumentList x := by
  rintro _ ⟨⟨_, arguments, _⟩, rfl, _, ha, _⟩
  cases arguments with
  | none => trivial
  | some a => exact ha a rfl

private theorem argumentList_holds : ∀ x, Holds Structural.argumentList x → argumentList x := by
  rintro _ ⟨⟨first, rest⟩, rfl, hf, hr⟩
  refine (argumentList_iff _).mpr fun a member => ?_
  rcases List.mem_cons.mp member with rfl | member
  · exact hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
    exact (hr y hy).2

private theorem elementModificationOrReplaceable_holds :
    ∀ x, Holds Structural.elementModificationOrReplaceable x → argument x := by
  rintro _ ⟨⟨_, _⟩, rfl, _, hm⟩
  exact hm

private theorem elementModification_holds :
    ∀ x, Holds Structural.elementModification x → elementModification x := by
  rintro _ ⟨⟨_, _, _⟩, rfl, hn, hm, hs⟩
  exact ⟨hn, optionalModification_of hm, hs⟩

private theorem equationSection_holds :
    ∀ x, Holds Structural.equationSection x → equationSection x := by
  rintro _ ⟨⟨_, equations⟩, rfl, _, h⟩ e member
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
  exact (h y hy).1

private theorem someEquation_holds : ∀ x, Holds Structural.someEquation x → someEquation x := by
  rintro _ ⟨⟨_, _⟩, rfl, he, hd⟩
  exact ⟨he, hd⟩

private theorem simpleEquation_holds : ∀ x, Holds Structural.simpleEquation x → equation x := by
  rintro _ ⟨⟨_, _, _⟩, rfl, hl, _, hr⟩
  exact ⟨hl, hr⟩

private theorem add_operator {t : Token} (h : t = .literal "+" ∨ t = .literal "-") :
    t ∈ operators := by
  rcases h with rfl | rfl <;> simp [operators]

private theorem mul_operator {t : Token}
    (h : t = .literal "*" ∨ t = .literal "/" ∨ t = .literal ".*") : t ∈ operators := by
  rcases h with rfl | rfl | rfl <;> simp [operators]

private theorem arithmeticExpression_holds :
    ∀ x, Holds Structural.arithmeticExpression x → expr x := by
  rintro _ (⟨⟨_, _⟩, rfl, hf, hr⟩ | ⟨⟨_, _, _⟩, rfl, hs, hf, hr⟩)
  · exact leftAssociate _ _ hf fun x member => ⟨add_operator (hr x member).1, (hr x member).2⟩
  · exact leftAssociate _ _ ⟨hs, hf⟩ fun x member => ⟨add_operator (hr x member).1, (hr x member).2⟩

private theorem addOperator_holds :
    ∀ x, Holds Structural.addOperator x → x = .literal "+" ∨ x = .literal "-" := by
  rintro _ (h | h)
  · exact .inl (literal_of_symbol h)
  · exact .inr (literal_of_symbol h)

private theorem term_holds : ∀ x, Holds Structural.term x → expr x := by
  rintro _ ⟨⟨_, _⟩, rfl, hf, hr⟩
  exact leftAssociate _ _ hf fun x member => ⟨mul_operator (hr x member).1, (hr x member).2⟩

private theorem mulOperator_holds : ∀ x, Holds Structural.mulOperator x →
    x = .literal "*" ∨ x = .literal "/" ∨ x = .literal ".*" := by
  rintro _ (h | h | h)
  · exact .inl (literal_of_symbol h)
  · exact .inr (.inl (literal_of_symbol h))
  · exact .inr (.inr (literal_of_symbol h))

private theorem primary_holds : ∀ x, Holds Structural.primary x → expr x := by
  rintro _ (⟨_, rfl, hr⟩ | ⟨⟨_, _⟩, rfl, hc, ha⟩ | ⟨_, rfl, ht⟩ | ⟨_, rfl, ht⟩ |
    ⟨⟨_, _, _⟩, rfl, _, hitems, _⟩)
  · exact hr
  · refine ⟨?_, ha⟩
    rcases hc with ⟨_, rfl, hr⟩ | ⟨_, rfl, _⟩
    · exact hr
    · trivial
  · exact .inl (literal_of_symbol ht)
  · exact .inr (literal_of_symbol ht)
  · exact hitems

private theorem name_holds : ∀ x, Holds Structural.name x → name x := by
  rintro _ ⟨⟨first, rest⟩, rfl, hf, hr⟩
  refine ⟨List.cons_ne_nil _ _, fun t member => ?_⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
    exact (hr y hy).2

private theorem componentReference_holds :
    ∀ x, Holds Structural.componentReference x → reference x := by
  rintro _ (⟨⟨_, _, _⟩, rfl, hf, hs, hr⟩ | ⟨⟨_, _, _, _⟩, rfl, _, hf, hs, hr⟩)
  · exact reference_of false hf hs hr
  · exact reference_of true hf hs hr

private theorem functionCallArgs_holds : ∀ x, Holds Structural.functionCallArgs x → exprs x := by
  rintro _ ⟨⟨_, arguments, _⟩, rfl, _, ha, _⟩
  cases arguments with
  | none => trivial
  | some a => exact ha a rfl

private theorem functionArguments_holds : ∀ x, Holds Structural.functionArguments x → exprs x := by
  rintro _ ⟨⟨_, _⟩, rfl, hf, hr⟩
  exact following_exprs hf hr

private theorem functionArgumentsNonFirst_holds :
    ∀ x, Holds Structural.functionArgumentsNonFirst x → expr x.1 ∧ exprs x.2 := by
  rintro _ ⟨⟨_, rest⟩, rfl, hf, hr⟩
  exact following_exprs hf hr

private theorem outputExpressionList_holds :
    ∀ x, Holds Structural.outputExpressionList x → outputs x := by
  rintro _ ⟨⟨first, rest⟩, rfl, hf, hr⟩
  refine (outputs_iff _).mpr fun o member => ?_
  rcases List.mem_cons.mp member with rfl | member
  · exact hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
    exact (hr y hy).2

private theorem arraySubscripts_holds : ∀ x, Holds Structural.arraySubscripts x → exprs x := by
  rintro _ ⟨⟨_, first, rest, _⟩, rfl, _, hf, hr, _⟩
  refine (exprs_iff _).mpr fun e member => ?_
  rcases List.mem_cons.mp member with rfl | member
  · exact hf
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
    exact (hr y hy).2

private theorem description_holds : ∀ x, Holds Structural.description x → description x := by
  rintro _ ⟨⟨_, _⟩, rfl, hs, ha⟩
  exact ⟨hs, ha⟩

private theorem descriptionString_holds :
    ∀ x, Holds Structural.descriptionString x → strings x := by
  rintro _ ⟨written, rfl, h⟩
  cases written with
  | none => intro t member; cases member
  | some pair =>
    obtain ⟨first, rest⟩ := pair
    obtain ⟨hf, hr⟩ := h _ rfl
    intro t member
    rcases List.mem_cons.mp member with rfl | member
    · exact hf
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp member
      exact (hr y hy).2

private theorem annotationClause_holds :
    ∀ x, Holds Structural.annotationClause x → argumentList x := by
  rintro _ ⟨⟨_, _⟩, rfl, _, ha⟩
  exact ha

/-- Every rule body establishes the invariant of its rule. -/
theorem establishes : Establishes rules Token.symbol invariant := by
  intro ruleName rule found
  unfold rules at found
  split at found <;> try contradiction
  all_goals cases Option.some.inj found
  · exact storedDefinition_holds
  · exact classDefinition_holds
  · exact classPrefixes_holds
  · exact fun _ h => h
  · exact longClassSpecifier_holds
  · exact composition_holds
  · exact elementList_holds
  · exact element_holds
  · exact componentClause_holds
  · exact typePrefix_holds
  · exact fun _ h => h
  · exact componentList_holds
  · exact componentDeclaration_holds
  · exact conditionAttribute_holds
  · exact declaration_holds
  · exact modification_holds
  · exact fun _ h => h
  · exact classModification_holds
  · exact argumentList_holds
  · exact fun _ h => h
  · exact elementModificationOrReplaceable_holds
  · exact elementModification_holds
  · exact equationSection_holds
  · exact someEquation_holds
  · exact fun _ h => h
  · exact simpleEquation_holds
  · exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h
  · exact fun _ h => h
  · exact arithmeticExpression_holds
  · exact addOperator_holds
  · exact term_holds
  · exact mulOperator_holds
  · exact fun _ h => h
  · exact primary_holds
  · exact name_holds
  · exact componentReference_holds
  · exact functionCallArgs_holds
  · exact functionArguments_holds
  · exact functionArgumentsNonFirst_holds
  · exact fun _ h => h
  · exact outputExpressionList_holds
  · exact arraySubscripts_holds
  · exact fun _ h => h
  · exact description_holds
  · exact descriptionString_holds
  · exact annotationClause_holds

/-- Every tree the certified parser builds satisfies the invariant. -/
theorem parse_good {tokens : List Token} {ast : StoredDefinition}
    (success : Structural.parse tokens = some ast) : storedDefinition ast := by
  obtain ⟨_, _, _, _, denotes⟩ := (Structural.parse_iff tokens ast).mp success
  exact Denotes.holds establishes denotes

end Rumoca.Modelica.Good
