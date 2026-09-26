import Parser.LALR.EBNFActions
import ModelicaParser.Syntax

/-! The entire Modelica grammar as typed, table-delegating actions.
Rule bodies contain only references to other rules, not their expansions.
AST constructors retain the original token payloads, including their lexical
category. There is no name resolution, profile selection or special call
action: `der`, `jacobian` and every other callee are ordinary syntax here. -/
namespace Rumoca.Modelica.Structural
open _root_.Parser LALR.Frontend

def Result : String → Type
  | "stored_definition" => AST.StoredDefinition
  | "class_definition" => AST.ClassDefinition
  | "class_prefixes" | "add_operator" | "mul_operator" => Token
  | "class_specifier" | "long_class_specifier" => AST.ClassSpecifier
  | "composition" => AST.Composition
  | "element_list" => List AST.Element
  | "element" => AST.Element
  | "component_clause" => AST.ComponentClause
  | "type_prefix" => Option Token
  | "type_specifier" | "name" => AST.Name
  | "component_list" => List AST.ComponentDeclaration
  | "component_declaration" => AST.ComponentDeclaration
  | "declaration" => AST.Declaration
  | "modification" => AST.Modification
  | "class_modification" | "argument_list" | "annotation_clause" => List AST.Argument
  | "argument" | "element_modification_or_replaceable" => AST.Argument
  | "element_modification" => AST.ElementModification
  | "equation_section" => AST.EquationSection
  | "some_equation" => AST.SomeEquation
  | "equation_or_procedure" | "simple_equation" => AST.Equation
  | "modification_expression" | "condition_attribute" | "expression" | "simple_expression" | "logical_expression"
    | "logical_term" | "logical_factor" | "relation" | "arithmetic_expression" | "term"
    | "factor" | "primary" | "function_argument" | "subscript" => AST.Expr
  | "component_reference" => AST.ComponentReference
  | "function_call_args" | "function_arguments" | "array_subscripts" => List AST.Expr
  | "function_arguments_non_first" => AST.Expr × List AST.Expr
  | "output_expression_list" => List (Option AST.Expr)
  | "description" => AST.Description
  | "description_string" => List Token
  | _ => Unit

abbrev Action := StructuralActions.Action Token Result
def lit (s : String) : Action Token := .terminal (.literal s)
def ident : Action Token := .terminal .ident
def string : Action Token := .terminal .string
local infixr:60 " ⋄ " => StructuralActions.Action.seq

def storedDefinition : Action AST.StoredDefinition :=
  .map (fun classes => ⟨classes.map Prod.fst⟩) (.many (.ref "class_definition" ⋄ lit ";"))

def classDefinition : Action AST.ClassDefinition :=
  .map (fun (prefixes, specifier) => ⟨prefixes, specifier⟩)
    (.ref "class_prefixes" ⋄ .ref "class_specifier")

def classPrefixes : Action Token := lit "model"

def classSpecifier : Action AST.ClassSpecifier := .ref "long_class_specifier"

def longClassSpecifier : Action AST.ClassSpecifier :=
  .map (fun (name, strings, composition, _, endName) => .long name strings composition endName)
    (ident ⋄ .ref "description_string" ⋄ .ref "composition" ⋄ lit "end" ⋄ ident)

def composition : Action AST.Composition :=
  .map (fun (elements, sections, annotation) => ⟨elements, sections, annotation.map Prod.fst⟩)
    (.ref "element_list" ⋄ .many (.ref "equation_section") ⋄
      .optional (.ref "annotation_clause" ⋄ lit ";"))

def elementList : Action (List AST.Element) :=
  .map (fun elements => elements.map Prod.fst) (.many (.ref "element" ⋄ lit ";"))

def element : Action AST.Element := .map .component (.ref "component_clause")

def componentClause : Action AST.ComponentClause :=
  .map (fun (typePrefix, typeName, subscripts, declarations) =>
      ⟨typePrefix, typeName, subscripts, declarations⟩)
    (.ref "type_prefix" ⋄ .ref "type_specifier" ⋄ .optional (.ref "array_subscripts") ⋄
      .ref "component_list")

def typePrefix : Action (Option Token) := .optional (.alt (lit "input") (lit "output"))

def typeSpecifier : Action AST.Name := .ref "name"

def componentList : Action (List AST.ComponentDeclaration) :=
  .map (fun (first, rest) => first :: rest.map Prod.snd)
    (.ref "component_declaration" ⋄ .many (lit "," ⋄ .ref "component_declaration"))

def componentDeclaration : Action AST.ComponentDeclaration :=
  .map (fun (declaration, condition, description) => ⟨declaration, condition, description⟩)
    (.ref "declaration" ⋄ .optional (.ref "condition_attribute") ⋄ .ref "description")

def conditionAttribute : Action AST.Expr :=
  .map (fun (_, condition) => condition) (lit "if" ⋄ .ref "expression")

def declaration : Action AST.Declaration :=
  .map (fun (name, subscripts, modification) => ⟨name, subscripts, modification⟩)
    (ident ⋄ .optional (.ref "array_subscripts") ⋄ .optional (.ref "modification"))

def modification : Action AST.Modification :=
  .alt (.map (fun (arguments, value) => .class arguments (value.map Prod.snd))
      (.ref "class_modification" ⋄ .optional (lit "=" ⋄ .ref "modification_expression")))
    (.map (fun (_, value) => .value value) (lit "=" ⋄ .ref "modification_expression"))

def modificationExpression : Action AST.Expr := .ref "expression"

/-- An absent argument list is the empty list; the parentheses are implied. -/
def classModification : Action (List AST.Argument) :=
  .map (fun (_, arguments, _) => arguments.getD [])
    (lit "(" ⋄ .optional (.ref "argument_list") ⋄ lit ")")

def argumentList : Action (List AST.Argument) :=
  .map (fun (first, rest) => first :: rest.map Prod.snd)
    (.ref "argument" ⋄ .many (lit "," ⋄ .ref "argument"))

def argument : Action AST.Argument := .ref "element_modification_or_replaceable"

def elementModificationOrReplaceable : Action AST.Argument :=
  .map (fun (each, modification) => ⟨each.isSome, modification⟩)
    (.optional (lit "each") ⋄ .ref "element_modification")

def elementModification : Action AST.ElementModification :=
  .map (fun (name, modification, description) => ⟨name, modification, description⟩)
    (.ref "name" ⋄ .optional (.ref "modification") ⋄ .ref "description_string")

def equationSection : Action AST.EquationSection :=
  .map (fun (_, equations) => ⟨equations.map Prod.fst⟩)
    (lit "equation" ⋄ .many (.ref "some_equation" ⋄ lit ";"))

def someEquation : Action AST.SomeEquation :=
  .map (fun (equation, description) => ⟨equation, description⟩)
    (.ref "equation_or_procedure" ⋄ .ref "description")
def equationOrProcedure : Action AST.Equation := .ref "simple_equation"

def simpleEquation : Action AST.Equation :=
  .map (fun (left, _, right) => .simple left right)
    (.ref "simple_expression" ⋄ lit "=" ⋄ .ref "expression")

def expression : Action AST.Expr := .ref "simple_expression"
def simpleExpression : Action AST.Expr := .ref "logical_expression"
def logicalExpression : Action AST.Expr := .ref "logical_term"
def logicalTerm : Action AST.Expr := .ref "logical_factor"
def logicalFactor : Action AST.Expr := .ref "relation"
def relation : Action AST.Expr := .ref "arithmetic_expression"

/-- The leading sign applies to the first term, before any addition. -/
def arithmeticExpression : Action AST.Expr :=
  .alt (.map (fun (first, rest) => AST.leftAssociate first rest)
      (.ref "term" ⋄ .many (.ref "add_operator" ⋄ .ref "term")))
    (.map (fun (sign, first, rest) => AST.leftAssociate (.unary sign first) rest)
      (.ref "add_operator" ⋄ .ref "term" ⋄ .many (.ref "add_operator" ⋄ .ref "term")))

def addOperator : Action Token := .alt (lit "+") (lit "-")

def term : Action AST.Expr :=
  .map (fun (first, rest) => AST.leftAssociate first rest)
    (.ref "factor" ⋄ .many (.ref "mul_operator" ⋄ .ref "factor"))

def mulOperator : Action Token := .alt (lit "*") (.alt (lit "/") (lit ".*"))

def factor : Action AST.Expr := .ref "primary"

def callee : Action AST.Callee :=
  .alt (.map AST.Callee.reference (.ref "component_reference"))
    (.map (fun _ => AST.Callee.der) (lit "der"))

def primary : Action AST.Expr :=
  .alt (.map AST.Expr.reference (.ref "component_reference"))
    (.alt (.map (fun (callee, arguments) => AST.Expr.call callee arguments)
        (callee ⋄ .ref "function_call_args"))
      (.alt (.map AST.Expr.string string)
        (.alt (.map AST.Expr.boolean (lit "false"))
          (.alt (.map AST.Expr.boolean (lit "true"))
            (.map (fun (_, items, _) => AST.Expr.parens items)
              (lit "(" ⋄ .ref "output_expression_list" ⋄ lit ")"))))))

def name : Action AST.Name :=
  .map (fun (first, rest) => first :: rest.map Prod.snd) (ident ⋄ .many (lit "." ⋄ ident))

/-- The components of a reference after its first one. -/
def partsTail : Action (List (Token × Token × Option (List AST.Expr))) :=
  .many (lit "." ⋄ ident ⋄ .optional (.ref "array_subscripts"))

def referenceSyntax (global : Bool) (first : Token) (subscripts : Option (List AST.Expr))
    (rest : List (Token × Token × Option (List AST.Expr))) : AST.ComponentReference :=
  ⟨global, ⟨first, subscripts⟩ :: rest.map fun (_, name, subscripts) => ⟨name, subscripts⟩⟩

def componentReference : Action AST.ComponentReference :=
  .alt (.map (fun (first, subscripts, rest) => referenceSyntax false first subscripts rest)
      (ident ⋄ .optional (.ref "array_subscripts") ⋄ partsTail))
    (.map (fun (_, first, subscripts, rest) => referenceSyntax true first subscripts rest)
      (lit "." ⋄ ident ⋄ .optional (.ref "array_subscripts") ⋄ partsTail))

/-- An absent argument list is the empty list; the parentheses are implied. -/
def functionCallArgs : Action (List AST.Expr) :=
  .map (fun (_, arguments, _) => arguments.getD [])
    (lit "(" ⋄ .optional (.ref "function_arguments") ⋄ lit ")")

/-- The arguments after a leading one, flattened in source order. -/
def following (rest : Option (Token × (AST.Expr × List AST.Expr))) : List AST.Expr :=
  rest.elim [] fun (_, next, more) => next :: more

def functionArguments : Action (List AST.Expr) :=
  .map (fun (first, rest) => first :: following rest)
    (.ref "expression" ⋄ .optional (lit "," ⋄ .ref "function_arguments_non_first"))

def functionArgumentsNonFirst : Action (AST.Expr × List AST.Expr) :=
  .map (fun (first, rest) => (first, following rest))
    (.ref "function_argument" ⋄ .optional (lit "," ⋄ .ref "function_arguments_non_first"))

def functionArgument : Action AST.Expr := .ref "expression"

def outputExpressionList : Action (List (Option AST.Expr)) :=
  .map (fun (first, rest) => first :: rest.map Prod.snd)
    (.optional (.ref "expression") ⋄ .many (lit "," ⋄ .optional (.ref "expression")))

def arraySubscripts : Action (List AST.Expr) :=
  .map (fun (_, first, rest, _) => first :: rest.map Prod.snd)
    (lit "[" ⋄ .ref "subscript" ⋄ .many (lit "," ⋄ .ref "subscript") ⋄ lit "]")

def subscript : Action AST.Expr := .ref "expression"

def description : Action AST.Description :=
  .map (fun (strings, annotation) => ⟨strings, annotation⟩)
    (.ref "description_string" ⋄ .optional (.ref "annotation_clause"))

/-- An absent description string is the empty list; the `+` separators are
implied. -/
def descriptionString : Action (List Token) :=
  .map (fun strings => strings.elim [] fun (first, rest) => first :: rest.map Prod.snd)
    (.optional (string ⋄ .many (lit "+" ⋄ string)))

def annotationClause : Action (List AST.Argument) :=
  .map (fun (_, arguments) => arguments) (lit "annotation" ⋄ .ref "class_modification")

set_option maxHeartbeats 1000000 in
def rules : StructuralActions.Rules Token Result
  | "stored_definition" => some storedDefinition
  | "class_definition" => some classDefinition
  | "class_prefixes" => some classPrefixes
  | "class_specifier" => some classSpecifier
  | "long_class_specifier" => some longClassSpecifier
  | "composition" => some composition
  | "element_list" => some elementList
  | "element" => some element
  | "component_clause" => some componentClause
  | "type_prefix" => some typePrefix
  | "type_specifier" => some typeSpecifier
  | "component_list" => some componentList
  | "component_declaration" => some componentDeclaration
  | "condition_attribute" => some conditionAttribute
  | "declaration" => some declaration
  | "modification" => some modification
  | "modification_expression" => some modificationExpression
  | "class_modification" => some classModification
  | "argument_list" => some argumentList
  | "argument" => some argument
  | "element_modification_or_replaceable" => some elementModificationOrReplaceable
  | "element_modification" => some elementModification
  | "equation_section" => some equationSection
  | "some_equation" => some someEquation
  | "equation_or_procedure" => some equationOrProcedure
  | "simple_equation" => some simpleEquation
  | "expression" => some expression
  | "simple_expression" => some simpleExpression
  | "logical_expression" => some logicalExpression
  | "logical_term" => some logicalTerm
  | "logical_factor" => some logicalFactor
  | "relation" => some relation
  | "arithmetic_expression" => some arithmeticExpression
  | "add_operator" => some addOperator
  | "term" => some term
  | "mul_operator" => some mulOperator
  | "factor" => some factor
  | "primary" => some primary
  | "name" => some name
  | "component_reference" => some componentReference
  | "function_call_args" => some functionCallArgs
  | "function_arguments" => some functionArguments
  | "function_arguments_non_first" => some functionArgumentsNonFirst
  | "function_argument" => some functionArgument
  | "output_expression_list" => some outputExpressionList
  | "array_subscripts" => some arraySubscripts
  | "subscript" => some subscript
  | "description" => some description
  | "description_string" => some descriptionString
  | "annotation_clause" => some annotationClause
  | _ => none

end Rumoca.Modelica.Structural
