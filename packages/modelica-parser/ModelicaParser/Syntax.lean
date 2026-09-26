import Parser.Token

/-! General Modelica syntax for the productions of `grammar/Modelica.ebnf`.
Each node keeps the original tokens that carry information: names, number
spellings, prefixes and operators keep their lexical category, so a number
(`Token.number`, grammar symbol `IDENT`) is never mistaken for a name. Fixed
punctuation and keywords are implied by the node. `Print` renders a node back
to its exact token sequence. Which classes, declarations, equations and
expressions are admitted is static semantics, decided after parsing. -/
namespace Rumoca.Modelica.AST
open _root_.Parser

/-- A dotted name, `IDENT { "." IDENT }`, as its identifier tokens. -/
abbrev Name := List Token

mutual
  /-- A.2.7 expressions. `unary` is the leading sign of an arithmetic
  expression; `binary` keeps the written left-to-right association. -/
  inductive Expr where
    | reference (ref : ComponentReference)
    | call (callee : Callee) (arguments : List Expr)
    | string (value : Token)
    | boolean (value : Token)
    | parens (items : List (Option Expr))
    | unary (operator : Token) (operand : Expr)
    | binary (operator : Token) (left right : Expr)

  /-- The called function of a `primary` call. -/
  inductive Callee where
    | reference (ref : ComponentReference)
    | der

  /-- `[ "." ] IDENT [ array-subscripts ] { "." IDENT [ array-subscripts ] }`;
  `global` records the leading `.`. -/
  structure ComponentReference where
    global : Bool
    parts : List Part

  structure Part where
    name : Token
    subscripts : Option (List Expr)
end

mutual
  /-- A.2.5 modifications: a class modification with an optional binding, or
  a binding alone. -/
  inductive Modification where
    | «class» (arguments : List Argument) (value : Option Expr)
    | value (value : Expr)

  structure Argument where
    each : Bool
    modification : ElementModification

  /-- `name [ modification ] description-string`. -/
  structure ElementModification where
    name : Name
    modification : Option Modification
    description : List Token
end

/-- A.2.7 `description`: the STRING tokens of its description string (the `+`
separators are implied) and the arguments of its optional annotation clause,
which is `annotation` followed by a class modification. -/
structure Description where
  strings : List Token
  annotation : Option (List Argument)

structure Declaration where
  name : Token
  subscripts : Option (List Expr)
  modification : Option Modification

/-- `declaration [ condition-attribute ] description`; the condition is the
expression after `if`. -/
structure ComponentDeclaration where
  declaration : Declaration
  condition : Option Expr
  description : Description

structure ComponentClause where
  typePrefix : Option Token
  typeName : Name
  subscripts : Option (List Expr)
  declarations : List ComponentDeclaration

inductive Element where
  | component (clause : ComponentClause)

inductive Equation where
  | simple (left right : Expr)

/-- `equation-or-procedure description`. -/
structure SomeEquation where
  equation : Equation
  description : Description

structure EquationSection where
  equations : List SomeEquation

/-- Elements, equation sections and the arguments of the trailing class
annotation clause. -/
structure Composition where
  elements : List Element
  sections : List EquationSection
  annotation : Option (List Argument)

inductive ClassSpecifier where
  /-- `IDENT description-string composition end IDENT`. -/
  | long (name : Token) (description : List Token) (composition : Composition) (endName : Token)

structure ClassDefinition where
  prefixes : Token
  specifier : ClassSpecifier

structure StoredDefinition where
  classes : List ClassDefinition

/-- Preserve written left-to-right association; do not reassociate. -/
def leftAssociate (first : Expr) (rest : List (Token × Expr)) : Expr :=
  rest.foldl (fun left (operator, right) => .binary operator left right) first

end Rumoca.Modelica.AST
