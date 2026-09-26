import ModelicaParser.Syntax

/-! Token rendering of the general Modelica syntax. Each printer emits exactly
the token sequence of its production: retained tokens as written, and the
fixed keywords and punctuation the node implies. `Structural.denotes_tokens`
proves that printing a parsed tree gives the parsed tokens. -/
namespace Rumoca.Modelica.Print
open _root_.Parser AST

def name : Name → List Token
  | [] => []
  | first :: rest => first :: rest.flatMap fun part => [.literal ".", part]

mutual
  def expr : Expr → List Token
    | .reference ref => reference ref
    | .call function arguments =>
        callee function ++ .literal "(" :: exprs arguments ++ [.literal ")"]
    | .boolean value => [value]
    | .parens items => .literal "(" :: outputs items ++ [.literal ")"]
    | .unary operator operand => operator :: expr operand
    | .binary operator left right => expr left ++ operator :: expr right

  def callee : Callee → List Token
    | .reference ref => reference ref
    | .der => [.literal "der"]

  def reference : ComponentReference → List Token
    | ⟨global, parts⟩ => (if global then [.literal "."] else []) ++ components parts

  def components : List Part → List Token
    | [] => []
    | first :: rest => component first ++ componentsTail rest

  def componentsTail : List Part → List Token
    | [] => []
    | next :: rest => .literal "." :: component next ++ componentsTail rest

  def component : Part → List Token
    | ⟨name, indices⟩ => name :: subscripts indices

  def subscripts : Option (List Expr) → List Token
    | none => []
    | some indices => .literal "[" :: exprs indices ++ [.literal "]"]

  /-- Comma-separated expressions. -/
  def exprs : List Expr → List Token
    | [] => []
    | first :: rest => expr first ++ exprsTail rest

  def exprsTail : List Expr → List Token
    | [] => []
    | next :: rest => .literal "," :: expr next ++ exprsTail rest

  def outputs : List (Option Expr) → List Token
    | [] => []
    | first :: rest => output first ++ outputsTail rest

  def outputsTail : List (Option Expr) → List Token
    | [] => []
    | next :: rest => .literal "," :: output next ++ outputsTail rest

  def output : Option Expr → List Token
    | none => []
    | some value => expr value
end

mutual
  def modification : Modification → List Token
    | .class arguments value =>
        .literal "(" :: argumentList arguments ++ .literal ")" :: binding value
    | .value value => .literal "=" :: expr value

  def binding : Option Expr → List Token
    | none => []
    | some value => .literal "=" :: expr value

  def argumentList : List Argument → List Token
    | [] => []
    | first :: rest => argument first ++ argumentsTail rest

  def argumentsTail : List Argument → List Token
    | [] => []
    | next :: rest => .literal "," :: argument next ++ argumentsTail rest

  def argument : Argument → List Token
    | ⟨each, target⟩ => (if each then [.literal "each"] else []) ++ elementModification target

  def elementModification : ElementModification → List Token
    | ⟨target, modification⟩ => name target ++ optionalModification modification

  def optionalModification : Option Modification → List Token
    | none => []
    | some value => modification value
end

def typePrefix (value : Option Token) : List Token := value.elim [] fun token => [token]

def declaration (d : Declaration) : List Token :=
  d.name :: subscripts d.subscripts ++ optionalModification d.modification

def declarations : List Declaration → List Token
  | [] => []
  | first :: rest => declaration first ++ rest.flatMap fun next => .literal "," :: declaration next

def componentClause (c : ComponentClause) : List Token :=
  typePrefix c.typePrefix ++ name c.typeName ++ subscripts c.subscripts ++ declarations c.declarations

def element : Element → List Token
  | .component clause => componentClause clause

def equation : Equation → List Token
  | .simple left right => expr left ++ .literal "=" :: expr right

def equationSection (s : EquationSection) : List Token :=
  .literal "equation" :: s.equations.flatMap fun e => equation e ++ [.literal ";"]

def composition (c : Composition) : List Token :=
  c.elements.flatMap (fun e => element e ++ [.literal ";"]) ++ c.sections.flatMap equationSection

def classSpecifier : ClassSpecifier → List Token
  | .long name body endName => name :: composition body ++ [.literal "end", endName]

def classDefinition (c : ClassDefinition) : List Token :=
  c.prefixes :: classSpecifier c.specifier

def storedDefinition (d : StoredDefinition) : List Token :=
  d.classes.flatMap fun c => classDefinition c ++ [.literal ";"]

/-- Written association is printed without parentheses: each operator sits
between the printed operands it joins. -/
theorem expr_leftAssociate (first : Expr) (rest : List (Token × Expr)) :
    expr (leftAssociate first rest) =
      expr first ++ rest.flatMap fun (operator, operand) => operator :: expr operand := by
  induction rest generalizing first with
  | nil => simp [leftAssociate]
  | cons head rest ih =>
    obtain ⟨operator, operand⟩ := head
    simp only [leftAssociate, List.foldl_cons] at ih ⊢
    rw [ih, expr]
    simp

end Rumoca.Modelica.Print
