import Parser.LALR.EBNFActions
import GALECParser.AST
import GALECParser.Generated

/-! The entire GALEC grammar as typed, table-delegating actions.
Rule bodies contain only references to other rules, not their expansions.
AST constructors retain the original Token payloads, including lexical category.
There is no source-name resolution, inferred shape, or special call action. -/
namespace Rumoca.GALEC.Structural
open _root_.Parser LALR.Frontend

def Result : String → Type
  | "block" => AST.Block
  | "declaration" => AST.Declaration
  | "direction" => AST.Kind
  | "primitive_type" | "additive_operator" | "multiplicative_operator" => Token
  | "method" => AST.Method
  | "statement" | "single_assignment" | "for_loop" => AST.Statement
  | "reference" | "local_reference" | "state_reference" => AST.Reference
  | "component_reference" => AST.Component
  | "expression_list" => List AST.Expr
  | "expression" | "term" | "primary" | "function_call" | "dimension_query" => AST.Expr
  | _ => Unit

abbrev Action := StructuralActions.Action Token Result
def lit (s : String) : Action Token := .terminal (.literal s)
def ident : Action Token := .terminal .ident
local infixr:60 " ⋄ " => StructuralActions.Action.seq

/-- The two declaration sections stay separate lists, in source order. -/
def block : Action AST.Block :=
  .map (fun (_, name, visible, _, hidden, _, methods, _, endName, _) =>
    (⟨name, visible, hidden, methods, endName⟩ : AST.Block))
    (lit "block" ⋄ ident ⋄ .many (.ref "declaration") ⋄ lit "protected" ⋄
      .many (.ref "declaration") ⋄ lit "public" ⋄ .many (.ref "method") ⋄
      lit "end" ⋄ ident ⋄ lit ";")

/-- A direction and `constant` are mutually exclusive; absence of both is a
variable. Legality of a kind in its section is static semantics, not parsing. -/
def declarationSyntax (kind : Option AST.Kind) (typeName name : Token)
    (extents : Option (Token × List AST.Expr × Token)) : AST.Declaration :=
  ⟨kind.getD .variable, typeName, (extents.map fun parsed => parsed.2.1).getD [], name⟩

def declaration : Action AST.Declaration :=
  .map (fun (kind, typeName, name, extents, _) => declarationSyntax kind typeName name extents)
    (.optional (.alt (.ref "direction") (.map (fun _ => AST.Kind.constant) (lit "constant"))) ⋄
      .ref "primitive_type" ⋄ ident ⋄
      .optional (lit "[" ⋄ .ref "expression_list" ⋄ lit "]") ⋄ lit ";")

def direction : Action AST.Kind :=
  .alt (.map (fun _ => .input) (lit "input")) (.map (fun _ => .output) (lit "output"))

def primitiveType : Action Token := .alt (lit "Real") (.alt (lit "Integer") (lit "Boolean"))

def method : Action AST.Method :=
  .map (fun (_, name, _, body, _, endName, _) => (⟨name, body, endName⟩ : AST.Method))
    (lit "method" ⋄ ident ⋄ lit "algorithm" ⋄ .many (.ref "statement") ⋄
      lit "end" ⋄ ident ⋄ lit ";")

def statement : Action AST.Statement :=
  .map Prod.fst ((.alt (.ref "single_assignment") (.ref "for_loop")) ⋄ lit ";")

def singleAssignment : Action AST.Statement :=
  .map (fun (target, _, value) => AST.Statement.assign target value)
    (.ref "reference" ⋄ lit ":=" ⋄ .ref "expression")

/-- Two range expressions mean `start:stop`; three mean `start:step:stop`,
so the middle expression of a three-part range is the step. -/
def loopSyntax (binder : Token) (start second : AST.Expr)
    (third : Option (Token × AST.Expr)) (body : List AST.Statement) : AST.Statement :=
  match third with
  | none => .forLoop binder start none second body
  | some (_, stop) => .forLoop binder start (some second) stop body

theorem loop_two_part (binder : Token) (start stop : AST.Expr) (body : List AST.Statement) :
    loopSyntax binder start stop none body = .forLoop binder start none stop body := rfl

theorem loop_three_part (binder colon : Token) (start step stop : AST.Expr)
    (body : List AST.Statement) :
    loopSyntax binder start step (some (colon, stop)) body =
      .forLoop binder start (some step) stop body := rfl

def forLoop : Action AST.Statement :=
  .map (fun (_, binder, _, start, _, second, third, _, body, _, _) =>
    loopSyntax binder start second third body)
    (lit "for" ⋄ ident ⋄ lit "in" ⋄ .ref "expression" ⋄ lit ":" ⋄ .ref "expression" ⋄
      .optional (lit ":" ⋄ .ref "expression") ⋄ lit "loop" ⋄ .many (.ref "statement") ⋄
      lit "end" ⋄ lit "for")

def reference : Action AST.Reference :=
  .alt (.ref "local_reference") (.ref "state_reference")

def localReference : Action AST.Reference :=
  .map (fun component => ⟨component, []⟩) (.ref "component_reference")

def stateSyntax (selfToken : Token) (head : AST.Component)
    (tail : List (Token × AST.Component)) : AST.Reference :=
  ⟨⟨selfToken, []⟩, head :: tail.map Prod.snd⟩

def stateReference : Action AST.Reference :=
  .map (fun (selfToken, _, head, tail) => stateSyntax selfToken head tail)
    (lit "self" ⋄ lit "." ⋄ .ref "component_reference" ⋄
      .many (lit "." ⋄ .ref "component_reference"))

def componentSyntax (name : Token) (indices : Option (Token × List AST.Expr × Token)) :
    AST.Component :=
  ⟨name, (indices.map fun parsed => parsed.2.1).getD []⟩

def componentReference : Action AST.Component :=
  .map (fun (name, indices) => componentSyntax name indices)
    (ident ⋄ .optional (lit "[" ⋄ .ref "expression_list" ⋄ lit "]"))

def expressionList : Action (List AST.Expr) :=
  .map (fun (first, rest) => first :: rest.map Prod.snd)
    (.ref "expression" ⋄ .many (lit "," ⋄ .ref "expression"))

/-- Preserve written left-to-right association; do not reassociate arithmetic. -/
def leftAssociate (first : AST.Expr) (rest : List (Token × AST.Expr)) : AST.Expr :=
  rest.foldl (fun left (op, right) => .binary op left right) first

def expression : Action AST.Expr :=
  .map (fun (first, rest) => leftAssociate first rest)
    (.ref "term" ⋄ .many (.ref "additive_operator" ⋄ .ref "term"))

def additiveOperator : Action Token := lit "+"

def term : Action AST.Expr :=
  .map (fun (first, rest) => leftAssociate first rest)
    (.ref "primary" ⋄ .many (.ref "multiplicative_operator" ⋄ .ref "primary"))

def multiplicativeOperator : Action Token := lit "*"

/-- A bare unindexed component whose token is a number is a literal; every
other reference, including a number token with indices, stays a reference. -/
def referenceExpr : AST.Reference → AST.Expr
  | ⟨⟨.number spelling, []⟩, []⟩ => .literal (.number spelling)
  | reference => .reference reference

def primary : Action AST.Expr :=
  .alt (.map referenceExpr (.ref "reference"))
    (.alt (.map (fun (_, body, _) => AST.Expr.parens body)
      (lit "(" ⋄ .ref "expression" ⋄ lit ")"))
      (.alt (.ref "function_call") (.ref "dimension_query")))

def functionCall : Action AST.Expr :=
  .map (fun (callee, _, arguments, _) => AST.Expr.call callee (arguments.getD []))
    (ident ⋄ lit "(" ⋄ .optional (.ref "expression_list") ⋄ lit ")")

def dimensionQuery : Action AST.Expr :=
  .map (fun (_, _, ref, _, axis, _) => AST.Expr.size ref axis)
    (lit "size" ⋄ lit "(" ⋄ .ref "reference" ⋄ lit "," ⋄ .ref "expression" ⋄ lit ")")

def rules : StructuralActions.Rules Token Result
  | "block" => some block
  | "declaration" => some declaration
  | "direction" => some direction
  | "primitive_type" => some primitiveType
  | "method" => some method
  | "statement" => some statement
  | "single_assignment" => some singleAssignment
  | "for_loop" => some forLoop
  | "reference" => some reference
  | "local_reference" => some localReference
  | "state_reference" => some stateReference
  | "component_reference" => some componentReference
  | "expression_list" => some expressionList
  | "expression" => some expression
  | "additive_operator" => some additiveOperator
  | "term" => some term
  | "multiplicative_operator" => some multiplicativeOperator
  | "primary" => some primary
  | "function_call" => some functionCall
  | "dimension_query" => some dimensionQuery
  | _ => none

end Rumoca.GALEC.Structural
