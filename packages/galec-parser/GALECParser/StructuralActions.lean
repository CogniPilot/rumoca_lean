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
  | "signal_interface" => List AST.Name
  | "statement" | "single_assignment" | "if_statement" | "for_loop"
    | "error_signal_statement" => AST.Statement
  | "error_signal_check" => AST.Condition
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

/-- A leading name followed by comma-separated names, in source order. -/
def nameList (first : Token) (rest : List (Token × Token)) : List Token :=
  first :: rest.map Prod.snd

/-- An absent signal interface is the empty name list. -/
def method : Action AST.Method :=
  .map (fun (_, name, signals, _, body, _, endName, _) =>
    (⟨name, signals.getD [], body, endName⟩ : AST.Method))
    (lit "method" ⋄ ident ⋄ .optional (.ref "signal_interface") ⋄ lit "algorithm" ⋄
      .many (.ref "statement") ⋄ lit "end" ⋄ ident ⋄ lit ";")

def signalInterface : Action (List AST.Name) :=
  .map (fun (_, first, rest, _) => nameList first rest)
    (lit "signals" ⋄ ident ⋄ .many (lit "," ⋄ ident) ⋄ lit ";")

def statement : Action AST.Statement :=
  .map Prod.fst ((.alt (.ref "single_assignment") (.alt (.ref "if_statement")
    (.alt (.ref "for_loop") (.ref "error_signal_statement")))) ⋄ lit ";")

/-- A branch condition is an expression or an error-signal check. Condition
typing and the admitted check forms are static semantics. -/
def condition : Action AST.Condition :=
  .alt (.map AST.Condition.expr (.ref "expression")) (.ref "error_signal_check")

/-- The `if` branch first, then every `elseif` branch in source order. -/
def ifSyntax (first : AST.Condition) (body : List AST.Statement)
    (elseifs : List (Token × AST.Condition × Token × List AST.Statement))
    (otherwise : Option (Token × List AST.Statement)) : AST.Statement :=
  .ifThen ((first, body) :: elseifs.map fun (_, condition, _, branch) => (condition, branch))
    (otherwise.map Prod.snd)

def ifStatement : Action AST.Statement :=
  .map (fun (_, first, _, body, elseifs, otherwise, _, _) => ifSyntax first body elseifs otherwise)
    (lit "if" ⋄ condition ⋄ lit "then" ⋄ .many (.ref "statement") ⋄
      .many (lit "elseif" ⋄ condition ⋄ lit "then" ⋄ .many (.ref "statement")) ⋄
      .optional (lit "else" ⋄ .many (.ref "statement")) ⋄ lit "end" ⋄ lit "if")

/-- Without an `in` part the check is unrestricted: not negated, no names. -/
def checkSyntax (closure : Option Token)
    (tested : Option (Option Token × Token × Token × List (Token × Token)))
    (fallback : Option (Token × AST.Expr)) : AST.Condition :=
  match tested with
  | none => .signalCheck closure false [] (fallback.map Prod.snd)
  | some (negation, _, first, rest) =>
      .signalCheck closure negation.isSome (nameList first rest) (fallback.map Prod.snd)

def errorSignalCheck : Action AST.Condition :=
  .map (fun (_, closure, tested, fallback) => checkSyntax closure tested fallback)
    (lit "signal" ⋄ .optional ident ⋄
      .optional (.optional (lit "not") ⋄ lit "in" ⋄ ident ⋄ .many (lit "," ⋄ ident)) ⋄
      .optional (lit "or" ⋄ .ref "expression"))

def errorSignalStatement : Action AST.Statement :=
  .map (fun (_, first, rest) => AST.Statement.signal (nameList first rest))
    (lit "signal" ⋄ ident ⋄ .many (lit "," ⋄ ident))
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
  | "signal_interface" => some signalInterface
  | "statement" => some statement
  | "single_assignment" => some singleAssignment
  | "if_statement" => some ifStatement
  | "error_signal_check" => some errorSignalCheck
  | "for_loop" => some forLoop
  | "error_signal_statement" => some errorSignalStatement
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
