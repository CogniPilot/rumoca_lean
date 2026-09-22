import Parser.LALR.EBNFActions
import GALECParser.AST
import GALECParser.Generated

/-! The entire current GALEC grammar as typed, table-delegating actions.
Rule bodies contain only references to other rules, not their expansions.
AST constructors retain the original Token payloads, including lexical category.
There is no source-name resolution, inferred shape, or special jacobian action. -/
namespace Rumoca.GALEC.Structural
open _root_.Parser LALR.Frontend

def Result : String → Type
  | "reference" => AST.Reference
  | "product" => AST.Expr
  | "startup" | "recalibrate" | "do_step" | "tensor_do_step" => AST.Method
  | "block" | "tensor_block" | "program" => AST.Block
  | _ => Unit

abbrev Action := StructuralActions.Action Token Result
def lit (s : String) : Action Token := .terminal (.literal s)
def ident : Action Token := .terminal .ident
local infixr:60 " ⋄ " => StructuralActions.Action.seq

def reference : Action AST.Reference :=
  .map (fun (base, _, field) => ⟨base, [field]⟩)
    (lit "self" ⋄ lit "." ⋄ ident)

def product : Action AST.Expr :=
  .map (fun (left, op, right) => .binary op (.reference left) (.reference right))
    (.ref "reference" ⋄ lit ".*" ⋄ .ref "reference")

def startup : Action AST.Method :=
  .map (fun (_, name, _, state, _, zero, _, clock, _, one, _, _, endName, _) =>
    ⟨.public, name, [.assign state (.literal zero), .assign clock (.literal one)], endName⟩)
    (lit "method" ⋄ lit "Startup" ⋄ lit "algorithm" ⋄
      .ref "reference" ⋄ lit ":=" ⋄ lit "0.0" ⋄ lit ";" ⋄
      .ref "reference" ⋄ lit ":=" ⋄ lit "1.0" ⋄ lit ";" ⋄
      lit "end" ⋄ lit "Startup" ⋄ lit ";")

def recalibrate : Action AST.Method :=
  .map (fun (_, name, _, _, endName, _) => ⟨.public, name, [], endName⟩)
    (lit "method" ⋄ lit "Recalibrate" ⋄ lit "algorithm" ⋄
      lit "end" ⋄ lit "Recalibrate" ⋄ lit ";")

def doStep : Action AST.Method :=
  .map (fun (_, name, _, target, _, _, read, op, one, _, _, _, endName, _) =>
    ⟨.public, name,
      [.assign target (.parens (.binary op (.reference read) (.literal one)))], endName⟩)
    (lit "method" ⋄ lit "DoStep" ⋄ lit "algorithm" ⋄
      .ref "reference" ⋄ lit ":=" ⋄ lit "(" ⋄ .ref "reference" ⋄ lit "+" ⋄
      lit "1.0" ⋄ lit ")" ⋄ lit ";" ⋄ lit "end" ⋄ lit "DoStep" ⋄ lit ";")

def tensorDoStep : Action AST.Method :=
  .map (fun (_, name, _, target, _, rhs, _, jacTarget, _, callee, _, arg, _, wrt, _, _,
      _, endName, _) =>
    ⟨.public, name,
      [.assign target rhs, .assign jacTarget (.call callee [arg, .reference wrt])], endName⟩)
    (lit "method" ⋄ lit "DoStep" ⋄ lit "algorithm" ⋄
      .ref "reference" ⋄ lit ":=" ⋄ .ref "product" ⋄ lit ";" ⋄
      .ref "reference" ⋄ lit ":=" ⋄ ident ⋄ lit "(" ⋄ .ref "product" ⋄ lit "," ⋄
      .ref "reference" ⋄ lit ")" ⋄ lit ";" ⋄ lit "end" ⋄ lit "DoStep" ⋄ lit ";")

def scalarBlock : Action AST.Block :=
  .map (fun (_, name, _, real, state, _, _, _, clockReal, clock, _, _, init, reset, step,
      _, endName, _) =>
    ⟨name, [⟨.public, .output, .variable, real, [], state⟩,
      ⟨.protected, .local, .constant, clockReal, [], clock⟩], [init, reset, step], endName⟩)
    (lit "block" ⋄ ident ⋄ lit "output" ⋄ lit "Real" ⋄ ident ⋄ lit ";" ⋄
      lit "protected" ⋄ lit "constant" ⋄ lit "Real" ⋄ ident ⋄ lit ";" ⋄
      lit "public" ⋄ .ref "startup" ⋄ .ref "recalibrate" ⋄ .ref "do_step" ⋄
      lit "end" ⋄ ident ⋄ lit ";")

def tensorBlock : Action AST.Block :=
  .map (fun (_, name, _, inputReal, input, _, n, _, _,
      _, stateReal, state, _, m, _, _,
      _, jacReal, jac, _, rows, _, cols, _, _,
      _, _, clockReal, clock, _, _, init, reset, step, _, endName, _) =>
    ⟨name, [⟨.public, .input, .variable, inputReal, [n], input⟩,
      ⟨.public, .output, .variable, stateReal, [m], state⟩,
      ⟨.public, .output, .variable, jacReal, [rows, cols], jac⟩,
      ⟨.protected, .local, .constant, clockReal, [], clock⟩], [init, reset, step], endName⟩)
    (lit "block" ⋄ ident ⋄
      lit "input" ⋄ lit "Real" ⋄ ident ⋄ lit "[" ⋄ lit "2" ⋄ lit "]" ⋄ lit ";" ⋄
      lit "output" ⋄ lit "Real" ⋄ ident ⋄ lit "[" ⋄ lit "2" ⋄ lit "]" ⋄ lit ";" ⋄
      lit "output" ⋄ lit "Real" ⋄ ident ⋄ lit "[" ⋄ lit "2" ⋄ lit "," ⋄ lit "2" ⋄ lit "]" ⋄ lit ";" ⋄
      lit "protected" ⋄ lit "constant" ⋄ lit "Real" ⋄ ident ⋄ lit ";" ⋄
      lit "public" ⋄ .ref "startup" ⋄ .ref "recalibrate" ⋄ .ref "tensor_do_step" ⋄
      lit "end" ⋄ ident ⋄ lit ";")

def program : Action AST.Block := .alt (.ref "block") (.ref "tensor_block")

def rules : StructuralActions.Rules Token Result
  | "reference" => some reference
  | "product" => some product
  | "startup" => some startup
  | "recalibrate" => some recalibrate
  | "do_step" => some doStep
  | "tensor_do_step" => some tensorDoStep
  | "block" => some scalarBlock
  | "tensor_block" => some tensorBlock
  | "program" => some program
  | _ => none

end Rumoca.GALEC.Structural
