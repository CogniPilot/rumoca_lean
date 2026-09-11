import RumocaFMI3.ResetCalls
import RumocaC.StringLiteral

/-! Independent concrete syntax for the current reset function. The grammar
spells out the signature, null/lifecycle guards and all eight writes. It uses
the shared scanner for nonliteral tokens and the independent C string grammar
for the diagnostic. This certifies a complete function fragment: placement in
a translation unit, preprocessing, headers and linkage remain separate. -/
namespace Rumoca.FMI3.Reset.Syntax
open CTree _root_.Parser

private def memberTokens (name : String) : List String := ["(", "m", "->", name, ")"]
private def modeTokens : List String → List String
  | [] => ["0"]
  | n :: ns => ["(", "("] ++ memberTokens "mode" ++ ["==", n, ")", "||"] ++
      modeTokens ns ++ [")"]
private def kindTokens (kind : String) : List String :=
  ["(", "("] ++ memberTokens "kind" ++ ["==", kind, ")", "&&"] ++
    modeTokens ["0", "1", "2", "3", "4", "5"] ++ [")"]

def openingTokens : List Token :=
  (["fmi3Status", "fmi3Reset", "(", "fmi3Instance", "instance", ")", "{",
    "Instance", "*", "m", "=", "(", "(", "Instance", "*", ")", "instance", ")", ";",
    "if", "(", "(", "!", "m", ")", ")", "{", "return", "fmi3Error", ";", "}",
    "if", "(", "(", "!", "("] ++ kindTokens "0" ++ ["||"] ++ kindTokens "1" ++
    [")", ")", ")", "{", "return", "fail", "(", "m", ","]).map Token.literal

private def zeroStore (name : String) : List String := memberTokens name ++ ["=", "0", ";"]

def closingTokens : List Token :=
  ([")", ";", "}", "(", "(", "m", "->", "model", ")", ".", "x", ")", "=",
    "(", "(", "double", ")", "0", ")", ";"] ++
    ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"].flatMap zeroStore ++
    ["return", "fmi3OK", ";", "}"]).map Token.literal

def message : String := "Call is not allowed in the current FMI state"

/-- The literal boundary is between a comma and a closing parenthesis. Neither
scanner segment admits comments, quotes or preprocessing directives. -/
def Denotes (text : String) : Prop :=
  ∃ before literal after : List Char,
    text.toList = before ++ literal ++ after ∧
    Scanner.Lexes CTree.Syntax.config before openingTokens ∧
    CString.Denotes literal (message.toUTF8.data.toList ++ [0]) ∧
    Scanner.Lexes CTree.Syntax.config after closingTokens

private def opening : String :=
  "fmi3Status fmi3Reset(fmi3Instance instance) {\n" ++
  "  Instance * m = ((Instance *)instance);\n" ++
  "  if ((!m)) {\n" ++
  "    return fmi3Error;\n" ++
  "  }\n" ++
  "  if ((!((((m->kind) == 0) && (((m->mode) == 0) || (((m->mode) == 1) || (((m->mode) == 2) || (((m->mode) == 3) || (((m->mode) == 4) || (((m->mode) == 5) || 0))))))) || (((m->kind) == 1) && (((m->mode) == 0) || (((m->mode) == 1) || (((m->mode) == 2) || (((m->mode) == 3) || (((m->mode) == 4) || (((m->mode) == 5) || 0)))))))))) {\n" ++
  "    return fail(m, "

private def closing : String :=
  ");\n" ++
  "  }\n" ++
  "  ((m->model).x) = ((double)0);\n" ++
  "  (m->time) = 0;\n" ++
  "  (m->timeMin) = 0;\n" ++
  "  (m->eventTime) = 0;\n" ++
  "  (m->lastCompleted) = 0;\n" ++
  "  (m->stop) = 0;\n" ++
  "  (m->stopDefined) = 0;\n" ++
  "  (m->mode) = 0;\n" ++
  "  return fmi3OK;\n" ++
  "}\n\n"

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem opening_lexes : Scanner.Lexes CTree.Syntax.config opening.toList openingTokens := by
  apply (Scanner.lex_correct _ _ _).mp
  have checked : (Scanner.lex CTree.Syntax.config opening).toOption = some openingTokens := by
    decide +kernel
  cases parsed : Scanner.lex CTree.Syntax.config opening with
  | error e => simp [parsed, Except.toOption] at checked
  | ok ts => exact congrArg Except.ok (by simpa [parsed, Except.toOption] using checked)

private theorem closing_lexes : Scanner.Lexes CTree.Syntax.config closing.toList closingTokens := by
  apply (Scanner.lex_correct _ _ _).mp
  have checked : (Scanner.lex CTree.Syntax.config closing).toOption = some closingTokens := by
    decide +kernel
  cases parsed : Scanner.lex CTree.Syntax.config closing with
  | error e => simp [parsed, Except.toOption] at checked
  | ok ts => exact congrArg Except.ok (by simpa [parsed, Except.toOption] using checked)

theorem printed (m : Solve.FMI3Model source) :
    (Runtime.function m signature).render = opening ++ quote message ++ closing := by
  simp [Runtime.function, Runtime.body, signature, Function.render, Signature.render,
    Parameter.render, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.reject, Runtime.branch, Runtime.negate, Runtime.allowedExpression,
    Runtime.either, Runtime.both, Runtime.eqv, Runtime.any, Runtime.field,
    Runtime.mode, permittedModes, Mode.code, Runtime.fail, Runtime.call,
    Runtime.ret, Runtime.v, Runtime.n, Runtime.x, Runtime.put, Runtime.setMode,
    Runtime.ok, CInitialization.Emission.statement, CInitialization.value_zero,
    Stmt.render, Expr.render, BinOp.render, opening, closing, message]
  decide +kernel

theorem render_denotes (m : Solve.FMI3Model source) :
    Denotes (Runtime.function m signature).render := by
  refine ⟨opening.toList, (quote message).toList, closing.toList, ?_,
    opening_lexes, CString.quote_correct message, closing_lexes⟩
  simp only [printed, String.toList_append]

end Rumoca.FMI3.Reset.Syntax
