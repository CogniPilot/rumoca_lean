import RumocaC.TensorFiniteScanCode
import RumocaC.TensorSyntax

/-! Independent token grammar for the shared whole-tensor finiteness scanner.
The scanner is deliberately specified separately from the structured printer;
the intrinsic `isfinite` remains part of the declared C boundary. -/
namespace Rumoca.CTensor.FiniteScan.Syntax
open _root_.Parser

def config : Scanner.Config :=
  { wordStart := identStart
    wordRest := identRest
    numberRest := fun c => identRest c || c == '.'
    classify := Token.literal
    single := fun c => ['(', ')', '{', '}', '[', ']', '*', '/', '-', ';', '=', '+', '<', ',', '!'].contains c
    pair := fun _ => none }

def tokens : List Token :=
  (["int32_t", "rumoca_tensor_all_finite", "(", "const", "double", "*", "values", ",",
    "size_t", "count", ")", "{", "int32_t", "valid", "=", "1", ";", "size_t", "k", "=", "0", ";",
    "while", "(", "(", "k", "<", "count", ")", ")", "{", "if", "(", "(", "!", "isfinite", "(",
    "values", "[", "k", "]", ")", ")", ")", "{", "valid", "=", "0", ";", "}", "k", "=", "(",
    "k", "+", "1", ")", ";", "}", "return", "valid", ";", "}"] : List String).map Token.literal

def Denotes (source : String) : Prop := Scanner.Lexes config source.toList tokens

macro "tensor_expand_finite_scan_printer" : tactic => `(tactic|
  simp [FiniteScan.function, FiniteScan.iteration, FiniteScan.iterationFor, indexed, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes : Denotes FiniteScan.function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex config FiniteScan.function.render).toOption = some tokens := by
    tensor_expand_finite_scan_printer
    decide +kernel
  cases hl : Scanner.lex config FiniteScan.function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he


end Rumoca.CTensor.FiniteScan.Syntax
