import RumocaC.TensorFinitePreflightCode
import RumocaC.TensorFiniteScanSyntax

/-! Independent token specification of the read-only preflight of a shared
binary tensor operation, given its function name and operator spelling. -/
namespace Rumoca.CTensor.FinitePreflight.Syntax
open _root_.Parser

def tokens (name operator : String) : List Token :=
  (["int32_t", name, "(", "const", "double", "*", "left", ",",
    "const", "double", "*", "right", ",", "size_t", "count", ")", "{",
    "double", "sample", "=", "0e0", ";",
    "int32_t", "valid", "=", "1", ";", "size_t", "k", "=", "0", ";",
    "while", "(", "(", "k", "<", "count", ")", ")", "{", "sample", "=",
    "(", "left", "[", "k", "]", operator, "right", "[", "k", "]", ")", ";",
    "if", "(", "(", "isfinite", "(", "sample", ")", "==", "0", ")", ")", "{",
    "valid", "=", "0", ";", "}", "k", "=", "(", "k", "+", "1", ")", ";", "}",
    "return", "valid", ";", "}"] : List String).map Token.literal

def Denotes (name operator source : String) : Prop :=
  Scanner.Lexes FiniteScan.Syntax.config source.toList (tokens name operator)

/-- Lexing the printed text to the operation tokens establishes their denotation. -/
theorem denotes_of_lex {name operator source : String}
    (lexed : (Scanner.lex FiniteScan.Syntax.config source).toOption = some (tokens name operator)) :
    Denotes name operator source := by
  apply (Scanner.lex_correct _ _ _).mp
  cases found : Scanner.lex FiniteScan.Syntax.config source with
  | error e => simp [found, Except.toOption] at lexed
  | ok ts =>
    have same : ts = tokens name operator := by
      simpa only [found, Except.toOption, Option.some.injEq] using lexed
    exact congrArg Except.ok same

macro "tensor_expand_operation_preflight_printer" : tactic => `(tactic|
  simp [FinitePreflight.operation, FinitePreflight.coordinate, FinitePreflight.body,
    FinitePreflight.segment, FinitePreflight.segmentWith,
    FinitePreflight.iteration, FiniteScan.iterationFor, CTree.Expr.nonfinite, indexed, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

end Rumoca.CTensor.FinitePreflight.Syntax
