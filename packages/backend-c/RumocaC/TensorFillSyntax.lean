import RumocaC.TensorFillCode
import RumocaC.TensorSyntax

/-! Independent complete token grammar for the fill helper. The actual
structured printer is checked against the existing shared C scanner. -/
namespace Rumoca.CTensor.Fill.Syntax
open _root_.Parser

def tokens : List Token :=
  (["void", "rumoca_tensor_fill", "(", "double", "value", ",", "double", "*", "out", ",",
    "size_t", "count", ")", "{", "size_t", "k", "=", "0", ";",
    "while", "(", "(", "k", "<", "count", ")", ")", "{",
    "out", "[", "k", "]", "=", "value", ";",
    "k", "=", "(", "k", "+", "1", ")", ";", "}", "return", ";", "}"] : List String).map Token.literal

def Denotes (source : String) : Prop := Scanner.Lexes CTensor.Syntax.config source.toList tokens

macro "tensor_expand_fill_printer" : tactic => `(tactic|
  simp [function, indexed, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

set_option maxRecDepth 10000

theorem render_denotes : Denotes function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex CTensor.Syntax.config function.render).toOption = some tokens := by
    tensor_expand_fill_printer
    decide +kernel
  cases hl : Scanner.lex CTensor.Syntax.config function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

end Rumoca.CTensor.Fill.Syntax
