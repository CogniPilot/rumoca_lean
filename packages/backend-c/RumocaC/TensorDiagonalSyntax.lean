import RumocaC.TensorDiagonalCode
import RumocaC.TensorSyntax

/-! Independently specified complete C tokens for the diagonal helper,
checked against the structured printer through the verified shared scanner. -/
namespace Rumoca.CTensor.Diagonal.Syntax
open _root_.Parser

def tokens : List Token :=
  (["void", "rumoca_tensor_diagonal", "(", "const", "double", "*", "coeff", ",", "double", "*", "out", ",",
    "size_t", "count", ",", "size_t", "cells", ")", "{",
    "rumoca_tensor_fill", "(", "(", "(", "double", ")", "0", ")", ",", "out", ",", "cells", ")", ";",
    "size_t", "offset", "=", "0", ";", "size_t", "stride", "=", "(", "count", "+", "1", ")", ";",
    "size_t", "k", "=", "0", ";", "while", "(", "(", "k", "<", "count", ")", ")", "{",
    "out", "[", "offset", "]", "=", "coeff", "[", "k", "]", ";",
    "offset", "=", "(", "offset", "+", "stride", ")", ";",
    "k", "=", "(", "k", "+", "1", ")", ";", "}", "return", ";", "}"] : List String).map Token.literal

def Denotes (source : String) : Prop := Scanner.Lexes CTensor.Syntax.config source.toList tokens

macro "tensor_expand_diagonal_printer" : tactic => `(tactic|
  simp [function, signatureParameters, Lowering.Syntax.Parameter.tree, Lowering.Syntax.ParamKind.type,
    tail, operation, Fill.invoke, Fill.function, CAlgorithm.literal, indexed,
    CLoops.counted, CLoops.loop, CLoops.counterStep, CTree.Function.render, CTree.Signature.render,
    CTree.Parameter.render, CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

set_option maxRecDepth 10000

theorem render_denotes : Denotes function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex CTensor.Syntax.config function.render).toOption = some tokens := by
    tensor_expand_diagonal_printer
    decide +kernel
  cases hl : Scanner.lex CTensor.Syntax.config function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have eq : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok eq

end Rumoca.CTensor.Diagonal.Syntax
