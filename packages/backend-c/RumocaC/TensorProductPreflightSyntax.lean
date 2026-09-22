import RumocaC.TensorProductPreflightCode
import RumocaC.TensorFiniteScanSyntax

/-! Independent token specification of the multiplication preflight. -/
namespace Rumoca.CTensor.ProductPreflight.Syntax
open _root_.Parser

def tokens : List Token :=
  (["int32_t", "rumoca_tensor_mul_finite", "(", "const", "double", "*", "left", ",",
    "const", "double", "*", "right", ",", "size_t", "count", ")", "{",
    "double", "sample", "=", "0e0", ";",
    "int32_t", "valid", "=", "1", ";", "size_t", "k", "=", "0", ";",
    "while", "(", "(", "k", "<", "count", ")", ")", "{", "sample", "=",
    "(", "left", "[", "k", "]", "*", "right", "[", "k", "]", ")", ";",
    "if", "(", "(", "!", "isfinite", "(", "sample", ")", ")", ")", "{",
    "valid", "=", "0", ";", "}", "k", "=", "(", "k", "+", "1", ")", ";", "}",
    "return", "valid", ";", "}"] : List String).map Token.literal

def Denotes (source : String) : Prop :=
  Scanner.Lexes FiniteScan.Syntax.config source.toList tokens

macro "tensor_expand_product_preflight_printer" : tactic => `(tactic|
  simp [ProductPreflight.function, ProductPreflight.value, FinitePreflight.body,
    FinitePreflight.iteration, FiniteScan.iterationFor, indexed, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes : Denotes ProductPreflight.function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex FiniteScan.Syntax.config ProductPreflight.function.render).toOption =
      some tokens := by
    tensor_expand_product_preflight_printer
    decide +kernel
  cases hl : Scanner.lex FiniteScan.Syntax.config ProductPreflight.function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

end Rumoca.CTensor.ProductPreflight.Syntax
