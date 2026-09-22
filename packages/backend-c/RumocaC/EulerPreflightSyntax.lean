import RumocaC.EulerPreflightCode
import RumocaC.TensorFiniteScanSyntax

/-! Independent fixed token specification of the scalar C preflight. This
scanner configuration adds != to the existing FiniteScan token profile. This is not a claim to recognize the complete C language. -/
namespace Rumoca.CEulerPreflight.Syntax
open _root_.Parser

def config : Scanner.Config :=
  { CTensor.FiniteScan.Syntax.config with
    pair := fun c => if c == '!' then some '=' else none }

def tokens : List Token :=
  (["int32_t", "rumoca_euler_finite", "(", "double", "initial", ",", "double", "rate", ",",
    "size_t", "count", ")", "{",
    "double", "sample", "=", "initial", ";", "double", "candidate", "=", "initial", ";",
    "int32_t", "valid", "=", "1", ";", "size_t", "n", "=", "0", ";",
    "while", "(", "(", "n", "<", "count", ")", ")", "{",
    "if", "(", "(", "valid", "!=", "0", ")", ")", "{",
    "candidate", "=", "(", "sample", "+", "rate", ")", ";",
    "if", "(", "(", "!", "isfinite", "(", "candidate", ")", ")", ")", "{",
    "valid", "=", "0", ";", "}",
    "if", "(", "(", "valid", "!=", "0", ")", ")", "{",
    "sample", "=", "candidate", ";", "}", "}",
    "n", "=", "(", "n", "+", "1", ")", ";", "}", "return", "valid", ";", "}"] : List String).map
      Token.literal

def Denotes (source : String) : Prop := Scanner.Lexes config source.toList tokens

macro "euler_expand_preflight_printer" : tactic => `(tactic|
  simp [CEulerPreflight.function, segment, iteration, active, copySample, guard,
    CTensor.FiniteScan.iterationFor, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes : Denotes CEulerPreflight.function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex config CEulerPreflight.function.render).toOption = some tokens := by
    euler_expand_preflight_printer
    decide +kernel
  cases hl : Scanner.lex config CEulerPreflight.function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

end Rumoca.CEulerPreflight.Syntax
