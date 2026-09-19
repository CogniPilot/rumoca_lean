import RumocaC.TensorCode
import Parser.Scanner

/-! Independent concrete syntax for the four counted tensor helpers. The token
grammar spells out their parameters, unsigned local, loop, indexed assignment,
increment and return. It does not call the emitter. Header preprocessing and
the meanings of `size_t` and `double` remain the declared target boundary. -/
namespace Rumoca.CTensor.Syntax
open _root_.Parser

def config : Scanner.Config where
  wordStart := identStart
  wordRest := identRest
  numberRest := fun c => identRest c || c == '.'
  classify := Token.literal
  single := fun c => ['(', ')', '{', '}', '[', ']', '*', '/', '-', ';', '=', '+', '<', ','].contains c
  pair := fun _ => none

def tokens (op : Tensor.BinaryOp) : List Token :=
  (["void", match op with
      | .add => "rumoca_tensor_add" | .mul => "rumoca_tensor_mul"
      | .sub => "rumoca_tensor_sub" | .div => "rumoca_tensor_div",
    "(", "const", "double", "*", "left", ",", "const", "double", "*", "right", ",",
    "double", "*", "out", ",", "size_t", "count", ")", "{",
    "size_t", "k", "=", "0", ";",
    "while", "(", "(", "k", "<", "count", ")", ")", "{",
    "out", "[", "k", "]", "=", "(", "left", "[", "k", "]",
    match op with | .add => "+" | .mul => "*" | .sub => "-" | .div => "/",
    "right", "[", "k", "]", ")", ";",
    "k", "=", "(", "k", "+", "1", ")", ";", "}", "return", ";", "}"] : List String).map Token.literal

def Denotes (source : String) (op : Tensor.BinaryOp) : Prop :=
  Scanner.Lexes config source.toList (tokens op)

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Unfold only the structured helper printer. Its well-founded statement
recursor is rewritten by its checked equations before reducing fixed text. -/
macro "tensor_expand_printer" : tactic => `(tactic|
  simp [function, body, operation, indexed, binaryOp, CLoops.counted, CLoops.loop,
    CLoops.counterStep, CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

/-- The actual structured printer emits the independently specified syntax. -/
theorem render_denotes (op : Tensor.BinaryOp) : Denotes (function op).render op := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex config (function op).render).toOption = some (tokens op) := by
    cases op <;> tensor_expand_printer <;> decide +kernel
  cases hl : Scanner.lex config (function op).render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens op := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

theorem denotes_unique {source : String} {a b : Tensor.BinaryOp}
    (ha : Denotes source a) (hb : Denotes source b) : a = b := by
  have h := Except.ok.inj (((Scanner.lex_correct _ _ _).mpr ha).symm.trans
    ((Scanner.lex_correct _ _ _).mpr hb))
  cases a <;> cases b <;> simp_all [tokens]

end Rumoca.CTensor.Syntax
