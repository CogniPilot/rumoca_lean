import RumocaC.Syntax

open _root_.Parser

/-! Structural printer correctness against the independent C character/token
grammar. No executable C reader is used to prove text membership. -/
namespace Rumoca.CSyntax

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

macro "numerical_c_lex_fixed" : tactic => `(tactic|
  repeat first
  | assumption
  | exact Lexes.nil
  | apply Lexes.space (by decide +kernel)
  | apply Lexes.word (by decide +kernel) (by decide +kernel)
  | apply Lexes.number (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | apply Lexes.ne
  | apply Lexes.punct (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))

theorem expression_render (e : C.Expr) (c : Char) (rest : List Char) (ts : List String)
    (stop : numberRest c = false) (h : Lexes (c :: rest) ts) :
    Lexes ((C.renderExpr e).toList ++ c :: rest) (exprTokens e ++ ts) := by
  induction e generalizing c rest ts with
  | one =>
    have take : ('.' :: '0' :: c :: rest).takeWhile numberRest = ['.', '0'] := by
      simp only [List.takeWhile_cons, show numberRest '.' = true from rfl,
        show numberRest '0' = true from rfl, stop, Bool.false_eq_true, ↓reduceIte]
    have drop : ('.' :: '0' :: c :: rest).dropWhile numberRest = c :: rest := by
      simp only [List.dropWhile_cons, show numberRest '.' = true from rfl,
        show numberRest '0' = true from rfl, stop, Bool.false_eq_true, ↓reduceIte]
    have step := Lexes.number (c := '1') (cs := '.' :: '0' :: c :: rest)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (drop ▸ h)
    simpa only [take, C.renderExpr, exprTokens, List.cons_append, List.nil_append] using step
  | arg =>
    have hi : identRest c = false := (Bool.or_eq_false_iff.mp stop).1
    have step := Lexes.word (c := 'x') (cs := c :: rest)
      (by decide +kernel) (by decide +kernel)
      (by simpa only [List.dropWhile_cons, hi, Bool.false_eq_true, ↓reduceIte] using h)
    simpa only [List.takeWhile_cons, hi, Bool.false_eq_true, ↓reduceIte, C.renderExpr,
      exprTokens, List.cons_append, List.nil_append] using step
  | add a b ha hb =>
    simp only [C.renderExpr, String.toList_append, exprTokens, List.cons_append,
      List.nil_append, List.append_assoc]
    numerical_c_lex_fixed
    apply ha ' ' _ _ (by decide +kernel)
    numerical_c_lex_fixed
    apply hb ')' _ _ (by decide +kernel)
    numerical_c_lex_fixed

theorem module_render (module : C.Module) : Denotes (C.render module) (fromTarget module) := by
  simp only [Denotes, C.render, String.toList_append, List.append_assoc]
  refine ⟨_, rfl, ?_⟩
  simp only [Program.tokens, fromTarget, rhsPrefix, stepPrefix, samplePrefix, sampleSuffix,
    List.cons_append, List.nil_append, List.append_assoc]
  numerical_c_lex_fixed
  apply expression_render module.rhs ';' _ _ (by decide +kernel)
  numerical_c_lex_fixed
  apply expression_render module.step ';' _ _ (by decide +kernel)
  numerical_c_lex_fixed
  apply expression_render module.step ';' _ _ (by decide +kernel)
  numerical_c_lex_fixed

end Rumoca.CSyntax
