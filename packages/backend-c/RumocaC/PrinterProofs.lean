import RumocaC.Syntax

open _root_.Parser

/-! Structural printer correctness against the independent C character/token
grammar. No executable C reader is used to prove text membership.

The lexing tactic discharges each character-class side condition by definitional
reflexivity on the concrete leading character, so no `Decidable` instance search
or kernel decision procedure runs per token. The fixed function scaffold is
reduced from its rendered string literals to explicit character lists once, with
the `String.toList` simproc, before it is lexed; this keeps the proof cost bounded
by the scaffold and independent of the repeated `String.toList` unfolding that a
whole-program reflexivity over the rendered text would incur. -/
namespace Rumoca.CSyntax

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Advance the grammar one concrete token at a time. Every side condition is a
closed fact about the leading character, so `rfl` discharges it by computation
without a `Decidable` instance or a kernel decision procedure. The punctuator and
`!=` cases precede the word and number cases so a single-character token never
forces a maximal-munch scan it does not need. -/
macro "numerical_c_lex_fixed" : tactic => `(tactic|
  repeat first
  | assumption
  | exact Lexes.nil
  | apply Lexes.space (by rfl)
  | apply Lexes.ne
  | apply Lexes.punct (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  | apply Lexes.number (by rfl) (by rfl) (by rfl)
  | apply Lexes.word (by rfl) (by rfl))

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
      (by rfl) (by rfl) (by rfl) (drop ▸ h)
    simpa only [take, C.renderExpr, exprTokens, List.cons_append, List.nil_append] using step
  | arg =>
    have hi : identRest c = false := (Bool.or_eq_false_iff.mp stop).1
    have step := Lexes.word (c := 'x') (cs := c :: rest)
      (by rfl) (by rfl)
      (by simpa only [List.dropWhile_cons, hi, Bool.false_eq_true, ↓reduceIte] using h)
    simpa only [List.takeWhile_cons, hi, Bool.false_eq_true, ↓reduceIte, C.renderExpr,
      exprTokens, List.cons_append, List.nil_append] using step
  | add a b ha hb =>
    simp only [C.renderExpr, String.toList_append, exprTokens, List.cons_append,
      List.nil_append, List.append_assoc]
    numerical_c_lex_fixed
    apply ha ' ' _ _ (by rfl)
    numerical_c_lex_fixed
    apply hb ')' _ _ (by rfl)
    numerical_c_lex_fixed

theorem module_render (module : C.Module) (linkage : C.Linkage := .external) :
    Denotes (C.render module linkage) (fromTarget module) linkage := by
  cases linkage <;>
    simp only [Denotes, C.render, C.Linkage.render, String.toList_append,
      String.reduceToList, List.cons_append, List.nil_append, List.append_assoc]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals simp only [Program.tokens, fromTarget, rhsPrefix, stepPrefix, samplePrefix, sampleSuffix,
    linkageTokens,
    List.cons_append, List.nil_append, List.append_assoc]
  all_goals
    numerical_c_lex_fixed
    apply expression_render module.rhs ';' _ _ (by rfl)
    numerical_c_lex_fixed
    apply expression_render module.step ';' _ _ (by rfl)
    numerical_c_lex_fixed
    apply expression_render module.step ';' _ _ (by rfl)
    numerical_c_lex_fixed

end Rumoca.CSyntax
