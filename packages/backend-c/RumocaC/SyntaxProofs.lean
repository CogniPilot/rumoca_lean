import RumocaC.Syntax

open _root_.Parser

/-! Uniqueness of the independent C grammar's denotation. This replaces the
use of an executable parser's determinism in the compiler's property theorem. -/
namespace Rumoca.CSyntax

theorem lexes_unique (ha : Lexes cs as) (hb : Lexes cs bs) : as = bs := by
  induction ha generalizing bs <;> cases hb <;>
    try simp_all only [List.cons.injEq, true_and, Bool.false_eq_true, Bool.true_eq_false]
  all_goals first
    | solve_by_elim
    | simp_all [asciiSpace, identStart, asciiLetter]

theorem expression_tokens_unique (a b : C.Expr) (xs ys : List String)
    (h : exprTokens a ++ xs = exprTokens b ++ ys) : a = b ∧ xs = ys := by
  induction a generalizing b xs ys with
  | one => cases b <;> simp_all [exprTokens]
  | arg => cases b <;> simp_all [exprTokens]
  | add a₁ a₂ ih₁ ih₂ =>
    cases b with
    | one | arg => simp [exprTokens] at h
    | add b₁ b₂ =>
      simp only [exprTokens, List.cons_append, List.nil_append, List.append_assoc] at h
      obtain ⟨rfl, ht⟩ := ih₁ b₁ _ _ (List.cons.inj h).2
      obtain ⟨rfl, ht'⟩ := ih₂ b₂ _ _ (List.cons.inj ht).2
      exact ⟨rfl, (List.cons.inj ht').2⟩

theorem program_tokens_unique (a b : Program) (h : a.tokens = b.tokens) : a = b := by
  simp only [Program.tokens, List.append_assoc] at h
  have hr := (List.append_right_inj rhsPrefix).mp h
  obtain ⟨rhs, hr⟩ := expression_tokens_unique a.rhs b.rhs _ _ hr
  have hs := (List.append_right_inj stepPrefix).mp hr
  obtain ⟨step, hs⟩ := expression_tokens_unique a.step b.step _ _ hs
  have ht := (List.append_right_inj samplePrefix).mp hs
  obtain ⟨sample, _⟩ := expression_tokens_unique a.sample b.sample _ _ ht
  cases a; cases b
  simp_all

theorem denotes_unique (ha : Denotes text a) (hb : Denotes text b) : a = b := by
  obtain ⟨ca, ha, la⟩ := ha
  obtain ⟨cb, hb, lb⟩ := hb
  have hc := (List.append_right_inj C.preamble.toList).mp (ha.symm.trans hb)
  cases hc
  exact program_tokens_unique a b (lexes_unique la lb)

end Rumoca.CSyntax
