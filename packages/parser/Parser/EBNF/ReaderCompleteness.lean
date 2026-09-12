import Parser.EBNF.ReaderSoundness

/-! Completeness of the EBNF token reader against independent notation syntax.
The phase bounds below discharge the reader's actual input-size budgets;
callers of the public grammar reader supply neither fuel nor a parse oracle. -/
namespace Parser.EBNF.Reader
open Metalanguage

private def SequenceEnd (rest : List Lexeme) : Prop :=
  startsPrimary rest = false ∧ rest.head? ≠ some (.punct ',')

private def ExpressionEnd (rest : List Lexeme) : Prop :=
  SequenceEnd rest ∧ rest.head? ≠ some (.punct '|')

private theorem expression_done
    (first : sequence fuel input = .ok (expr, rest))
    (stop : rest.head? ≠ some (.punct '|')) :
    expression (fuel + 1) input = .ok (expr, rest) := by
  unfold expression
  rw [first]
  simp only [bind, Except.bind]
  split <;> simp_all [pure, Except.pure]

private theorem sequence_done
    (first : primary fuel input = .ok (expr, rest)) (stop : SequenceEnd rest) :
    sequence (fuel + 1) input = .ok (expr, rest) := by
  unfold sequence
  rw [first]
  simp only [bind, Except.bind]
  split <;> simp_all [SequenceEnd, pure, Except.pure]

private def CompleteAt
    (reader : Nat → List Lexeme → Except String (Expr × List Lexeme))
    (judgment : Expr → List Lexeme → Prop) (follow : List Lexeme → Prop)
    (phase fuel : Nat) : Prop :=
  ∀ {expr tokens rest}, judgment expr tokens → follow rest →
    4 * (tokens ++ rest).length + phase ≤ fuel →
    reader fuel (tokens ++ rest) = .ok (expr, rest)

private theorem readers_complete (fuel : Nat) :
    CompleteAt expression Expression ExpressionEnd 3 fuel ∧
    CompleteAt sequence Sequence SequenceEnd 2 fuel ∧
    CompleteAt primary Primary (fun _ => True) 1 fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro expr tokens rest valid follow budget <;> omega
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro expr tokens rest valid follow budget
      cases valid with
      | sequence valid =>
        exact expression_done (ih.2.1 valid follow.1 (by omega)) follow.2
      | @alternative a left b right first second =>
        have leftRead := ih.2.1 first (rest := .punct '|' :: (right ++ rest))
          (by simp [SequenceEnd, startsPrimary])
          (by
            simp only [List.length_append, List.length_cons] at budget ⊢
            omega)
        have rightRead := ih.1 second follow (by
          simp only [List.length_append, List.length_cons] at budget ⊢
          omega)
        simp only [List.append_assoc, List.cons_append]
        unfold expression
        rw [leftRead]
        simp [rightRead, bind, Except.bind, pure, Except.pure]
    · intro expr tokens rest valid follow budget
      cases valid with
      | primary valid => exact sequence_done (ih.2.2 valid trivial (by omega)) follow
      | @comma a left b right first second =>
        have leftRead := ih.2.2 first (rest := .punct ',' :: (right ++ rest)) trivial (by
          simp only [List.length_append, List.length_cons] at budget ⊢
          omega)
        have rightRead := ih.2.1 second follow (by
          simp only [List.length_append, List.length_cons] at budget ⊢
          omega)
        simp only [List.append_assoc, List.cons_append]
        unfold sequence
        rw [leftRead]
        simp [rightRead, bind, Except.bind, pure, Except.pure]
      | @adjacent a left b right first second =>
        have nonempty := first.nonempty
        have positive : 0 < left.length := List.length_pos_iff.mpr nonempty
        have leftRead := ih.2.2 first (rest := right ++ rest) trivial (by
          simp only [List.length_append] at budget ⊢
          omega)
        have rightRead := ih.2.1 second follow (by
          simp only [List.length_append] at budget ⊢
          omega)
        have starts := sequence_starts second rest
        simp only [List.append_assoc]
        unfold sequence
        rw [leftRead]
        simp only [bind, Except.bind]
        split
        · rename_i tail equal
          simp [equal, startsPrimary] at starts
        · simp [starts, rightRead, pure, Except.pure]
    · intro expr tokens rest valid _ budget
      cases valid with
      | identifier => rfl
      | reference ordinary =>
        exact primary.eq_3 fuel _ rest ordinary
      | literal => rfl
      | group valid =>
        have body := ih.1 valid (rest := .punct ')' :: rest)
          (by simp [ExpressionEnd, SequenceEnd, startsPrimary]) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at budget ⊢
            omega)
        simp only [List.cons_append, List.append_assoc]
        rw [primary.eq_def]
        simp [body, expect, bind, Except.bind, pure, Except.pure]
      | optional valid =>
        have body := ih.1 valid (rest := .punct ']' :: rest)
          (by simp [ExpressionEnd, SequenceEnd, startsPrimary]) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at budget ⊢
            omega)
        simp only [List.cons_append, List.append_assoc]
        rw [primary.eq_def]
        simp [body, expect, bind, Except.bind, pure, Except.pure]
      | many valid =>
        have body := ih.1 valid (rest := .punct '}' :: rest)
          (by simp [ExpressionEnd, SequenceEnd, startsPrimary]) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at budget ⊢
            omega)
        simp only [List.cons_append, List.append_assoc]
        rw [primary.eq_def]
        simp [body, expect, bind, Except.bind, pure, Except.pure]

/-- A complete expression is accepted at the documented input-size budget. -/
theorem expression_complete (valid : Expression expr tokens)
    (budget : 4 * tokens.length + 3 ≤ fuel) :
    expression fuel tokens = .ok (expr, []) := by
  have result := (readers_complete fuel).1 valid (rest := [])
    (by simp [ExpressionEnd, SequenceEnd, startsPrimary]) (by simpa using budget)
  simpa using result

/-- Every declaratively valid rule list is read using the actual rule budget.
Name uniqueness and the reserved lexical category are checked independently. -/
theorem rules_complete (valid : Rules grammar tokens) (names : NamesValid grammar)
    (budget : tokens.length + 1 ≤ fuel) : rules fuel tokens = .ok grammar := by
  induction valid generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at budget
    | succ fuel => rfl
  | @cons sep expr bodyTokens grammar suffix name separator body rest ih =>
    obtain ⟨ordinary, fresh, names⟩ := namesValid_cons.mp names
    cases fuel with
    | zero => omega
    | succ fuel =>
      have bodyRead := (readers_complete ((bodyTokens ++ .punct ';' :: suffix).length * 4 + 4)).1
        body (rest := .punct ';' :: suffix)
        (by simp [ExpressionEnd, SequenceEnd, startsPrimary]) (by omega)
      have restRead := ih names (fuel := fuel) (by
        simp only [List.length_cons, List.length_append] at budget ⊢
        omega)
      have unique : grammar.any (fun rule => rule.1 == name) = false := by
        apply List.any_eq_false.mpr
        intro rule member
        have different : rule.1 ≠ name := by
          intro same
          exact fresh (List.mem_map.mpr ⟨rule, member, same⟩)
        simpa using different
      simp only [List.length_append, List.length_cons] at bodyRead
      rcases separator with rfl | rfl <;>
        simp [rules, ordinary, bodyRead, expect, restRead, unique,
          bind, Except.bind, pure, Except.pure]

end Parser.EBNF.Reader

namespace Parser.EBNF

/-- Completeness of the public token reader, with no extra execution premise. -/
theorem parseTokens_complete (valid : Metalanguage.DenotesTokens tokens grammar) :
    parseTokens tokens = .ok grammar := by
  have read := Reader.rules_complete valid.1 valid.2.1 (Nat.le_refl (tokens.length + 1))
  simp [parseTokens, read, valid.2.2, bind, Except.bind, pure, Except.pure]

theorem parseTokens_iff : parseTokens tokens = .ok grammar ↔
    Metalanguage.DenotesTokens tokens grammar :=
  ⟨parseTokens_sound, parseTokens_complete⟩

end Parser.EBNF
