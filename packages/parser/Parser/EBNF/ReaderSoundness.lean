import Parser.EBNF
import Parser.EBNF.Metalanguage

/-! Successful EBNF reading produces declaratively valid notation. The source
syntax relation is in a separate module with no reader dependency. -/
namespace Parser.EBNF.Reader
open Metalanguage

private theorem bind_ok {m : Except ε α} {k : α → Except ε β} {value : β}
    (result : (m >>= k) = .ok value) : ∃ x, m = .ok x ∧ k x = .ok value := by
  cases m with
  | error error => cases result
  | ok x => exact ⟨x, rfl, result⟩

theorem expect_iff (symbol : Char) (input rest : List Lexeme) :
    expect symbol input = .ok rest ↔ input = .punct symbol :: rest := by
  cases input with
  | nil => simp [expect]
  | cons token tail =>
    cases token with
    | name name => simp [expect]
    | text text => simp [expect]
    | punct char =>
      by_cases same : symbol = char
      · subst char; simp [expect]
      · simp [expect, same, Ne.symm same]

/-- First-token coverage for arbitrary trailing input, used by implicit
sequence completeness. The source syntax relation supplies the premise. -/
theorem primary_starts (h : Primary expr tokens) (rest : List Lexeme) :
    startsPrimary (tokens ++ rest) = true := by
  cases h <;> simp [startsPrimary]

theorem sequence_starts (h : Sequence expr tokens) (rest : List Lexeme) :
    startsPrimary (tokens ++ rest) = true := by
  cases h with
  | primary p => exact primary_starts p rest
  | comma p s => simpa only [List.append_assoc] using primary_starts p (_ ++ rest)
  | adjacent p s => simpa only [List.append_assoc] using primary_starts p (_ ++ rest)

theorem expression_starts (h : Expression expr tokens) (rest : List Lexeme) :
    startsPrimary (tokens ++ rest) = true := by
  cases h with
  | sequence s => exact sequence_starts s rest
  | alternative s e => simpa only [List.append_assoc] using sequence_starts s (_ ++ rest)

private def SoundAt
    (reader : Nat → List Lexeme → Except String (Expr × List Lexeme))
    (judgment : Expr → List Lexeme → Prop) (fuel : Nat) : Prop :=
  ∀ {input expr rest}, reader fuel input = .ok (expr, rest) →
    ∃ consumed, input = consumed ++ rest ∧ judgment expr consumed

private theorem readers_sound (fuel : Nat) :
    SoundAt expression Expression fuel ∧ SoundAt sequence Sequence fuel ∧
      SoundAt primary Primary fuel := by
  induction fuel with
  | zero =>
    simp [SoundAt, expression, sequence, primary]
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro input expr rest parsed
      unfold expression at parsed
      obtain ⟨⟨first, following⟩, firstRead, finish⟩ := bind_ok parsed
      obtain ⟨left, inputEq, firstSyntax⟩ := ih.2.1 firstRead
      dsimp only at finish
      split at finish
      ·
        obtain ⟨⟨second, tailRest⟩, secondRead, result⟩ := bind_ok finish
        obtain ⟨right, tailEq, secondSyntax⟩ := ih.1 secondRead
        cases Except.ok.inj result
        exact ⟨left ++ .punct '|' :: right,
          by simp [inputEq, tailEq, List.append_assoc],
          .alternative firstSyntax secondSyntax⟩
      · cases Except.ok.inj finish
        exact ⟨left, inputEq, .sequence firstSyntax⟩
    · intro input expr rest parsed
      unfold sequence at parsed
      obtain ⟨⟨first, following⟩, firstRead, finish⟩ := bind_ok parsed
      obtain ⟨left, inputEq, firstSyntax⟩ := ih.2.2 firstRead
      dsimp only at finish
      split at finish
      ·
        obtain ⟨⟨second, tailRest⟩, secondRead, result⟩ := bind_ok finish
        obtain ⟨right, tailEq, secondSyntax⟩ := ih.2.1 secondRead
        cases Except.ok.inj result
        exact ⟨left ++ .punct ',' :: right,
          by simp [inputEq, tailEq, List.append_assoc],
          .comma firstSyntax secondSyntax⟩
      · split at finish
        · obtain ⟨⟨second, tailRest⟩, secondRead, result⟩ := bind_ok finish
          obtain ⟨right, tailEq, secondSyntax⟩ := ih.2.1 secondRead
          cases Except.ok.inj result
          exact ⟨left ++ right, by simp [inputEq, tailEq, List.append_assoc],
            .adjacent firstSyntax secondSyntax⟩
        · cases Except.ok.inj finish
          exact ⟨left, inputEq, .primary firstSyntax⟩
    · intro input expr rest parsed
      cases input with
      | nil => simp [primary] at parsed
      | cons token tail =>
        cases token with
        | name name =>
          by_cases identifier : name = "IDENT"
          · subst name
            simp only [primary] at parsed
            cases Except.ok.inj parsed
            exact ⟨_, rfl, .identifier⟩
          · have result := (primary.eq_3 fuel name tail identifier).symm.trans parsed
            cases Except.ok.inj result
            exact ⟨_, rfl, .reference identifier⟩
        | text text =>
          simp only [primary] at parsed
          cases Except.ok.inj parsed
          exact ⟨_, rfl, .literal⟩
        | punct char =>
          by_cases group : char = '('
          · subst char
            simp only [primary] at parsed
            obtain ⟨⟨body, following⟩, bodyRead, finish⟩ := bind_ok parsed
            obtain ⟨tailRest, closing, result⟩ := bind_ok finish
            obtain ⟨inside, tailEq, bodySyntax⟩ := ih.1 bodyRead
            have followingEq := (expect_iff _ _ _).mp closing
            dsimp only at followingEq
            cases Except.ok.inj result
            exact ⟨.punct '(' :: inside ++ [.punct ')'],
              by simp [tailEq, followingEq, List.append_assoc], .group bodySyntax⟩
          · by_cases optional : char = '['
            · subst char
              simp only [primary] at parsed
              obtain ⟨⟨body, following⟩, bodyRead, finish⟩ := bind_ok parsed
              obtain ⟨tailRest, closing, result⟩ := bind_ok finish
              obtain ⟨inside, tailEq, bodySyntax⟩ := ih.1 bodyRead
              have followingEq := (expect_iff _ _ _).mp closing
              dsimp only at followingEq
              cases Except.ok.inj result
              exact ⟨.punct '[' :: inside ++ [.punct ']'],
                by simp [tailEq, followingEq, List.append_assoc], .optional bodySyntax⟩
            · by_cases many : char = '{'
              · subst char
                simp only [primary] at parsed
                obtain ⟨⟨body, following⟩, bodyRead, finish⟩ := bind_ok parsed
                obtain ⟨tailRest, closing, result⟩ := bind_ok finish
                obtain ⟨inside, tailEq, bodySyntax⟩ := ih.1 bodyRead
                have followingEq := (expect_iff _ _ _).mp closing
                dsimp only at followingEq
                cases Except.ok.inj result
                exact ⟨.punct '{' :: inside ++ [.punct '}'],
                  by simp [tailEq, followingEq, List.append_assoc], .many bodySyntax⟩
              · rw [primary.eq_def] at parsed
                simp [group, optional, many] at parsed

theorem expression_sound (parsed : expression fuel input = .ok (expr, rest)) :
    ∃ consumed, input = consumed ++ rest ∧ Expression expr consumed :=
  (readers_sound fuel).1 parsed

theorem sequence_sound (parsed : sequence fuel input = .ok (expr, rest)) :
    ∃ consumed, input = consumed ++ rest ∧ Sequence expr consumed :=
  (readers_sound fuel).2.1 parsed

theorem primary_sound (parsed : primary fuel input = .ok (expr, rest)) :
    ∃ consumed, input = consumed ++ rest ∧ Primary expr consumed :=
  (readers_sound fuel).2.2 parsed

theorem rules_sound (parsed : rules fuel input = .ok grammar) :
    Rules grammar input ∧ NamesValid grammar := by
  induction fuel generalizing input grammar with
  | zero => simp [rules] at parsed
  | succ fuel ih =>
    cases input with
    | nil =>
      simp only [rules] at parsed
      cases Except.ok.inj parsed
      exact ⟨.nil, namesValid_nil⟩
    | cons first tail =>
      cases first with
      | text text => simp [rules] at parsed
      | punct char => simp [rules] at parsed
      | name name =>
        cases tail with
        | nil => simp [rules] at parsed
        | cons separator input =>
          cases separator with
          | name name => simp [rules] at parsed
          | text text => simp [rules] at parsed
          | punct sep =>
            simp only [rules] at parsed
            split at parsed
            · contradiction
            · rename_i allowed
              have separator : sep = '=' ∨ sep = ':' := by
                by_cases equal : sep = '='
                · exact .inl equal
                · by_cases other : sep = ':'
                  · exact .inr other
                  · simp [equal, other] at allowed
              simp only [pure_bind] at parsed
              split at parsed
              · contradiction
              · rename_i ordinary
                have nameAllowed : name ≠ "IDENT" := by simpa using ordinary
                obtain ⟨⟨body, following⟩, bodyRead, finish⟩ := bind_ok parsed
                obtain ⟨remaining, closing, finish⟩ := bind_ok finish
                obtain ⟨rest, restRead, finish⟩ := bind_ok finish
                split at finish
                · contradiction
                · rename_i fresh
                  obtain ⟨bodyTokens, inputEq, bodySyntax⟩ := expression_sound bodyRead
                  have followingEq := (expect_iff _ _ _).mp closing
                  dsimp only at followingEq
                  have restSyntax := ih restRead
                  cases Except.ok.inj finish
                  constructor
                  · simpa only [inputEq, followingEq] using
                      Rules.cons separator bodySyntax restSyntax.1 (name := name)
                  · apply namesValid_cons.mpr
                    refine ⟨nameAllowed, ?_, restSyntax.2⟩
                    intro member
                    obtain ⟨rule, belongs, same⟩ := List.mem_map.mp member
                    apply fresh
                    exact List.any_eq_true.mpr ⟨rule, belongs, by simpa using same⟩

end Parser.EBNF.Reader

namespace Parser.EBNF

theorem parseTokens_sound (parsed : parseTokens input = .ok grammar) :
    Metalanguage.DenotesTokens input grammar := by
  unfold parseTokens at parsed
  obtain ⟨candidate, readRules, finish⟩ := Reader.bind_ok parsed
  split at finish
  · contradiction
  · rename_i nonempty
    cases Except.ok.inj finish
    have checked := Reader.rules_sound readRules
    exact ⟨checked.1, checked.2, by simpa using nonempty⟩

/-- Source lexing remains a separate obligation; this theorem proves notation
soundness for the exact tokens produced by the actual public reader. -/
theorem parse_syntax_sound (parsed : parse source = .ok grammar) :
    ∃ tokens, lex source = .ok tokens ∧ Metalanguage.DenotesTokens tokens grammar := by
  unfold parse at parsed
  obtain ⟨tokens, lexed, read⟩ := Reader.bind_ok parsed
  exact ⟨tokens, lexed, parseTokens_sound read⟩

end Parser.EBNF
