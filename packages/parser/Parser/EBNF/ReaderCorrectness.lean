import Parser.EBNF.ReaderCompleteness
import Parser.EBNF.LexerSoundness

/-! The actual EBNF text reader is sound and complete for independent character
and notation syntax. Its public entry supplies all execution budgets itself.
Rejection is characterized semantically; error wording is not a promised API. -/
namespace Parser.EBNF

theorem parse_sound (parsed : parse source = .ok grammar) :
    Metalanguage.Denotes source grammar := by
  obtain ⟨tokens, lexed, valid⟩ := parse_syntax_sound parsed
  exact ⟨tokens, lex_sound lexed, valid⟩

theorem parse_complete (valid : Metalanguage.Denotes source grammar) :
    parse source = .ok grammar := by
  obtain ⟨tokens, lexical, syntactic⟩ := valid
  rw [parse_of_lex (lex_complete lexical)]
  exact parseTokens_complete syntactic

theorem parse_iff : parse source = .ok grammar ↔ Metalanguage.Denotes source grammar :=
  ⟨parse_sound, parse_complete⟩

/-- All source strings are covered. A rejected input has no denotation in the
supported dialect; a valid input never requires a larger caller-supplied budget. -/
theorem parse_rejected_iff : (∃ message, parse source = .error message) ↔
    ¬ ∃ grammar, Metalanguage.Denotes source grammar := by
  cases result : parse source with
  | error message =>
    constructor
    · rintro _ ⟨grammar, valid⟩
      have parsed := parse_complete valid
      rw [result] at parsed
      contradiction
    · intro _
      exact ⟨message, rfl⟩
  | ok grammar =>
    constructor
    · rintro ⟨_, impossible⟩
      contradiction
    · intro absent
      exact False.elim (absent ⟨grammar, parse_sound result⟩)

end Parser.EBNF
