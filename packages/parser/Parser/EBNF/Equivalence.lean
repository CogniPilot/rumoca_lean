import Parser.EBNF.Rules

/-! Language equivalences between EBNF expression shapes. A grammar may write a
production in a left-factored form when the form the standard publishes is not
LR(1) under the checked lowering; these lemmas show that both forms denote the
same words, so the substitution does not change the accepted language. -/
namespace Parser.EBNF

/-- A leading optional part is the alternative between the sequence without it
and the sequence with it. -/
theorem Derives.optional_seq_iff {grammar : Grammar} {head rest : Expr} {word : List Symbol} :
    Derives grammar (.seq (.optional head) rest) word ↔
      Derives grammar (.alt rest (.seq head rest)) word := by
  rw [Derives.seq_iff, Derives.alt_iff]
  constructor
  · rintro ⟨a, b, first, second, rfl⟩
    rcases Derives.optional_iff.mp first with rfl | present
    · exact .inl second
    · exact .inr (.seq present second)
  · rintro (absent | present)
    · exact ⟨[], word, .optionalEmpty, absent, rfl⟩
    · obtain ⟨a, b, first, second, rfl⟩ := Derives.seq_iff.mp present
      exact ⟨a, b, .optionalSome first, second, rfl⟩

end Parser.EBNF
