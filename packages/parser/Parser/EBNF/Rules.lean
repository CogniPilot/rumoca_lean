import Parser.EBNF.Semantics

/-! One-step equations for source grammar rules. These describe the independent
EBNF language, without evaluating a parser. Recursive rules unfold once, so
frontends can use induction over their own ASTs as the grammar grows. -/
namespace Parser.EBNF

theorem Derives.terminal_iff {grammar symbol word} (h : symbol ≠ .literal "") :
    Derives grammar (.terminal symbol) word ↔ word = [symbol] := by
  constructor
  · intro derivation
    cases derivation with
    | empty => exact False.elim (h rfl)
    | terminal _ => rfl
  · rintro rfl
    exact .terminal h

theorem Derives.empty_iff {grammar word} :
    Derives grammar (.terminal (.literal "")) word ↔ word = [] := by
  constructor
  · intro derivation
    cases derivation with
    | empty => rfl
    | terminal nonempty => exact False.elim (nonempty rfl)
  · rintro rfl
    exact .empty

theorem Derives.seq_iff {grammar left right word} :
    Derives grammar (.seq left right) word ↔
      ∃ a b, Derives grammar left a ∧ Derives grammar right b ∧ word = a ++ b := by
  constructor
  · intro derivation
    cases derivation with
    | seq first second => exact ⟨_, _, first, second, rfl⟩
  · rintro ⟨a, b, first, second, rfl⟩
    exact .seq first second

theorem Derives.alt_iff {grammar left right word} :
    Derives grammar (.alt left right) word ↔
      Derives grammar left word ∨ Derives grammar right word := by
  constructor
  · intro derivation
    cases derivation with
    | altLeft d => exact .inl d
    | altRight d => exact .inr d
  · rintro (d | d)
    · exact .altLeft d
    · exact .altRight d

theorem Derives.optional_iff {grammar body word} :
    Derives grammar (.optional body) word ↔ word = [] ∨ Derives grammar body word := by
  constructor
  · intro derivation
    cases derivation with
    | optionalEmpty => exact .inl rfl
    | optionalSome d => exact .inr d
  · rintro (rfl | d)
    · exact .optionalEmpty
    · exact .optionalSome d

/-- A finite checked lookup justifies unfolding a named rule. No language
equivalence is assumed by the lookup certificate. -/
theorem Derives.ref_iff_of_filter {grammar : Grammar} {name body}
    (lookup : grammar.filter (fun rule => rule.1 == name) = [(name, body)]) (word) :
    Derives grammar (.ref name) word ↔ Derives grammar body word := by
  constructor
  · intro derivation
    cases derivation with
    | ref rule d =>
      have member := (List.mem_filter
        (p := fun rule : String × Expr => rule.1 == name)).mpr ⟨rule, by simp⟩
      rw [lookup] at member
      have eq := congrArg Prod.snd (List.mem_singleton.mp member)
      dsimp only at eq
      simpa only [eq] using d
  · intro d
    apply Derives.ref (body := body) _ d
    have member : (name, body) ∈ grammar.filter (fun rule => rule.1 == name) := by
      rw [lookup]
      exact List.mem_singleton_self _
    exact (List.mem_filter.mp member).1

theorem accepts_iff_of_head {grammar : Grammar} {name body}
    (head : grammar.head? = some (name, body)) (word) :
    Accepts grammar word ↔ Derives grammar (.ref name) word := by
  cases grammar with
  | nil => simp at head
  | cons first tail =>
    have eq : first = (name, body) := Option.some.inj head
    subst first
    simp [Accepts]

end Parser.EBNF
