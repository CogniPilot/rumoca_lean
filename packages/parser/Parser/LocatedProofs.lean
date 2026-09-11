import Parser.Located

/-! Exact refinement of span attachment. This direct recursive specification
records the original cursor decisions, including failure. It is proof-only;
the executable entry point uses the accumulator implementation. -/
namespace Parser.Source

variable {source : String}

/-- Reference cursor policy, independent of accumulator state. In particular,
`Aligned` alone does not impose this greedy choice for arbitrary token text. -/
noncomputable def attachReference (trivia : Char → Bool) (p : source.Pos)
    (ts : List Token) :
    Option { xs : List (Located source Token) // Aligned trivia p ts xs } :=
  match ts with
  | [] => if h : Gap trivia p source.endPos then some ⟨[], .nil h⟩ else none
  | t :: ts =>
    let start := p.find (fun c => !trivia c)
    let stop := start.nextn t.text.length
    if hg : Gap trivia p start then
      if ho : start ≤ stop then
        let span : Span source := ⟨start, stop, ho⟩
        if ht : span.text = t.text then
          (attachReference trivia stop ts).map
            (fun tail => ⟨⟨t, span⟩ :: tail.val, .cons hg ht tail.property⟩)
        else none
      else none
    else none

/-- Every accumulator state refines the reference result, including `none`.
The invariant affects only the erased proof, not the returned tokens or spans. -/
theorem attachLoop_eq_reference (trivia : Char → Bool) (origin : source.Pos)
    (input : List Token) (p : source.Pos) (ts : List Token)
    (acc : List (Located source Token))
    (hprefix : ∀ xs, Aligned trivia p ts xs →
      Aligned trivia origin input (acc.reverse ++ xs)) :
    (attachLoop trivia origin input p ts acc hprefix).map Subtype.val =
      (attachReference trivia p ts).map (fun xs => acc.reverse ++ xs.val) := by
  induction ts generalizing p acc with
  | nil => simp only [attachLoop, attachReference]; split <;> simp
  | cons t ts ih =>
    simp only [attachLoop, attachReference]
    split
    · split
      · split
        · rw [ih]
          simp [Option.map_map, Function.comp_def, List.append_assoc]
        · rfl
      · rfl
    · rfl

/-- Exact successful locations and failures of the public implementation. -/
theorem attach_eq_reference (trivia : Char → Bool) (p : source.Pos) (ts : List Token) :
    attach trivia p ts = attachReference trivia p ts := by
  apply Option.map_injective (f := Subtype.val) (fun _ _ h => Subtype.ext h)
  simpa [attach] using
    attachLoop_eq_reference trivia p ts p ts [] (by intro xs h; simpa using h)

/-- The pre-refinement located-lexer behavior, used only as a specification. -/
noncomputable def lexLocatedReference
    (lexer : String → Except Parser.Diagnostic (List Token))
    (source : String) (trivia : Char → Bool) :
    Except (Diagnostic source) (Lexed lexer source trivia) :=
  match hl : lexer source with
  | .error e => .error (.ofCharacterOffset source e)
  | .ok ts => match attachReference trivia source.startPos ts with
    | none => .error ⟨"location", .point source.startPos, "lexer/source alignment failed", []⟩
    | some xs => .ok ⟨xs.val, by rw [xs.property.erases]; exact hl,
        by simpa only [xs.property.erases] using xs.property⟩

/-- Whole located-lexer results are unchanged: tokens, every span, lexical and
alignment failures, diagnostic phases/messages, and their valid byte ranges. -/
theorem lexLocated_eq_reference
    (lexer : String → Except Parser.Diagnostic (List Token))
    (source : String) (trivia : Char → Bool) :
    lexLocated lexer source trivia = lexLocatedReference lexer source trivia := by
  simp only [lexLocated, lexLocatedReference, attach_eq_reference]
  rfl

end Parser.Source
