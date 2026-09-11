import Parser.CursorProofs

/-! Grammar-independent completeness of exact-spelling span attachment. The
lexer must justify a nontrivia first character for every token and preserve
its source spelling; this is independent of attachment's implementation. -/
namespace Parser.Source

/-- Token spellings separated by trivia, including the final suffix. Token
classes and maximal munch belong to the frontend's independent lexer relation. -/
inductive Spelled (trivia : Char → Bool) : List Char → List Token → Prop where
  | nil {chars : List Char} : chars.all trivia = true → Spelled trivia chars []
  | cons {gap : List Char} {t : Token} {c : Char} {chars rest : List Char} {ts : List Token} :
      gap.all trivia = true → t.text.toList = c :: chars → trivia c = false →
      Spelled trivia rest ts → Spelled trivia (gap ++ t.text.toList ++ rest) (t :: ts)

theorem Spelled.space (space : trivia c = true) (spelling : Spelled trivia cs ts) :
    Spelled trivia (c :: cs) ts := by
  cases spelling with
  | nil all => exact .nil (by simp [space, all])
  | @cons gap t first chars rest ts all text nontrivia tail =>
      exact .cons (gap := c :: gap) (by simp [space, all]) text nontrivia tail

private theorem attachReference_complete {source : String} {trivia : Char → Bool}
    (spelling : Spelled trivia cs ts) (p : source.Pos) (before : String)
    (split : p.Splits before (String.ofList cs)) :
    ∃ xs, attachReference trivia p ts = some xs := by
  induction spelling generalizing p before with
  | @nil chars all =>
      have right : source.endPos.Splits (before ++ String.ofList chars) "" :=
        ⟨by simpa using split.eq_append, by simp [← split.eq_append]⟩
      have range := Cursor.extract_between p source.endPos before (String.ofList chars) ""
        (by simpa using split) right
      have gap : Gap trivia p source.endPos := ⟨range.1, by rw [range.2]; simpa using all⟩
      simp [attachReference, gap]
  | @cons gap t c chars rest ts all text nontrivia tail ih =>
      have boundary : p.Splits before
          (String.ofList gap ++ (String.singleton c ++ String.ofList (chars ++ rest))) := by
        simpa only [text, String.ofList_append, Cursor.ofList_cons, String.append_assoc] using split
      have found := Cursor.find_splits (fun d => !trivia d) p before gap c
        (String.ofList (chars ++ rest)) boundary (by simpa using all) (by simp [nontrivia])
      have found' : (p.find (fun d => !trivia d)).Splits (before ++ String.ofList gap)
          (t.text ++ String.ofList rest) := by
        have tokenText : t.text = String.singleton c ++ String.ofList chars := by
          calc
            t.text = String.ofList t.text.toList := String.ofList_toList.symm
            _ = _ := by rw [text, Cursor.ofList_cons]
        simpa only [tokenText, String.ofList_append, String.append_assoc] using found
      have skipped := Cursor.extract_between p (p.find (fun d => !trivia d)) before
        (String.ofList gap) (t.text ++ String.ofList rest) (by
          simpa only [String.ofList_append, String.ofList_toList, String.append_assoc] using split) found'
      have skippedGap : Gap trivia p (p.find (fun d => !trivia d)) :=
        ⟨skipped.1, by rw [skipped.2]; simpa using all⟩
      have stopped := Cursor.nextn_splits (p.find (fun d => !trivia d))
        (before ++ String.ofList gap) t.text.toList (String.ofList rest) (by simpa using found')
      have consumed := Cursor.extract_between (p.find (fun d => !trivia d))
        ((p.find (fun d => !trivia d)).nextn t.text.length)
        (before ++ String.ofList gap) t.text (String.ofList rest) found'
        (by simpa using stopped)
      obtain ⟨xs, accepted⟩ := ih ((p.find (fun d => !trivia d)).nextn t.text.length)
        ((before ++ String.ofList gap) ++ t.text) (by simpa using stopped)
      simp only [attachReference]
      rw [dif_pos skippedGap, dif_pos consumed.1]
      have exactText : (Span.mk _ _ consumed.1).text = t.text := consumed.2
      rw [dif_pos exactText, accepted]
      exact ⟨_, rfl⟩

/-- Every token sequence satisfying the independent spelling/trivia contract
receives checked locations. No successful-attachment premise is needed. -/
theorem attach_complete {source : String} {trivia : Char → Bool}
    (spelling : Spelled trivia cs ts) (p : source.Pos) (before : String)
    (split : p.Splits before (String.ofList cs)) : ∃ xs, attach trivia p ts = some xs := by
  rw [attach_eq_reference]
  exact attachReference_complete spelling p before split

end Parser.Source
