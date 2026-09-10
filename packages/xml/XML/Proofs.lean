import XML.Syntax

namespace XML

theorem escapeChar_correct (c : Char) (valid : TextChar c) :
    EscapedChar c (escapeChar c).toList := by
  unfold escapeChar
  split
  · exact .amp
  · exact .lt
  · exact .gt
  · exact .quot
  · exact .apos
  · rename_i h₁ h₂ h₃ h₄ h₅
    simpa using EscapedChar.literal c valid h₁ h₂ h₃ h₄ h₅

theorem join_toList (strings : List String) :
    (String.join strings).toList = strings.flatMap String.toList := by
  have go : ∀ strings : List String, ∀ start : String,
      (strings.foldl (· ++ ·) start).toList = start.toList ++ strings.flatMap String.toList := by
    intro strings
    induction strings with
    | nil => intro start; simp
    | cons s ss ih => intro start; simp [List.foldl, ih, String.toList_append, List.append_assoc]
  simpa [String.join] using go strings ""

theorem escape_correct (value : String) (valid : Text value) :
    Escaped value.toList (escape value).toList := by
  unfold escape
  rw [join_toList, List.flatMap_map]
  have go : ∀ chars : List Char, (∀ c ∈ chars, TextChar c) →
      Escaped chars (chars.flatMap fun c => (escapeChar c).toList) := by
    intro chars h
    induction chars with
    | nil => exact .nil
    | cons c cs ih =>
      exact .cons (escapeChar_correct c (h c (by simp)))
        (ih (fun c hc => h c (by simp [hc])))
  exact go _ valid

theorem attributes_correct (attrs : List (String × String)) (valid : AttributesValid attrs) :
    Attributes attrs
      (String.join (attrs.map fun (k, v) => " " ++ k ++ "=\"" ++ escape v ++ "\"")).toList := by
  induction attrs with
  | nil => exact .nil
  | cons a attrs ih =>
    obtain ⟨key, value⟩ := a
    obtain ⟨unique, each⟩ := valid
    have hn := (List.nodup_cons.mp unique)
    have hv := each (key, value) (by simp)
    have ht : AttributesValid attrs := ⟨hn.2, fun a ha => each a (by simp [ha])⟩
    simpa [join_toList, List.flatMap_map, String.toList_append, List.append_assoc] using
      Attributes.cons hv.1 hn.1 (escape_correct value hv.2) (ih ht)

theorem render_correct (e : Element) (depth : Nat) (valid : e.valid = true) :
    Parses e (e.render depth).toList := by
  refine Element.rec
    (motive_1 := fun e => ∀ depth, e.valid = true → Parses e (e.render depth).toList)
    (motive_2 := fun es => ∀ depth, (∀ c ∈ es, c.valid = true) →
      ParsesMany es (es.flatMap fun c => (c.render depth).toList)) ?_ ?_ ?_ e depth valid
  · intro name attrs children value ih depth valid
    simp only [Element.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_map,
      Function.comp_def, id_eq, List.all_eq_true] at valid
    obtain ⟨⟨hn, ha, ht, content⟩, hc⟩ := valid
    have attributes := attributes_correct attrs ha
    cases children with
    | nil =>
      by_cases empty : value = ""
      · subst value
        simpa [Element.render, String.toList_append, List.append_assoc] using
          Parses.empty depth hn attributes
      · simpa [Element.render, String.isEmpty_iff, empty, String.toList_append,
          List.append_assoc] using Parses.text depth hn attributes (escape_correct value ht)
    | cons child rest =>
      have empty : value = "" := content.resolve_right (by simp)
      subst value
      simpa [Element.render, escape, String.toList_append, join_toList, List.flatMap_map,
        List.append_assoc] using Parses.branch depth hn attributes (ih (depth + 1) hc)
  · intro depth valid; exact .nil
  · intro c cs ihc ihcs depth valid
    exact .cons (ihc depth (valid c (by simp))) (ihcs depth (fun c h => valid c (by simp [h])))

theorem document_correct (root : Element) (valid : root.valid = true) :
    Document root (document root) :=
  ⟨(root.render 0).toList, String.toList_append, render_correct root 0 valid⟩

end XML
