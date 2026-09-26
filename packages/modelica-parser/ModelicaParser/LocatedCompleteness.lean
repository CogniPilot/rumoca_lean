import ModelicaParser.LocatedParser
import Parser.LocatedCompleteness

/-! Location attachment covers every successful result of the actual Modelica
lexer. This adds no grammar and no extra acceptance hypothesis. The total
construction below attaches locations to an already certified parse; the
attachment pass runs once and its failure branch is impossible. -/
namespace Rumoca
open _root_.Parser

private theorem classifyWord_text (word : String) : (classifyWord word).text = word := by
  simp only [classifyWord]
  split <;> rfl

/-- The frontend's maximal-munch relation supplies the generic exact-spelling
contract. In particular, no emitted token starts with trivia. -/
theorem Lexes.spelled (lexical : Lexes cs ts) : Source.Spelled modelicaSpace cs ts := by
  induction lexical with
  | nil => exact .nil rfl
  | space hs _ ih => exact ih.space hs
  | @ident c ts cs hs hi _ ih =>
      have text : (classifyWord (String.ofList (c :: cs.takeWhile identRest))).text.toList =
          c :: cs.takeWhile identRest := by simp [classifyWord_text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | @number c cs ts hs hi hd _ ih =>
      have positive := numberLength_pos c cs hd
      have split : (c :: cs).take (numberLength (c :: cs)) =
          c :: cs.take (numberLength (c :: cs) - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, numberLength (c :: cs) = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos positive).symm⟩
        rw [hk]; rfl
      have text : (Token.number (String.ofList ((c :: cs).take (numberLength (c :: cs))))).text.toList =
          c :: cs.take (numberLength (c :: cs) - 1) := by simp [Token.text, split]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      rw [List.nil_append, text, ← split, List.take_append_drop] at result
      exact result
  | @string cs n ts _ _ ih =>
      have text : (Token.string (String.ofList ('"' :: cs.take n))).text.toList =
          '"' :: cs.take n := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text (by decide) ih
      simpa only [List.nil_append, text, List.cons_append, List.take_append_drop] using result
  | @lineComment ts cs _ ih =>
      have text : (Token.comment (String.ofList ('/' :: '/' :: cs.take (lineCommentLength cs)))).text.toList =
          '/' :: '/' :: cs.take (lineCommentLength cs) := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text (by decide) ih
      simpa only [List.nil_append, text, List.cons_append, List.take_append_drop] using result
  | @blockComment cs n ts _ _ ih =>
      have text : (Token.comment (String.ofList ('/' :: '*' :: cs.take n))).text.toList =
          '/' :: '*' :: cs.take n := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text (by decide) ih
      simpa only [List.nil_append, text, List.cons_append, List.take_append_drop] using result
  | dotmul _ ih =>
      exact Source.Spelled.cons (gap := []) (by rfl) (t := .literal ".*") (c := '.')
        (chars := ['*']) rfl (by decide +kernel) ih
  | @punct c cs ts hs hi hd hc hop hp _ ih =>
      have text : (Token.literal (String.singleton c)).text.toList = [c] := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append] using result

namespace Modelica

/-- Every certified parse has exact aligned token locations. -/
theorem Parsed.locations_exist (parsed : Parsed source) :
    ∃ xs, Source.attach modelicaSpace source.startPos parsed.lexemes = some xs := by
  apply Source.attach_complete parsed.lexes.spelled source.startPos ""
  simp

/-- A computed token-location table and the equality identifying its actual
attachment result. Both the alignment certificate and this equality are erased. -/
def Parsed.checkedLocations (parsed : Parsed source) :
    { xs // Source.attach modelicaSpace source.startPos parsed.lexemes = some xs } :=
  match result : Source.attach modelicaSpace source.startPos parsed.lexemes with
  | some xs => ⟨xs, rfl⟩
  | none => False.elim (by
      obtain ⟨xs, accepted⟩ := parsed.locations_exist
      rw [result] at accepted
      contradiction)

def Parsed.located (parsed : Parsed source) : LocatedParsed source :=
  let locations := parsed.checkedLocations.val
  ⟨parsed, locations.val, locations.property⟩

/-- Requiring location data does not change the parse. -/
theorem Parsed.located_parsed (parsed : Parsed source) : parsed.located.parsed = parsed := rfl

/-- The total construction identifies the actual public located parser. -/
theorem Parsed.parseLocated_eq (parsed : Parsed source) :
    parseLocated source = .ok parsed.located := by
  have lexed : Source.lexLocated lex source modelicaSpace = .ok
      ⟨parsed.checkedLocations.val.val, by
        rw [parsed.checkedLocations.val.property.erases]
        exact parsed.lexical, by
        simpa only [parsed.checkedLocations.val.property.erases] using
          parsed.checkedLocations.val.property⟩ := by
    unfold Source.lexLocated
    split
    · rename_i error failed
      rw [parsed.lexical] at failed
      contradiction
    · rename_i tokens accepted
      have same : tokens = parsed.lexemes := Except.ok.inj (accepted.symm.trans parsed.lexical)
      subst tokens
      split
      · rename_i missing
        rw [parsed.checkedLocations.property] at missing
        contradiction
      · rename_i locations attached
        have same := Option.some.inj (attached.symm.trans parsed.checkedLocations.property)
        subst locations
        rfl
  simp only [parseLocated, lexed]
  have erases := parsed.checkedLocations.val.property.erases
  split
  · rename_i rejected
    rw [erases, parsed.syntactic] at rejected
    contradiction
  · rename_i ast accepted
    have same : ast = parsed.ast := by
      rw [erases, parsed.syntactic] at accepted
      exact (Option.some.inj accepted).symm
    subst ast
    unfold Parsed.located
    congr 2
    exact Parsed.unique _ _

/-- Every certified parse succeeds with spans. -/
theorem parseLocated_complete (parsed : Parsed source) :
    ∃ located, parseLocated source = .ok located ∧ located.parsed = parsed :=
  ⟨parsed.located, parsed.parseLocated_eq, rfl⟩

end Modelica
end Rumoca
