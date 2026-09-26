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
  | @number c ts cs hs hi hd _ ih =>
      have text : (numberToken (c :: cs.takeWhile numberChar)).text.toList =
          c :: cs.takeWhile numberChar := by simp [numberToken_text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append, List.takeWhile_append_dropWhile] using result
  | dotmul _ ih =>
      exact Source.Spelled.cons (gap := []) (by rfl) (t := .literal ".*") (c := '.')
        (chars := ['*']) rfl (by decide +kernel) ih
  | @punct c cs ts hs hi hd hop hp _ ih =>
      have text : (Token.literal (String.singleton c)).text.toList = [c] := by simp [Token.text]
      have result := Source.Spelled.cons (gap := []) (by rfl) text hs ih
      simpa only [List.nil_append, text, List.cons_append] using result

namespace Modelica

/-- Every certified parse has exact aligned token locations. -/
theorem Parsed.locations_exist (parsed : Parsed source) :
    ∃ xs, Source.attach modelicaSpace source.startPos parsed.tokens = some xs := by
  apply Source.attach_complete parsed.lexes.spelled source.startPos ""
  simp

/-- A computed token-location table and the equality identifying its actual
attachment result. Both the alignment certificate and this equality are erased. -/
def Parsed.checkedLocations (parsed : Parsed source) :
    { xs // Source.attach modelicaSpace source.startPos parsed.tokens = some xs } :=
  match result : Source.attach modelicaSpace source.startPos parsed.tokens with
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
      have same : tokens = parsed.tokens := Except.ok.inj (accepted.symm.trans parsed.lexical)
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
