import ModelicaParser.LocatedCompleteness
import ModelicaParser.LocatedProofs

/-! Total source-location construction for an already certified Modelica parse.
Attachment failure is impossible by lexer completeness, not hidden by a fallback.
The proof branches are erased; the actual attachment pass runs once. -/
namespace Rumoca
open _root_.Parser

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

/-- Requiring location data does not change the semantic parse. -/
theorem Parsed.located_parsed (parsed : Parsed source) : parsed.located.parsed = parsed := rfl

/-- The total construction identifies the actual public located parser, not an
alternative parser with a weaker acceptance contract. -/
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
    apply Except.ok.inj
    exact (parse_eq_parsed _).symm.trans (parse_eq_parsed parsed)

/-- Every source in the existing lexical/AST specification succeeds with spans. -/
theorem parseLocated_complete (source : String) (model : AST.Model)
    (syntaxValid : Lexes source.toList model.tokens) :
    ∃ parsed, parseLocated source = .ok parsed ∧ parsed.parsed.ast = model :=
  ⟨(parsedOfSyntax source model syntaxValid).located,
    (parsedOfSyntax source model syntaxValid).parseLocated_eq, rfl⟩

end Rumoca
