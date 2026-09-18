import ModelicaParser.ActionsLocated
import ModelicaParser.LocatedCompleteness

/-! Total source-location construction for any certified action-profile parse.
This is the reusable mechanism the unit profile uses in `LocatedTotal`, lifted to
every `ParserActions.Actions` profile: attachment failure is impossible by lexer
completeness, not hidden by a fallback. The proof branches are erased; the actual
attachment pass runs once. A profile-specific certificate can therefore emit a
completed located parse for a pinned AST without kernel-evaluating the LR parser
on the source text. -/
namespace Rumoca.ParserActions
open _root_.Parser

variable {α : Type} {actions : Actions α} {source : String}

/-- Every certified action-profile parse has exact aligned token locations. The
lexical guarantee is shared with the unit profile, so the same maximal-munch
spelling contract discharges attachment completeness. -/
theorem Parsed.locations_exist (parsed : Parsed actions source) :
    ∃ xs, Source.attach modelicaSpace source.startPos parsed.tokens = some xs := by
  apply Source.attach_complete ((lex_correct source parsed.tokens).mp parsed.lexical).spelled
    source.startPos ""
  simp

/-- A computed token-location table and the equality identifying its actual
attachment result. Both the alignment certificate and this equality are erased. -/
def Parsed.checkedLocations (parsed : Parsed actions source) :
    { xs // Source.attach modelicaSpace source.startPos parsed.tokens = some xs } :=
  match result : Source.attach modelicaSpace source.startPos parsed.tokens with
  | some xs => ⟨xs, rfl⟩
  | none => False.elim (by
      obtain ⟨xs, accepted⟩ := parsed.locations_exist
      rw [result] at accepted
      contradiction)

def Parsed.located (parsed : Parsed actions source) : LocatedParsed actions source :=
  let locations := parsed.checkedLocations.val
  ⟨parsed, locations.val, locations.property⟩

/-- Requiring location data does not change the semantic parse. -/
theorem Parsed.located_parsed (parsed : Parsed actions source) : parsed.located.parsed = parsed := rfl

/-- The total construction identifies the actual public located parser, not an
alternative parser with a weaker acceptance contract. -/
theorem Parsed.parseLocated_eq (parsed : Parsed actions source) :
    parseLocated actions source = .ok parsed.located := by
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
    exact (parse_eq_parsed actions _).symm.trans (parse_eq_parsed actions parsed)

/-- Every action-profile source in the existing lexical/AST specification
succeeds with spans. -/
theorem parseLocated_complete (actions : Actions α) (source : String) (a : α)
    (syntaxValid : Lexes source.toList (actions.tokens a)) :
    ∃ parsed, parseLocated actions source = .ok parsed ∧ parsed.parsed.ast = a := by
  obtain ⟨parsed, hparse, hast⟩ := parse_complete actions source a syntaxValid
  exact ⟨parsed.located, parsed.parseLocated_eq, hast⟩

end Rumoca.ParserActions
