import ModelicaParser.LocatedCompleteness

/-! Admission as static semantics over the general syntax tree. A selection
reads a record from the parsed tree, or rejects it with a message at the token
that violates the selection. Each selection states the token sequence of the
record it returns and proves that a selected tree prints to exactly those
tokens, so a selected record is bound to the characters of the source text
without any token-pattern recognition. `Selection.parse` and
`Selection.parseLocated` compose the one certified parse with one selection;
the admitted selections are `AST.selection`, `ArrayProfile.selection` and
`ConstantProfile.selection`. -/
namespace Rumoca.Modelica
open _root_.Parser

/-- A rejection of a parsed tree, located at the index of an offending token. -/
structure Rejection where
  token : Nat
  message : String
  deriving Repr, DecidableEq

structure Selection (α : Type) where
  select : AST.StoredDefinition → Except Rejection α
  tokens : α → List Token
  printed : ∀ tree a, select tree = .ok a → Print.storedDefinition tree = tokens a

namespace Selection
variable {α : Type} (s : Selection α)

/-- The source has no comment. Comments are lexed with their ranges but are
not admitted yet, so every selection rejects a commented source. -/
def Uncommented (lexemes : List Token) : Prop := lexemes.all (fun t => !isComment t) = true

instance (lexemes : List Token) : Decidable (Uncommented lexemes) :=
  inferInstanceAs (Decidable (_ = true))

/-- A certified parse of an uncommented source together with the record
selected from its tree. -/
structure Parsed (source : String) where
  tree : Modelica.Parsed source
  ast : α
  selected : s.select tree.ast = .ok ast
  uncommented : Uncommented tree.lexemes := by decide

variable {s} {source : String}

def Parsed.tokens (p : s.Parsed source) : List Token := p.tree.tokens

/-- A selected source has no comment, so its tokens are all its lexemes. -/
theorem Parsed.tokens_lexemes (p : s.Parsed source) : p.tokens = p.tree.lexemes :=
  code_uncommented p.uncommented

theorem Parsed.lexical (p : s.Parsed source) : lex source = .ok p.tokens := by
  rw [p.tokens_lexemes]
  exact p.tree.lexical

/-- The parsed tokens are the tokens of the selected record. -/
theorem Parsed.tokens_eq (p : s.Parsed source) : p.tokens = s.tokens p.ast :=
  p.tree.printed.symm.trans (s.printed _ _ p.selected)

/-- Soundness reaches the characters of the input file. -/
theorem Parsed.lexes (p : s.Parsed source) : Lexes source.toList (s.tokens p.ast) := by
  rw [← p.tokens_eq, p.tokens_lexemes]
  exact p.tree.lexes

theorem Parsed.in_ebnf (p : s.Parsed source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) := p.tree.in_ebnf

variable (s) in
def parse (source : String) : Except Diagnostic (s.Parsed source) :=
  match Modelica.parse source with
  | .error diagnostic => .error diagnostic
  | .ok tree =>
    if uncommented : Uncommented tree.lexemes then
      match selected : s.select tree.ast with
      | .error rejection => .error ⟨"select", 0, rejection.message⟩
      | .ok ast => .ok ⟨tree, ast, selected, uncommented⟩
    else .error ⟨"select", 0, "comments are not admitted yet"⟩

/-- Completeness of a selection from the characters of a source: an
uncommented record whose tokens the source lexes to, whose tokens parse to a
tree, and which selection reads back from that tree, is the selected parse. -/
theorem Parsed.complete {m : α} {ast : AST.StoredDefinition}
    (lexes : Lexes source.toList (s.tokens m)) (uncommented : Uncommented (s.tokens m))
    (syntactic : Structural.parse (s.tokens m) = some ast) (selected : s.select ast = .ok m) :
    ∃ p : s.Parsed source, p.ast = m :=
  ⟨⟨⟨s.tokens m, ast, (lex_correct source _).mpr lexes,
    by rw [code_uncommented uncommented]; exact syntactic⟩, m, selected, uncommented⟩, rfl⟩

/-- A selected parse describes the actual executable result. -/
theorem parse_eq_parsed (p : s.Parsed source) : s.parse source = .ok p := by
  obtain ⟨tree, ast, selected, uncommented⟩ := p
  simp only [parse, Modelica.parse_eq_parsed tree, dif_pos uncommented]
  split
  · rename_i rejection rejected
    rw [selected] at rejected
    contradiction
  · rename_i other same
    cases Except.ok.inj (same.symm.trans selected)
    rfl

theorem Parsed.unique (p q : s.Parsed source) : p = q :=
  Except.ok.inj ((parse_eq_parsed p).symm.trans (parse_eq_parsed q))

/-- Located tokens and the record selected from their tree. -/
structure LocatedParsed (s : Selection α) (source : String) where
  tree : Modelica.LocatedParsed source
  ast : α
  selected : s.select tree.parsed.ast = .ok ast
  uncommented : Uncommented tree.parsed.lexemes

namespace LocatedParsed

def parsed (p : s.LocatedParsed source) : s.Parsed source :=
  ⟨p.tree.parsed, p.ast, p.selected, p.uncommented⟩

def locations (p : s.LocatedParsed source) : List (Source.Located source Token) :=
  p.tree.locations

theorem aligned (p : s.LocatedParsed source) :
    Source.Aligned modelicaSpace source.startPos p.parsed.tokens p.locations := by
  rw [p.parsed.tokens_lexemes]
  exact p.tree.aligned

/-- Without comments, every location is a code token location. -/
theorem codeLocations_eq (p : s.LocatedParsed source) : codeLocations p.locations = p.locations := by
  apply List.filter_eq_self.mpr
  intro located member
  have erased := p.tree.aligned.erases
  have all := p.uncommented
  simp only [Uncommented, List.all_eq_true] at all
  simpa using all located.value (erased ▸ List.mem_map_of_mem member)

/-- A token range is read directly from the locations. -/
theorem tokenSpan_eq (p : s.LocatedParsed source) (index : Nat) :
    p.tree.tokenSpan index = ((p.locations[index]?).map (·.span)).getD (.point source.endPos) := by
  simp only [Modelica.LocatedParsed.tokenSpan, locatedSpan]
  rw [show codeLocations p.tree.locations = p.locations from p.codeLocations_eq]

def tokenSpan (p : s.LocatedParsed source) (index : Nat) : Source.Span source :=
  p.tree.tokenSpan index

theorem erases (p : s.LocatedParsed source) : s.parse source = .ok p.parsed :=
  parse_eq_parsed p.parsed

theorem lexemes (p : s.LocatedParsed source) :
    ∀ token ∈ p.locations, token.span.text = token.value.text := p.tree.lexemes

theorem disjoint (p : s.LocatedParsed source) :
    p.locations.Pairwise (fun a b => a.span.stop ≤ b.span.start) := p.tree.disjoint

theorem tokenSpan_text (p : s.LocatedParsed source) (index : Nat) (token : Token)
    (h : p.parsed.tokens[index]? = some token) :
    (p.tokenSpan index).text = token.text :=
  p.tree.tokenSpan_text index token h

/-- The range of a token of the selected record. -/
theorem tokenSpan_record (p : s.LocatedParsed source) (index : Nat) (token : Token)
    (h : (s.tokens p.ast)[index]? = some token) :
    (p.tokenSpan index).text = token.text :=
  p.tokenSpan_text index token (by rw [show p.parsed.tokens = _ from p.parsed.tokens_eq]; exact h)

end LocatedParsed

/-- The range of the first comment, or the end of the text. -/
def commentSpan (locations : List (Source.Located source Token)) : Source.Span source :=
  ((locations.find? fun token => isComment token.value).map (·.span)).getD (.point source.endPos)

variable (s) in
/-- Select a record from a located parse; a rejection is reported at its token,
a comment at the first comment. -/
def selectLocated (tree : Modelica.LocatedParsed source) :
    Except (Source.Diagnostic source) (s.LocatedParsed source) :=
  if uncommented : Uncommented tree.parsed.lexemes then
    match selected : s.select tree.parsed.ast with
    | .error rejection => .error ⟨"select", tree.tokenSpan rejection.token, rejection.message, []⟩
    | .ok ast => .ok ⟨tree, ast, selected, uncommented⟩
  else .error ⟨"select", commentSpan tree.locations, "comments are not admitted yet", []⟩

variable (s) in
def parseLocated (source : String) :
    Except (Source.Diagnostic source) (s.LocatedParsed source) :=
  match Modelica.parseLocated source with
  | .error diagnostic => .error diagnostic
  | .ok tree => s.selectLocated tree

/-- Attaching locations to a selected parse is total. -/
def Parsed.located (p : s.Parsed source) : s.LocatedParsed source :=
  ⟨p.tree.located, p.ast, p.selected, p.uncommented⟩

/-- Requiring location data does not change the selected parse. -/
theorem Parsed.located_parsed (p : s.Parsed source) : p.located.parsed = p := rfl

/-- The total construction identifies the actual public located parser. -/
theorem Parsed.parseLocated_eq (p : s.Parsed source) : s.parseLocated source = .ok p.located := by
  simp only [parseLocated, p.tree.parseLocated_eq, selectLocated, Modelica.Parsed.located_parsed,
    dif_pos p.uncommented]
  split
  · rename_i rejection rejected
    rw [p.selected] at rejected
    contradiction
  · rename_i ast same
    rw [p.selected] at same
    cases Except.ok.inj same
    rfl

/-- Every selected parse succeeds with spans. -/
theorem parseLocated_complete (p : s.Parsed source) :
    ∃ located, s.parseLocated source = .ok located ∧ located.parsed = p :=
  ⟨p.located, p.parseLocated_eq, rfl⟩

end Selection
end Rumoca.Modelica
