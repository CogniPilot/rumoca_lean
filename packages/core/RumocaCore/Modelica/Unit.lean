import RumocaCore.Modelica.Select
import ModelicaParser.Certificate

/-! The unit profile: one plain `Real` state and the equation `der(state) = 1`,
selected from the general syntax tree. The record keeps the four written names;
name agreement belongs to resolution, which reports each mismatch at its source
occurrence. -/
namespace Rumoca.AST
open _root_.Parser

structure Model where
  name : String
  state : String
  derivativeName : String
  endName : String
  deriving Repr, BEq, DecidableEq

/-- The token sequence of a unit-profile source. -/
def Model.tokens (m : Model) : List Token :=
  [.literal "model", .ident m.name, .ident "Real", .ident m.state,
   .literal ";", .literal "equation", .literal "der", .literal "(",
   .ident m.derivativeName, .literal ")", .literal "=", .number "1",
   .literal ";", .literal "end", .ident m.endName, .literal ";"]

/-- A resolved value carries proofs tied to this exact source AST. -/
structure Resolved (m : Model) : Prop where
  end_matches : m.endName = m.name
  derivative_resolves : m.derivativeName = m.state

def resolve (m : Model) : Except Diagnostic (PLift (Resolved m)) :=
  if hn : m.endName = m.name then
    if hd : m.derivativeName = m.state then .ok ⟨⟨hn, hd⟩⟩
    else .error ⟨"resolve", 0, s!"der({m.derivativeName}) does not refer to declared state {m.state}"⟩
  else .error ⟨"resolve", 0, s!"end {m.endName} does not match model {m.name}"⟩

theorem resolve_complete (m : Model) (h : Resolved m) :
    resolve m = .ok ⟨h⟩ := by
  simp [resolve, h.end_matches, h.derivative_resolves]

open Modelica Modelica.Select in
/-- Select the unit profile from a parsed tree. -/
def select (d : Modelica.AST.StoredDefinition) : Except Rejection Model := do
  let header ← Select.model d
  let element ← one 2 "the unit profile declares exactly one state" header.2.1.elements
  let state ← Select.state 2 "the state declaration" element
  let width := elementsWidth header.2.1.elements
  let equations ← Select.equations (2 + width) header.2.1
  let equation ← one (3 + width) "the unit profile has exactly one equation" equations
  match equation with
  | .simple left right =>
    let derivative ← Select.derivative (3 + width) left
    exactly (4 + width + (Modelica.Print.expr left).length) "the unit derivative" "1" right
    return ⟨header.1, state, derivative, header.2.2⟩

open Modelica Modelica.Select in
/-- A selected tree prints to the tokens of its record. -/
theorem select_printed {d : Modelica.AST.StoredDefinition} {m : Model} (h : select d = .ok m) :
    Modelica.Print.storedDefinition d = m.tokens := by
  obtain ⟨⟨name, body, endName⟩, found, h⟩ := bind_ok h
  obtain ⟨element, single, h⟩ := bind_ok h
  obtain ⟨state, declared, h⟩ := bind_ok h
  obtain ⟨equations, sectioned, h⟩ := bind_ok h
  obtain ⟨equation, exact, h⟩ := bind_ok h
  obtain ⟨left, right⟩ := equation
  obtain ⟨derivative, differentiated, h⟩ := bind_ok h
  obtain ⟨_, unit, h⟩ := bind_ok h
  cases h
  obtain ⟨elements, sections⟩ := body
  have elements_one : elements = [element] := one_ok single
  have sections_one : sections = [⟨equations⟩] := equations_ok sectioned
  have equations_one : equations = [.simple left right] := one_ok exact
  subst elements_one sections_one equations_one
  rw [model_ok found, state_ok declared, derivative_ok differentiated, exactly_ok unit]
  rfl

def selection : Modelica.Selection Model := ⟨select, Model.tokens, fun _ _ => select_printed⟩

/-! ### Completeness -/

/-- The names a unit-profile record reads from its source. -/
def Model.names (m : Model) : List String := [m.name, m.state, m.derivativeName, m.endName]

/-- Selection admits exactly the records whose names are not predefined type
names. -/
def Model.Admissible (m : Model) : Prop := ∀ n ∈ m.names, Modelica.Select.predefined n = false

instance (m : Model) : Decidable m.Admissible := by
  unfold Model.Admissible; infer_instance

certify_family sourceFamily (name state derivativeName endName)
  (Model.tokens ⟨name, state, derivativeName, endName⟩)

open Modelica Modelica.Select in
/-- Selection reads every admissible record back from the parse of its tokens. -/
theorem select_complete (m : Model) (admissible : m.Admissible) :
    ∃ ast, Structural.parse m.tokens = some ast ∧ select ast = .ok m := by
  obtain ⟨name, state, derivativeName, endName⟩ := m
  refine ⟨_, sourceFamily.syntactic name state derivativeName endName, ?_⟩
  simp only [Model.Admissible, Model.names, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at admissible
  obtain ⟨named, stated, differentiated, ended⟩ := admissible
  simp [select, sourceFamily.ast, Select.model, Select.name, named, stated, differentiated, ended,
    one, Select.state, declaration, Select.equations, Select.derivative, reference, exactly, numeral,
    bind, Except.bind, pure, Except.pure, Except.map]

/-- Every admissible record whose tokens a source lexes to is the selected
parse of that source. -/
theorem parse_complete {source : String} (m : Model) (lexes : Lexes source.toList m.tokens)
    (admissible : m.Admissible) : ∃ p : selection.Parsed source, p.ast = m := by
  obtain ⟨ast, syntactic, selected⟩ := select_complete m admissible
  exact Modelica.Selection.Parsed.complete lexes
    (by simp [Modelica.Selection.Uncommented, selection, Model.tokens, Modelica.isComment])
    syntactic selected

end Rumoca.AST

namespace Rumoca
open _root_.Parser

/-- A certified parse selected as the unit profile. -/
abbrev Parsed (source : String) := AST.selection.Parsed source

def parse (source : String) : Except Diagnostic (Parsed source) := AST.selection.parse source

abbrev LocatedParsed (source : String) := AST.selection.LocatedParsed source

def parseLocated (source : String) : Except (Parser.Source.Diagnostic source) (LocatedParsed source) :=
  AST.selection.parseLocated source

variable {source : String}

theorem parse_eq_parsed (p : Parsed source) : parse source = .ok p :=
  Modelica.Selection.parse_eq_parsed p

/-- Soundness reaches the characters of the input file, not just token codes. -/
theorem parsed_lexes (p : Parsed source) : Lexes source.toList p.ast.tokens :=
  Modelica.Selection.Parsed.lexes p

theorem parsed_in_ebnf (p : Parsed source) :
    EBNF.Accepts Generated.sourceGrammar (p.tokens.map Token.symbol) :=
  Modelica.Selection.Parsed.in_ebnf p

theorem Parsed.tokens_eq (p : Parsed source) : p.tokens = p.ast.tokens :=
  Modelica.Selection.Parsed.tokens_eq p

def Parsed.located (p : Parsed source) : LocatedParsed source := Modelica.Selection.Parsed.located p

theorem Parsed.located_parsed (p : Parsed source) : p.located.parsed = p := rfl

theorem Parsed.parseLocated_eq (p : Parsed source) : parseLocated source = .ok p.located :=
  Modelica.Selection.Parsed.parseLocated_eq p

namespace LocatedParsed

/-- Every admitted AST has sixteen terminals. Semantic field accessors have
total indices into the actual tokens, without an EOF fallback. -/
theorem location_count (p : LocatedParsed source) : p.locations.length = 16 := by
  have h := congrArg List.length p.aligned.erases
  simp only [List.length_map] at h
  rw [Modelica.Selection.Parsed.tokens_eq] at h
  exact h

/-- Required span for an AST field; the bound is erased during compilation. -/
def fieldSpan (p : LocatedParsed source) (index : Fin 16) : Parser.Source.Span source :=
  (p.locations[index.val]'(by rw [p.location_count]; exact index.isLt)).span

def modelSpan (p : LocatedParsed source) : Parser.Source.Span source :=
  (p.tokenSpan 0).cover (p.tokenSpan 15)

/-- Name agreement is still the compiler's resolver. Locations only enrich its
failure report; an end-name error takes the same priority as in AST.resolve. -/
def resolve (p : LocatedParsed source) :
    Except (Parser.Source.Diagnostic source) (PLift (AST.Resolved p.parsed.ast)) :=
  match AST.resolve p.parsed.ast with
  | .ok resolved => .ok resolved
  | .error e => .error ⟨e.phase,
      p.tokenSpan (if p.parsed.ast.endName = p.parsed.ast.name then 8 else 14), e.message,
      [if p.parsed.ast.endName = p.parsed.ast.name then
        ⟨p.tokenSpan 3, "state declared here"⟩
      else ⟨p.tokenSpan 1, "model declared here"⟩]⟩

theorem erases (p : LocatedParsed source) : parse source = .ok p.parsed :=
  parse_eq_parsed p.parsed

theorem fieldSpan_eq_tokenSpan (p : LocatedParsed source) (index : Fin 16) :
    p.fieldSpan index = p.tokenSpan index.val := by
  have bound : index.val < p.tree.locations.length := by
    have count := p.location_count
    simp only [Modelica.Selection.LocatedParsed.locations] at count
    rw [count]
    exact index.isLt
  simp only [Modelica.Selection.LocatedParsed.tokenSpan]
  rw [Modelica.Selection.LocatedParsed.tokenSpan_eq]
  simp [fieldSpan, Modelica.Selection.LocatedParsed.locations, List.getElem?_eq_getElem bound]

private theorem record_text (p : LocatedParsed source) (index : Nat) (token : Token)
    (h : p.parsed.ast.tokens[index]? = some token) : (p.tokenSpan index).text = token.text :=
  Modelica.Selection.LocatedParsed.tokenSpan_record p index token h

theorem modelName_text (p : LocatedParsed source) :
    (p.tokenSpan 1).text = p.parsed.ast.name :=
  p.record_text 1 (.ident p.parsed.ast.name) rfl

theorem state_text (p : LocatedParsed source) :
    (p.tokenSpan 3).text = p.parsed.ast.state :=
  p.record_text 3 (.ident p.parsed.ast.state) rfl

theorem state_field_text (p : LocatedParsed source) :
    (p.fieldSpan 3).text = p.parsed.ast.state := by
  rw [p.fieldSpan_eq_tokenSpan]
  exact p.state_text

theorem derivativeName_text (p : LocatedParsed source) :
    (p.tokenSpan 8).text = p.parsed.ast.derivativeName :=
  p.record_text 8 (.ident p.parsed.ast.derivativeName) rfl

theorem endName_text (p : LocatedParsed source) :
    (p.tokenSpan 14).text = p.parsed.ast.endName :=
  p.record_text 14 (.ident p.parsed.ast.endName) rfl

theorem constant_text (p : LocatedParsed source) : (p.tokenSpan 11).text = "1" :=
  p.record_text 11 (.number "1") rfl

theorem resolved_references (p : LocatedParsed source) (h : AST.Resolved p.parsed.ast) :
    (p.tokenSpan 8).text = (p.tokenSpan 3).text ∧
    (p.tokenSpan 14).text = (p.tokenSpan 1).text := by
  simp [p.derivativeName_text, p.state_text, p.endName_text, p.modelName_text,
    h.derivative_resolves, h.end_matches]

/-- Enriching diagnostics preserves every successful resolution. -/
theorem resolve_complete (p : LocatedParsed source) (h : AST.Resolved p.parsed.ast) :
    p.resolve = .ok ⟨h⟩ := by
  simp [resolve, AST.resolve_complete _ h]

/-- Every name error identifies the offending AST occurrence and its actual
declaration, including the source text at both ranges. End-name disagreement
takes precedence when both names are wrong. No search for equal text is used. -/
theorem resolve_error_locations (p : LocatedParsed source) (e : Parser.Source.Diagnostic source)
    (h : p.resolve = .error e) :
    e.phase = "resolve" ∧
      ((p.parsed.ast.endName ≠ p.parsed.ast.name ∧
        e.span = p.tokenSpan 14 ∧ e.span.text = p.parsed.ast.endName ∧
        e.related.map (·.span) = [p.tokenSpan 1] ∧
        e.related.map (fun note => note.span.text) = [p.parsed.ast.name]) ∨
       (p.parsed.ast.endName = p.parsed.ast.name ∧
        p.parsed.ast.derivativeName ≠ p.parsed.ast.state ∧
        e.span = p.tokenSpan 8 ∧ e.span.text = p.parsed.ast.derivativeName ∧
        e.related.map (·.span) = [p.tokenSpan 3] ∧
        e.related.map (fun note => note.span.text) = [p.parsed.ast.state])) := by
  by_cases hn : p.parsed.ast.endName = p.parsed.ast.name
  · by_cases hd : p.parsed.ast.derivativeName = p.parsed.ast.state
    · simp [resolve, AST.resolve, hn, hd] at h
    · simp only [resolve, AST.resolve, hn, hd, ↓reduceDIte, ↓reduceIte,
        Except.error.injEq] at h
      subst e
      exact ⟨rfl, .inr ⟨hn, hd, rfl, p.derivativeName_text, rfl,
        by simp [p.state_text]⟩⟩
  · simp only [resolve, AST.resolve, hn, ↓reduceDIte, ↓reduceIte,
      Except.error.injEq] at h
    subst e
    exact ⟨rfl, .inl ⟨hn, rfl, p.endName_text, rfl,
      by simp [p.modelName_text]⟩⟩

end LocatedParsed
end Rumoca
