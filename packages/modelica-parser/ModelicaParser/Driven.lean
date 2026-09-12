import ModelicaParser.Actions
import ModelicaParser.Grammar

open _root_.Parser

/-! Minimal input/output Modelica profile for FMI: one external Real input and
one continuous Real output state, initialized exactly to zero. Attribute names
are identifiers in MLS; attribute lookup is checked during resolution. -/
namespace Rumoca.Driven

structure Model where
  name : String
  input : String
  state : String
  startAttribute : String
  fixedAttribute : String
  derivativeName : String
  rhsName : String
  endName : String
  deriving Repr, BEq, DecidableEq

def Model.tokens (m : Model) : List Token :=
  [.literal "model", .ident m.name,
   .literal "input", .literal "Real", .ident m.input, .literal ";",
   .literal "output", .literal "Real", .ident m.state, .literal "(",
   .ident m.startAttribute, .literal "=", .literal "0", .literal ",",
   .ident m.fixedAttribute, .literal "=", .literal "true", .literal ")", .literal ";",
   .literal "equation", .literal "der", .literal "(", .ident m.derivativeName,
   .literal ")", .literal "=", .ident m.rhsName, .literal ";",
   .literal "end", .ident m.endName, .literal ";"]

/-- Extract the eight semantic fields, then check the complete token sequence.
This avoids the large native decision tree generated for a 30-token nested
constructor/literal pattern. Equality checks are linear and fully checked. -/
def identifiers (ts : List Token) : List String :=
  ts.filterMap fun t => match t with | .ident name => some name | .literal _ => none

def decode (ts : List Token) : Option Model :=
  match identifiers ts with
  | [name, input, state, startAttribute, fixedAttribute, derivativeName, rhsName, endName] =>
    let model := Model.mk name input state startAttribute fixedAttribute derivativeName rhsName endName
    if ts = model.tokens then some model else none
  | _ => none

theorem decode_sound (ts : List Token) (m : Model) (h : decode ts = some m) :
    ts = m.tokens := by
  unfold decode at h
  split at h
  · dsimp only at h
    split at h
    · cases Option.some.inj h; assumption
    · contradiction
  · contradiction

theorem decode_complete (m : Model) : decode m.tokens = some m := by
  cases m
  simp [decode, identifiers, Model.tokens]

theorem in_grammar (m : Model) :
    EBNF.Accepts Generated.sourceGrammar (m.tokens.map Token.symbol) := by
  apply Grammar.accepts_composition
    ((m.tokens.drop 2).take (m.tokens.length - 5) |>.map Token.symbol)
  simp [Generated.rule_composition, Generated.rule_driven_composition,
    Generated.rule_input, Generated.rule_output, Generated.rule_component_clause,
    Generated.rule_type_specifier, Generated.rule_component_list,
    Generated.rule_component_declaration, Generated.rule_declaration,
    Generated.rule_initialized_component_clause, Generated.rule_initialized_declaration,
    Generated.rule_class_modification, Generated.rule_argument_list,
    Generated.rule_zero_modification, Generated.rule_fixed_modification,
    Generated.rule_true, Generated.rule_driven_equation_section,
    Generated.rule_driven_equation, Generated.rule_component_reference,
    Generated.rule_equation, Generated.rule_der, Generated.rule_ident,
    EBNF.Derives.seq_iff, EBNF.Derives.alt_iff, EBNF.Derives.terminal_iff,
    Model.tokens, Token.symbol]

def actions : ParserActions.Actions Model :=
  ⟨Model.tokens, decode, decode_sound, decode_complete, in_grammar⟩

abbrev Parsed := ParserActions.Parsed actions
def parse := ParserActions.parse actions

def Resolved (m : Model) : Prop :=
  m.endName = m.name ∧ m.derivativeName = m.state ∧ m.rhsName = m.input ∧
  m.input ≠ m.state ∧ m.startAttribute = "start" ∧ m.fixedAttribute = "fixed"

instance (m : Model) : Decidable (Resolved m) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def resolve (m : Model) : Except Diagnostic (PLift (Resolved m)) :=
  if h : Resolved m then .ok ⟨h⟩
  else .error ⟨"resolve", 0, "expected distinct input/state, matching references, start=0 and fixed=true"⟩

theorem resolve_complete (h : Resolved m) : resolve m = .ok ⟨h⟩ := by simp [resolve, h]

end Rumoca.Driven
