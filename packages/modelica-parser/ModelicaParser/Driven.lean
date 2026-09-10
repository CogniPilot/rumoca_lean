import ModelicaParser.Actions

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

def pattern : List RuntimeGenerated.Letter :=
  (Model.mk "" "" "" "" "" "" "" "").tokens.map (RuntimeGenerated.encode ∘ Token.symbol)

set_option maxRecDepth 10000 in
theorem recognized (m : Model) :
    RuntimeGenerated.recognize (m.tokens.map (RuntimeGenerated.encode ∘ Token.symbol)) = true := by
  change RuntimeGenerated.recognize pattern = true
  decide +kernel

def actions : ParserActions.Actions Model :=
  ⟨Model.tokens, decode, decode_sound, decode_complete, recognized⟩

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
