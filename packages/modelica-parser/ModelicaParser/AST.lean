import ModelicaParser.Lexer

open _root_.Parser

namespace Rumoca.AST

/-- Syntax only. Name agreement belongs to resolution, not parsing. -/
structure Model where
  name : String
  state : String
  derivativeName : String
  endName : String
  deriving Repr, BEq, DecidableEq

def Model.tokens (m : Model) : List Token :=
  [.literal "model", .ident m.name, .literal "Real", .ident m.state,
   .literal ";", .literal "equation", .literal "der", .literal "(",
   .ident m.derivativeName, .literal ")", .literal "=", .literal "1",
   .literal ";", .literal "end", .ident m.endName, .literal ";"]

def decode : List Token → Option Model
  | [.literal "model", .ident name, .literal "Real", .ident state,
     .literal ";", .literal "equation", .literal "der", .literal "(",
     .ident derivativeName, .literal ")", .literal "=", .literal "1",
     .literal ";", .literal "end", .ident endName, .literal ";"] =>
       some ⟨name, state, derivativeName, endName⟩
  | _ => none

theorem decode_complete (m : Model) : decode m.tokens = some m := by
  cases m; rfl

theorem decode_sound (ts : List Token) (m : Model) (h : decode ts = some m) :
    ts = m.tokens := by
  unfold decode at h
  split at h
  · cases Option.some.inj h; rfl
  · contradiction

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

end Rumoca.AST
