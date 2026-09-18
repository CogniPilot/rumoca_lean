import Parser.Token
import ModelicaParser.Lexer

/-! Syntax for the G01 constant-rate profile: two or more scalar Real states,
each with one `der(state) = literal` equation whose right-hand side is a signed
decimal literal recognized as a single value-erasing number token. Names remain
in the AST; resolution binds derivative references and parses the rate
spellings. No core IR is imported by this frontend. -/
namespace Rumoca.ConstantProfile
open _root_.Parser

/-- One equation: the differentiated name and the literal spelling of its rate
(the number token text, for example "2.5" or "-1"). -/
structure Equation where
  derivative : String
  rate : String
  deriving Repr, BEq, DecidableEq

/-- Two or more states (`state0`, `state1`, `statesRest`) and one or more
equations (`equation0`, `equationsRest`). Encoding the mandatory items keeps
every value's token stream inside the generated `constant_composition`. -/
structure Model where
  name : String
  state0 : String
  state1 : String
  statesRest : List String
  equation0 : Equation
  equationsRest : List Equation
  endName : String
  deriving Repr, BEq, DecidableEq

def declTokens (s : String) : List Token :=
  [.literal "Real", .ident s, .literal ";"]

def equationTokens (e : Equation) : List Token :=
  [.literal "der", .literal "(", .ident e.derivative, .literal ")", .literal "=",
   .number e.rate, .literal ";"]

def Model.states (m : Model) : List String := m.state0 :: m.state1 :: m.statesRest
def Model.equations (m : Model) : List Equation := m.equation0 :: m.equationsRest

def Model.tokens (m : Model) : List Token :=
  [.literal "model", .ident m.name] ++
    (m.states.flatMap declTokens) ++
    [.literal "equation"] ++
    (m.equations.flatMap equationTokens) ++
    [.literal "end", .ident m.endName, .literal ";"]

/-- Greedy structural decoders. `decodeDecls` consumes `Real ident ;` groups;
`decodeEqs` consumes `der ( ident ) = ident ;` groups. Both stop at the first
token that does not match, returning the consumed list and the remainder. -/
def decodeDecls : List Token → List String × List Token
  | .literal "Real" :: .ident s :: .literal ";" :: rest =>
      let (ss, tail) := decodeDecls rest
      (s :: ss, tail)
  | rest => ([], rest)

def decodeEqs : List Token → List Equation × List Token
  | .literal "der" :: .literal "(" :: .ident d :: .literal ")" :: .literal "=" ::
      .number r :: .literal ";" :: rest =>
      let (es, tail) := decodeEqs rest
      (⟨d, r⟩ :: es, tail)
  | rest => ([], rest)

/-- The structural pass recovers the model; the exact-token guard makes
soundness immediate. As in the array profile, decoding never substitutes a
successful example for the general token-language contract. -/
def decode (ts : List Token) : Option Model :=
  match ts with
  | .literal "model" :: .ident name :: rest =>
      match decodeDecls rest with
      | (s0 :: s1 :: ssRest, .literal "equation" :: rest1) =>
          match decodeEqs rest1 with
          | (e0 :: esRest, [.literal "end", .ident endName, .literal ";"]) =>
              let m : Model := ⟨name, s0, s1, ssRest, e0, esRest, endName⟩
              if ts = m.tokens then some m else none
          | _ => none
      | _ => none
  | _ => none

/-! ### Round-trip soundness and completeness -/

theorem decode_sound (ts : List Token) (m : Model) (h : decode ts = some m) :
    ts = m.tokens := by
  unfold decode at h
  repeat' split at h
  all_goals simp_all

/-- Both greedy passes stop exactly at the following section keyword. -/
theorem decodeDecls_append (ss : List String) (rest : List Token)
    (hrest : decodeDecls rest = ([], rest)) :
    decodeDecls (ss.flatMap declTokens ++ rest) = (ss, rest) := by
  induction ss with
  | nil => simpa using hrest
  | cons s ss ih => simp only [List.flatMap_cons, declTokens,
      List.cons_append, List.nil_append, decodeDecls, ih]

theorem decodeEqs_append (es : List Equation) (rest : List Token)
    (hrest : decodeEqs rest = ([], rest)) :
    decodeEqs (es.flatMap equationTokens ++ rest) = (es, rest) := by
  induction es with
  | nil => simpa using hrest
  | cons e es ih => simp only [List.flatMap_cons, equationTokens,
      List.cons_append, List.nil_append, decodeEqs, ih]

theorem decodeDecls_equation (rest : List Token) :
    decodeDecls (.literal "equation" :: rest) = ([], .literal "equation" :: rest) := by
  simp [decodeDecls]

theorem decodeEqs_end (rest : List Token) :
    decodeEqs (.literal "end" :: rest) = ([], .literal "end" :: rest) := by
  simp [decodeEqs]

theorem decode_complete (m : Model) : decode m.tokens = some m := by
  obtain ⟨name, s0, s1, ssRest, e0, esRest, endName⟩ := m
  have htok : Model.tokens ⟨name, s0, s1, ssRest, e0, esRest, endName⟩ =
      .literal "model" :: .ident name ::
        ((s0 :: s1 :: ssRest).flatMap declTokens ++ .literal "equation" ::
          ((e0 :: esRest).flatMap equationTokens ++
            [.literal "end", .ident endName, .literal ";"])) := by
    simp only [Model.tokens, Model.states, Model.equations, List.cons_append,
      List.nil_append, List.append_assoc]
  simp only [decode, htok, decodeDecls_append (s0 :: s1 :: ssRest) _ (decodeDecls_equation _),
    decodeEqs_append (e0 :: esRest) _ (decodeEqs_end _), if_true]

end Rumoca.ConstantProfile
