import Parser.Scanner

open _root_.Parser

/-! Named syntax for the exact GALEC unit profile. This layer resolves neither
DAE equations nor tensor shapes. It records every declaration/use/end name so
the checked phase cannot silently repair a mismatched generated reference. -/
namespace Rumoca.GALEC.Syntax

structure Block where
  name : String
  state : String
  clock : String
  initialState : String
  initialClock : String
  stepTarget : String
  stepRead : String
  endName : String
  deriving Repr, BEq, DecidableEq

def Block.tokens (b : Block) : List Token :=
  [.literal "block", .ident b.name, .literal "output", .literal "Real", .ident b.state,
   .literal ";", .literal "protected", .literal "constant", .literal "Real", .ident b.clock,
   .literal ";", .literal "public", .literal "method", .literal "Startup", .literal "algorithm",
   .literal "self", .literal ".", .ident b.initialState, .literal ":=", .literal "0.0", .literal ";",
   .literal "self", .literal ".", .ident b.initialClock, .literal ":=", .literal "1.0", .literal ";",
   .literal "end", .literal "Startup", .literal ";", .literal "method", .literal "Recalibrate",
   .literal "algorithm", .literal "end", .literal "Recalibrate", .literal ";",
   .literal "method", .literal "DoStep", .literal "algorithm", .literal "self", .literal ".",
   .ident b.stepTarget, .literal ":=", .literal "(", .literal "self", .literal ".", .ident b.stepRead,
   .literal "+", .literal "1.0", .literal ")", .literal ";", .literal "end", .literal "DoStep", .literal ";",
   .literal "end", .ident b.endName, .literal ";"]

def identifiers (ts : List Token) : List String :=
  ts.filterMap fun t => match t with | .ident name => some name | _ => none

/-- A linear token equality check avoids a large nested literal-match tree.
The fields are still explicit, and every punctuation/literal is checked. -/
def decode (ts : List Token) : Option Block :=
  match identifiers ts with
  | [name, state, clock, initialState, initialClock, stepTarget, stepRead, endName] =>
    let b := Block.mk name state clock initialState initialClock stepTarget stepRead endName
    if ts = b.tokens then some b else none
  | _ => none

set_option maxRecDepth 10000 in
theorem decode_tokens (b : Block) : decode b.tokens = some b := by
  cases b
  simp [decode, identifiers, Block.tokens]

set_option maxRecDepth 10000 in
theorem tokens_of_decode (h : decode ts = some b) : ts = b.tokens := by
  unfold decode at h
  split at h
  · dsimp only at h
    split at h
    · cases Option.some.inj h; assumption
    · contradiction
  · contradiction

def Resolved (b : Block) : Prop :=
  b.name = b.endName ∧ b.state ≠ b.clock ∧
  b.initialState = b.state ∧ b.initialClock = b.clock ∧
  b.stepTarget = b.state ∧ b.stepRead = b.state

instance (b : Block) : Decidable (Resolved b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def unit : Block :=
  ⟨"UnitIntegrator", "x", "samplePeriod", "x", "samplePeriod", "x", "x", "UnitIntegrator"⟩

theorem unit_resolved : Resolved unit := by decide

/-- The finite profile recognizes method names as distinguished words. Full
GALEC quoted names, comments, numeric forms and reserved-name analysis are not
implemented by this lexical profile. Unknown words still reach syntax checking.
Number runs are coarse tokens; the grammar admits only `0.0` and `1.0`. -/
def scanner : Scanner.Config where
  wordStart := asciiLetter
  wordRest := identRest
  numberRest := fun c => c.isDigit || c == '.'
  classify := fun word =>
    if ["block", "output", "Real", "protected", "constant", "public", "method", "algorithm",
        "self", "end", "Startup", "Recalibrate", "DoStep", "input", "parameter", "function",
        "record", "signals", "Boolean", "Integer", "limit", "if", "signal", "in", "then",
        "elseif", "else", "for", "loop", "and", "or", "not", "size", "while", "do", "until",
        "break", "return", "enumeration", "true", "false"].contains word
    then .literal word else .ident word
  single := fun c => [';', '.', '+', '(', ')'].contains c
  pair := fun c => if c == ':' then some '=' else none

end Rumoca.GALEC.Syntax
