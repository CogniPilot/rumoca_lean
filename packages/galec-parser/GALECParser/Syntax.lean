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

/-- Proof-only pre-cutover profile specification. Production source parsing
uses the actual CST and typed structural actions, not this token decoder.
The fields remain explicit, and every punctuation/literal is checked. -/
noncomputable def decode (ts : List Token) : Option Block :=
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

/-! Named syntax for the fixed-extent tensor square profile. Like the scalar
layer it resolves no shapes; it records every declaration, reference and end
name so the checked phase cannot silently repair a mismatched generated block.
Array extents are the concrete `2` literals of the admitted profile. -/

structure TensorBlock where
  name : String
  input : String
  state : String
  jacobian : String
  clock : String
  initialState : String
  initialClock : String
  stepState : String
  derivLeft : String
  derivRight : String
  jacTarget : String
  jacFn : String
  jacLeft : String
  jacRight : String
  jacArg : String
  endName : String
  deriving Repr, BEq, DecidableEq

def TensorBlock.tokens (b : TensorBlock) : List Token :=
  [.literal "block", .ident b.name,
   .literal "input", .literal "Real", .literal "[", .literal "2", .literal "]", .ident b.input, .literal ";",
   .literal "output", .literal "Real", .literal "[", .literal "2", .literal "]", .ident b.state, .literal ";",
   .literal "output", .literal "Real", .literal "[", .literal "2", .literal ",", .literal "2", .literal "]",
   .ident b.jacobian, .literal ";",
   .literal "protected", .literal "constant", .literal "Real", .ident b.clock, .literal ";",
   .literal "public",
   .literal "method", .literal "Startup", .literal "algorithm",
   .literal "self", .literal ".", .ident b.initialState, .literal ":=", .literal "0.0", .literal ";",
   .literal "self", .literal ".", .ident b.initialClock, .literal ":=", .literal "1.0", .literal ";",
   .literal "end", .literal "Startup", .literal ";",
   .literal "method", .literal "Recalibrate", .literal "algorithm", .literal "end", .literal "Recalibrate", .literal ";",
   .literal "method", .literal "DoStep", .literal "algorithm",
   .literal "self", .literal ".", .ident b.stepState, .literal ":=",
   .literal "self", .literal ".", .ident b.derivLeft, .literal ".*", .literal "self", .literal ".", .ident b.derivRight,
   .literal ";",
   .literal "self", .literal ".", .ident b.jacTarget, .literal ":=", .ident b.jacFn, .literal "(",
   .literal "self", .literal ".", .ident b.jacLeft, .literal ".*", .literal "self", .literal ".", .ident b.jacRight,
   .literal ",", .literal "self", .literal ".", .ident b.jacArg, .literal ")", .literal ";",
   .literal "end", .literal "DoStep", .literal ";",
   .literal "end", .ident b.endName, .literal ";"]

/-- Proof-only tensor profile specification retained for exact compatibility.
Every bracket, extent, operator and punctuation remains checked. -/
noncomputable def decodeTensor (ts : List Token) : Option TensorBlock :=
  match identifiers ts with
  | [name, input, state, jacobian, clock, initialState, initialClock, stepState,
     derivLeft, derivRight, jacTarget, jacFn, jacLeft, jacRight, jacArg, endName] =>
    let b := TensorBlock.mk name input state jacobian clock initialState initialClock stepState
      derivLeft derivRight jacTarget jacFn jacLeft jacRight jacArg endName
    if ts = b.tokens then some b else none
  | _ => none

set_option maxRecDepth 20000 in
theorem decodeTensor_tokens (b : TensorBlock) : decodeTensor b.tokens = some b := by
  cases b
  simp [decodeTensor, identifiers, TensorBlock.tokens]

set_option maxRecDepth 20000 in
theorem tokens_of_decodeTensor (h : decodeTensor ts = some b) : ts = b.tokens := by
  unfold decodeTensor at h
  split at h
  · dsimp only at h
    split at h
    · cases Option.some.inj h; assumption
    · contradiction
  · contradiction

/-- Name resolution of the tensor square profile: matching block/end names, a
state distinct from the clock, startup and step targets equal to the state, the
elementwise product of the input with itself, a Jacobian output whose built-in
is `jacobian` applied to that same product differentiated by the input. -/
def ResolvedTensor (b : TensorBlock) : Prop :=
  b.name = b.endName ∧ b.state ≠ b.clock ∧
  b.initialState = b.state ∧ b.initialClock = b.clock ∧
  b.stepState = b.state ∧
  b.derivLeft = b.input ∧ b.derivRight = b.input ∧
  b.jacTarget = b.jacobian ∧ b.jacFn = "jacobian" ∧
  b.jacLeft = b.input ∧ b.jacRight = b.input ∧ b.jacArg = b.input

instance (b : TensorBlock) : Decidable (ResolvedTensor b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def tensorUnit : TensorBlock :=
  ⟨"TensorSquare", "u", "x", "J", "samplePeriod", "x", "samplePeriod", "x",
   "u", "u", "J", "jacobian", "u", "u", "u", "TensorSquare"⟩

theorem tensorUnit_resolved : ResolvedTensor tensorUnit := by decide

/-- The tensor profile shares the scalar keyword classifier but adds array
bracket and comma punctuation and the elementwise `.*` operator. `.` remains a
single symbol for `self.` references and pairs to `.*` only before `*`. -/
def tensorScanner : Scanner.Config where
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
  single := fun c => [';', '.', '+', '(', ')', '[', ']', ','].contains c
  pair := fun c => if c == ':' then some '=' else if c == '.' then some '*' else none

end Rumoca.GALEC.Syntax
