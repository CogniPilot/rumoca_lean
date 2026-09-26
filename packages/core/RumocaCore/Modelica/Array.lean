import RumocaCore.Modelica.Select

/-! The square Jacobian array profile, selected from the general syntax tree:
an input and a state of extent two, a dense two-by-two Jacobian output, the
pointwise square as the state derivative, and a call of the Jacobian built-in.
A product is one tensor operation whose operands are source names. Calls retain
their name and arguments, so recognizing call syntax is separate from resolving
the intrinsic. Static extents belong to the profile; no element is enumerated. -/
namespace Rumoca.ArrayProfile
open _root_.Parser

structure Product where
  left : String
  right : String
  deriving Repr, BEq, DecidableEq

def Product.tokens (p : Product) : List Token :=
  [.ident p.left, .literal ".*", .ident p.right]

/-- Only the argument form needed by the first Jacobian is admitted. -/
structure Call where
  name : String
  expression : Product
  wrt : String
  deriving Repr, BEq, DecidableEq

inductive Builtin where
  | jacobian
  deriving Repr, BEq, DecidableEq

def Call.builtin? (c : Call) : Option Builtin :=
  if c.name = "jacobian" then some .jacobian else none

theorem Call.jacobian_iff (c : Call) : c.builtin? = some .jacobian ↔ c.name = "jacobian" := by
  simp [builtin?]

def Call.tokens (c : Call) : List Token :=
  [.ident c.name, .literal "("] ++ c.expression.tokens ++
    [.literal ",", .ident c.wrt, .literal ")"]

structure Header where
  name : String
  input : String
  state : String
  startAttribute : String
  fixedAttribute : String
  deriving Repr, BEq, DecidableEq

inductive Body where
  | jacobian (output derivative : String) (rhs : Product) (assigned : String) (call : Call)
  deriving Repr, BEq, DecidableEq

structure Model where
  header : Header
  body : Body
  endName : String
  deriving Repr, BEq, DecidableEq

/-- Static extents belong to this profile; no elements are enumerated. -/
def Model.stateDimensions (_ : Model) : List Nat := [2]

def Model.jacobianDimensions (_ : Model) : List Nat := [2, 2]

def Header.tokens (h : Header) : List Token :=
  [.literal "model", .ident h.name,
   .literal "input", .ident "Real", .ident h.input,
   .literal "[", .number "2", .literal "]", .literal ";",
   .literal "output", .ident "Real", .ident h.state,
   .literal "[", .number "2", .literal "]", .literal "(",
   .literal "each", .ident h.startAttribute, .literal "=", .number "0", .literal ",",
   .literal "each", .ident h.fixedAttribute, .literal "=", .literal "true", .literal ")",
   .literal ";"]

def Body.tokens : Body → List Token
  | .jacobian output derivative rhs assigned call =>
    [.literal "output", .ident "Real", .ident output, .literal "[", .number "2",
     .literal ",", .number "2", .literal "]", .literal ";",
     .literal "equation", .literal "der", .literal "(", .ident derivative,
     .literal ")", .literal "="] ++ rhs.tokens ++
    [.literal ";", .ident assigned, .literal "="] ++ call.tokens ++ [.literal ";"]

/-- The token sequence of a square-profile source. -/
def Model.tokens (m : Model) : List Token :=
  m.header.tokens ++ m.body.tokens ++ [.literal "end", .ident m.endName, .literal ";"]

/-- The token sequence determines the record. -/
theorem Model.tokens_injective {m m' : Model} (same : m.tokens = m'.tokens) : m = m' := by
  obtain ⟨⟨_, _, _, _, _⟩, body, _⟩ := m
  obtain ⟨⟨_, _, _, _, _⟩, body', _⟩ := m'
  obtain ⟨_, _, ⟨_, _⟩, _, ⟨_, ⟨_, _⟩, _⟩⟩ := body
  obtain ⟨_, _, ⟨_, _⟩, _, ⟨_, ⟨_, _⟩, _⟩⟩ := body'
  simp [Model.tokens, Header.tokens, Body.tokens, Product.tokens, Call.tokens] at same
  simp [same]

/-- This semantic restriction selects the existing proved square operator.
Selection also retains other names, allowing resolution to report their ranges. -/
def Model.Resolved (m : Model) : Prop :=
  m.endName = m.header.name ∧ m.header.input ≠ m.header.state ∧
  m.header.startAttribute = "start" ∧ m.header.fixedAttribute = "fixed" ∧
  match m.body with
  | .jacobian output derivative rhs assigned call =>
    output ≠ m.header.input ∧ output ≠ m.header.state ∧
    derivative = m.header.state ∧ rhs.left = m.header.input ∧ rhs.right = m.header.input ∧
    assigned = output ∧ call.builtin? = some .jacobian ∧
    call.expression.left = m.header.input ∧ call.expression.right = m.header.input ∧
    call.wrt = m.header.input

instance (m : Model) : Decidable m.Resolved := by
  unfold Model.Resolved
  cases m.body; infer_instance

/-! ### Selection from the general syntax tree -/

section Selection
open Modelica Modelica.Select

/-- The extents `[2]`. -/
def vector (pos : Nat) (what : String) : Option (List Modelica.AST.Expr) → Except Rejection Unit
  | some [extent] => exactly (pos + 1) what "2" extent
  | _ => .error ⟨pos, s!"{what} must have the extents [2]"⟩

theorem vector_ok {pos : Nat} {what : String} {indices : Option (List Modelica.AST.Expr)}
    {u : Unit} (h : vector pos what indices = .ok u) : indices = some [bare (.number "2")] := by
  unfold vector at h
  split at h
  · rw [exactly_ok h]
  · cases h

/-- The extents `[2, 2]`. -/
def matrix (pos : Nat) (what : String) : Option (List Modelica.AST.Expr) → Except Rejection Unit
  | some [rows, columns] => do
    exactly (pos + 1) what "2" rows
    exactly (pos + 3) what "2" columns
  | _ => .error ⟨pos, s!"{what} must have the extents [2, 2]"⟩

theorem matrix_ok {pos : Nat} {what : String} {indices : Option (List Modelica.AST.Expr)}
    {u : Unit} (h : matrix pos what indices = .ok u) :
    indices = some [bare (.number "2"), bare (.number "2")] := by
  unfold matrix at h
  split at h
  · obtain ⟨_, rows, columns⟩ := bind_ok h
    rw [exactly_ok rows, exactly_ok columns]
  · cases h

/-- One `each NAME = value` modification argument. -/
def eachArgument (pos : Nat) (what : String) (value : Modelica.AST.Expr → Except Rejection Unit) :
    Modelica.AST.Argument → Except Rejection String
  | ⟨true, ⟨[attr], some (.value written)⟩⟩ => do
    let name ← Select.name (pos + 1) what attr
    value written
    return name
  | _ => .error ⟨pos, s!"{what} must be written each NAME = value"⟩

theorem eachArgument_ok {pos : Nat} {what : String}
    {value : Modelica.AST.Expr → Except Rejection Unit} {a : Modelica.AST.Argument} {s : String}
    (h : eachArgument pos what value a = .ok s) :
    ∃ written u, value written = .ok u ∧ a = ⟨true, ⟨[.ident s], some (.value written)⟩⟩ := by
  unfold eachArgument at h
  split at h
  · rename_i attr written
    obtain ⟨name, named, h⟩ := bind_ok h
    obtain ⟨u, valued, h⟩ := bind_ok h
    cases h
    exact ⟨written, u, valued, by rw [name_ok named]⟩
  · cases h

/-- The value `true`. -/
def trueValue (pos : Nat) : Modelica.AST.Expr → Except Rejection Unit
  | .boolean (.literal "true") => .ok ()
  | _ => .error ⟨pos, "the fixed attr must be true"⟩

theorem trueValue_ok {pos : Nat} {e : Modelica.AST.Expr} {u : Unit} (h : trueValue pos e = .ok u) :
    e = .boolean (.literal "true") := by
  unfold trueValue at h
  split at h
  · rfl
  · cases h

/-- `(each start = 0, each fixed = true)` with the attr names retained. -/
def initialization (pos : Nat) : Option Modelica.AST.Modification → Except Rejection (String × String)
  | some (.class [start, fixed] none) => do
    let startName ← eachArgument (pos + 1) "the start attr" (exactly (pos + 4) "the start value" "0")
      start
    let fixedName ← eachArgument (pos + 1 + (Modelica.Print.argument start).length + 1)
      "the fixed attr" (trueValue (pos + 1 + (Modelica.Print.argument start).length + 4)) fixed
    return (startName, fixedName)
  | _ => .error ⟨pos, "the state must be initialized with (each start = 0, each fixed = true)"⟩

theorem initialization_ok {pos : Nat} {m : Option Modelica.AST.Modification} {names : String × String}
    (h : initialization pos m = .ok names) :
    m = some (.class [⟨true, ⟨[.ident names.1], some (.value (bare (.number "0")))⟩⟩,
      ⟨true, ⟨[.ident names.2], some (.value (.boolean (.literal "true")))⟩⟩] none) := by
  unfold initialization at h
  split at h
  · obtain ⟨startName, started, h⟩ := bind_ok h
    obtain ⟨fixedName, fixed, h⟩ := bind_ok h
    cases h
    obtain ⟨start, _, startValue, startShape⟩ := eachArgument_ok started
    obtain ⟨written, _, fixedValue, fixedShape⟩ := eachArgument_ok fixed
    rw [startShape, fixedShape, exactly_ok startValue, trueValue_ok fixedValue]
  · cases h

/-- `NAME .* NAME`. -/
def selectProduct (pos : Nat) : Modelica.AST.Expr → Except Rejection Product
  | .binary (.literal ".*") left right => do
    let l ← reference pos "the product operand" left
    let r ← reference (pos + (Modelica.Print.expr left).length + 1) "the product operand" right
    return ⟨l, r⟩
  | _ => .error ⟨pos, "expected the pointwise product of two names"⟩

theorem selectProduct_ok {pos : Nat} {e : Modelica.AST.Expr} {p : Product} (h : selectProduct pos e = .ok p) :
    e = .binary (.literal ".*") (bare (.ident p.left)) (bare (.ident p.right)) := by
  unfold selectProduct at h
  split at h
  · obtain ⟨l, left, h⟩ := bind_ok h
    obtain ⟨r, right, h⟩ := bind_ok h
    cases h
    rw [reference_ok left, reference_ok right]
  · cases h

/-- `NAME(NAME .* NAME, NAME)`: an ordinary call; resolution selects the built-in. -/
def selectCall (pos : Nat) : Modelica.AST.Expr → Except Rejection Call
  | .call (.reference ⟨false, [⟨callee, none⟩]⟩) [argument, wrt] => do
    let name ← Select.name pos "the callee" callee
    let expression ← selectProduct (pos + 2) argument
    let withRespectTo ← reference (pos + 3 + (Modelica.Print.expr argument).length)
      "the differentiation withRespectTo" wrt
    return ⟨name, expression, withRespectTo⟩
  | _ => .error ⟨pos, "expected a call of a named function with a product and a name"⟩

theorem selectCall_ok {pos : Nat} {e : Modelica.AST.Expr} {c : Call} (h : selectCall pos e = .ok c) :
    e = .call (.reference ⟨false, [⟨.ident c.name, none⟩]⟩)
      [.binary (.literal ".*") (bare (.ident c.expression.left)) (bare (.ident c.expression.right)),
       bare (.ident c.wrt)] := by
  unfold selectCall at h
  split at h
  · obtain ⟨name, named, h⟩ := bind_ok h
    obtain ⟨expression, product, h⟩ := bind_ok h
    obtain ⟨withRespectTo, varied, h⟩ := bind_ok h
    cases h
    rw [name_ok named, selectProduct_ok product, reference_ok varied]
  · cases h

/-- Select the square Jacobian profile from a parsed tree. -/
def select (d : Modelica.AST.StoredDefinition) : Except Rejection Model := do
  let header ← Select.model d
  let body := header.2.1
  match body.elements with
  | [inputElement, stateElement, outputElement] =>
    let input ← Select.declaration 2 "the input declaration" (some (.literal "input")) inputElement
    vector 5 "the input" input.2.1
    absent 8 "the input has no modification" input.2.2
    let state ← Select.declaration 9 "the state declaration" (some (.literal "output")) stateElement
    vector 12 "the state" state.2.1
    let attributes ← initialization 15 state.2.2
    let width := 2 + elementsWidth [inputElement, stateElement]
    let output ← Select.declaration width "the Jacobian output declaration"
      (some (.literal "output")) outputElement
    matrix (width + 3) "the Jacobian output" output.2.1
    absent (width + 8) "the Jacobian output has no modification" output.2.2
    let equations ← Select.equations (width + 9) body
    match equations with
    | [.simple derivativeSide rhs, .simple assignedSide callSide] =>
      let derivative ← Select.derivative (width + 10) derivativeSide
      let square ← selectProduct (width + 15) rhs
      let position := width + 16 + (Modelica.Print.expr rhs).length
      let assigned ← reference position "the assigned Jacobian" assignedSide
      let jacobian ← selectCall (position + 2) callSide
      return ⟨⟨header.1, input.1, state.1, attributes.1, attributes.2⟩,
        .jacobian output.1 derivative square assigned jacobian, header.2.2⟩
    | _ => throw ⟨width + 9, "the square profile has a derivative and a Jacobian equation"⟩
  | _ => throw ⟨2, "the square profile declares an input, a state and a Jacobian output"⟩

/-- A selected tree prints to the tokens of its record. -/
theorem select_printed {d : Modelica.AST.StoredDefinition} {m : Model} (h : select d = .ok m) :
    Modelica.Print.storedDefinition d = m.tokens := by
  unfold select at h
  obtain ⟨⟨name, ⟨elements, sections⟩, endName⟩, found, h⟩ := bind_ok h
  rw [model_ok found]
  simp only at h
  split at h
  · rename_i inputElement stateElement outputElement
    obtain ⟨input, inputDeclared, h⟩ := bind_ok h
    obtain ⟨_, inputVector, h⟩ := bind_ok h
    obtain ⟨_, inputPlain, h⟩ := bind_ok h
    obtain ⟨state, stateDeclared, h⟩ := bind_ok h
    obtain ⟨_, stateVector, h⟩ := bind_ok h
    obtain ⟨attributes, initialized, h⟩ := bind_ok h
    obtain ⟨output, outputDeclared, h⟩ := bind_ok h
    obtain ⟨_, outputMatrix, h⟩ := bind_ok h
    obtain ⟨_, outputPlain, h⟩ := bind_ok h
    obtain ⟨equations, sectioned, h⟩ := bind_ok h
    split at h
    · rename_i derivativeSide rhs assignedSide callSide
      obtain ⟨derivative, differentiated, h⟩ := bind_ok h
      obtain ⟨square, squared, h⟩ := bind_ok h
      obtain ⟨assigned, assignedName, h⟩ := bind_ok h
      obtain ⟨jacobian, called, h⟩ := bind_ok h
      cases h
      obtain ⟨inputName, inputIndices, inputModification⟩ := input
      obtain ⟨stateName, stateIndices, stateModification⟩ := state
      obtain ⟨outputName, outputIndices, outputModification⟩ := output
      have sections_eq : sections = _ := equations_ok sectioned
      have inputVector : inputIndices = _ := vector_ok inputVector
      have inputPlain : inputModification = _ := absent_ok inputPlain
      have stateVector : stateIndices = _ := vector_ok stateVector
      have initialized : stateModification = _ := initialization_ok initialized
      have outputMatrix : outputIndices = _ := matrix_ok outputMatrix
      have outputPlain : outputModification = _ := absent_ok outputPlain
      rw [sections_eq, declaration_ok inputDeclared, declaration_ok stateDeclared, declaration_ok outputDeclared,
        inputVector, inputPlain, stateVector, initialized, outputMatrix, outputPlain,
        derivative_ok differentiated, selectProduct_ok squared, reference_ok assignedName, selectCall_ok called]
      rfl
    · cases h
  · cases h

def selection : Selection Model := ⟨select, Model.tokens, fun _ _ => select_printed⟩

end Selection

open Modelica

abbrev Parsed (source : String) := selection.Parsed source

def parse (source : String) : Except Diagnostic (Parsed source) := selection.parse source

abbrev LocatedParsed (source : String) := selection.LocatedParsed source

def parseLocated (source : String) :
    Except (_root_.Parser.Source.Diagnostic source) (LocatedParsed source) :=
  selection.parseLocated source

variable {source : String}

theorem parse_eq_parsed (p : Parsed source) : parse source = .ok p :=
  Selection.parse_eq_parsed p

def Parsed.located (p : Parsed source) : LocatedParsed source := Selection.Parsed.located p

theorem Parsed.parseLocated_eq (p : Parsed source) : parseLocated source = .ok p.located :=
  Selection.Parsed.parseLocated_eq p

/-! ### Located calls and resolution -/

/-- A call's spelling is certified at each operand's actual position. Keeping
the complete aligned token stream also preserves punctuation and dimensions. -/
structure LocatedCall (source : String) (call : Call) where
  name : _root_.Parser.Source.Span source
  left : _root_.Parser.Source.Span source
  right : _root_.Parser.Source.Span source
  wrt : _root_.Parser.Source.Span source
  closing : _root_.Parser.Source.Span source
  name_text : name.text = call.name
  left_text : left.text = call.expression.left
  right_text : right.text = call.expression.right
  wrt_text : wrt.text = call.wrt
  closing_text : closing.text = ")"

def LocatedCall.expressionSpan (c : LocatedCall source call) : _root_.Parser.Source.Span source :=
  c.left.cover c.right

def LocatedCall.span (c : LocatedCall source call) : _root_.Parser.Source.Span source :=
  ((c.name.cover c.expressionSpan).cover c.wrt).cover c.closing

theorem LocatedCall.arguments_contained (c : LocatedCall source call) :
    c.span.Contains c.expressionSpan ∧ c.span.Contains c.wrt := by
  have h₁ := (c.name.cover c.expressionSpan).cover_right c.wrt
  have h₂ := ((c.name.cover c.expressionSpan).cover c.wrt).cover_left c.closing
  have h₃ := (c.name.cover c.expressionSpan).cover_left c.wrt
  have h₄ := c.name.cover_right c.expressionSpan
  exact ⟨⟨Nat.le_trans h₂.1 (Nat.le_trans h₃.1 h₄.1),
      Nat.le_trans h₄.2 (Nat.le_trans h₃.2 h₂.2)⟩,
    ⟨Nat.le_trans h₂.1 h₁.1, Nat.le_trans h₁.2 h₂.2⟩⟩

private theorem field_text (p : LocatedParsed source)
    (h : p.parsed.ast.body = .jacobian output derivative rhs assigned call)
    (index : Nat) (token : Token)
    (ht : (p.parsed.ast.header.tokens ++
      (Body.jacobian output derivative rhs assigned call).tokens ++
      [.literal "end", .ident p.parsed.ast.endName, .literal ";"])[index]? = some token) :
    (p.tokenSpan index).text = token.text := by
  have body : p.ast.body = .jacobian output derivative rhs assigned call := h
  apply Selection.LocatedParsed.tokenSpan_record p index token
  simpa only [selection, Model.tokens, body] using ht

def LocatedParsed.callLocation (p : LocatedParsed source)
    (h : p.parsed.ast.body = .jacobian output derivative rhs assigned call) :
    LocatedCall source call where
  name := p.tokenSpan 48
  left := p.tokenSpan 50
  right := p.tokenSpan 52
  wrt := p.tokenSpan 54
  closing := p.tokenSpan 55
  name_text := field_text p h 48 (.ident call.name) (by rfl)
  left_text := field_text p h 50 (.ident call.expression.left) (by rfl)
  right_text := field_text p h 52 (.ident call.expression.right) (by rfl)
  wrt_text := field_text p h 54 (.ident call.wrt) (by rfl)
  closing_text := field_text p h 55 (.literal ")") (by rfl)

def LocatedParsed.call? (p : LocatedParsed source) : Option ((c : Call) × LocatedCall source c) :=
  match h : p.parsed.ast.body with
  | .jacobian _ _ _ _ call => some ⟨call, p.callLocation h⟩

/-- Resolution failures keep structured ranges and the unresolved AST. -/
def LocatedParsed.resolve (p : LocatedParsed source) :
    Except (_root_.Parser.Source.Diagnostic source) (PLift p.parsed.ast.Resolved) :=
  if h : p.parsed.ast.Resolved then .ok ⟨h⟩
  else
    let m := p.parsed.ast
    let (index, message) :=
      if m.endName ≠ m.header.name then (58, "end name does not match the model name")
      else if m.header.startAttribute ≠ "start" then (17, "expected each start=0")
      else if m.header.fixedAttribute ≠ "fixed" then (22, "expected each fixed=true")
      else match m.body with
      | .jacobian output derivative rhs assigned call =>
        if m.header.input = m.header.state then (11, "input and state names must be distinct")
        else if output = m.header.input ∨ output = m.header.state then (29, "Jacobian output must have a distinct name")
        else if derivative ≠ m.header.state then (39, "derivative must reference the state")
        else if rhs.left ≠ m.header.input then (42, "product operand must reference the input")
        else if rhs.right ≠ m.header.input then (44, "product operand must reference the input")
        else if assigned ≠ output then (46, "equation must assign the Jacobian output")
        else if call.builtin? ≠ some .jacobian then (48, "expected the jacobian built-in")
        else if call.expression.left ≠ m.header.input then (50, "product operand must reference the input")
        else if call.expression.right ≠ m.header.input then (52, "product operand must reference the input")
        else (54, "differentiate with respect to the input")
    .error ⟨"resolve", p.tokenSpan index, message, []⟩

theorem LocatedParsed.resolve_complete (p : LocatedParsed source) (h : p.parsed.ast.Resolved) :
    p.resolve = .ok ⟨h⟩ := by simp [resolve, h]

end Rumoca.ArrayProfile
