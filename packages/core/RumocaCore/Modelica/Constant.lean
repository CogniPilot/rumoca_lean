import RumocaCore.Modelica.Select
import ModelicaParser.Constant.Decimal

/-! The G01 constant-rate profile, selected from the general syntax tree: two
or more plain scalar `Real` states, each with one `der(state) = literal`
equation whose right-hand side is one signed decimal number token. Names remain
in the record; resolution binds derivative references and parses the rate
spellings. Resolution rejects a mismatched end name, duplicate state
declarations, an equation set that is not a permutation of the declared states,
any right-hand side that is not a signed decimal literal, and any rate whose
magnitude exceeds the admitted bound (`Decimal.admitted`). The permutation
condition makes the equation order immaterial. -/
namespace Rumoca.ConstantProfile
open _root_.Parser

/-- One equation: the differentiated name and the spelling of its rate: an
optional sign followed by an unsigned number, for example "2.5" or "-1". -/
structure Equation where
  derivative : String
  rate : String
  deriving Repr, BEq, DecidableEq

/-- Two or more states (`state0`, `state1`, `statesRest`) and one or more
equations (`equation0`, `equationsRest`). -/
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
  [.ident "Real", .ident s, .literal ";"]

/-- The tokens of a rate: its sign, when it has one, and the unsigned number. -/
def rateTokens (rate : String) : List Token :=
  match rate.toList with
  | '-' :: rest => [.literal "-", .number (String.ofList rest)]
  | '+' :: rest => [.literal "+", .number (String.ofList rest)]
  | _ => [.number rate]

def equationTokens (e : Equation) : List Token :=
  [.literal "der", .literal "(", .ident e.derivative, .literal ")", .literal "="] ++
    rateTokens e.rate ++ [.literal ";"]

def Model.states (m : Model) : List String := m.state0 :: m.state1 :: m.statesRest
def Model.equations (m : Model) : List Equation := m.equation0 :: m.equationsRest

/-- The token sequence of a constant-rate source. -/
def Model.tokens (m : Model) : List Token :=
  [.literal "model", .ident m.name] ++
    (m.states.flatMap declTokens) ++
    [.literal "equation"] ++
    (m.equations.flatMap equationTokens) ++
    [.literal "end", .ident m.endName, .literal ";"]

/-- A resolved constant-rate model. The permutation of derivative names against
declared states binds every equation to a distinct declared state and covers
every state exactly once, independently of the written order. Every rate is a
signed decimal literal within the admitted magnitude. -/
def Model.Resolved (m : Model) : Prop :=
  m.endName = m.name ∧
  m.states.Nodup ∧
  (m.equations.map Equation.derivative).Perm m.states ∧
  ∀ e ∈ m.equations, (parseDecimal e.rate).any Decimal.admitted

instance (m : Model) : Decidable m.Resolved := by
  unfold Model.Resolved; infer_instance

/-! ### Selection from the general syntax tree -/

section Selection
open Modelica Modelica.Select

/-- The element of a plain `Real NAME;` state declaration. -/
def stateElement (s : String) : Modelica.AST.Element :=
  .component ⟨none, [.ident "Real"], none, [⟨.ident s, none, none⟩]⟩

/-- The right-hand side written for a rate spelling: a sign applied to the
unsigned number, or the number alone. -/
def rateExpr (rate : String) : Modelica.AST.Expr :=
  match rate.toList with
  | '-' :: rest => .unary (.literal "-") (bare (.number (String.ofList rest)))
  | '+' :: rest => .unary (.literal "+") (bare (.number (String.ofList rest)))
  | _ => bare (.number rate)

/-- The equation `der(NAME) = RATE;`. -/
def rateEquation (e : Equation) : Modelica.AST.Equation :=
  .simple (.call .der [bare (.ident e.derivative)]) (rateExpr e.rate)

/-- An unsigned number spelling, which begins with a digit or a point. -/
def unsignedSpelling (spelling : String) : Bool :=
  match spelling.toList with
  | c :: _ => c.isDigit || c == '.'
  | [] => false

/-- A rate: a signed number, or an unsigned number that is not a digit run. As in
the earlier lexical profile, an unsigned integer spelling is not a rate literal. -/
def rate (pos : Nat) : Modelica.AST.Expr → Except Rejection String
  | .reference ⟨false, [⟨.number spelling, none⟩]⟩ =>
    if unsignedSpelling spelling && !spelling.toList.all Char.isDigit then .ok spelling
    else .error ⟨pos, s!"the rate may not be {spelling}"⟩
  | .unary (.literal sign) (.reference ⟨false, [⟨.number spelling, none⟩]⟩) =>
    if (sign == "-" || sign == "+") && unsignedSpelling spelling then .ok (sign ++ spelling)
    else .error ⟨pos, s!"the rate may not be {sign}{spelling}"⟩
  | _ => .error ⟨pos, "the rate must be a signed decimal number"⟩

theorem rate_ok {pos : Nat} {e : Modelica.AST.Expr} {s : String} (h : rate pos e = .ok s) :
    e = rateExpr s := by
  unfold rate at h
  split at h
  · rename_i spelling
    split at h
    · rename_i admitted
      cases h
      have first : unsignedSpelling s = true := by simp_all
      unfold unsignedSpelling at first
      unfold rateExpr
      split
      · rename_i rest same; simp [same] at first
      · rename_i rest same; simp [same] at first
      · rfl
    · cases h
  · rename_i sign spelling
    split at h
    · rename_i admitted
      cases h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at admitted
      obtain ⟨signed | signed, _⟩ := admitted <;> subst signed <;>
        simp [rateExpr, bare, String.toList_append, String.ofList_toList]
    · cases h
  · cases h

theorem rateExpr_printed (s : String) : Modelica.Print.expr (rateExpr s) = rateTokens s := by
  unfold rateExpr rateTokens
  split <;> rfl

def states (pos : Nat) : List Modelica.AST.Element → Except Rejection (List String)
  | [] => .ok []
  | first :: rest => do
    let state ← Select.state pos "a state declaration" first
    let others ← states (pos + 3) rest
    return state :: others

theorem states_ok {pos : Nat} {elements : List Modelica.AST.Element} {names : List String}
    (h : states pos elements = .ok names) : elements = names.map stateElement := by
  induction elements generalizing pos names with
  | nil => cases h; rfl
  | cons first rest ih =>
    obtain ⟨state, declared, h⟩ := bind_ok h
    obtain ⟨others, following, h⟩ := bind_ok h
    cases h
    rw [state_ok declared, ih following]
    rfl

def rates (pos : Nat) : List Modelica.AST.Equation → Except Rejection (List Equation)
  | [] => .ok []
  | .simple left right :: rest => do
    let derivative ← Select.derivative pos left
    let rate ← rate (pos + 5) right
    let others ← rates (pos + 7) rest
    return ⟨derivative, rate⟩ :: others

theorem rates_ok {pos : Nat} {equations : List Modelica.AST.Equation} {read : List Equation}
    (h : rates pos equations = .ok read) : equations = read.map rateEquation := by
  induction equations generalizing pos read with
  | nil => cases h; rfl
  | cons first rest ih =>
    obtain ⟨left, right⟩ := first
    obtain ⟨derivative, differentiated, h⟩ := bind_ok h
    obtain ⟨rate, numbered, h⟩ := bind_ok h
    obtain ⟨others, following, h⟩ := bind_ok h
    cases h
    rw [derivative_ok differentiated, rate_ok numbered, ih following]
    rfl

/-- Select the constant-rate profile from a parsed tree. -/
def select (d : Modelica.AST.StoredDefinition) : Except Rejection Model := do
  let header ← Select.model d
  let declared ← states 2 header.2.1.elements
  let equations ← Select.equations (2 + elementsWidth header.2.1.elements) header.2.1
  let read ← rates (3 + elementsWidth header.2.1.elements) equations
  match declared, read with
  | state0 :: state1 :: statesRest, equation0 :: equationsRest =>
    return ⟨header.1, state0, state1, statesRest, equation0, equationsRest, header.2.2⟩
  | _ :: _ :: _, [] =>
    throw ⟨3 + elementsWidth header.2.1.elements, "the constant-rate profile has at least one equation"⟩
  | _, _ => throw ⟨2, "the constant-rate profile declares at least two states"⟩

private theorem elements_printed (names : List String) :
    ((names.map stateElement).flatMap fun e => Modelica.Print.element e ++ [.literal ";"]) =
      names.flatMap declTokens := by
  induction names with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl

private theorem equation_printed (e : Equation) :
    Modelica.Print.equation (rateEquation e) ++ [.literal ";"] = equationTokens e := by
  simp only [rateEquation, Modelica.Print.equation, rateExpr_printed, equationTokens]
  rfl

private theorem equations_printed (read : List Equation) :
    ((read.map rateEquation).flatMap fun e => Modelica.Print.equation e ++ [.literal ";"]) =
      read.flatMap equationTokens := by
  induction read with
  | nil => rfl
  | cons e _ ih =>
    simp only [List.map_cons, List.flatMap_cons, ih, equation_printed]

/-- A selected tree prints to the tokens of its record. -/
theorem select_printed {d : Modelica.AST.StoredDefinition} {m : Model} (h : select d = .ok m) :
    Modelica.Print.storedDefinition d = m.tokens := by
  unfold select at h
  obtain ⟨⟨name, ⟨elements, sections⟩, endName⟩, found, h⟩ := bind_ok h
  obtain ⟨declared, stated, h⟩ := bind_ok h
  obtain ⟨equations, sectioned, h⟩ := bind_ok h
  obtain ⟨read, rated, h⟩ := bind_ok h
  have elements_eq : elements = _ := states_ok stated
  have sections_eq : sections = _ := equations_ok sectioned
  have equations_eq := rates_ok rated
  rw [model_ok found, elements_eq, sections_eq, equations_eq]
  split at h
  · cases h
    simp only [Modelica.Print.storedDefinition, Modelica.Print.classDefinition,
      Modelica.Print.classSpecifier, Modelica.Print.composition, Modelica.Print.equationSection,
      List.flatMap_cons, List.flatMap_nil, elements_printed, equations_printed, Model.tokens,
      Model.states, Model.equations]
    simp
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

/-- Resolution failures keep a structured range and a specific message. -/
def LocatedParsed.resolve (p : LocatedParsed source) :
    Except (_root_.Parser.Source.Diagnostic source) (PLift p.parsed.ast.Resolved) :=
  if h : p.parsed.ast.Resolved then .ok ⟨h⟩
  else
    let m := p.parsed.ast
    let message :=
      if m.endName ≠ m.name then "end name does not match the model name"
      else if ¬ m.states.Nodup then "duplicate state declaration"
      else if ¬ (m.equations.map Equation.derivative).Perm m.states then
        "each declared state must have exactly one der equation"
      else if ¬ m.equations.all (fun e => (parseDecimal e.rate).isSome) then
        "right-hand side is not a signed decimal literal"
      else "rate magnitude must be below 2^969"
    .error ⟨"resolve", p.tokenSpan 1, message, []⟩

theorem LocatedParsed.resolve_complete (p : LocatedParsed source) (h : p.parsed.ast.Resolved) :
    p.resolve = .ok ⟨h⟩ := by simp [resolve, h]

end Rumoca.ConstantProfile
