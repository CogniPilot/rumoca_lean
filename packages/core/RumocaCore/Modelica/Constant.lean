import RumocaCore.Modelica.Select
import ModelicaParser.Constant.Decimal
import ModelicaParser.Inversion
import ModelicaParser.Derivations

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
  .component ⟨none, [.ident "Real"], none, [⟨⟨.ident s, none, none⟩, none, ⟨[], none⟩⟩]⟩

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

/-- Every point of a spelling is followed by a digit. -/
def interiorPoints : List Char → Bool
  | [] => true
  | '.' :: c :: rest => c.isDigit && interiorPoints (c :: rest)
  | ['.'] => false
  | _ :: rest => interiorPoints rest

/-- An unsigned number spelling admitted in a rate: it begins with a digit and
every point is followed by a digit. The MLS spellings with a point at an edge,
such as `2.`, `.5` and `2.e3`, are lexed as numbers but not admitted as rates. -/
def unsignedSpelling (spelling : String) : Bool :=
  match spelling.toList with
  | c :: _ => c.isDigit && interiorPoints spelling.toList
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
    let others ← rates (pos + (Modelica.Print.equation (.simple left right)).length + 1) rest
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
    Modelica.Print.someEquation (plain (rateEquation e)) ++ [.literal ";"] = equationTokens e := by
  simp only [plain, rateEquation, Modelica.Print.someEquation, Modelica.Print.equation,
    Modelica.Print.description, Modelica.Print.descriptionString, Modelica.Print.annotation,
    rateExpr_printed, equationTokens, List.append_nil]
  rfl

private theorem equations_printed (read : List Equation) :
    (((read.map rateEquation).map plain).flatMap fun q => Modelica.Print.someEquation q ++ [.literal ";"]) =
      read.flatMap equationTokens := by
  induction read with
  | nil => rfl
  | cons e _ ih =>
    simp only [List.map_cons, List.flatMap_cons, ih, equation_printed]

/-- A selected tree prints to the tokens of its record. -/
theorem select_printed {d : Modelica.AST.StoredDefinition} {m : Model} (h : select d = .ok m) :
    Modelica.Print.storedDefinition d = m.tokens := by
  unfold select at h
  obtain ⟨⟨name, ⟨elements, sections, annotation⟩, endName⟩, found, h⟩ := bind_ok h
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
      Modelica.Print.descriptionString, Modelica.Print.classAnnotation, List.flatMap_cons, List.flatMap_nil, elements_printed, equations_printed, Model.tokens,
      Model.states, Model.equations]
    simp
  · cases h
  · cases h

def selection : Selection Model := ⟨select, Model.tokens, fun _ _ => select_printed⟩

/-! ### Completeness -/

/-- A rate spelling selection admits: a sign and an unsigned spelling, or an
unsigned spelling that is not a digit run. -/
def rateSpelling (rate : String) : Bool :=
  match rate.toList with
  | '-' :: rest | '+' :: rest => unsignedSpelling (String.ofList rest)
  | _ => unsignedSpelling rate && !rate.toList.all Char.isDigit

/-- The names a constant-rate record reads from its source. -/
def Model.names (m : Model) : List String :=
  m.name :: m.states ++ m.equations.map Equation.derivative ++ [m.endName]

/-- Selection admits exactly the records whose names are not predefined type
names and whose rates have admitted spellings. -/
def Model.Admissible (m : Model) : Prop :=
  (∀ n ∈ m.names, predefined n = false) ∧ ∀ e ∈ m.equations, rateSpelling e.rate = true

instance (m : Model) : Decidable m.Admissible := by
  unfold Model.Admissible; infer_instance

/-- The syntax tree of a record. -/
def syntaxTree (m : Model) : Modelica.AST.StoredDefinition :=
  ⟨[⟨.literal "model", .long (.ident m.name) []
    ⟨m.states.map stateElement, [⟨(m.equations.map rateEquation).map plain⟩], none⟩
    (.ident m.endName)⟩]⟩

/-- The tokens of a rate: signs and one number. -/
theorem rateTokens_cases (rate : String) :
    rateTokens rate = [.number rate] ∨
      ∃ sign rest, (sign = .literal "+" ∨ sign = .literal "-") ∧
        rateTokens rate = [sign, .number rest] ∧ rateExpr rate = .unary sign (bare (.number rest)) := by
  unfold rateTokens rateExpr
  split
  · exact .inr ⟨_, _, .inr rfl, rfl, rfl⟩
  · exact .inr ⟨_, _, .inl rfl, rfl, rfl⟩
  · exact .inl rfl

private theorem rateTokens_member {rate : String} {t : Token} (member : t ∈ rateTokens rate) :
    t = .literal "+" ∨ t = .literal "-" ∨ ∃ s, t = .number s := by
  rcases rateTokens_cases rate with same | ⟨sign, rest, signed, same, _⟩ <;>
    rw [same] at member <;> simp at member
  · exact .inr (.inr ⟨_, member⟩)
  · rcases member with rfl | rfl
    · rcases signed with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨_, rfl⟩)

private theorem rateTokens_free {rate : String} {s : String}
    (other : s ≠ "+" ∧ s ≠ "-" := by decide) : Token.literal s ∉ rateTokens rate := by
  intro member
  rcases rateTokens_member member with h | h | ⟨_, h⟩
  · exact other.1 (Token.literal.inj h)
  · exact other.2 (Token.literal.inj h)
  · cases h

open Derivations in
/-- The certified grammar accepts the tokens of every record. -/
theorem accepts (m : Model) :
    EBNF.Accepts Generated.sourceGrammar (m.tokens.map Token.symbol) := by
  have rated : ∀ rate, EBNF.Derives Generated.sourceGrammar (.ref "expression")
      ((rateTokens rate).map Token.symbol) := by
    intro rate
    rcases rateTokens_cases rate with same | ⟨sign, rest, signed, same, _⟩ <;> rw [same]
    · exact expression_of_arithmetic arithmetic_ident
    · apply expression_of_arithmetic
      apply arithmetic_signed _ (by rcases signed with rfl | rfl <;> simp [Token.symbol])
      exact term_of_primary primary_ident
  have declared := many (body := .seq (.ref "element") (.terminal (.literal ";")))
    (fun _ : String => [Symbol.ident, .ident] ++ [.literal ";"]) m.states
    fun _ _ => .seq element_declaration (.terminal (by decide))
  have equated := many (body := .seq (.ref "some_equation") (.terminal (.literal ";")))
    (fun e : Equation => ([Symbol.literal "der", .literal "(", .ident, .literal ")"] ++
      .literal "=" :: (rateTokens e.rate).map Token.symbol) ++ [.literal ";"]) m.equations
    fun e _ => .seq (someEquation (simpleExpression_of_arithmetic
      (arithmetic_of_term (term_of_primary primary_derivative))) (rated e.rate))
      (.terminal (by decide))
  have accepted := accepts_model (composition declared equated)
  convert accepted using 1
  simp [Model.tokens, declTokens, equationTokens, Token.symbol, List.map_flatMap]

private theorem elements_of {names : List String} {elements : List Modelica.AST.Element}
    (valid : ∀ e ∈ elements, Good.element e)
    (printed : elements.flatMap (fun e => Modelica.Print.element e ++ [.literal ";"]) =
      names.flatMap declTokens) : elements = names.map stateElement := by
  induction names generalizing elements with
  | nil =>
    cases elements with
    | nil => rfl
    | cons _ _ => simp at printed
  | cons name rest ih =>
    cases elements with
    | nil => simp [declTokens] at printed
    | cons e es =>
      simp only [List.flatMap_cons, declTokens, List.append_assoc, List.cons_append,
        List.nil_append] at printed
      obtain ⟨single, following⟩ := Good.split_unique
        (Good.not_mem_of_tokens (Good.element_tokens (valid e (List.mem_cons_self ..)))
          (t := .literal ";") (by decide)) (by simp)
        (show Modelica.Print.element e ++ .literal ";" :: _ =
          [.ident "Real", .ident name] ++ .literal ";" :: _ from printed)
      rw [Good.element_of_printed (valid e (List.mem_cons_self ..)) (by rfl) single,
        ih (fun x member => valid x (List.mem_cons_of_mem _ member)) following]
      rfl

private theorem rateExpr_of_printed {rate : String} {r : Modelica.AST.Expr} (valid : Good.expr r)
    (printed : Modelica.Print.expr r = rateTokens rate) : r = rateExpr rate := by
  rcases rateTokens_cases rate with same | ⟨sign, rest, signed, same, expression⟩
  · rw [same] at printed
    rw [Good.bare_of_printed valid (by rfl) printed]
    unfold rateExpr rateTokens at *
    split at same
    · simp at same
    · simp at same
    · rfl
  · rw [same] at printed
    rw [expression, Good.signed_of_printed valid (by rfl) signed printed]
    rfl

private theorem rateTokens_plain {rate : String} : ∀ t ∈ rateTokens rate, Good.Plain t := by
  intro t member
  rcases rateTokens_member member with rfl | rfl | ⟨_, rfl⟩ <;> simp [Good.Plain, Token.symbol]

private theorem equations_of {read : List Equation} {equations : List Modelica.AST.SomeEquation}
    (valid : ∀ q ∈ equations, Good.someEquation q)
    (printed : equations.flatMap (fun q => Modelica.Print.someEquation q ++ [.literal ";"]) =
      read.flatMap equationTokens) : equations = (read.map rateEquation).map plain := by
  induction read generalizing equations with
  | nil =>
    cases equations with
    | nil => rfl
    | cons _ _ => simp at printed
  | cons e rest ih =>
    cases equations with
    | nil => simp [equationTokens] at printed
    | cons q qs =>
      simp only [List.flatMap_cons, equationTokens, List.append_assoc, List.cons_append,
        List.nil_append] at printed
      obtain ⟨single, following⟩ := Good.split_unique
        (Good.not_mem_of_tokens (Good.someEquation_tokens (valid q (List.mem_cons_self ..)))
          (t := .literal ";") (by decide))
        (by simp [rateTokens_free])
        (show Modelica.Print.someEquation q ++ .literal ";" :: _ =
          ([.literal "der", .literal "(", .ident e.derivative, .literal ")"] ++
            .literal "=" :: rateTokens e.rate) ++ .literal ";" :: _ by simpa using printed)
      obtain ⟨l, r, rfl, validLeft, validRight, left, right⟩ :=
        Good.equation_of_printed (valid _ (List.mem_cons_self ..)) (by simp) rateTokens_plain single
      rw [Good.derivative_of_printed validLeft (by rfl) left, rateExpr_of_printed validRight right,
        ih (fun x member => valid x (List.mem_cons_of_mem _ member)) following]
      rfl

/-- No token of a record is a STRING or the keyword `annotation`. -/
theorem Model.tokens_plain (m : Model) : ∀ t ∈ m.tokens, Good.Plain t := by
  intro t member
  simp only [Model.tokens, List.mem_append, List.mem_cons, List.mem_flatMap, declTokens,
    equationTokens, List.not_mem_nil, or_false] at member
  rcases member with ((((rfl | rfl) | ⟨_, _, rfl | rfl | rfl⟩) | rfl) |
      ⟨_, _, ((rfl | rfl | rfl | rfl | rfl) | member) | rfl⟩) | rfl | rfl | rfl <;>
    first | exact rateTokens_plain t member | simp [Good.Plain, Token.symbol]

/-- The certified parse of a record's tokens is the syntax tree of the record. -/
theorem parse_tree {m : Model} {ast : Modelica.AST.StoredDefinition}
    (success : Structural.parse m.tokens = some ast) : ast = syntaxTree m := by
  have valid := Good.parse_good success
  have printed := Structural.parse_printed success
  have body : m.tokens = .literal "model" :: .ident m.name ::
      (m.states.flatMap declTokens ++ .literal "equation" :: m.equations.flatMap equationTokens) ++
        [.literal "end", .ident m.endName, .literal ";"] := by
    simp [Model.tokens]
  have unstrung : ∀ t ∈ m.tokens, t.symbol ≠ .string := fun t member => (m.tokens_plain t member).1
  rw [body] at printed unstrung
  obtain ⟨c, rfl, validBody, printedBody⟩ := Good.storedDefinition_of_printed valid
    (by simp [declTokens, equationTokens, rateTokens_free])
    (fun t member => unstrung t (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_append_left _ member))))
    printed
  obtain ⟨equations, sectioned, unannotated, declared, equated⟩ := Good.composition_of_printed
    validBody (by simp [declTokens]) (by simp [equationTokens, rateTokens_free])
    (by simp [equationTokens, rateTokens_free]) printedBody
  obtain ⟨elements, sections, annotation⟩ := c
  obtain ⟨validElements, validSections, _⟩ := validBody
  simp only at sectioned unannotated declared validElements validSections
  subst sectioned unannotated
  rw [elements_of validElements declared,
    equations_of (equations := equations) (validSections _ (List.mem_singleton_self _)) equated]
  rfl

private theorem states_map (pos : Nat) (names : List String)
    (admitted : ∀ n ∈ names, predefined n = false) : states pos (names.map stateElement) = .ok names := by
  induction names generalizing pos with
  | nil => rfl
  | cons name rest ih =>
    have named := admitted name (List.mem_cons_self ..)
    simp [states, stateElement, Select.state, declaration, Select.name, named, absent,
      Select.description, Select.descriptionString,
      ih (pos + 3) (fun n member => admitted n (List.mem_cons_of_mem _ member)),
      bind, Except.bind, pure, Except.pure]

private theorem rate_rateExpr (pos : Nat) {r : String} (admitted : rateSpelling r = true) :
    rate pos (rateExpr r) = .ok r := by
  unfold rateSpelling at admitted
  unfold rateExpr
  split
  · rename_i rest same
    rw [same] at admitted
    simp only at admitted
    simp only [rate, bare, beq_self_eq_true, Bool.true_or, admitted, Bool.and_self, ↓reduceIte]
    congr 1
    apply String.toList_injective
    simp [same]
  · rename_i rest same
    rw [same] at admitted
    simp only at admitted
    simp only [rate, bare, beq_self_eq_true, Bool.or_true, admitted, Bool.and_self, ↓reduceIte]
    congr 1
    apply String.toList_injective
    simp [same]
  · rename_i minus plus
    split at admitted
    · rename_i rest same; exact absurd same (minus rest)
    · rename_i rest same; exact absurd same (plus rest)
    · simp [rate, bare, admitted]

private theorem rates_map (pos : Nat) (read : List Equation)
    (admitted : ∀ e ∈ read, predefined e.derivative = false ∧ rateSpelling e.rate = true) :
    rates pos (read.map rateEquation) = .ok read := by
  induction read generalizing pos with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨named, spelled⟩ := admitted e (List.mem_cons_self ..)
    simp [rates, rateEquation, Select.derivative, reference, bare, Select.name, named,
      rate_rateExpr _ spelled, ih _ (fun x member => admitted x (List.mem_cons_of_mem _ member)),
      bind, Except.bind, pure, Except.pure]

/-- Selection reads every admissible record back from the parse of its tokens. -/
theorem select_complete (m : Model) (admissible : m.Admissible) :
    ∃ ast, Structural.parse m.tokens = some ast ∧ select ast = .ok m := by
  obtain ⟨ast, success⟩ := (Structural.accepts_iff _).mpr (accepts m)
  refine ⟨ast, success, ?_⟩
  rw [parse_tree success]
  obtain ⟨names, spellings⟩ := admissible
  have named : predefined m.name = false :=
    names _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))
  have ended : predefined m.endName = false :=
    names _ (List.mem_append_right _ (List.mem_singleton_self _))
  have stated := states_map 2 m.states fun n member =>
    names n (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ member)))
  have rated := rates_map (3 + elementsWidth (m.states.map stateElement)) m.equations
    fun e member => ⟨names _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem (f := Equation.derivative) member))), spellings e member⟩
  obtain ⟨name, state0, state1, statesRest, equation0, equationsRest, endName⟩ := m
  simp only [Model.states, Model.equations, List.map_cons] at stated rated
  have planned : ∀ pos, plainEquations pos (plain (rateEquation equation0) ::
      List.map (plain ∘ rateEquation) equationsRest) =
      .ok (rateEquation equation0 :: List.map rateEquation equationsRest) := fun pos => by
    simpa using plainEquations_plain pos (rateEquation equation0 :: equationsRest.map rateEquation)
  simp [select, syntaxTree, Select.model, Select.name, named, ended, Model.states,
    Model.equations, stated, Select.descriptionString, absent, Select.equations,
    planned, rated, bind, Except.bind, pure, Except.pure]

/-- Every admissible record whose tokens a source lexes to is the selected
parse of that source. -/
theorem parse_complete {source : String} (m : Model) (lexes : Lexes source.toList m.tokens)
    (admissible : m.Admissible) : ∃ p : selection.Parsed source, p.ast = m := by
  obtain ⟨ast, syntactic, selected⟩ := select_complete m admissible
  refine Selection.Parsed.complete lexes ?_ syntactic selected
  simp [Selection.Uncommented, selection, Model.tokens, declTokens, equationTokens, isComment,
    List.all_flatMap]
  intro _ _ t member
  rcases rateTokens_member member with rfl | rfl | ⟨_, rfl⟩ <;> rfl

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
