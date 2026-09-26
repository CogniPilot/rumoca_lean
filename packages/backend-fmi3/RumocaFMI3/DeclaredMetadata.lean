import RumocaCore.Solve.Interface
import RumocaFMI3.Identifier
import RumocaC.Decimal
import XML.Certificate
import Mathlib.Data.List.Nodup

/-! The FMI 3 model description of a declared interface, for every profile.

One builder turns the resolved declarations of a prepared model into its
`ModelVariables` and `ModelStructure`. Value references follow one rule: the
independent time variable is `0`; the declarations then take the next
references in source order, each continuous state immediately followed by its
derivative `der(name)`. Every declaration is one `Float64` variable with its
declared causality and one `Dimension` per declared extent (FMI 3.0.2
§2.4.7.2): arrays stay array variables and scalars stay scalars. The model
structure is computed from the same table: every `output` is listed in
`<Output>` (§2.4.8, Table 23), every state derivative in
`<ContinuousStateDerivative>` in state order, and every calculated output or
derivative in `<InitialUnknown>`; exact states are not initial unknowns.
Dependencies are whole-variable value references (§2.4.8): an output state
depends on itself, every other value on the names its equation reads.

The theorems are universal over the interface. -/
namespace Rumoca.FMI3.DeclaredMetadata
open XML Rumoca.Solve Rumoca.Tensor

/-! ### Value-reference table -/

/-- What a value reference denotes: a declared variable, or the derivative of a
declared state together with the state's reference. -/
inductive Target where
  | value (d : Declaration)
  | derivative (d : Declaration) (state : Nat)
  deriving Repr, DecidableEq

/-- One value reference and what it denotes. -/
structure Entry where
  reference : Nat
  target : Target
  deriving Repr, DecidableEq

/-- The declaration an entry belongs to. -/
def Entry.declaration (e : Entry) : Declaration :=
  match e.target with
  | .value d => d
  | .derivative d _ => d

/-- References from `next` onward, in source order; each state is followed by
its derivative. -/
def entries (next : Nat) : List Declaration → List Entry
  | [] => []
  | d :: ds =>
    match d.role with
    | .state => ⟨next, .value d⟩ :: ⟨next + 1, .derivative d next⟩ :: entries (next + 2) ds
    | _ => ⟨next, .value d⟩ :: entries (next + 1) ds

/-- The value-reference table of an interface. Reference `0` is the independent
time variable. -/
def table (i : Interface) : List Entry := entries 1 i.declarations

/-- The reference of a declared variable, by name. -/
def referenceOf (i : Interface) (name : String) : Option Nat :=
  (table i).findSome? fun e =>
    match e.target with
    | .value d => if d.name = name then some e.reference else none
    | .derivative _ _ => none

/-- The whole-variable dependencies of an entry: an output state depends on
itself; every other value and every derivative on the declared names its
equation reads. -/
def Entry.dependencies (i : Interface) (e : Entry) : List Nat :=
  match e.target with
  | .value d =>
    match d.role with
    | .state => [e.reference]
    | _ => d.dependencies.filterMap (referenceOf i)
  | .derivative d _ => d.dependencies.filterMap (referenceOf i)

/-! ### Attribute text -/

def causalityText : Causality → String
  | .input => "input"
  | .output => "output"
  | .local => "local"

def initialText : Initial → String
  | .exact => "exact"
  | .calculated => "calculated"

/-- A space-separated list. -/
def joined (l : List String) : String :=
  l.foldr (fun s acc => s ++ (if acc.isEmpty then "" else " " ++ acc)) ""

/-- One `start` entry per element of a declaration, all spelling its uniform start
value. -/
def startEntries (shape : Shape) (value : Nat) : List String := List.replicate shape.volume (toString value)

theorem startEntries_length (shape : Shape) (value : Nat) : (startEntries shape value).length = shape.volume := by
  simp [startEntries]

/-- FMI 3.0.2 array `start`: one value per element (the product of the
`Dimension` starts), here the declaration's uniform start value. -/
def startValue (shape : Shape) (value : Nat) : String :=
  joined (startEntries shape value)

/-- One `Dimension` element with a constant extent. -/
def dimension (n : Nat) : Element := ⟨"Dimension", [("start", toString n)], [], ""⟩

/-- One `Dimension` per declared extent, in declaration order; none for a
scalar. -/
def dimensions (shape : Shape) : List Element := shape.dimensions.map dimension

def initialAttributes (d : Declaration) : List (String × String) :=
  match d.initial with
  | none => []
  | some initial => [("initial", initialText initial)]

/-- A calculated variable has no start value (FMI 3.0.2 §2.4.7.5). -/
def startAttributes (d : Declaration) : List (String × String) :=
  match d.initial, d.start with
  | some .calculated, _ => []
  | _, some value => [("start", startValue d.shape value)]
  | _, none => []

def valueAttributes (d : Declaration) (reference : Nat) : List (String × String) :=
  [("name", d.name), ("valueReference", toString reference),
    ("causality", causalityText d.causality), ("variability", "continuous")] ++
    initialAttributes d ++ startAttributes d

def derivativeName (d : Declaration) : String := "der(" ++ d.name ++ ")"

def derivativeAttributes (d : Declaration) (reference state : Nat) : List (String × String) :=
  [("name", derivativeName d), ("valueReference", toString reference),
    ("causality", "local"), ("variability", "continuous"),
    ("initial", "calculated"), ("derivative", toString state)]

/-! ### Document builder -/

def timeVariable (i : Interface) : Element :=
  ⟨"Float64", [("name", timeName), ("valueReference", "0"),
    ("causality", "independent"), ("variability", "continuous")], [], ""⟩

def Entry.variable (e : Entry) : Element :=
  match e.target with
  | .value d => ⟨"Float64", valueAttributes d e.reference, dimensions d.shape, ""⟩
  | .derivative d state => ⟨"Float64", derivativeAttributes d e.reference state, dimensions d.shape, ""⟩

def modelVariables (i : Interface) : List Element := timeVariable i :: (table i).map Entry.variable

def Entry.isOutput (e : Entry) : Bool :=
  match e.target with
  | .value d => d.causality == .output
  | .derivative _ _ => false

def Entry.isDerivative (e : Entry) : Bool :=
  match e.target with
  | .value _ => false
  | .derivative _ _ => true

def Entry.isCalculated (e : Entry) : Bool :=
  match e.target with
  | .value d => d.initial == some .calculated
  | .derivative _ _ => true

def dependencyAttributes : List Nat → List (String × String)
  | [] => [("dependencies", "")]
  | references => [("dependencies", joined (references.map toString)),
      ("dependenciesKind", joined (references.map fun _ => "dependent"))]

def Entry.node (i : Interface) (kind : String) (e : Entry) : Element :=
  ⟨kind, ("valueReference", toString e.reference) :: dependencyAttributes (e.dependencies i), [], ""⟩

def outputs (i : Interface) : List Element := ((table i).filter Entry.isOutput).map (Entry.node i "Output")

def stateDerivatives (i : Interface) : List Element :=
  ((table i).filter Entry.isDerivative).map (Entry.node i "ContinuousStateDerivative")

def initialUnknowns (i : Interface) : List Element :=
  ((table i).filter Entry.isCalculated).map (Entry.node i "InitialUnknown")

def modelStructure (i : Interface) : List Element := outputs i ++ stateDerivatives i ++ initialUnknowns i

/-- The model description of a declared interface, its model name and its
instantiation token. -/
def modelDescription (name token : String) (i : Interface) : Element :=
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", name),
    ("instantiationToken", token), ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier name)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier name),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], modelVariables i, ""⟩,
    ⟨"ModelStructure", [], modelStructure i, ""⟩], ""⟩

theorem token_attribute (name token : String) (i : Interface) :
    (modelDescription name token i).attributes.lookup "instantiationToken" = some token := rfl

theorem modelName_attribute (name token : String) (i : Interface) :
    (modelDescription name token i).attributes.lookup "modelName" = some name := rfl

/-! ### The exported interface -/

/-- The extents read back from a variable's `Dimension` start attributes. -/
def dimStarts (v : Element) : List Nat :=
  v.children.filterMap (fun d => (d.attributes.lookup "start").map (fun s => Rumoca.CDecimal.value s.toList))

theorem dimStarts_dimensions (shape : Shape) (name text : String) (attrs : List (String × String)) :
    dimStarts ⟨name, attrs, dimensions shape, text⟩ = shape.dimensions := by
  simp only [dimStarts, dimensions]
  induction shape.dimensions with
  | nil => rfl
  | cons n ns ih =>
    have hl : ((dimension n).attributes.lookup "start").map
        (fun s => Rumoca.CDecimal.value s.toList) = some n := by
      have hlook : (dimension n).attributes.lookup "start" = some (toString n) := rfl
      rw [hlook]
      exact congrArg some (Rumoca.CDecimal.render_denotes n).2.2
    simp only [List.map_cons, List.filterMap_cons, hl, ih]

/-- A variable an importer sees for a source declaration: any variable except
the independent time and the state derivatives, read back as name, causality
and dimensions. -/
def exportedOf (v : Element) : Option (String × String × List Nat) :=
  if v.attributes.lookup "derivative" = none ∧ v.attributes.lookup "causality" ≠ some "independent" then
    some ((v.attributes.lookup "name").getD "", (v.attributes.lookup "causality").getD "", dimStarts v)
  else none

/-- The exported variables of a model description, in `ModelVariables` order. -/
def exported (root : Element) : List (String × String × List Nat) :=
  (root.children.filter (·.name == "ModelVariables")).flatMap fun declared =>
    declared.children.filterMap exportedOf

/-- How a declaration is exported: its name, its causality and its declared
extents. -/
def Declaration.exported (d : Declaration) : String × String × List Nat :=
  (d.name, causalityText d.causality, d.shape.dimensions)

theorem causalityText_ne (c : Causality) : causalityText c ≠ "independent" := by
  cases c <;> decide

theorem exportedOf_value (reference : Nat) (d : Declaration) :
    exportedOf (Entry.variable ⟨reference, .value d⟩) = some (Declaration.exported d) := by
  have derivative : (valueAttributes d reference).lookup "derivative" = none := by
    simp only [valueAttributes, initialAttributes, startAttributes, List.cons_append, List.lookup]
    rcases d.initial with _ | ⟨_ | _⟩ <;> rcases d.start with _ | _ <;> simp
  have dims := dimStarts_dimensions d.shape "Float64" "" (valueAttributes d reference)
  simp only [exportedOf, Entry.variable, derivative, dims]
  simp [valueAttributes, List.lookup, causalityText_ne, Declaration.exported]

theorem exportedOf_derivative (reference state : Nat) (d : Declaration) :
    exportedOf (Entry.variable ⟨reference, .derivative d state⟩) = none := by
  simp [exportedOf, Entry.variable, derivativeAttributes, List.lookup]

theorem entries_exported (next : Nat) (ds : List Declaration) :
    (entries next ds).filterMap (fun e => exportedOf e.variable) = ds.map Declaration.exported := by
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih =>
    unfold entries
    cases d.role <;> simp [exportedOf_value, exportedOf_derivative, ih]

/-- Every source declaration is exported exactly once, in source order, with its
declared name, causality and dimensions; nothing else is exported. -/
theorem exported_interface (name token : String) (i : Interface) :
    exported (modelDescription name token i) = i.declarations.map Declaration.exported := by
  have time : exportedOf (timeVariable i) = none := by simp [exportedOf, timeVariable, List.lookup]
  simp [exported, modelDescription, modelVariables, time, List.filterMap_map, Function.comp_def,
    entries_exported, table]

/-! ### Printable text -/

theorem digit_text_char {c : Char} (h : c.isDigit = true) : XML.TextChar c := by
  have bounds : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simpa only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] using h
  exact ⟨by omega, by omega⟩

/-- Every decimal rendering of a natural number is printable XML text. -/
theorem text_toString (n : Nat) : XML.Text (toString n) := by
  intro c hc
  exact digit_text_char (List.all_eq_true.mp (Rumoca.CDecimal.render_denotes n).2.1 c hc)

theorem text_append {s t : String} (hs : XML.Text s) (ht : XML.Text t) : XML.Text (s ++ t) := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with h | h
  · exact hs c h
  · exact ht c h

/-- A space-separated join of printable text is printable text. -/
theorem text_joined (l : List String) (h : ∀ s ∈ l, XML.Text s) : XML.Text (joined l) := by
  induction l with
  | nil => intro c hc; exact absurd hc (by simp [joined])
  | cons a as ih =>
    have hacc := ih (fun s hs => h s (by simp [hs]))
    refine text_append (h a (by simp)) ?_
    split
    · intro c hc; exact absurd hc (by simp)
    · exact text_append (by decide) hacc

theorem startValue_text (shape : Shape) (value : Nat) : XML.Text (startValue shape value) := by
  refine text_joined _ ?_
  intro s hs
  unfold startEntries at hs
  rw [List.eq_of_mem_replicate hs]
  exact text_toString value

theorem timeName_text : XML.Text timeName := by
  unfold timeName; decide

/-! ### Well-formedness -/

theorem dimension_valid (n : Nat) : (dimension n).valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨(by decide : XML.Name "Dimension"),
      ⟨(by decide : (["start"] : List String).Nodup), ?_⟩,
      (by decide : XML.Text ""), Or.inl rfl⟩
    intro a ha
    cases ha with
    | head => exact ⟨(by decide : XML.Name "start"), text_toString n⟩
    | tail _ h => cases h
  · rfl

/-- Every element of a list is valid, hence the mapped validity flags all hold. -/
theorem all_valid_of_forall {l : List Element} (h : ∀ e ∈ l, e.valid = true) :
    (l.map Element.valid).all id = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    exact Certificate.children_valid_cons a as (h a (by simp)) (ih (fun e he => h e (by simp [he])))

theorem dimensions_valid (shape : Shape) : ((dimensions shape).map Element.valid).all id = true :=
  all_valid_of_forall (fun e he => by
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact dimension_valid n)

/-- An element without text, with valid attributes and valid children, is
valid. -/
theorem leaf_valid (kind : String) (attrs : List (String × String)) (children : List Element)
    (kind_name : XML.Name kind) (hattrs : XML.AttributesValid attrs)
    (hchildren : (children.map Element.valid).all id = true) :
    (⟨kind, attrs, children, ""⟩ : Element).valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    exact ⟨kind_name, hattrs, (by decide : XML.Text ""), Or.inl rfl⟩
  · exact hchildren

theorem initialText_text (initial : Initial) : XML.Text (initialText initial) := by
  cases initial <;> decide

theorem causalityText_text (c : Causality) : XML.Text (causalityText c) := by
  cases c <;> decide

theorem valueAttributes_valid (d : Declaration) (reference : Nat) (name_text : XML.Text d.name) :
    XML.AttributesValid (valueAttributes d reference) := by
  have base : ∀ a ∈ [("name", d.name), ("valueReference", toString reference),
      ("causality", causalityText d.causality), ("variability", "continuous")],
      XML.Name a.1 ∧ XML.Text a.2 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨(by decide : XML.Name "name"), name_text⟩
    · exact ⟨(by decide : XML.Name "valueReference"), text_toString reference⟩
    · exact ⟨(by decide : XML.Name "causality"), causalityText_text _⟩
    · exact ⟨(by decide : XML.Name "variability"), (by decide : XML.Text "continuous")⟩
  have initial : ∀ a ∈ initialAttributes d, XML.Name a.1 ∧ XML.Text a.2 := by
    unfold initialAttributes
    split
    · intro a ha; cases ha
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨(by decide : XML.Name "initial"), initialText_text _⟩
  have start : ∀ a ∈ startAttributes d, XML.Name a.1 ∧ XML.Text a.2 := by
    unfold startAttributes
    split
    · intro a ha; cases ha
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact ⟨(by decide : XML.Name "start"), startValue_text _ _⟩
    · intro a ha; cases ha
  have keys : ((valueAttributes d reference).map Prod.fst).Nodup := by
    unfold valueAttributes initialAttributes startAttributes
    rcases d.initial with _ | ⟨_ | _⟩ <;> rcases d.start with _ | value <;>
      simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.append_nil] <;> decide
  refine ⟨keys, fun a ha => ?_⟩
  simp only [valueAttributes, List.mem_append] at ha
  rcases ha with (ha | ha) | ha
  · exact base a ha
  · exact initial a ha
  · exact start a ha

theorem derivativeAttributes_valid (d : Declaration) (reference state : Nat)
    (name_text : XML.Text d.name) : XML.AttributesValid (derivativeAttributes d reference state) := by
  refine ⟨(by decide : (["name", "valueReference", "causality", "variability", "initial",
    "derivative"] : List String).Nodup), ?_⟩
  intro a ha
  simp only [derivativeAttributes, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(by decide : XML.Name "name"),
      text_append (text_append (by decide : XML.Text "der(") name_text) (by decide : XML.Text ")")⟩
  · exact ⟨(by decide : XML.Name "valueReference"), text_toString reference⟩
  · exact ⟨(by decide : XML.Name "causality"), (by decide : XML.Text "local")⟩
  · exact ⟨(by decide : XML.Name "variability"), (by decide : XML.Text "continuous")⟩
  · exact ⟨(by decide : XML.Name "initial"), (by decide : XML.Text "calculated")⟩
  · exact ⟨(by decide : XML.Name "derivative"), text_toString state⟩

theorem variable_valid (e : Entry) (name_text : XML.Text e.declaration.name) :
    e.variable.valid = true := by
  rcases e with ⟨reference, d | ⟨d, state⟩⟩
  · exact leaf_valid _ _ _ (by decide) (valueAttributes_valid d reference name_text) (dimensions_valid _)
  · exact leaf_valid _ _ _ (by decide) (derivativeAttributes_valid d reference state name_text)
      (dimensions_valid _)

theorem entries_declaration (next : Nat) (ds : List Declaration) :
    ∀ e ∈ entries next ds, e.declaration ∈ ds := by
  induction ds generalizing next with
  | nil => intro e he; cases he
  | cons d ds ih =>
    intro e he
    unfold entries at he
    split at he
    · simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact List.mem_cons_self ..
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ e he)
    · simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ e he)

theorem timeVariable_valid (i : Interface) : (timeVariable i).valid = true := by
  refine leaf_valid _ _ _ (by decide)
    ⟨(by decide : (["name", "valueReference", "causality", "variability"] : List String).Nodup), ?_⟩ rfl
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨(by decide : XML.Name "name"), timeName_text⟩
  · exact ⟨(by decide : XML.Name "valueReference"), (by decide : XML.Text "0")⟩
  · exact ⟨(by decide : XML.Name "causality"), (by decide : XML.Text "independent")⟩
  · exact ⟨(by decide : XML.Name "variability"), (by decide : XML.Text "continuous")⟩

theorem modelVariables_valid (i : Interface) (names : ∀ d ∈ i.declarations, XML.Text d.name) :
    ((modelVariables i).map Element.valid).all id = true := by
  refine Certificate.children_valid_cons _ _ (timeVariable_valid i) (all_valid_of_forall ?_)
  intro v hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact variable_valid e (names _ (entries_declaration 1 _ e he))

theorem nodeAttributes_valid (reference : Nat) (references : List Nat) :
    XML.AttributesValid (("valueReference", toString reference) :: dependencyAttributes references) := by
  have deps : ∀ a ∈ dependencyAttributes references, XML.Name a.1 ∧ XML.Text a.2 := by
    intro a ha
    cases references with
    | nil =>
      simp only [dependencyAttributes, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      exact ⟨(by decide : XML.Name "dependencies"), (by decide : XML.Text "")⟩
    | cons r rs =>
      simp only [dependencyAttributes, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨(by decide : XML.Name "dependencies"), text_joined _ (fun s hs => by
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hs
          exact text_toString n)⟩
      · exact ⟨(by decide : XML.Name "dependenciesKind"), text_joined _ (fun s hs => by
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hs
          exact (by decide : XML.Text "dependent"))⟩
  have keys : ((("valueReference", toString reference) :: dependencyAttributes references).map
      Prod.fst).Nodup := by
    cases references with
    | nil => exact (by decide : (["valueReference", "dependencies"] : List String).Nodup)
    | cons r rs => exact (by decide :
        (["valueReference", "dependencies", "dependenciesKind"] : List String).Nodup)
  refine ⟨keys, fun a ha => ?_⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ⟨(by decide : XML.Name "valueReference"), text_toString reference⟩
  · exact deps a ha

theorem node_valid (i : Interface) (kind : String) (kind_name : XML.Name kind) (e : Entry) :
    (e.node i kind).valid = true :=
  leaf_valid _ _ _ kind_name (nodeAttributes_valid _ _) rfl

theorem modelStructure_valid (i : Interface) :
    ((modelStructure i).map Element.valid).all id = true := by
  refine all_valid_of_forall ?_
  intro node hn
  simp only [modelStructure, outputs, stateDerivatives, initialUnknowns, List.mem_append] at hn
  rcases hn with (hn | hn) | hn <;> obtain ⟨e, _, rfl⟩ := List.mem_map.mp hn
  · exact node_valid i _ (by decide) e
  · exact node_valid i _ (by decide) e
  · exact node_valid i _ (by decide) e

/-- The model description is a well-formed tree, given a printable model name,
token and declared names. -/
theorem valid (name token : String) (i : Interface) (name_text : XML.Text name)
    (token_text : XML.Text token) (names : ∀ d ∈ i.declarations, XML.Text d.name) :
    (modelDescription name token i).valid = true := by
  have identifier : XML.Text (modelIdentifier name) :=
    text_append (by decide : XML.Text "Rumoca_") name_text
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨(by decide : XML.Name "fmiModelDescription"),
      ⟨(by decide : (["fmiVersion", "modelName", "instantiationToken", "generationTool"] :
        List String).Nodup), ?_⟩, (by decide : XML.Text ""), Or.inl rfl⟩
    intro a ha
    simp only [modelDescription, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨(by decide : XML.Name "fmiVersion"), (by decide : XML.Text "3.0")⟩
    · exact ⟨(by decide : XML.Name "modelName"), name_text⟩
    · exact ⟨(by decide : XML.Name "instantiationToken"), token_text⟩
    · exact ⟨(by decide : XML.Name "generationTool"), (by decide : XML.Text "lean_rumoca")⟩
  · refine Certificate.children_valid_cons _ _ (leaf_valid _ _ _ (by decide)
      ⟨(by decide : (["modelIdentifier"] : List String).Nodup), fun a ha => by
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨(by decide : XML.Name "modelIdentifier"), identifier⟩⟩ rfl) ?_
    refine Certificate.children_valid_cons _ _ (leaf_valid _ _ _ (by decide)
      ⟨(by decide : (["modelIdentifier", "canHandleVariableCommunicationStepSize",
        "fixedInternalStepSize"] : List String).Nodup), fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨(by decide : XML.Name "modelIdentifier"), identifier⟩
        · exact ⟨(by decide : XML.Name "canHandleVariableCommunicationStepSize"),
            (by decide : XML.Text "true")⟩
        · exact ⟨(by decide : XML.Name "fixedInternalStepSize"), (by decide : XML.Text "1")⟩⟩ rfl) ?_
    refine Certificate.children_valid_cons _ _ (leaf_valid _ _ _ (by decide) (by decide)
      (Certificate.children_valid_cons _ _ (leaf_valid _ _ _ (by decide) (by decide) rfl) rfl)) ?_
    refine Certificate.children_valid_cons _ _ (leaf_valid _ _ _ (by decide) (by decide) rfl) ?_
    refine Certificate.children_valid_cons _ _
      (leaf_valid _ _ _ (by decide) (by decide) (modelVariables_valid i names)) ?_
    exact Certificate.children_valid_cons _ _
      (leaf_valid _ _ _ (by decide) (by decide) (modelStructure_valid i)) rfl

/-- The document is a well-formed XML tree accepted by the in-tree renderer and
syntax proofs. -/
theorem document (name token : String) (i : Interface) (name_text : XML.Text name)
    (token_text : XML.Text token) (names : ∀ d ∈ i.declarations, XML.Text d.name) :
    XML.Document (modelDescription name token i) (XML.document (modelDescription name token i)) :=
  XML.document_correct _ (valid name token i name_text token_text names)

/-! ### Value references are pairwise distinct -/

/-- The number of references a declaration takes: two for a state and its
derivative, one otherwise. -/
def referenceWidth (d : Declaration) : Nat :=
  match d.role with
  | .state => 2
  | _ => 1

def width (ds : List Declaration) : Nat := (ds.map referenceWidth).sum

theorem entries_references (next : Nat) (ds : List Declaration) :
    (entries next ds).map Entry.reference = List.range' next (width ds) := by
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih =>
    have hw : width (d :: ds) = referenceWidth d + width ds := by simp [width]
    rw [hw]
    cases hr : d.role <;> simp only [entries, hr, referenceWidth, List.map_cons, ih]
    · rw [show 1 + width ds = width ds + 1 by omega, List.range'_succ]
    · rw [show 2 + width ds = width ds + 1 + 1 by omega, List.range'_succ, List.range'_succ]
    · rw [show 1 + width ds = width ds + 1 by omega, List.range'_succ]

theorem filterMap_eq_map_of {l : List α} {f : α → Option β} {g : α → β}
    (h : ∀ a ∈ l, f a = some (g a)) : l.filterMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.filterMap_cons, h a (List.mem_cons_self ..), List.map_cons,
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The value references of the declared variables, in `ModelVariables` order. -/
def valueReferences (i : Interface) : List Nat := 0 :: (table i).map Entry.reference

theorem valueReferences_nodup (i : Interface) : (valueReferences i).Nodup := by
  rw [valueReferences, table, entries_references]
  refine List.nodup_cons.mpr ⟨fun member => ?_, List.nodup_range'⟩
  have := (List.mem_range'.mp member)
  omega

/-- The rendered `valueReference` attributes are the value references. -/
theorem variable_references (i : Interface) :
    (modelVariables i).filterMap (fun v => (v.attributes.lookup "valueReference").map
      (fun s => Rumoca.CDecimal.value s.toList)) = valueReferences i := by
  have render : ∀ n : Nat, Rumoca.CDecimal.value (toString n).toList = n :=
    fun n => (Rumoca.CDecimal.render_denotes n).2.2
  simp only [modelVariables, valueReferences, List.filterMap_cons, List.filterMap_map]
  have time : ((timeVariable i).attributes.lookup "valueReference").map
      (fun s => Rumoca.CDecimal.value s.toList) = some 0 := rfl
  simp only [time]
  congr 1
  apply filterMap_eq_map_of
  intro e _
  rcases e with ⟨reference, d | ⟨d, state⟩⟩ <;> simp [Entry.variable, valueAttributes,
    derivativeAttributes, List.lookup] <;> exact render reference

/-! ### Dimensions are the declared extents -/

theorem dims_as_declared (e : Entry) : dimStarts e.variable = e.declaration.shape.dimensions := by
  rcases e with ⟨reference, d | ⟨d, state⟩⟩ <;> exact dimStarts_dimensions _ _ _ _

/-! ### Derivatives reference their states -/

theorem derivative_references_state (i : Interface) :
    ∀ e ∈ table i, ∀ d state, e.target = .derivative d state →
      (⟨state, .value d⟩ : Entry) ∈ table i ∧ d.role = .state := by
  suffices h : ∀ next ds, ∀ e ∈ entries next ds, ∀ d state, e.target = .derivative d state →
      (⟨state, .value d⟩ : Entry) ∈ entries next ds ∧ d.role = .state from h 1 _
  intro next ds
  induction ds generalizing next with
  | nil => intro e he; cases he
  | cons d ds ih =>
    intro e he d' state target
    unfold entries at he ⊢
    split at he <;> rename_i hr
    · simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he
      · cases target
      · cases target; exact ⟨List.mem_cons_self .., hr⟩
      · obtain ⟨mem, role⟩ := ih _ e he d' state target
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem), role⟩
    · simp only [List.mem_cons] at he
      rcases he with rfl | he
      · cases target
      · obtain ⟨mem, role⟩ := ih _ e he d' state target
        exact ⟨List.mem_cons_of_mem _ mem, role⟩

/-- The derivatives appear in the order of the declared states. This order is
the order of the continuous-state vector (FMI 3.0.2 §2.4.8, Table 23). -/
theorem derivative_order (i : Interface) :
    ((table i).filter Entry.isDerivative).map Entry.declaration =
      i.declarations.filter (fun d => d.role == .state) := by
  suffices h : ∀ next ds, ((entries next ds).filter Entry.isDerivative).map Entry.declaration =
      ds.filter (fun d => d.role == .state) from h 1 _
  intro next ds
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih =>
    unfold entries
    cases hr : d.role <;> simp [hr, Entry.isDerivative, Entry.declaration, ih]

/-! ### Model-structure entries reference declared variables -/

theorem structure_references_declared (i : Interface) :
    ∀ node ∈ modelStructure i, ∃ e ∈ table i,
      node.attributes.lookup "valueReference" = some (toString e.reference) := by
  intro node hn
  simp only [modelStructure, outputs, stateDerivatives, initialUnknowns, List.mem_append] at hn
  rcases hn with (hn | hn) | hn <;> obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn <;>
    exact ⟨e, (List.mem_filter.mp he).1, rfl⟩

theorem referenceOf_declared (i : Interface) (name : String) (reference : Nat)
    (found : referenceOf i name = some reference) :
    ∃ e ∈ table i, e.reference = reference ∧ ∃ d, e.target = .value d ∧ d.name = name := by
  obtain ⟨e, he, hsome⟩ := List.exists_of_findSome?_eq_some found
  rcases e with ⟨r, d | ⟨d, state⟩⟩
  · by_cases hn : d.name = name
    · simp only [hn, if_true, Option.some.injEq] at hsome
      exact ⟨_, he, hsome, d, rfl, hn⟩
    · simp [hn] at hsome
  · cases hsome

/-- Every listed dependency is the value reference of a declared variable. -/
theorem dependencies_declared (i : Interface) :
    ∀ e ∈ table i, ∀ reference ∈ e.dependencies i, ∃ e' ∈ table i, e'.reference = reference := by
  intro e he reference hr
  have named : ∀ names : List String, reference ∈ names.filterMap (referenceOf i) →
      ∃ e' ∈ table i, e'.reference = reference := by
    intro names member
    obtain ⟨name, _, found⟩ := List.mem_filterMap.mp member
    obtain ⟨e', he', eq, _⟩ := referenceOf_declared i name reference found
    exact ⟨e', he', eq⟩
  rcases e with ⟨r, d | ⟨d, state⟩⟩
  · simp only [Entry.dependencies] at hr
    split at hr
    · simp only [List.mem_singleton] at hr
      exact ⟨_, he, hr.symm⟩
    · exact named _ hr
  · exact named _ hr

/-! ### Outputs, state derivatives and initial unknowns -/

private theorem names_filter (i : Interface) (kind : String) (l : List Entry) :
    (l.map (Entry.node i kind)).filter (fun node => node.name == kind) = l.map (Entry.node i kind) := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [Entry.node, ih]

private theorem names_other (i : Interface) (kind other : String) (distinct : kind ≠ other)
    (l : List Entry) : (l.map (Entry.node i kind)).filter (fun node => node.name == other) = [] := by
  induction l with
  | nil => rfl
  | cons e es ih => simp [Entry.node, distinct, ih]

/-- FMI 3.0.2 §2.4.8, Table 23: the `<Output>` elements are exactly the
declared outputs, in value-reference order, and every variable with causality
`output` is listed. -/
theorem outputs_complete (i : Interface) :
    (modelStructure i).filter (fun node => node.name == "Output") =
      ((table i).filter Entry.isOutput).map (Entry.node i "Output") := by
  simp only [modelStructure, outputs, stateDerivatives, initialUnknowns, List.filter_append,
    names_filter, names_other i _ _ (by decide : "ContinuousStateDerivative" ≠ "Output"),
    names_other i _ _ (by decide : "InitialUnknown" ≠ "Output"), List.append_nil]

theorem isOutput_iff (e : Entry) :
    e.isOutput = true ↔ ∃ d, e.target = .value d ∧ d.causality = .output := by
  rcases e with ⟨r, d | ⟨d, state⟩⟩ <;> simp [Entry.isOutput]

/-- The `<ContinuousStateDerivative>` elements are the derivatives in state
order. -/
theorem stateDerivatives_complete (i : Interface) :
    (modelStructure i).filter (fun node => node.name == "ContinuousStateDerivative") =
      ((table i).filter Entry.isDerivative).map (Entry.node i "ContinuousStateDerivative") := by
  simp only [modelStructure, outputs, stateDerivatives, initialUnknowns, List.filter_append,
    names_filter, names_other i _ _ (by decide : "Output" ≠ "ContinuousStateDerivative"),
    names_other i _ _ (by decide : "InitialUnknown" ≠ "ContinuousStateDerivative"),
    List.append_nil, List.nil_append]

/-- FMI 3.0.2 §2.4.8, Table 23: the `<InitialUnknown>` elements are exactly the
derivatives and the calculated outputs; an exact state is not an initial
unknown. -/
theorem initialUnknowns_complete (i : Interface) :
    (modelStructure i).filter (fun node => node.name == "InitialUnknown") =
      ((table i).filter Entry.isCalculated).map (Entry.node i "InitialUnknown") := by
  simp only [modelStructure, outputs, stateDerivatives, initialUnknowns, List.filter_append,
    names_filter, names_other i _ _ (by decide : "Output" ≠ "InitialUnknown"),
    names_other i _ _ (by decide : "ContinuousStateDerivative" ≠ "InitialUnknown"),
    List.nil_append]

theorem isCalculated_iff (e : Entry) :
    e.isCalculated = true ↔
      e.isDerivative = true ∨ ∃ d, e.target = .value d ∧ d.initial = some .calculated := by
  rcases e with ⟨r, d | ⟨d, state⟩⟩ <;> simp [Entry.isCalculated, Entry.isDerivative]

theorem state_exact (e : Entry) (d : Declaration) (value : e.target = .value d)
    (state : d.role = .state) : e.isCalculated = false := by
  rcases e with ⟨r, d' | ⟨d', s⟩⟩
  · cases value
    simp [Entry.isCalculated, Declaration.initial, state]
  · cases value

/-! ### Variable names are unique (FMI 3.0.2 §2.4.7, Table 17) -/

/-- The name of the variable an entry exports. -/
def Entry.name (e : Entry) : String :=
  match e.target with
  | .value d => d.name
  | .derivative d _ => derivativeName d

/-- The names the declarations of an interface export, in order. -/
def declarationNames (d : Declaration) : List String :=
  match d.role with
  | .state => [d.name, derivativeName d]
  | _ => [d.name]

/-- The `name` attributes of the exported variables, in `ModelVariables` order. -/
def variableNames (root : Element) : List String :=
  (root.children.filter (·.name == "ModelVariables")).flatMap fun declared =>
    declared.children.map fun v => (v.attributes.lookup "name").getD ""

theorem entry_name (e : Entry) : (e.variable.attributes.lookup "name").getD "" = e.name := by
  rcases e with ⟨r, d | ⟨d, s⟩⟩ <;> simp [Entry.variable, valueAttributes, derivativeAttributes,
    Entry.name, List.lookup]

theorem entries_names (next : Nat) (ds : List Declaration) :
    (entries next ds).map Entry.name = ds.flatMap declarationNames := by
  induction ds generalizing next with
  | nil => rfl
  | cons d ds ih =>
    cases hr : d.role <;> simp [entries, hr, declarationNames, Entry.name, ih]

theorem variableNames_eq (name token : String) (i : Interface) :
    variableNames (modelDescription name token i) = timeName :: i.declarations.flatMap declarationNames := by
  simp [variableNames, modelDescription, modelVariables, timeVariable, List.lookup, entry_name,
    ← entries_names 1, table, List.map_map, Function.comp_def]

theorem paren_derivativeName (d : Declaration) : '(' ∈ (derivativeName d).toList := by
  simp [derivativeName]

theorem derivativeName_injective (a b : Declaration) (same : derivativeName a = derivativeName b) :
    a.name = b.name := by
  have chars := congrArg String.toList same
  simp only [derivativeName, String.toList_append, List.append_assoc] at chars
  exact String.toList_injective (List.append_cancel_right (List.append_cancel_left chars))

/-- Given distinct declared names that are identifiers other than `time`, every
exported variable name is distinct: the time base, each declaration and each
state derivative `der(name)`. -/
theorem names_nodup (name token : String) (i : Interface)
    (distinct : (i.declarations.map Declaration.name).Nodup)
    (words : ∀ d ∈ i.declarations, d.name ≠ timeName ∧ '(' ∉ d.name.toList) :
    (variableNames (modelDescription name token i)).Nodup := by
  rw [variableNames_eq]
  have noParenTime : '(' ∉ timeName.toList := by decide
  refine List.nodup_cons.mpr ⟨fun member => ?_, List.nodup_flatMap.mpr ⟨?_, ?_⟩⟩
  · obtain ⟨d, hd, hn⟩ := List.mem_flatMap.mp member
    unfold declarationNames at hn
    split at hn <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    · rcases hn with hn | hn
      · exact (words d hd).1 hn.symm
      · exact noParenTime (hn ▸ paren_derivativeName d)
    · exact (words d hd).1 hn.symm
  · intro d hd
    unfold declarationNames
    split
    · refine List.nodup_cons.mpr ⟨fun member => ?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton] at member
      exact (words d hd).2 (member ▸ paren_derivativeName d)
    · exact List.nodup_singleton _
  · have pairwise : i.declarations.Pairwise (fun a b => a.name ≠ b.name) :=
      List.pairwise_map.mp distinct
    refine pairwise.imp_of_mem ?_
    intro a b ha hb different x xa xb
    have names : ∀ d ∈ i.declarations, x ∈ declarationNames d → x = d.name ∨ x = derivativeName d := by
      intro d _ member
      unfold declarationNames at member
      split at member <;> simp_all
    rcases names a ha xa with rfl | rfl <;> rcases names b hb xb with same | same
    · exact different same
    · exact (words a ha).2 (same ▸ paren_derivativeName b)
    · exact (words b hb).2 (same ▸ paren_derivativeName a)
    · exact different (derivativeName_injective a b same)

/-! ### Every declared dependency is listed -/

theorem entries_value (next : Nat) (ds : List Declaration) (d : Declaration) (member : d ∈ ds) :
    ∃ r, (⟨r, .value d⟩ : Entry) ∈ entries next ds := by
  induction ds generalizing next with
  | nil => cases member
  | cons e es ih =>
    rcases List.mem_cons.mp member with same | member
    · subst same
      cases hr : d.role <;> exact ⟨next, by simp [entries, hr]⟩
    · cases hrole : e.role
      · obtain ⟨r, hr⟩ := ih (next + 1) member
        exact ⟨r, by simp [entries, hrole, hr]⟩
      · obtain ⟨r, hr⟩ := ih (next + 2) member
        exact ⟨r, by simp [entries, hrole, hr]⟩
      · obtain ⟨r, hr⟩ := ih (next + 1) member
        exact ⟨r, by simp [entries, hrole, hr]⟩

/-- A declared name always resolves to its value reference. -/
theorem referenceOf_isSome (i : Interface) (name : String)
    (declared : name ∈ i.declarations.map Declaration.name) : (referenceOf i name).isSome := by
  obtain ⟨d, member, rfl⟩ := List.mem_map.mp declared
  obtain ⟨r, entry⟩ := entries_value 1 i.declarations d member
  exact List.findSome?_isSome_iff.mpr ⟨_, entry, by simp⟩

/-- For a closed interface no dependency is dropped: every name a declaration
reads becomes a listed value reference. -/
theorem dependencies_complete (i : Interface) (closed : i.Closed) (d : Declaration)
    (member : d ∈ i.declarations) :
    (d.dependencies.filterMap (referenceOf i)).length = d.dependencies.length := by
  have resolved : ∀ name ∈ d.dependencies, (referenceOf i name).isSome :=
    fun name read => referenceOf_isSome i name (closed d member name read)
  generalize d.dependencies = names at resolved ⊢
  induction names with
  | nil => rfl
  | cons name rest ih =>
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (resolved name List.mem_cons_self)
    simp [List.filterMap_cons, hr, ih (fun n m => resolved n (List.mem_cons_of_mem _ m))]

/-! ### The model structure read from the rendered attributes (Table 23) -/

/-- The `ModelVariables` elements of a model description. -/
def variablesOf (root : Element) : List Element :=
  (root.children.filter (·.name == "ModelVariables")).flatMap (·.children)

/-- The `ModelStructure` elements of one kind. -/
def structureOf (root : Element) (kind : String) : List Element :=
  (root.children.filter (·.name == "ModelStructure")).flatMap fun layout =>
    layout.children.filter (·.name == kind)

def referenceAttribute (e : Element) : Option String := e.attributes.lookup "valueReference"

theorem variablesOf_eq (name token : String) (i : Interface) :
    variablesOf (modelDescription name token i) = timeVariable i :: (table i).map Entry.variable := by
  simp [variablesOf, modelDescription, modelVariables]

theorem structureOf_eq (name token : String) (i : Interface) (kind : String) :
    structureOf (modelDescription name token i) kind =
      (modelStructure i).filter (·.name == kind) := by
  simp [structureOf, modelDescription]

theorem entry_reference (e : Entry) : referenceAttribute e.variable = some (toString e.reference) := by
  rcases e with ⟨r, d | ⟨d, s⟩⟩ <;> simp [referenceAttribute, Entry.variable, valueAttributes,
    derivativeAttributes, List.lookup]

theorem node_reference (i : Interface) (kind : String) (e : Entry) :
    referenceAttribute (e.node i kind) = some (toString e.reference) := by
  simp [referenceAttribute, Entry.node, List.lookup]

theorem valueAttributes_prefix (d : Declaration) (reference : Nat) (key : String)
    (fresh : key ≠ "name" ∧ key ≠ "valueReference" ∧ key ≠ "causality" ∧ key ≠ "variability") :
    (valueAttributes d reference).lookup key = (initialAttributes d ++ startAttributes d).lookup key := by
  obtain ⟨h1, h2, h3, h4⟩ := fresh
  have b1 : (key == "name") = false := by simp [h1]
  have b2 : (key == "valueReference") = false := by simp [h2]
  have b3 : (key == "causality") = false := by simp [h3]
  have b4 : (key == "variability") = false := by simp [h4]
  simp [valueAttributes, List.lookup, b1, b2, b3, b4]

theorem variable_output (e : Entry) :
    (e.variable.attributes.lookup "causality" == some "output") = e.isOutput := by
  rcases e with ⟨r, d | ⟨d, s⟩⟩
  · cases hc : d.causality <;>
      simp [Entry.variable, valueAttributes, Entry.isOutput, List.lookup, causalityText, hc]
  · simp [Entry.variable, derivativeAttributes, Entry.isOutput, List.lookup]

theorem variable_calculated (e : Entry) :
    (e.variable.attributes.lookup "initial" == some "calculated") = e.isCalculated := by
  rcases e with ⟨r, d | ⟨d, s⟩⟩
  · simp only [Entry.variable, Entry.isCalculated]
    rw [valueAttributes_prefix d r "initial" (by decide)]
    unfold initialAttributes startAttributes
    rcases d.initial with _ | ⟨_ | _⟩ <;> rcases d.start with _ | v <;> simp [List.lookup, initialText]
  · simp [Entry.variable, derivativeAttributes, Entry.isCalculated, List.lookup]

theorem variable_derivative (e : Entry) :
    (e.variable.attributes.lookup "derivative").isSome = e.isDerivative := by
  rcases e with ⟨r, d | ⟨d, s⟩⟩
  · simp only [Entry.variable, Entry.isDerivative]
    rw [valueAttributes_prefix d r "derivative" (by decide)]
    unfold initialAttributes startAttributes
    rcases d.initial with _ | ⟨_ | _⟩ <;> rcases d.start with _ | v <;> simp [List.lookup]
  · simp [Entry.variable, derivativeAttributes, Entry.isDerivative, List.lookup]

private theorem rendered_filter (i : Interface) (kind : String) (keep : Entry → Bool)
    (test : Element → Bool) (agrees : ∀ e, test e.variable = keep e) (time : test (timeVariable i) = false)
    (listed : (modelStructure i).filter (·.name == kind) = ((table i).filter keep).map (Entry.node i kind))
    (name token : String) :
    (structureOf (modelDescription name token i) kind).map referenceAttribute =
      ((variablesOf (modelDescription name token i)).filter test).map referenceAttribute := by
  rw [structureOf_eq, listed, variablesOf_eq, List.filter_cons, time]
  simp only [Bool.false_eq_true, if_false, List.filter_map, List.map_map]
  have same : (fun e => test e.variable) = keep := funext agrees
  simp only [Function.comp_def, same, node_reference, entry_reference]

/-- The `<Output>` value references are exactly those of the variables whose
rendered causality is `output`, in `ModelVariables` order. -/
theorem outputs_rendered (name token : String) (i : Interface) :
    (structureOf (modelDescription name token i) "Output").map referenceAttribute =
      ((variablesOf (modelDescription name token i)).filter
        (fun v => v.attributes.lookup "causality" == some "output")).map referenceAttribute :=
  rendered_filter i "Output" Entry.isOutput _ variable_output (by simp [timeVariable, List.lookup])
    (outputs_complete i) name token

/-- The `<InitialUnknown>` value references are exactly those of the variables
whose rendered `initial` is `calculated` (the calculated outputs and every
derivative); no variable is rendered with `initial="approx"`, and exact states
are not listed. -/
theorem initialUnknowns_rendered (name token : String) (i : Interface) :
    (structureOf (modelDescription name token i) "InitialUnknown").map referenceAttribute =
      ((variablesOf (modelDescription name token i)).filter
        (fun v => v.attributes.lookup "initial" == some "calculated")).map referenceAttribute :=
  rendered_filter i "InitialUnknown" Entry.isCalculated _ variable_calculated
    (by simp [timeVariable, List.lookup]) (initialUnknowns_complete i) name token

/-- The `<ContinuousStateDerivative>` value references are exactly those of the
variables carrying a `derivative` attribute, in state order. -/
theorem stateDerivatives_rendered (name token : String) (i : Interface) :
    (structureOf (modelDescription name token i) "ContinuousStateDerivative").map referenceAttribute =
      ((variablesOf (modelDescription name token i)).filter
        (fun v => (v.attributes.lookup "derivative").isSome)).map referenceAttribute :=
  rendered_filter i "ContinuousStateDerivative" Entry.isDerivative _ variable_derivative
    (by simp [timeVariable, List.lookup]) (stateDerivatives_complete i) name token

/-- A calculated variable carries no `start` attribute (FMI 3.0.2 §2.4.7.5). -/
theorem calculated_no_start (name token : String) (i : Interface) :
    ∀ v ∈ variablesOf (modelDescription name token i),
      v.attributes.lookup "initial" = some "calculated" → v.attributes.lookup "start" = none := by
  rw [variablesOf_eq]
  intro v member calculated
  rcases List.mem_cons.mp member with rfl | member
  · simp [timeVariable, List.lookup] at calculated
  · obtain ⟨⟨r, d | ⟨d, s⟩⟩, _, rfl⟩ := List.mem_map.mp member
    · simp only [Entry.variable] at calculated ⊢
      rw [valueAttributes_prefix d r "initial" (by decide)] at calculated
      rw [valueAttributes_prefix d r "start" (by decide)]
      revert calculated
      unfold initialAttributes startAttributes
      rcases d.initial with _ | ⟨_ | _⟩ <;> rcases d.start with _ | v <;> simp [List.lookup, initialText]
    · simp [Entry.variable, derivativeAttributes, List.lookup]

end Rumoca.FMI3.DeclaredMetadata
