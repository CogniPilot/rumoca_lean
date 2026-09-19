import RumocaFMI3.Metadata
import RumocaFMI3.SourceLinkageProofs
import RumocaFMI3.TensorInstanceStorage
import RumocaCore.Solve.TensorFMI3
import RumocaC.Decimal
import XML.Certificate

/-! Tensor FMI 3 model description as a proved product. This builds a model
description for a prepared `TensorFMI3Model`, universally over the tensor shape:
rank and extents stay symbolic and no coordinate is enumerated. Each tensor
variable is one `Float64` declaration carrying one `Dimension` per extent, with
one value reference per variable, and the model structure lists the output,
continuous-state derivative and initial unknowns.

This is a package-checked product only. It is not emitted by production and does
not change the existing scalar unit `modelDescription` or any existing contract.
Array `start` attributes render the profile's uniform fixed-zero initialization
as one flattened value per element, per the FMI 3.0.2 array `start` rule. -/
namespace Rumoca.FMI3.TensorMetadata
open XML Rumoca.Tensor Rumoca.Solve

/-! ### Document builder -/

/-- One flattened `start` entry per element of a tensor, all equal to the
profile's fixed-zero initialization. -/
def startEntries (shape : Shape) : List String := List.replicate shape.volume "0"

/-- FMI 3.0.2 array `start`: a space-separated list of one value per element
(the product of the `Dimension` starts), here the fixed-zero initialization of
the admitted profile. -/
def startValue (shape : Shape) : String :=
  (startEntries shape).foldr (fun s acc => s ++ (if acc.isEmpty then "" else " " ++ acc)) ""

/-- One `Dimension` element with a constant extent, the FMI schema's
`Dimension` with a `start` attribute rather than a dynamic `valueReference`. -/
def dimension (n : Nat) : Element := ⟨"Dimension", [("start", toString n)], [], ""⟩

/-- One `Dimension` per tensor extent, in declaration order. -/
def dimensions (shape : Shape) : List Element := shape.dimensions.map dimension

/-- Independent time base. Scalar, no dimensions. -/
def timeVar : Element :=
  ⟨"Float64", [("name", "time"), ("valueReference", "0"),
    ("causality", "independent"), ("variability", "continuous")], [], ""⟩

/-- Input tensor `u`. Inputs carry one flattened start value per element; the
profile initializes to the fixed-zero fill. -/
def inputVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "u"), ("valueReference", "1"),
    ("causality", "input"), ("variability", "continuous"),
    ("start", startValue shape)], dimensions shape, ""⟩

/-- State tensor `x`, exact initialization from the fixed-zero program, one
flattened start value per element. -/
def stateVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "x"), ("valueReference", "2"),
    ("causality", "local"), ("variability", "continuous"),
    ("initial", "exact"), ("start", startValue shape)], dimensions shape, ""⟩

/-- Derivative tensor `der(x)`, referencing the state's value reference. -/
def derivativeVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "der(x)"), ("valueReference", "3"),
    ("causality", "local"), ("variability", "continuous"),
    ("initial", "calculated"), ("derivative", "2")], dimensions shape, ""⟩

/-- Explicit dense output tensor `J`, a `rows * columns` matrix over the state
element count. -/
def outputVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "J"), ("valueReference", "4"),
    ("causality", "output"), ("variability", "continuous"),
    ("initial", "calculated")], dimensions (matrixShape shape.volume shape.volume), ""⟩

/-- Declared model variables. The output is present exactly when the prepared
problem carries a diagonal (Jacobian) observation. -/
def variableNodes (shape : Shape) : Bool → List Element
  | true => [timeVar, inputVar shape, stateVar shape, derivativeVar shape, outputVar shape]
  | false => [timeVar, inputVar shape, stateVar shape, derivativeVar shape]

-- Both der(x) = u .* u and J = jacobian(u .* u, u) depend on the input u
-- (value reference 1). An omitted `dependencies` attribute means "depends on
-- all"; the explicit `dependencies="1"` with `dependenciesKind="dependent"`
-- records the actual single input dependency.
def continuousStateDerivative : Element :=
  ⟨"ContinuousStateDerivative",
    [("valueReference", "3"), ("dependencies", "1"), ("dependenciesKind", "dependent")], [], ""⟩
def initialUnknownDerivative : Element :=
  ⟨"InitialUnknown",
    [("valueReference", "3"), ("dependencies", "1"), ("dependenciesKind", "dependent")], [], ""⟩
def outputEntry : Element :=
  ⟨"Output",
    [("valueReference", "4"), ("dependencies", "1"), ("dependenciesKind", "dependent")], [], ""⟩
def initialUnknownOutput : Element :=
  ⟨"InitialUnknown",
    [("valueReference", "4"), ("dependencies", "1"), ("dependenciesKind", "dependent")], [], ""⟩

/-- Model structure: outputs, continuous-state derivatives and initial unknowns.
The output entries are present exactly when the problem exposes a dense output. -/
def structureNodes : Bool → List Element
  | true => [outputEntry, continuousStateDerivative, initialUnknownDerivative, initialUnknownOutput]
  | false => [continuousStateDerivative, initialUnknownDerivative]

/-- The tensor model's instantiation token (FMI 3.0.2 §2.4.1 `instantiationToken`),
the tensor namespace paired with the model name. The tensor factory validates this
literal, and it is the `instantiationToken` attribute of the model description. -/
def token (m : TensorFMI3Model shape) : String := "lean-rumoca-tensor-v1:" ++ m.name

/-- The tensor model description for a prepared `TensorFMI3Model`, universal in
the tensor shape. -/
def modelDescription (m : TensorFMI3Model shape) : Element :=
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", m.name),
    ("instantiationToken", token m),
    ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier m.name)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier m.name),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], variableNodes shape m.hasOutput, ""⟩,
    ⟨"ModelStructure", [], structureNodes m.hasOutput, ""⟩], ""⟩

/-- The model description's declared `instantiationToken` attribute is exactly the
tensor token the tensor factory validates, so the emitted adapter accepts precisely
the token the model description declares (FMI 3.0.2 §2.4.1). -/
theorem token_attribute (m : TensorFMI3Model shape) :
    (modelDescription m).attributes.lookup "instantiationToken" = some (token m) := rfl

/-! ### Text of decimal extents -/

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

/-- A space-separated join of printable-text tokens is printable text. -/
theorem text_startFold (l : List String) (h : ∀ s ∈ l, XML.Text s) :
    XML.Text (l.foldr (fun s acc => s ++ (if acc.isEmpty then "" else " " ++ acc)) "") := by
  induction l with
  | nil => intro c hc; exact absurd hc (by simp)
  | cons a as ih =>
    have hacc := ih (fun s hs => h s (by simp [hs]))
    refine text_append (h a (by simp)) ?_
    split
    · intro c hc; exact absurd hc (by simp)
    · exact text_append (by decide) hacc

/-! ### Array start values -/

theorem startEntries_length (shape : Shape) : (startEntries shape).length = shape.volume := by
  simp [startEntries]

theorem startValue_text (shape : Shape) : XML.Text (startValue shape) := by
  refine text_startFold (startEntries shape) ?_
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  decide

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

theorem dims_all_valid (ds : List Nat) :
    ((ds.map dimension).map Element.valid).all id = true := by
  induction ds with
  | nil => rfl
  | cons n ns ih =>
    exact Certificate.children_valid_cons (dimension n) (ns.map dimension) (dimension_valid n) ih

/-- Every element of a list is valid, hence the mapped validity flags all hold. -/
theorem all_valid_of_forall {l : List Element} (h : ∀ e ∈ l, e.valid = true) :
    (l.map Element.valid).all id = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    exact Certificate.children_valid_cons a as (h a (by simp)) (ih (fun e he => h e (by simp [he])))

theorem dimensions_valid (shape : Shape) :
    ((dimensions shape).map Element.valid).all id = true :=
  dims_all_valid shape.dimensions

/-- Any `Float64` declaration with valid literal attributes and valid dimension
children passes the restricted XML validator. -/
theorem float64_valid (attrs : List (String × String)) (dims : List Element)
    (hattrs : XML.AttributesValid attrs)
    (hdims : (dims.map Element.valid).all id = true) :
    (⟨"Float64", attrs, dims, ""⟩ : Element).valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    exact ⟨(by decide : XML.Name "Float64"), hattrs, (by decide : XML.Text ""), Or.inl rfl⟩
  · exact hdims

theorem inputAttrs_valid (shape : Shape) :
    XML.AttributesValid [("name", "u"), ("valueReference", "1"), ("causality", "input"),
      ("variability", "continuous"), ("start", startValue shape)] := by
  refine ⟨(by decide :
    (["name", "valueReference", "causality", "variability", "start"] : List String).Nodup), ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨(by decide : XML.Name "start"), startValue_text shape⟩

theorem stateAttrs_valid (shape : Shape) :
    XML.AttributesValid [("name", "x"), ("valueReference", "2"), ("causality", "local"),
      ("variability", "continuous"), ("initial", "exact"), ("start", startValue shape)] := by
  refine ⟨(by decide :
    (["name", "valueReference", "causality", "variability", "initial", "start"] : List String).Nodup),
    ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨(by decide : XML.Name "start"), startValue_text shape⟩

theorem inputVar_valid (shape : Shape) : (inputVar shape).valid = true :=
  float64_valid [("name", "u"), ("valueReference", "1"), ("causality", "input"),
    ("variability", "continuous"), ("start", startValue shape)] (dimensions shape)
    (inputAttrs_valid shape) (dimensions_valid shape)

theorem stateVar_valid (shape : Shape) : (stateVar shape).valid = true :=
  float64_valid [("name", "x"), ("valueReference", "2"), ("causality", "local"),
    ("variability", "continuous"), ("initial", "exact"), ("start", startValue shape)] (dimensions shape)
    (stateAttrs_valid shape) (dimensions_valid shape)

theorem derivativeVar_valid (shape : Shape) : (derivativeVar shape).valid = true :=
  float64_valid [("name", "der(x)"), ("valueReference", "3"), ("causality", "local"),
    ("variability", "continuous"), ("initial", "calculated"), ("derivative", "2")] (dimensions shape)
    (by decide) (dimensions_valid shape)

theorem outputVar_valid (shape : Shape) : (outputVar shape).valid = true :=
  float64_valid [("name", "J"), ("valueReference", "4"), ("causality", "output"),
    ("variability", "continuous"), ("initial", "calculated")]
    (dimensions (matrixShape shape.volume shape.volume))
    (by decide) (dimensions_valid (matrixShape shape.volume shape.volume))

theorem timeVar_valid : timeVar.valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
  · rfl

/-- Every declared variable node passes the restricted XML validator. -/
theorem variableNodes_valid (shape : Shape) (hasOutput : Bool) :
    ((variableNodes shape hasOutput).map Element.valid).all id = true := by
  cases hasOutput
  · refine Certificate.children_valid_cons _ _ timeVar_valid ?_
    refine Certificate.children_valid_cons _ _ (inputVar_valid shape) ?_
    refine Certificate.children_valid_cons _ _ (stateVar_valid shape) ?_
    exact Certificate.children_valid_cons _ _ (derivativeVar_valid shape) rfl
  · refine Certificate.children_valid_cons _ _ timeVar_valid ?_
    refine Certificate.children_valid_cons _ _ (inputVar_valid shape) ?_
    refine Certificate.children_valid_cons _ _ (stateVar_valid shape) ?_
    refine Certificate.children_valid_cons _ _ (derivativeVar_valid shape) ?_
    exact Certificate.children_valid_cons _ _ (outputVar_valid shape) rfl

theorem structureNodes_valid (hasOutput : Bool) :
    ((structureNodes hasOutput).map Element.valid).all id = true := by
  apply all_valid_of_forall
  intro e he
  cases hasOutput
  · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      · apply Certificate.node_valid
        · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
        · rfl
  · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;>
      · apply Certificate.node_valid
        · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
        · rfl

/-- The model description is a well-formed tree, given a printable model name. -/
theorem valid (m : TensorFMI3Model shape) (name_text : XML.Text m.name) :
    (modelDescription m).valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨(by decide : XML.Name "fmiModelDescription"),
      ⟨(by decide :
        (["fmiVersion", "modelName", "instantiationToken", "generationTool"] : List String).Nodup),
        ?_⟩,
      (by decide : XML.Text ""), Or.inl rfl⟩
    intro a ha
    simp only [modelDescription, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨(by decide : XML.Name "modelName"), name_text⟩
    · exact ⟨(by decide : XML.Name "instantiationToken"),
        text_append (by decide : XML.Text "lean-rumoca-tensor-v1:") name_text⟩
    · exact ⟨by decide, by decide⟩
  · -- ModelExchange, CoSimulation carry the model identifier; the rest are closed.
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        refine ⟨(by decide : XML.Name "ModelExchange"),
          ⟨(by decide : (["modelIdentifier"] : List String).Nodup), ?_⟩,
          (by decide : XML.Text ""), Or.inl rfl⟩
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨(by decide : XML.Name "modelIdentifier"),
          text_append (by decide : XML.Text "Rumoca_") name_text⟩
      · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        refine ⟨(by decide : XML.Name "CoSimulation"),
          ⟨(by decide :
            (["modelIdentifier", "canHandleVariableCommunicationStepSize",
              "fixedInternalStepSize"] : List String).Nodup), ?_⟩,
          (by decide : XML.Text ""), Or.inl rfl⟩
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨(by decide : XML.Name "modelIdentifier"),
            text_append (by decide : XML.Text "Rumoca_") name_text⟩
        · exact ⟨by decide, by decide⟩
        · exact ⟨by decide, by decide⟩
      · rfl
    -- LogCategories (with its Category child) and DefaultExperiment are closed.
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
      · refine Certificate.children_valid_cons _ _ ?_ rfl
        apply Certificate.node_valid
        · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
        · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
      · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        exact ⟨(by decide : XML.Name "ModelVariables"),
          (by decide : XML.AttributesValid ([] : List (String × String))),
          (by decide : XML.Text ""), Or.inl rfl⟩
      · exact variableNodes_valid shape m.hasOutput
    refine Certificate.children_valid_cons _ _ ?_ rfl
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        exact ⟨(by decide : XML.Name "ModelStructure"),
          (by decide : XML.AttributesValid ([] : List (String × String))),
          (by decide : XML.Text ""), Or.inl rfl⟩
      · exact structureNodes_valid m.hasOutput

/-- The document is a well-formed XML tree accepted by the in-tree renderer and
syntax proofs, given a printable model name. -/
theorem document (m : TensorFMI3Model shape) (name_text : XML.Text m.name) :
    XML.Document (modelDescription m) (XML.document (modelDescription m)) :=
  XML.document_correct (modelDescription m) (valid m name_text)

/-! ### Value references are pairwise distinct -/

/-- The declared value references, in declaration order. -/
def valueReferences (m : TensorFMI3Model shape) : List String :=
  (variableNodes shape m.hasOutput).filterMap (fun v => v.attributes.lookup "valueReference")

theorem valueReferences_eq (m : TensorFMI3Model shape) :
    valueReferences m
      = if m.hasOutput then (["0", "1", "2", "3", "4"] : List String) else ["0", "1", "2", "3"] := by
  simp only [valueReferences]
  cases hm : m.hasOutput <;> rfl

theorem valueReferences_nodup (m : TensorFMI3Model shape) : (valueReferences m).Nodup := by
  rw [valueReferences_eq]
  cases hm : m.hasOutput <;> decide

/-- The declared value references are exactly the tensor profile's Float64
getter references, in order: the profile record's `references.get` is the single
source of truth the model description's value-reference table is checked against.
Holds for the dense-output tensor profile (the tensor profile carries an
output). -/
theorem valueReferences_profile (m : TensorFMI3Model shape) (hasOutput : m.hasOutput = true) :
    valueReferences m
      = (Rumoca.FMI3.TensorInstance.tensorProfile.references.get).map toString := by
  rw [valueReferences_eq, hasOutput]; rfl

/-! ### Dimension starts multiply to the tensor element count -/

/-- The extents read back from a variable's `Dimension` start attributes. -/
def dimStarts (v : Element) : List Nat :=
  v.children.filterMap (fun d => (d.attributes.lookup "start").map (fun s => Rumoca.CDecimal.value s.toList))

theorem dimStarts_dimensions (shape : Shape) (name text : String)
    (attrs : List (String × String)) :
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

theorem stateVar_dim_product (shape : Shape) :
    (dimStarts (stateVar shape)).foldr (· * ·) 1 = shape.volume := by
  rw [stateVar, dimStarts_dimensions]; rfl

theorem inputVar_dim_product (shape : Shape) :
    (dimStarts (inputVar shape)).foldr (· * ·) 1 = shape.volume := by
  rw [inputVar, dimStarts_dimensions]; rfl

theorem derivativeVar_dim_product (shape : Shape) :
    (dimStarts (derivativeVar shape)).foldr (· * ·) 1 = shape.volume := by
  rw [derivativeVar, dimStarts_dimensions]; rfl

theorem outputVar_dim_product (shape : Shape) :
    (dimStarts (outputVar shape)).foldr (· * ·) 1
      = (matrixShape shape.volume shape.volume).volume := by
  rw [outputVar, dimStarts_dimensions]
  simp [matrixShape, Shape.volume]

/-! ### The derivative attribute references the state -/

theorem derivative_references_state (shape : Shape) :
    (derivativeVar shape).attributes.lookup "derivative"
      = (stateVar shape).attributes.lookup "valueReference" := by
  rfl

/-! ### Model-structure entries reference declared variables -/

theorem structure_references_declared (m : TensorFMI3Model shape) :
    ∀ node ∈ structureNodes m.hasOutput,
      ∃ ref, node.attributes.lookup "valueReference" = some ref ∧ ref ∈ valueReferences m := by
  have key : ∀ b : Bool, ∀ node ∈ structureNodes b, ∃ ref,
      node.attributes.lookup "valueReference" = some ref ∧
      ref ∈ (if b then (["0", "1", "2", "3", "4"] : List String) else ["0", "1", "2", "3"]) := by
    intro b node hn
    cases b
    · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact ⟨"3", rfl, by decide⟩
      · exact ⟨"3", rfl, by decide⟩
    · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨"4", rfl, by decide⟩
      · exact ⟨"3", rfl, by decide⟩
      · exact ⟨"3", rfl, by decide⟩
      · exact ⟨"4", rfl, by decide⟩
  intro node hn
  rw [valueReferences_eq]
  exact key m.hasOutput node hn

/-- Each model-structure entry lists exactly one dependency reference (the input
`u`, value reference 1); that listed reference is a declared variable's value
reference. -/
theorem structure_dependencies_declared (m : TensorFMI3Model shape) :
    ∀ node ∈ structureNodes m.hasOutput, ∃ dep,
      node.attributes.lookup "dependencies" = some dep ∧ dep ∈ valueReferences m := by
  have key : ∀ b : Bool, ∀ node ∈ structureNodes b, ∃ dep,
      node.attributes.lookup "dependencies" = some dep ∧
      dep ∈ (if b then (["0", "1", "2", "3", "4"] : List String) else ["0", "1", "2", "3"]) := by
    intro b node hn
    cases b
    · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact ⟨"1", rfl, by decide⟩
      · exact ⟨"1", rfl, by decide⟩
    · simp only [structureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact ⟨"1", rfl, by decide⟩
      · exact ⟨"1", rfl, by decide⟩
      · exact ⟨"1", rfl, by decide⟩
      · exact ⟨"1", rfl, by decide⟩
  intro node hn
  rw [valueReferences_eq]
  exact key m.hasOutput node hn

/-! ### Model identifiers decode exactly as the unit document -/

theorem modelIdentifiers_decode (m : TensorFMI3Model shape) :
    decodeModelIdentifiers (modelDescription m)
      = some (m.name, modelIdentifier m.name, modelIdentifier m.name) := by
  simp [decodeModelIdentifiers, modelDescription, guard, Build.only?, List.filter, List.lookup]

/-! ### Constant-rate profile model description

The constant-rate profile (`G01`) exposes no input tensor and no output tensor.
Its states are a homogeneous vector of scalar states, and the profile keeps the
state rank and extent symbolic: the model description declares one array state
variable `x` of the state shape (one `Dimension` per extent) rather than
enumerating one scalar variable per element, matching the record's contiguous
state region and the compiler's rule against enumerating tensor coordinates.
Value references are renumbered without the input: `0` time, `1` state, `2`
derivative. The derivative `der(x)` is a signed decimal constant, so its
`ContinuousStateDerivative` lists an empty dependency set. -/

/-- The constant-rate model's instantiation token. -/
def constantToken (name : String) : String := "lean-rumoca-constant-v1:" ++ name

/-- State vector `x`, exact fixed-zero initialization, value reference `1`. -/
def constantStateVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "x"), ("valueReference", "1"),
    ("causality", "local"), ("variability", "continuous"),
    ("initial", "exact"), ("start", startValue shape)], dimensions shape, ""⟩

/-- Derivative vector `der(x)`, referencing the state's value reference `1`. -/
def constantDerivativeVar (shape : Shape) : Element :=
  ⟨"Float64", [("name", "der(x)"), ("valueReference", "2"),
    ("causality", "local"), ("variability", "continuous"),
    ("initial", "calculated"), ("derivative", "1")], dimensions shape, ""⟩

/-- Declared constant-rate model variables: the time base, the state vector and
its derivative. -/
def constantVariableNodes (shape : Shape) : List Element :=
  [timeVar, constantStateVar shape, constantDerivativeVar shape]

/-- The derivative is a constant, so it lists an empty dependency set. -/
def constantContinuousStateDerivative : Element :=
  ⟨"ContinuousStateDerivative", [("valueReference", "2"), ("dependencies", "")], [], ""⟩
def constantInitialUnknownDerivative : Element :=
  ⟨"InitialUnknown", [("valueReference", "2"), ("dependencies", "")], [], ""⟩

/-- Constant-rate model structure: the continuous-state derivative and the initial
unknown, each with an empty dependency set. -/
def constantStructureNodes : List Element :=
  [constantContinuousStateDerivative, constantInitialUnknownDerivative]

/-- The constant-rate model description, universal in the state shape. -/
def constantModelDescription (shape : Shape) (name : String) : Element :=
  ⟨"fmiModelDescription", [("fmiVersion", "3.0"), ("modelName", name),
    ("instantiationToken", constantToken name),
    ("generationTool", "lean_rumoca")], [
    ⟨"ModelExchange", [("modelIdentifier", modelIdentifier name)], [], ""⟩,
    ⟨"CoSimulation", [("modelIdentifier", modelIdentifier name),
      ("canHandleVariableCommunicationStepSize", "true"), ("fixedInternalStepSize", "1")], [], ""⟩,
    ⟨"LogCategories", [], [⟨"Category", [("name", "logStatus")], [], ""⟩], ""⟩,
    ⟨"DefaultExperiment", [("startTime", "0"), ("stopTime", "3"), ("stepSize", "1")], [], ""⟩,
    ⟨"ModelVariables", [], constantVariableNodes shape, ""⟩,
    ⟨"ModelStructure", [], constantStructureNodes, ""⟩], ""⟩

theorem constantToken_attribute (shape : Shape) (name : String) :
    (constantModelDescription shape name).attributes.lookup "instantiationToken"
      = some (constantToken name) := rfl

/-! #### Well-formedness -/

theorem constantStateAttrs_valid (shape : Shape) :
    XML.AttributesValid [("name", "x"), ("valueReference", "1"), ("causality", "local"),
      ("variability", "continuous"), ("initial", "exact"), ("start", startValue shape)] := by
  refine ⟨(by decide :
    (["name", "valueReference", "causality", "variability", "initial", "start"] : List String).Nodup),
    ?_⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨(by decide : XML.Name "start"), startValue_text shape⟩

theorem constantStateVar_valid (shape : Shape) : (constantStateVar shape).valid = true :=
  float64_valid [("name", "x"), ("valueReference", "1"), ("causality", "local"),
    ("variability", "continuous"), ("initial", "exact"), ("start", startValue shape)] (dimensions shape)
    (constantStateAttrs_valid shape) (dimensions_valid shape)

theorem constantDerivativeVar_valid (shape : Shape) : (constantDerivativeVar shape).valid = true :=
  float64_valid [("name", "der(x)"), ("valueReference", "2"), ("causality", "local"),
    ("variability", "continuous"), ("initial", "calculated"), ("derivative", "1")] (dimensions shape)
    (by decide) (dimensions_valid shape)

theorem constantVariableNodes_valid (shape : Shape) :
    ((constantVariableNodes shape).map Element.valid).all id = true := by
  refine Certificate.children_valid_cons _ _ timeVar_valid ?_
  refine Certificate.children_valid_cons _ _ (constantStateVar_valid shape) ?_
  exact Certificate.children_valid_cons _ _ (constantDerivativeVar_valid shape) rfl

theorem constantStructureNodes_valid :
    ((constantStructureNodes).map Element.valid).all id = true := by
  apply all_valid_of_forall
  intro e he
  simp only [constantStructureNodes, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;>
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
      · rfl

/-- The constant-rate model description is a well-formed tree, given a printable
model name. -/
theorem constant_valid (shape : Shape) (name : String) (name_text : XML.Text name) :
    (constantModelDescription shape name).valid = true := by
  apply Certificate.node_valid
  · rw [decide_eq_true_eq]
    refine ⟨(by decide : XML.Name "fmiModelDescription"),
      ⟨(by decide :
        (["fmiVersion", "modelName", "instantiationToken", "generationTool"] : List String).Nodup),
        ?_⟩,
      (by decide : XML.Text ""), Or.inl rfl⟩
    intro a ha
    simp only [constantModelDescription, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide⟩
    · exact ⟨(by decide : XML.Name "modelName"), name_text⟩
    · exact ⟨(by decide : XML.Name "instantiationToken"),
        text_append (by decide : XML.Text "lean-rumoca-constant-v1:") name_text⟩
    · exact ⟨by decide, by decide⟩
  · refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        refine ⟨(by decide : XML.Name "ModelExchange"),
          ⟨(by decide : (["modelIdentifier"] : List String).Nodup), ?_⟩,
          (by decide : XML.Text ""), Or.inl rfl⟩
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        exact ⟨(by decide : XML.Name "modelIdentifier"),
          text_append (by decide : XML.Text "Rumoca_") name_text⟩
      · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        refine ⟨(by decide : XML.Name "CoSimulation"),
          ⟨(by decide :
            (["modelIdentifier", "canHandleVariableCommunicationStepSize",
              "fixedInternalStepSize"] : List String).Nodup), ?_⟩,
          (by decide : XML.Text ""), Or.inl rfl⟩
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨(by decide : XML.Name "modelIdentifier"),
            text_append (by decide : XML.Text "Rumoca_") name_text⟩
        · exact ⟨by decide, by decide⟩
        · exact ⟨by decide, by decide⟩
      · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
      · refine Certificate.children_valid_cons _ _ ?_ rfl
        apply Certificate.node_valid
        · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
        · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]; exact ⟨by decide, by decide, by decide, Or.inl rfl⟩
      · rfl
    refine Certificate.children_valid_cons _ _ ?_ ?_
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        exact ⟨(by decide : XML.Name "ModelVariables"),
          (by decide : XML.AttributesValid ([] : List (String × String))),
          (by decide : XML.Text ""), Or.inl rfl⟩
      · exact constantVariableNodes_valid shape
    refine Certificate.children_valid_cons _ _ ?_ rfl
    · apply Certificate.node_valid
      · rw [decide_eq_true_eq]
        exact ⟨(by decide : XML.Name "ModelStructure"),
          (by decide : XML.AttributesValid ([] : List (String × String))),
          (by decide : XML.Text ""), Or.inl rfl⟩
      · exact constantStructureNodes_valid

/-- The constant-rate document is a well-formed XML tree accepted by the in-tree
renderer and syntax proofs, given a printable model name. -/
theorem constant_document (shape : Shape) (name : String) (name_text : XML.Text name) :
    XML.Document (constantModelDescription shape name) (XML.document (constantModelDescription shape name)) :=
  XML.document_correct (constantModelDescription shape name) (constant_valid shape name name_text)

/-! #### Value references are pairwise distinct -/

def constantValueReferences (shape : Shape) : List String :=
  (constantVariableNodes shape).filterMap (fun v => v.attributes.lookup "valueReference")

theorem constantValueReferences_eq (shape : Shape) :
    constantValueReferences shape = (["0", "1", "2"] : List String) := rfl

theorem constantValueReferences_nodup (shape : Shape) : (constantValueReferences shape).Nodup := by
  rw [constantValueReferences_eq]; decide

/-- The declared constant-rate value references are exactly the constant profile's
Float64 getter references, in order: the profile record's `references.get` is the
single source of truth the constant model description's value-reference table is
checked against. -/
theorem constantValueReferences_profile (shape : Shape) :
    constantValueReferences shape
      = (Rumoca.FMI3.TensorInstance.constantProfile.references.get).map toString := rfl

/-! #### Dimension starts multiply to the state element count -/

theorem constantStateVar_dim_product (shape : Shape) :
    (dimStarts (constantStateVar shape)).foldr (· * ·) 1 = shape.volume := by
  rw [constantStateVar, dimStarts_dimensions]; rfl

theorem constantDerivativeVar_dim_product (shape : Shape) :
    (dimStarts (constantDerivativeVar shape)).foldr (· * ·) 1 = shape.volume := by
  rw [constantDerivativeVar, dimStarts_dimensions]; rfl

/-! #### The derivative attribute references the state -/

theorem constant_derivative_references_state (shape : Shape) :
    (constantDerivativeVar shape).attributes.lookup "derivative"
      = (constantStateVar shape).attributes.lookup "valueReference" := rfl

/-! #### Model-structure entries reference declared variables -/

theorem constant_structure_references_declared (shape : Shape) :
    ∀ node ∈ constantStructureNodes, ∃ ref,
      node.attributes.lookup "valueReference" = some ref ∧ ref ∈ constantValueReferences shape := by
  intro node hn
  rw [constantValueReferences_eq]
  simp only [constantStructureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact ⟨"2", rfl, by decide⟩
  · exact ⟨"2", rfl, by decide⟩

/-- Each constant-rate structure entry lists an empty dependency set: the constant
derivative depends on no variable. -/
theorem constant_structure_dependencies_empty :
    ∀ node ∈ constantStructureNodes, node.attributes.lookup "dependencies" = some "" := by
  intro node hn
  simp only [constantStructureNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;> rfl

/-! #### Model identifiers decode exactly as the unit document -/

theorem constant_modelIdentifiers_decode (shape : Shape) (name : String) :
    decodeModelIdentifiers (constantModelDescription shape name)
      = some (name, modelIdentifier name, modelIdentifier name) := by
  simp [decodeModelIdentifiers, constantModelDescription, guard, Build.only?, List.filter, List.lookup]

end Rumoca.FMI3.TensorMetadata
