import RumocaFMI3.CountMetadata
import RumocaCore.Real.Binary64

/-! Independent scalar nominal and state-order interpretation for actual XML.
This is a profile-specific judgment; arrays require a volume and serialization extension. -/
noncomputable section
namespace Rumoca.FMI3.NominalMetadata
open XML

/-- The metadata supplies neither an explicit nor inherited nominal. Dimensions
are excluded in this scalar relation; arrays require their own volume mapping. -/
def DefaultNominal (state : XML.Element) (value : ℝ) : Prop :=
  state.name = "Float64" ∧ state.attributes.lookup "variability" = some "continuous" ∧
  state.attributes.lookup "nominal" = none ∧ state.attributes.lookup "declaredType" = none ∧
  state.children.all (fun child => child.name != "Dimension") = true ∧ value = 1

/-- Resolve a ModelStructure derivative entry, then its derivative attribute,
to exactly one state. The output list preserves ModelStructure order. -/
def StateNominal (nodes : List XML.Element) (entry : XML.Element) (stateName : String) (value : ℝ) : Prop :=
  ∃ derivativeReference derivative stateReference state,
    entry.attributes.lookup "valueReference" = some derivativeReference ∧
    nodes.filter (fun node => node.attributes.lookup "valueReference" == some derivativeReference) = [derivative] ∧
    derivative.name = "Float64" ∧ derivative.attributes.lookup "variability" = some "continuous" ∧
    derivative.children.all (fun child => child.name != "Dimension") = true ∧
    derivative.attributes.lookup "derivative" = some stateReference ∧
    nodes.filter (fun node => node.attributes.lookup "valueReference" == some stateReference) = [state] ∧
    state.attributes.lookup "name" = some stateName ∧ DefaultNominal state value

def OrderedNominals (root : XML.Element) (states : List (String × ℝ)) : Prop :=
  ∃ nodes layout,
    root.children.filter (fun node => node.name == "ModelVariables") = [nodes] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    List.Forall₂ (fun entry state => StateNominal nodes.children entry state.1 state.2)
      (layout.children.filter (fun node => node.name == "ContinuousStateDerivative")) states

theorem described_nominals (model : Solve.FMI3Model source) :
    OrderedNominals (modelDescription model) [(source.state, Binary64.value Binary64.one)] := by
  refine ⟨_, _, rfl, rfl, List.Forall₂.cons ?_ .nil⟩
  refine ⟨"2", _, "1", _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, Binary64.value_one⟩

theorem default_positive (default : DefaultNominal state value) : 0 < value := by
  rw [default.2.2.2.2.2]
  exact zero_lt_one

def Contract (source : AST.Model) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ OrderedNominals root [(source.state, Binary64.value Binary64.one)]

theorem artifact_nominals (model : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription model) text) : Contract source text :=
  ⟨modelDescription model, metadata, described_nominals model⟩

end Rumoca.FMI3.NominalMetadata
