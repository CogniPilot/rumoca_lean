import RumocaFMI3.CountMetadata

noncomputable section
/-! Independent interpretation of the scalar state vector in ModelStructure.
State identity does not depend on nominal values or initialization attributes.
Array serialization requires an explicit extension of this scalar relation. -/
namespace Rumoca.FMI3.StateMetadata
open XML

def ScalarContinuous (node : XML.Element) : Prop :=
  node.name = "Float64" ∧ node.attributes.lookup "variability" = some "continuous" ∧
  node.children.all (fun child => child.name != "Dimension") = true

/-- Follow the derivative entry's value reference to its declaration, then
follow the declaration's derivative attribute to the unique state declaration. -/
def StateReference (nodes : List XML.Element) (entry : XML.Element) (stateName : String) : Prop :=
  ∃ derivativeReference derivative stateReference state,
    entry.attributes.lookup "valueReference" = some derivativeReference ∧
    nodes.filter (fun node => node.attributes.lookup "valueReference" == some derivativeReference) = [derivative] ∧
    ScalarContinuous derivative ∧
    derivative.attributes.lookup "derivative" = some stateReference ∧
    nodes.filter (fun node => node.attributes.lookup "valueReference" == some stateReference) = [state] ∧
    state.attributes.lookup "name" = some stateName ∧ ScalarContinuous state

def OrderedStates (root : XML.Element) (states : List String) : Prop :=
  ∃ nodes layout,
    root.children.filter (fun node => node.name == "ModelVariables") = [nodes] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    List.Forall₂ (StateReference nodes.children)
      (layout.children.filter (fun node => node.name == "ContinuousStateDerivative")) states

theorem StateReference.unique (first : StateReference nodes entry name)
    (second : StateReference nodes entry other) : name = other := by
  obtain ⟨dref, derivative, sref, state, hdref, hd, _, hsref, hs, hn, _⟩ := first
  obtain ⟨dref', derivative', sref', state', hdref', hd', _, hsref', hs', hn', _⟩ := second
  have dr := Option.some.inj (hdref.symm.trans hdref')
  subst dref'
  have de := List.singleton_inj.mp (hd.symm.trans hd')
  subst derivative'
  have sr := Option.some.inj (hsref.symm.trans hsref')
  subst sref'
  have st := List.singleton_inj.mp (hs.symm.trans hs')
  subst state'
  exact Option.some.inj (hn.symm.trans hn')

private theorem names_unique (first : List.Forall₂ (StateReference nodes) entries names)
    (second : List.Forall₂ (StateReference nodes) entries others) : names = others := by
  induction first generalizing others with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => rw [head.unique other, ih rest]

theorem OrderedStates.unique (first : OrderedStates root names)
    (second : OrderedStates root others) : names = others := by
  obtain ⟨nodes, layout, hn, hl, ordered⟩ := first
  obtain ⟨nodes', layout', hn', hl', ordered'⟩ := second
  have ne := List.singleton_inj.mp (hn.symm.trans hn')
  subst nodes'
  have le := List.singleton_inj.mp (hl.symm.trans hl')
  subst layout'
  exact names_unique ordered ordered'

theorem described_states (model : Solve.FMI3Model source) :
    OrderedStates (modelDescription model) [source.state] := by
  refine ⟨_, _, rfl, rfl, List.Forall₂.cons ?_ .nil⟩
  exact ⟨"2", _, "1", _, rfl, rfl, ⟨rfl, rfl, rfl⟩,
    rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

def Contract (source : AST.Model) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ OrderedStates root [source.state]

theorem artifact_states (model : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription model) text) : Contract source text :=
  ⟨modelDescription model, metadata, described_states model⟩

end Rumoca.FMI3.StateMetadata
