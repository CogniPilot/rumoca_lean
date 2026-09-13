import RumocaFMI3.Float64Metadata
import RumocaFMI3.StateMetadata

namespace Rumoca.FMI3.Float64SetMetadata
open XML Float64Metadata

/-- FMI 3.0.2's schema defaults an absent reinit attribute to false. -/
def NoReinit (declaration : Element) : Prop :=
  declaration.attributes.lookup "reinit" = none ∨
  declaration.attributes.lookup "reinit" = some "false" ∨
  declaration.attributes.lookup "reinit" = some "0"

/-- A scalar state that accepts an exact start value. Numeric reference
resolution binds the API selection to the very declaration reached through
ModelStructure and its derivative attribute, without assuming names unique. -/
def Writable (root : Element) (reference : Nat) (name : String) : Prop :=
  ∃ modelVariables layout entry derivative declaration derivativeReference,
    root.children.filter (fun node => node.name == "ModelVariables") = [modelVariables] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    entry ∈ layout.children.filter (fun node => node.name == "ContinuousStateDerivative") ∧
    referenceOf entry = some derivativeReference ∧
    modelVariables.children.filter (fun node => referenceOf node == some derivativeReference) = [derivative] ∧
    StateMetadata.ScalarContinuous derivative ∧
    (derivative.attributes.lookup "derivative").bind decimal = some reference ∧
    modelVariables.children.filter (fun node => referenceOf node == some reference) = [declaration] ∧
    declaration.name = "Float64" ∧
    declaration.attributes.lookup "name" = some name ∧
    declaration.attributes.lookup "variability" = some "continuous" ∧
    declaration.children.filter (fun node => node.name == "Dimension") = [] ∧
    declaration.attributes.lookup "causality" = some "local" ∧
    declaration.attributes.lookup "initial" = some "exact" ∧ NoReinit declaration

theorem Writable.lookup (writable : Writable root reference variableName) : Lookup root reference variableName := by
  obtain ⟨modelVariables, layout, entry, derivative, declaration, derivativeReference,
    hv, _, _, _, _, _, _, hd, ht, hn, hc, hs, _⟩ := writable
  exact ⟨modelVariables, declaration, hv, hd, ht, hn, hc, hs⟩

theorem Writable.unique (first : Writable root reference variableName)
    (second : Writable root reference other) : variableName = other :=
  first.lookup.unique second.lookup

theorem described_state (model : Solve.FMI3Model source) :
    Writable (modelDescription model) 1 source.state := by
  let vars := (modelDescription model).children[4]'(by simp [modelDescription])
  let layout := (modelDescription model).children[5]'(by simp [modelDescription])
  refine ⟨vars, layout, layout.children[0]'(by simp [layout, modelDescription]),
    vars.children[2]'(by simp [vars, modelDescription]), vars.children[1]'(by simp [vars, modelDescription]),
    2, rfl, rfl, ?_, rfl, rfl, ⟨rfl, rfl, rfl⟩, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  simp [layout, modelDescription]

theorem described_reference (model : Solve.FMI3Model source) (reference : Nat) :
    (∃ name, Writable (modelDescription model) reference name) ↔ reference = 1 := by
  have enough : 4 < (modelDescription model).children.length := by simp [modelDescription]
  constructor
  · rintro ⟨name, modelVariables, layout, entry, derivative, declaration, derivativeReference,
      hv, _, _, _, _, _, _, hd, _, _, _, _, causality, initial, _⟩
    have vars : modelVariables = (modelDescription model).children[4]'(by simp [modelDescription]) :=
      (List.singleton_inj.mp hv).symm
    subst modelVariables
    have selected : declaration ∈ (modelDescription model).children[4].children.filter
        (fun node => referenceOf node == some reference) := by rw [hd]; simp
    obtain ⟨member, found⟩ := List.mem_filter.mp selected
    have found := beq_iff_eq.mp found
    simp only [modelDescription, List.getElem_cons_zero, List.getElem_cons_succ,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · change some "independent" = some "local" at causality
      simp at causality
    · change some 1 = some reference at found
      exact (Option.some.inj found).symm
    · change some "calculated" = some "exact" at initial
      simp at initial
  · rintro rfl
    exact ⟨_, described_state model⟩

def Contract (source : AST.Model) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ Writable root 1 source.state ∧
    ∀ reference, (∃ name, Writable root reference name) ↔ reference = 1

theorem artifact_state (model : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription model) text) : Contract source text :=
  ⟨modelDescription model, metadata, described_state model, described_reference model⟩

end Rumoca.FMI3.Float64SetMetadata
