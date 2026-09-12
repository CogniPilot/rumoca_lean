import RumocaFMI3.Metadata
import XML.Proofs

/-! Independent count interpretation for the admitted scalar metadata profile.
ModelStructure references must resolve uniquely to scalar Float64 nodes;
dimensions require a future volume interpretation, not counting array nodes
as scalars. This relation is not a complete FMI schema/conformance judgment. -/
namespace Rumoca.FMI3.CountMetadata

def ScalarReference (nodes : List XML.Element) (node : XML.Element) : Prop :=
  ∃ reference declaration,
    node.attributes.lookup "valueReference" = some reference ∧
    nodes.filter (fun v => v.attributes.lookup "valueReference" == some reference) = [declaration] ∧
    declaration.name = "Float64" ∧
    declaration.attributes.lookup "variability" = some "continuous" ∧
    declaration.children.all (fun child => child.name != "Dimension") = true

def GroupCount (nodes entries : List XML.Element) (tag : String) (count : Nat) : Prop :=
  let selected := entries.filter (fun node => node.name == tag)
  selected.length = count ∧
    (selected.map (fun node => node.attributes.lookup "valueReference")).Nodup ∧
    ∀ node ∈ selected, ScalarReference nodes node

def ScalarCounts (root : XML.Element) (states events : Nat) : Prop :=
  ∃ nodes layout,
    root.children.filter (fun node => node.name == "ModelVariables") = [nodes] ∧
    root.children.filter (fun node => node.name == "ModelStructure") = [layout] ∧
    GroupCount nodes.children layout.children "ContinuousStateDerivative" states ∧
    GroupCount nodes.children layout.children "EventIndicator" events

theorem described_counts (m : Solve.FMI3Model source) :
    ScalarCounts (modelDescription m) m.problem.stateShape.volume 0 := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, by simp, ?_⟩
    intro node member
    have same : node = (⟨"ContinuousStateDerivative",
        [("valueReference", "2"), ("dependencies", "")], [], ""⟩ : XML.Element) := by
      simpa using member
    subst node
    refine ⟨"2", _, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, .nil, fun node member => by simp at member⟩

def Contract (m : Solve.FMI3Model source) (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ ScalarCounts root m.problem.stateShape.volume 0

theorem artifact_counts (m : Solve.FMI3Model source) (text : String)
    (metadata : XML.Document (modelDescription m) text) : Contract m text :=
  ⟨modelDescription m, metadata, described_counts m⟩

end Rumoca.FMI3.CountMetadata
