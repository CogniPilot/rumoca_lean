import RumocaFMI3.Metadata
import XML.Syntax

/-! Exact omission of the discrete-evaluation capability in each interface.
FMI 3.0.2 §2.4.2 supplies the false default; this predicate binds the actual
XML tree without claiming to formalize every schema Boolean spelling. -/
namespace Rumoca.FMI3.DiscreteEvaluation

def InterfaceWithoutEvaluation (root : XML.Element) (tag : String) : Prop :=
  ∃ node, root.children.filter (fun child => child.name == tag) = [node] ∧
    node.attributes.lookup "providesEvaluateDiscreteStates" = none

def MetadataContract (text : String) : Prop :=
  ∃ root, XML.Document root text ∧ root.name = "fmiModelDescription" ∧
    InterfaceWithoutEvaluation root "ModelExchange" ∧
    InterfaceWithoutEvaluation root "CoSimulation"

theorem described_capability (model : Solve.FMI3Model source) :
    InterfaceWithoutEvaluation (modelDescription model) "ModelExchange" ∧
    InterfaceWithoutEvaluation (modelDescription model) "CoSimulation" := by
  exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem artifact_capability (model : Solve.FMI3Model source) (text : String)
    (document : XML.Document (modelDescription model) text) : MetadataContract text :=
  ⟨modelDescription model, document, rfl, described_capability model⟩

end Rumoca.FMI3.DiscreteEvaluation
