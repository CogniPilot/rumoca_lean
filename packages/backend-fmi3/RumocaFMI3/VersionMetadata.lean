import RumocaFMI3.Metadata
import RumocaFMI3.BuildDescriptionProofs

/-! Interpret the two actual XML documents independently of C execution.
This is their version correspondence, not full normative XML conformance or
proof of the included native header's macro interpretation. -/
namespace Rumoca.FMI3.Version

def MetadataContract (metadata description version : String) : Prop :=
  ∃ model build : XML.Element,
    XML.Document model metadata ∧ XML.Document build description ∧
    model.name = "fmiModelDescription" ∧ build.name = "fmiBuildDescription" ∧
    model.attributes.lookup "fmiVersion" = some version ∧
    build.attributes.lookup "fmiVersion" = some version

theorem metadata_correct (m : Solve.FMI3Model source)
    (model : XML.Document (modelDescription m) metadata)
    (build : Build.ArtifactContract source.name description) :
    MetadataContract metadata description "3.0" := by
  obtain ⟨root, document, configurations⟩ := build
  obtain ⟨recipe, decoded, _⟩ := configurations .x86_64Linux
  obtain ⟨name, version⟩ := Build.decode_version decoded
  exact ⟨modelDescription m, root, model, document, rfl, name, rfl, version⟩

end Rumoca.FMI3.Version
