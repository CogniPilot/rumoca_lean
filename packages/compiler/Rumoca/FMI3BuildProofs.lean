import Rumoca.Verified
import RumocaFMI3.SourceLinkageProofs
import Rumoca.FMI3NameProofs

namespace Rumoca.FMI3

/-- Strengthen the existing numerical C file contract with the actual source-build
document, its public model identifiers and its source prefix. This does not
certify the rest of the FMI adapter/model description, native compilation/linking,
or the containing ZIP. -/
structure SourceBuildContract (a : Artifact source) (c description adapter metadata : String) : Prop where
  numerical : Rumoca.ArtifactContract a c .internal
  build : Build.ArtifactContract a.parsed.ast.name description
  source_prefix : SourcePrefixContract a.parsed.ast.name adapter
  model_identifiers : ModelIdentifiersContract a.parsed.ast.name metadata

theorem sourceBuild_correct (a : Artifact source) (c description adapter metadata : String)
    (numerical : Rumoca.ArtifactContract a c .internal)
    (text : XML.document (Build.description a.parsed.ast.name) = description)
    (sourcePrefix : SourcePrefixContract a.parsed.ast.name adapter)
    (identifiers : ModelIdentifiersContract a.parsed.ast.name metadata) :
    SourceBuildContract a c description adapter metadata :=
  ⟨numerical, text ▸ Build.artifact_correct _ (parsed_name a.parsed), sourcePrefix, identifiers⟩

end Rumoca.FMI3
