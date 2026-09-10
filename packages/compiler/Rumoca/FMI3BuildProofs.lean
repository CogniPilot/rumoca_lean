import Rumoca.Verified
import RumocaFMI3.BuildDescriptionProofs

namespace Rumoca.FMI3

/-- Strengthen the existing numerical C file contract with the actual source-build
document. This does not certify the FMI adapter, modelDescription.xml, native
compilation/linking, or the containing ZIP. -/
structure SourceBuildContract (a : Artifact source) (c description : String) : Prop where
  numerical : Rumoca.ArtifactContract a c
  build : Build.ArtifactContract description

theorem sourceBuild_correct (a : Artifact source) (c description : String)
    (numerical : Rumoca.ArtifactContract a c)
    (text : XML.document Build.description = description) :
    SourceBuildContract a c description :=
  ⟨numerical, text ▸ Build.artifact_correct⟩

end Rumoca.FMI3
