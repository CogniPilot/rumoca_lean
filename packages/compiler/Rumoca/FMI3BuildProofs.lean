import Rumoca.Verified
import RumocaFMI3.SourceLinkageProofs
import Rumoca.FMI3NameProofs
import Rumoca.FMI3AdapterProofs

namespace Rumoca.FMI3

/-- Numerical C, build dependencies, public identifiers and the source prefix
are joined with complete adapter byte identity and the proved reset fragment.
This does not certify the other public bodies, whole-C preprocessing/header
semantics, full normative metadata conformance, native linking or the ZIP. -/
structure SourceBuildContract (a : Artifact source) (c description adapter metadata : String) : Prop where
  numerical : Rumoca.ArtifactContract a c .internal
  build : Build.ArtifactContract a.parsed.ast.name description
  source_prefix : SourcePrefixContract a.parsed.ast.name adapter
  model_identifiers : ModelIdentifiersContract a.parsed.ast.name metadata
  adapter : AdapterContract a adapter
  metadata : XML.Document (modelDescription a.solve.prepareFMI3) metadata

theorem sourceBuild_correct (a : Artifact source) (c description adapter metadata : String)
    (numerical : Rumoca.ArtifactContract a c .internal)
    (text : XML.document (Build.description a.parsed.ast.name) = description)
    (sourcePrefix : SourcePrefixContract a.parsed.ast.name adapter)
    (identifiers : ModelIdentifiersContract a.parsed.ast.name metadata)
    (adapterContract : AdapterContract a adapter)
    (metadataDocument : XML.Document (modelDescription a.solve.prepareFMI3) metadata) :
    SourceBuildContract a c description adapter metadata :=
  ⟨numerical, text ▸ Build.artifact_correct _ (parsed_name a.parsed), sourcePrefix,
    identifiers, adapterContract, metadataDocument⟩

end Rumoca.FMI3
