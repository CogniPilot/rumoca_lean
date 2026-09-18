import Rumoca.Verified
import RumocaFMI3.SourceLinkageProofs
import Rumoca.FMI3NameProofs
import Rumoca.FMI3AdapterProofs
import RumocaFMI3.CallPolicy

namespace Rumoca.FMI3

/-- Numerical C, build dependencies, public identifiers, source prefix and
actual XML share one adapter contract. Its mandatory header coverage binds
every exported signature to its existing execution/printer contract. Those
contracts retain their explicit preconditions and modeled call/history scope;
whole-C preprocessing/ABI, legal-history correspondence, native linking and
complete correlated archive/provenance obligations remain separate. -/
structure SourceBuildContract (a : Artifact source) (c description adapter metadata : String) : Prop where
  numerical : Rumoca.ArtifactContract a c .internal
  build : Build.ArtifactContract a.parsed.ast.name description
  source_prefix : SourcePrefixContract a.parsed.ast.name adapter
  model_identifiers : ModelIdentifiersContract a.parsed.ast.name metadata
  /-- The complete rendered call graph obeys the checked no-heap policy (no
  callee is an allocation entry point; every callee is a defined function, a
  declared kernel entry or a named external) and its direct-call relation among
  defined functions is acyclic. This is a proved consequence of the mandatory
  adapter contract, carried as an explicit conjunct on the actual bytes. -/
  no_heap_acyclic : ∃ sigs : List CTree.Signature,
    Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
    CCallPolicy.NoHeap (LiteralPreparation.functions a.solve.prepareFMI3 sigs) CallPolicy.bUnit = true ∧
    CCallPolicy.Acyclic (LiteralPreparation.functions a.solve.prepareFMI3 sigs)
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
    identifiers,
    (by
      obtain ⟨sigs, printed, covered⟩ := adapter_covered adapterContract
      exact ⟨sigs, printed, CallPolicy.unit_no_heap _ sigs,
        CallPolicy.unit_acyclic _ sigs covered⟩),
    adapterContract, metadataDocument⟩

end Rumoca.FMI3
