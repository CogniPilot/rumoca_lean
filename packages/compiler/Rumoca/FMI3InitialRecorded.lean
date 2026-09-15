import Rumoca.FMI3PublicContracts
import RumocaFMI3.InitialRecordedExecution

namespace Rumoca.FMI3.StaticRuntime
open CTree CLiteral

/-- The actual source/adapter certificate supplies initial storage and complete
public C call contracts for recorded creation and release. The initial factory
lease is its fresh invocation serial, and its observed pointer is the exact
handle consumed by the later release. Full concurrent lifecycle and native
correspondence obligations are not removed by this sequential witness. -/
theorem source_recorded_creation (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      PublicAPI.Covered sigs ∧ InitialRecordedExecution a.solve.prepareFMI3 sigs := by
  obtain ⟨sigs, printed, functions, ready, covered, contracts⟩ := adapter_public_contracts contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have storage : FunctionContract a.solve.prepareFMI3 sigs (StaticStorage.render StaticStorage.deploymentCapacity) :=
    contracts .release
  exact ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, printed, functions, covered, initial_recorded storage.execution⟩

end Rumoca.FMI3.StaticRuntime
