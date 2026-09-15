import Rumoca.FMI3BuildProofs
import RumocaFMI3.CountMetadata
import RumocaFMI3.MEEventIndicatorExecution

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- The same source, actual numerical C, XML count and printed public body
supply the shared-runtime contract. No caller-supplied future heap or selected
successful return is needed to obtain it. Lifetime composition remains a
separate theorem; native headers and machine execution remain a boundary. -/
theorem event_indicators_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        EventIndicatorCalls.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      EventIndicatorEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, query, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    EventIndicatorCalls.signature query.member
  exact ⟨compiled, contract.numerical, CountMetadata.artifact_counts _ _ contract.metadata,
    sigs, pool, made, printed, grammar, ⟨before, _, after, printed ▸ located, query⟩,
    query.runtime pool made⟩

end Rumoca.FMI3
end

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral StaticFactory CCalls.Events

/-- Source and actual C/XML certificates supply the complete ME query contract
on a current invariant. History induction must derive that invariant; this
theorem does not assume an expected return value or a successful callback. -/
theorem event_indicators_me_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        EventIndicatorCalls.FunctionContract a.solve.prepareFMI3 sigs text) ∧
      ∀ (header : CFenv.Header) (objects : Objects)
        (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation) (config : MEMixedRun.Configuration),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        ∀ heap p clock reference addresses buffer (request : EventIndicatorAccess.Request)
          (owners : SlotOwners.State objects.capacity),
          config.Valid program objects addresses buffer → config.Stored heap p →
          p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
          CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
          MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
          request.Allowed .me reference.control.mode →
          ∃ returns blocked, MEEventIndicatorCalls.Contract program objects owners config heap p
            addresses buffer clock reference request returns blocked := by
  obtain ⟨compiled, numerical, described, sigs, pool, made, printed, functions, located, prepared⟩ :=
    event_indicators_source compiled contract
  refine ⟨compiled, numerical, described, sigs, pool, made, printed, functions, located, ?_⟩
  intro header objects baseHeap firstBlock signed
  exact MEEventIndicatorCalls.execution header objects a.solve.prepareFMI3 sigs pool
    prepared baseHeap firstBlock signed

end Rumoca.FMI3
end
