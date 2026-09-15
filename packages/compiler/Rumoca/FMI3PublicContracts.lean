import Rumoca.FMI3BuildProofs
import RumocaFMI3.CapabilityMetadata
import RumocaFMI3.PublicAPI

/-! The mandatory exact-header coverage witness and every named public
function contract are joined with the same compiled source and artifact.
This retains all per-family preconditions; it does not close independent
native/ABI or normative legal-history obligations. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral PublicAPI

/-- Every indexed contract follows from the actual mandatory adapter bundle.
No separate successful public-call premise is supplied. -/
theorem adapter_public_contracts (contract : AdapterContract a adapter) :
    ∃ sigs, Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (LiteralPreparation.prepare a.solve.prepareFMI3 sigs).isSome = true ∧
      PublicAPI.Covered sigs ∧
      ∀ api : PublicAPI.Entry, api.Contract a.solve.prepareFMI3 sigs := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, reset, counts, ready, version, _, _,
    nominals, states, derivatives, getter, setter, initialization, _, factories, storage,
    termination, time, entries, completed, discrete, step, logging, indicators, evaluation,
    absent, capabilities, covered⟩ := contract
  refine ⟨sigs, printed, grammar, ready, covered, ?_⟩
  intro api
  cases api with
  | version => exact version
  | debugLogging => exact logging
  | factory kind => exact ⟨factories, storage⟩
  | scheduled => exact capabilities.scheduled
  | release => exact storage
  | initialization enter => exact initialization
  | reset => exact reset
  | counts events => exact fun static => counts static events
  | nominals => exact nominals
  | states write => exact states
  | derivatives => exact derivatives
  | float64 write => cases write <;> assumption
  | terminate => exact termination
  | time => exact time
  | entry which => exact entries which
  | completed => exact completed
  | discrete => exact discrete
  | step => exact step
  | eventIndicators => exact indicators
  | evaluation => exact evaluation
  | absent ty write => exact absent ty write
  | capability sig member => exact capabilities.family sig member


/-- Coverage, each existing execution contract and every actual function
fragment belong to the same source, adapter table and constructed literal pool.
Every per-family precondition and native/standards boundary is retained. -/
theorem public_functions_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      PublicAPI.Covered sigs ∧
      ∀ sig ∈ sigs, ∃ api : PublicAPI.Entry, api.signature = sig ∧ api.Contract a.solve.prepareFMI3 sigs ∧
        ∃ before after, adapter = before ++ (Runtime.function a.solve.prepareFMI3 sig).render ++ after := by
  obtain ⟨sigs, printed, functions, ready, covered, contracts⟩ := adapter_public_contracts contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  exact ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, printed, functions, covered,
    PublicAPI.every_export a.solve.prepareFMI3 sigs covered contracts printed⟩

end Rumoca.FMI3
end
