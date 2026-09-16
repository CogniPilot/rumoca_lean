import RumocaFMI3.AuthorizedReleaseHistories
import RumocaFMI3.RuntimeLinkage
import Rumoca.FMI3PublicContracts
import RumocaC.Fenv

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls CCalls.Events RuntimeLinkage
open CCalls.Concurrent (BeforeReturn)
open StaticRelease.ConcurrentInvariant

/-- The actual source, numerical C, adapter, metadata and prepared logged
program supply the exact release bindings for the public authority contract.
The original entry/history derive the captured operands. Current authority,
physical representation and prefix metadata interference are explicit legal
caller obligations; no native C11 or complete lifetime claim is made. -/
theorem source_authorized_release (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    CapabilityMetadata.ArtifactContract metadata ∧
    ∃ sigs, ∃ pool : CLiteral.Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      PublicAPI.Covered sigs ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags) (firstBlock : Nat),
        let objects := StaticRuntime.objects instances flags separate
        letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
        ∀ (tag : CAtomicBoolean.Calls.Event → Invocation)
          (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
          (logger : Address) (environment : Option Address)
          (effect : ReturningEffect (Logging.signature hostName)),
        ∃ program : Events.Program Invocation,
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs ∧
          (Logging.Capability.present logger environment hostName effect).Bound program ∧
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn → program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ policy : Host.Policy,
            ReleaseContract program policy tag instances flags StaticStorage.deploymentCapacity := by
  obtain ⟨sigs, rendered, functions, prepared, covered, contracts⟩ := adapter_public_contracts contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp prepared
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, statics, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, statics, floor, rounding, ?_⟩
  have release : StaticRuntime.FunctionContract a.solve.prepareFMI3 sigs
      (StaticStorage.render StaticStorage.deploymentCapacity) := contracts .release
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact release.release_defined, rfl, rfl, rfl, rfl, rfl, rfl,
      statics "atomic_store" _ rfl⟩
  intro policy initial before authority thread handle call entryHeap savedHeap args stack ticks
    fresh active original entered metadata path stillActive linked borrowed calling represented
  exact captured_authorized_clear program policy tag bindings initial before authority instances flags thread handle call
    rfl fresh active original entered metadata path stillActive linked borrowed calling represented

end Rumoca.FMI3.InstanceAuthority
