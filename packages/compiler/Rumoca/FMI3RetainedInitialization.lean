import Rumoca.FMI3ResourceHistories
import RumocaFMI3.RetainedInitialization

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls CCalls.Events RuntimeLinkage
open CCalls.Concurrent (BeforeReturn)
open StaticRelease.ConcurrentInvariant

/-- The same checked source/artifact program carries the captured-release,
coupled resource-history and retained-initialization contracts. This connects
the actual initializer result to the prepared source IVP without assuming its
later reservation or initialized return. Private-value frames, starting typed
storage and complete public lifecycle admission remain explicit boundaries. -/
theorem source_retained_initialization (compiled : compile input = .ok a)
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
            ReleaseContract program policy tag instances flags StaticStorage.deploymentCapacity ∧
            Resources.Publication.InitializationContract program policy a.solve.prepareFMI3.solve
              instances flags StaticStorage.deploymentCapacity ∧
            ∀ (heap : Heap) (ticks : List (Host.Recording.Tick Invocation))
              (after : Resources.Publication.Configuration StaticStorage.deploymentCapacity),
              Transition.Events.Reaches (Resources.Publication.Step program policy instances flags)
                (Resources.Publication.initial StaticStorage.deploymentCapacity heap) ticks after →
              Resources.Publication.Invariant instances after ∧
              Transition.Events.Reaches (Resources.Step program policy instances flags)
                (Resources.initial StaticStorage.deploymentCapacity heap) ticks after.resources ∧
              Transition.Events.Reaches (PublicationRegistry.Step program policy instances flags)
                (Resources.Publication.initial StaticStorage.deploymentCapacity heap).published ticks after.published ∧
              ∀ handle, Owns after.resources.authority handle →
                ∃ tick ∈ ticks, PublicationRegistry.Observed instances handle.slot handle.lease tick := by
  obtain ⟨compiled, numerical, metadataContract, sigs, pool, prepared, rendered, functions, covered, implementation⟩ :=
    source_resource_histories compiled contract
  refine ⟨compiled, numerical, metadataContract, sigs, pool, prepared, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect
  obtain ⟨program, actual, callback, statics, floor, rounding, resources⟩ :=
    implementation header instances flags separate firstBlock tag observed range logger environment effect
  refine ⟨program, actual, callback, statics, floor, rounding, ?_⟩
  intro policy
  obtain ⟨release, history⟩ := resources policy
  refine ⟨release, ?_, history⟩
  intro ticks value following kind env types
  exact Resources.Publication.initialized_from_history program policy a.solve.prepareFMI3.solve kind env types instances flags

end Rumoca.FMI3.InstanceAuthority
