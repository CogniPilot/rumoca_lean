import Rumoca.FMI3RetainedInitialization
import RumocaFMI3.ControlledInitialization

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls CCalls.Events RuntimeLinkage
open CCalls.Concurrent (BeforeReturn)
open StaticRelease.ConcurrentInvariant

/-- The actual source-bound program retains its existing release, resource
history and initialization guarantees, and also admits initialization derived
from computed current destinations. Full public-control admission and explicit
importer/callback effect boundaries remain separate obligations. -/
theorem source_controlled_initialization (compiled : compile input = .ok a)
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
            Resources.Publication.ControlledInitializationContract program policy a.solve.prepareFMI3.solve
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
    source_retained_initialization compiled contract
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
  obtain ⟨release, initialization, history⟩ := resources policy
  exact ⟨release, initialization,
    Resources.Publication.initialized_from_controls program policy a.solve.prepareFMI3.solve
      instances flags StaticStorage.deploymentCapacity, history⟩

end Rumoca.FMI3.InstanceAuthority
