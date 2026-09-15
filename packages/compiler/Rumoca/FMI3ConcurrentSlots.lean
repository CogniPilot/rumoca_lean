import Rumoca.FMI3RuntimeStorage
import RumocaFMI3.ConcurrentSlotHistories

/-! The actual source and adapter contract provides one runtime for the emitted 32-slot pool and annotated concurrent lease histories. -/
noncomputable section
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- The actual source/adapter contract supplies the shared atomic bindings
for the emitted 32-slot pool. Annotated histories preserve leases and project
to actual C steps; deriving annotations for every factory path and the native
atomic/ABI correspondence remain explicit obligations. -/
theorem source_slot_histories (compiled : compile input = .ok a)
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
          (∀ entry args before events target,
            Transition.Events.Reaches (Events.machine program).step
              (.calling entry args before .done) events target → CCallDepth.stateDepth target ≤ 3) ∧
          ∀ (before after : Configuration StaticStorage.deploymentCapacity) (ticks : List (Tick Invocation StaticStorage.deploymentCapacity)),
            SlotOwners.Represents flags before.runtime.heap before.owners →
            Transition.Events.Reaches (ScheduledStep program flags) before ticks after →
            SlotOwners.Represents flags after.runtime.heap after.owners ∧
            Transition.Events.Reaches OwnerStep before.owners (ownerTrace ticks) after.owners ∧
            Transition.Events.Reaches (runtimeStep program) before.runtime (runtimeTrace ticks) after.runtime ∧
            ∀ slot lease nextLease nextOwners, before.owners slot = some lease →
              Claim after.owners slot nextLease false nextOwners → Action.release slot lease ∈ ownerTrace ticks := by
  obtain ⟨compiled, numerical, capabilities, sigs, pool, prepared, rendered, printed, covered, environment⟩ :=
    RuntimeStorage.source_resource_environment compiled contract
  refine ⟨compiled, numerical, capabilities, sigs, pool, prepared, rendered, printed, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger hostEnvironment effect
  obtain ⟨program, actual, logging, library, floor, rounding, depth, _, _⟩ :=
    environment header instances flags separate firstBlock tag observed range logger hostEnvironment effect
  refine ⟨program, actual, logging, library, floor, rounding, depth, ?_⟩
  intro before after ticks represented path
  have exchangeBound := library "atomic_exchange" _ rfl
  have writeBound := library "atomic_store" _ rfl
  obtain ⟨memory, ownership, runtime⟩ := history_refines program tag rfl exchangeBound writeBound path represented
  exact ⟨memory, ownership, runtime,
    fun _ _ _ _ owned claimed => reclaim_requires_release ownership owned claimed⟩

end Rumoca.FMI3.ConcurrentSlots
