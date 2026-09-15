import Rumoca.FMI3ReservationOrigins
import RumocaFMI3.ScanClaimOutcome

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCalls.Events RuntimeLinkage ReservationOrigin
open CCalls.Concurrent (BeforeReturn)

/-- The actual source/adapter contract supplies the emitted pool, table,
header types and library. Raw host history computes the enclosing factory;
actual helper execution supplies the selected slot and the observed outcome.
This is an atomic-claim boundary, not concurrent handle publication. -/
theorem source_scan_claims (compiled : compile input = .ok a)
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
          ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
            (memory : Concurrent.State → Nat → Heap → Prop),
            let policy := Host.publicPolicy sigs domain memory
            ∀ initialHeap trace current, Host.History program policy ⟨initialHeap, fun _ => none⟩ trace current →
              ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨initialHeap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                ∀ (before : Concurrent.State) (tracked : Nat) (savedHeap : Heap) (stack : Typed.Continuation),
                  before.threads tracked = some (.calling CAtomicScan.function.signature.name
                    [.pointer (some objects.flags), .integer objects.capacity] savedHeap stack) →
                  Transition.Reaches (fun s t => ∃ chosen events,
                    Concurrent.Step program s chosen events t ∧ BeforeReturn tracked stack s chosen) before current →
                  ∀ args oldHeap later, current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                    ∀ events after, Concurrent.Step program current tracked events after →
                      ∀ owners : SlotOwners.State StaticStorage.deploymentCapacity,
                        SlotOwners.Represents flags current.heap owners →
                        ∃ call, ledger.active tracked = some call ∧ factory call.name ∧ call.serial < ledger.next ∧
                          (∃ tick ∈ ticks, Host.Recording.Started tracked call tick) ∧
                          ScanClaimOutcome program policy tag flags current ledger owners tracked call stack args events after := by
  obtain ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, environment⟩ :=
    source_reservation_origins compiled contract
  refine ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger hostEnvironment effect
  obtain ⟨program, actualProgram, callback, library, floor, rounding, histories⟩ :=
    environment header instances flags separate firstBlock tag observed range logger hostEnvironment effect
  refine ⟨program, actualProgram, callback, library, floor, rounding, ?_⟩
  intro domain memory initialHeap trace current path
  let policy := Host.publicPolicy sigs domain memory
  obtain ⟨ledger, ticks, erased, recorded, unique, origins⟩ := histories domain memory initialHeap trace current path
  refine ⟨ledger, ticks, erased, recorded, unique, ?_⟩
  intro before tracked savedHeap stack entry priorSteps args oldHeap later calling events after actual owners represented
  obtain ⟨call, active, isFactory, fresh, started⟩ :=
    origins tracked "atomic_exchange" args oldHeap later calling (by decide +kernel)
  have defined : program.internal.definitions CAtomicScan.function.signature.name = some (.tree CAtomicScan.function) := by
    rw [actualProgram]
    exact StaticRuntime.reservation_bound a.solve.prepareFMI3 sigs
  exact ⟨call, active, isFactory, fresh, started,
    scan_claim_outcome program policy tag rfl rfl rfl rfl rfl (library "atomic_exchange" _ rfl)
      defined objects.bounded entry priorSteps calling actual active represented⟩

end Rumoca.FMI3.ConcurrentSlots
