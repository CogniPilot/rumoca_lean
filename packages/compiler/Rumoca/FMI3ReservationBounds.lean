import Rumoca.FMI3RuntimeStorage
import RumocaC.AtomicScanEntryInvariant
import RumocaFMI3.FactoryScanEntry
import RumocaFMI3.ReservationClaims

/-! Same-source factory argument binding and bounded reservation addresses for the emitted pool. -/
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCalls.Events RuntimeLinkage
open CAtomicScan.ConcurrentInvariant
open CCalls.Concurrent (BeforeReturn)

/-- The actual compiler/adapter contract constructs the exact helper binding,
concrete flag array and emitted capacity. Within any invocation of that helper,
every exchange remains in this pool under arbitrary shared-heap interleavings.
Represented shared flags then derive the unique next atomic operation and
its lease annotation. The invocation interval ends before the original caller resumes. -/
theorem source_reservation_bounds (compiled : compile input = .ok a)
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
          (∀ (kind : Kind) (args : FactoryArguments.Raw) (types : CLoops.Types) (heap : Heap) (stack : Typed.Continuation),
            Events.internalNext program
              (.body (.running (StaticFactory.code a.solve.prepareFMI3.solve kind)
                (FactoryValidation.locals kind args true) types heap) "fmi3Instance" stack) =
              some (.calling CAtomicScan.function.signature.name
                [.pointer (some objects.flags), .integer objects.capacity] heap
                (.caller (.declare "size_t" "slot")
                  (StaticFactory.guard :: StaticFactory.initializeInstance a.solve.prepareFMI3.solve kind)
                  (FactoryValidation.locals kind args true) types "fmi3Instance" stack))) ∧
          ∀ (before after : Concurrent.State) (tracked : Nat) (savedHeap : Heap) (stack : Typed.Continuation),
            before.threads tracked = some (.calling CAtomicScan.function.signature.name
              [.pointer (some objects.flags), .integer objects.capacity] savedHeap stack) →
            Transition.Reaches (fun a b => ∃ chosen events,
              Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after →
            (∀ args heap later, after.threads tracked = some (.calling "atomic_exchange" args heap later) →
              ∃ slot : Fin StaticStorage.deploymentCapacity,
                args = [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value true]) ∧
            (∀ value heap, after.threads tracked = some (.returning value heap stack) →
              ∃ k : Nat, k ≤ StaticStorage.deploymentCapacity ∧ value = .integer k) ∧
            (∀ args heap later,
              after.threads tracked = some (.calling "atomic_exchange" args heap later) →
              ∀ (owners : SlotOwners.State StaticStorage.deploymentCapacity),
                SlotOwners.Represents flags after.heap owners → ∀ lease : Nat,
                ∃ slot : Fin StaticStorage.deploymentCapacity, ∃ next : Concurrent.State,
                  let busy := (SlotOwners.occupied owners) slot
                  let ownersAfter := claimOwners owners slot lease
                  (∀ effects target, Concurrent.Step program after tracked effects target ↔
                    effects = [tag (.exchange (AtomicSlots.address flags slot) busy true)] ∧ target = next) ∧
                  Claim owners slot lease busy ownersAfter ∧
                  SlotOwners.Represents flags next.heap ownersAfter ∧
                  ScheduledStep program flags ⟨after, owners⟩
                    [⟨tracked, [tag (.exchange (AtomicSlots.address flags slot) busy true)], some (.claim slot lease busy)⟩]
                    ⟨next, ownersAfter⟩ ∧
                  next.threads tracked = some (Concurrent.control (.returning (CAtomicBoolean.value busy) next.heap later)) ∧
                  (∀ other, other ≠ tracked → next.threads other = after.threads other)) := by
  obtain ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, environment⟩ :=
    RuntimeStorage.source_resource_environment compiled contract
  refine ⟨compiled, numerical, metadata, sigs, pool, prepared, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger hostEnvironment effect
  obtain ⟨program, actual, callback, library, floor, rounding, _⟩ :=
    environment header instances flags separate firstBlock tag observed range logger hostEnvironment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_, ?_⟩
  · intro kind args types heap stack
    exact StaticFactory.header_reserve_entry header objects (pool.addresses firstBlock)
      program a.solve.prepareFMI3.solve kind args types heap stack
  · intro before after tracked savedHeap stack entry path
    have defined : program.internal.definitions CAtomicScan.function.signature.name = some (.tree CAtomicScan.function) := by
      rw [actual]
      exact StaticRuntime.reservation_bound a.solve.prepareFMI3 sigs
    obtain ⟨exchanges, returned⟩ := call_prefix_bounds program tag rfl rfl rfl rfl rfl
      (library "atomic_exchange" _ rfl) defined objects.bounded entry path
    have addresses : ∀ args heap later,
        after.threads tracked = some (.calling "atomic_exchange" args heap later) →
        ∃ slot : Fin StaticStorage.deploymentCapacity,
          args = [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value true] := by
      intro args heap later calling
      obtain ⟨k, bounded, values⟩ := exchanges args heap later calling
      refine ⟨⟨k, bounded⟩, ?_⟩
      simpa only [objects, StaticRuntime.objects, StaticFactory.Objects.flags, Address.index,
        Nat.zero_add, AtomicSlots.address] using values
    refine ⟨addresses, returned, ?_⟩
    intro args heap later calling owners represented lease
    exact bounded_reservation_claim program tag rfl rfl (library "atomic_exchange" _ rfl)
      addresses calling represented lease

end Rumoca.FMI3.ConcurrentSlots
