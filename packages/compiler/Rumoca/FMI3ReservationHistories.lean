import Rumoca.FMI3PublicContracts
import RumocaFMI3.ReservationRegistryRuntime
import RumocaC.InvocationReplay
import RumocaFMI3.ScanReadyOutcome
import RumocaFMI3.ScanOnce

namespace Rumoca.FMI3.ReservationRegistry
open CTree CMemory CCalls CCalls.Events RuntimeLinkage ConcurrentSlots FactoryControl

/-- The source-bound adapter, prepared literal pool and actual C library yield
a computed reservation history from initially free static flags. The final
representation is derived, not an assumption about the current heap.
The same history supplies each actual factory claim and excludes further
reservation by that invocation. Live-instance publication and authority for
clearing a flag are separate. -/
theorem source_reservation_histories (compiled : compile input = .ok a)
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
          (∀ args before result after, effect.execute args before result after → CAtomicBoolean.Preserves before after) →
        ∃ program : Events.Program Invocation,
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs ∧
          (Logging.Capability.present logger environment hostName effect).Bound program ∧
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn → program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
            (memory : Concurrent.State → Nat → Heap → Prop),
            (∀ state thread heap, memory state thread heap → CAtomicBoolean.Preserves state.heap heap) →
            let policy := Host.publicPolicy sigs domain memory
            FactoryControl.AdmitsFactories policy →
            ∀ initialHeap trace current,
              let heap := CAtomicBoolean.initial initialHeap flags StaticStorage.deploymentCapacity
              Host.History program policy ⟨heap, fun _ => none⟩ trace current →
              ∃ ledger ticks, ∃ owners : SlotOwners.State StaticStorage.deploymentCapacity,
                Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                Transition.Events.Reaches (Step program policy flags)
                  ⟨⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩, fun _ => none⟩ ticks
                  ⟨⟨current, ledger⟩, owners⟩ ∧
                SlotOwners.Represents flags current.heap owners ∧
                ∀ tracked args oldHeap later,
                  current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                  ∀ events after, Concurrent.Step program current tracked events after →
                    ∃ call kind raw types, ledger.active tracked = some call ∧
                      call.name = (FactoryArguments.signature kind).name ∧
                      call.args = FactoryArguments.arguments kind raw ∧ call.serial < ledger.next ∧
                      (∃ tick ∈ ticks, Host.Recording.Started tracked call tick) ∧
                      ScanClaimOutcome program policy tag flags current ledger owners tracked call
                        (scanCaller a.solve.prepareFMI3 kind raw types) args events after ∧
                      ∃ k : Nat, ∃ busy : Bool, ∃ nextHeap : Heap,
                        k < objects.capacity ∧
                        args = [.pointer (some (objects.flags.index k)), CAtomicBoolean.value true] ∧
                        CAtomicBoolean.exchange current.heap (objects.flags.index k) true = some (busy, nextHeap) ∧
                        events = [tag (.exchange (objects.flags.index k) busy true)] ∧ after.heap = nextHeap ∧
                        (busy = false → ∀ future finish,
                          Transition.Events.Reaches (Host.Recording.Step program policy) ⟨after, ledger⟩ future finish →
                          ∀ laterCall name values heap stack,
                            finish.ledger.active tracked = some laterCall → laterCall.serial = call.serial →
                            finish.runtime.threads tracked = some (.calling name values heap stack) →
                            ReservationOrigin.allowed name = true) := by
  obtain ⟨sigs, unique, _, rendered, _, functions, _, _, _, prepared, _, _, _,
    _, _, _, _, _, _, _, factories, _, _, _, _, _, _, _, _, _, _, _, _, covered⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp prepared
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect callbackFrame
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, library, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_⟩
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, _, _⟩ := Identity.constants_ready
    a.solve.prepareFMI3 sigs (FactoryArguments.signature .cs) (factories.member .cs) .cs rfl made
    (fun _ => none) firstBlock false
  intro domain memory hostFrame admitted initialHeap trace current path
  let heap := CAtomicBoolean.initial initialHeap flags StaticStorage.deploymentCapacity
  let policy := Host.publicPolicy sigs domain memory
  obtain ⟨ledger, ticks, owners, erased, recorded, issued, registry, represented⟩ :=
    logged_reservations header objects (pool.addresses firstBlock) flags rfl a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect callbackFrame
      domain memory hostFrame admitted initialHeap trace current path
  obtain ⟨otherLedger, otherTicks, otherErased, otherRecorded, _, origins⟩ :=
    logged_host_atomic header objects (pool.addresses firstBlock) a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect
      domain memory admitted heap trace current path
  have same : otherLedger = ledger :=
    Host.Recording.history_same_ledger otherRecorded recorded (otherErased.trans erased.symm)
  subst otherLedger
  refine ⟨ledger, ticks, owners, erased, recorded, issued, registry, represented, ?_⟩
  intro tracked args oldHeap later calling events after actualStep
  obtain ⟨call, kind, raw, types, active, name, arguments, fresh, _, scan, _⟩ :=
    origins tracked args oldHeap later calling
  have started : ∃ tick ∈ ticks, Host.Recording.Started tracked call tick := by
    rcases Host.Recording.history_origin recorded active with absent | started
    · contradiction
    · exact started
  refine ⟨call, kind, raw, types, active, name, arguments, fresh, started,
    scan_ready_outcome program policy tag rfl rfl rfl (library "atomic_exchange" _ rfl)
      objects.bounded scan calling actualStep active represented, ?_⟩
  exact scan_once a.solve.prepareFMI3 sigs program rfl
    (fun _ outside => ReservationOrigin.logged_named_only a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
      observed range logger effect outside) policy tag rfl rfl rfl (library "atomic_exchange" _ rfl)
    objects.bounded scan calling actualStep active fresh

end Rumoca.FMI3.ReservationRegistry
