import Rumoca.FMI3PublicContracts
import RumocaFMI3.FactoryHistory
import RumocaFMI3.ScanReadyOutcome
import RumocaFMI3.ScanOnce

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCalls.Events RuntimeLinkage FactoryControl

/-- The actual source and emitted adapter supply the complete factory control
chain. A raw host history derives its original public arguments, prepared pool
and exact reservation continuation before the actual atomic claim. No separate
helper-entry interval or post-validation local environment is assumed.

The input ABI profile and current owner/flag representation remain explicit.
A successful exchange excludes later reservation by that same recorded
factory invocation, including after helper return and across thread reuse.
The successful atomic result is not yet concurrent initialization, handle
publication, or an unrestricted lifetime/ownership theorem. -/
theorem source_factory_claims (compiled : compile input = .ok a)
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
            AdmitsFactories policy →
            ∀ initialHeap trace current, Host.History program policy ⟨initialHeap, fun _ => none⟩ trace current →
              ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨initialHeap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                ∀ tracked args oldHeap later,
                  current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                  ∀ events after, Concurrent.Step program current tracked events after →
                    ∀ owners : SlotOwners.State StaticStorage.deploymentCapacity,
                      SlotOwners.Represents flags current.heap owners →
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
  intro tag observed range logger environment effect
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, library, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_⟩
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, _, _⟩ := Identity.constants_ready
    a.solve.prepareFMI3 sigs (FactoryArguments.signature .cs) (factories.member .cs) .cs rfl made
    (fun _ => none) firstBlock false
  intro domain memory admitted initialHeap trace current path
  let policy := Host.publicPolicy sigs domain memory
  obtain ⟨ledger, ticks, erased, recorded, unique, origins⟩ :=
    logged_host_atomic header objects (pool.addresses firstBlock) a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect
      domain memory admitted initialHeap trace current path
  refine ⟨ledger, ticks, erased, recorded, unique, ?_⟩
  intro tracked args oldHeap later calling events after actualStep owners represented
  obtain ⟨call, kind, raw, types, active, name, arguments, fresh, started, scan, _⟩ :=
    origins tracked args oldHeap later calling
  refine ⟨call, kind, raw, types, active, name, arguments, fresh, started,
    scan_ready_outcome program policy tag rfl rfl rfl (library "atomic_exchange" _ rfl)
      objects.bounded scan calling actualStep active represented, ?_⟩
  exact scan_once a.solve.prepareFMI3 sigs program rfl
    (fun _ outside => ReservationOrigin.logged_named_only a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
      observed range logger effect outside) policy tag rfl rfl rfl (library "atomic_exchange" _ rfl)
    objects.bounded scan calling actualStep active fresh

end Rumoca.FMI3.ConcurrentSlots
