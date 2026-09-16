import Rumoca.FMI3PublicContracts
import RumocaFMI3.FactoryHistory
import RumocaFMI3.ExchangeInitialization
import RumocaFMI3.HostInstanceStorage
import RumocaFMI3.PublicationProjection
import RumocaFMI3.ReservationRegistryRuntime
import RumocaC.InvocationReplay

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CCalls CCalls.Events RuntimeLinkage FactoryControl

/-- Authored static declarations establish each slot's initial storage;
the same actual generated program retains it throughout public histories.
The actual successful reservation therefore needs no reached writable-pool
premise. Foreign effects preserve storage descriptors, and private value
interference and legal lifetime authority remain separate obligations. -/
theorem source_static_factory_initializations (compiled : compile input = .ok a)
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
          (∀ args before result after, effect.execute args before result after → CStorage.Preserves before after) →
        ∃ program : Events.Program Invocation,
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs ∧
          (Logging.Capability.present logger environment hostName effect).Bound program ∧
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn → program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
            (memory : Concurrent.State → Nat → Heap → Prop),
            (∀ state thread heap, memory state thread heap → CStorage.Preserves state.heap heap) →
            let policy := Host.publicPolicy sigs domain memory
            FactoryControl.AdmitsFactories policy →
            ∀ initialHeap, StaticStorage.Fresh objects initialHeap → ∀ trace current,
              let heap := StaticStorage.initial objects initialHeap
              Host.History program policy ⟨heap, fun _ => none⟩ trace current →
              CReadOnly.Preserves initialHeap heap ∧
              ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                ∀ tracked args oldHeap later,
                  current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                  ∀ events after, Concurrent.Step program current tracked events after →
                    ∃ call kind raw, ledger.active tracked = some call ∧
                      call.name = (FactoryArguments.signature kind).name ∧
                      call.args = FactoryArguments.arguments kind raw ∧ call.serial < ledger.next ∧
                      (∃ tick ∈ ticks, Host.Recording.Started tracked call tick) ∧
                      Outcome program policy tag kind objects.instances objects.flags objects.capacity tracked
                        raw.environment raw.logger raw.logging current ledger call args events after := by
  obtain ⟨sigs, unique, _, rendered, _, functions, _, _, _, prepared, _, _, _,
    _, _, _, _, _, _, _, factories, _, _, _, _, _, _, _, _, _, _, _, _, covered⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp prepared
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect callbackStorage
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, library, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_⟩
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, _, _⟩ := Identity.constants_ready
    a.solve.prepareFMI3 sigs (FactoryArguments.signature .cs) (factories.member .cs) .cs rfl made
    (fun _ => none) firstBlock false
  intro domain memory memoryStorage admitted initialHeap freshStorage trace current path
  let heap := StaticStorage.initial objects initialHeap
  let policy := Host.publicPolicy sigs domain memory
  obtain ⟨ledger, ticks, erased, recorded, uniqueInvocations, origins⟩ :=
    logged_host_atomic header objects (pool.addresses firstBlock) a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect
      domain memory admitted heap trace current path
  have fresh := (Host.Recording.history_invariants recorded (Host.Recording.initial_aligned heap)
    Host.Recording.initial_fresh).2
  have storage := RuntimeStorage.logged_initial_slots a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
    observed range logger effect callbackStorage policy memoryStorage objects initialHeap path
  refine ⟨StaticStorage.initial_preserves freshStorage, ledger, ticks, erased, recorded, uniqueInvocations, ?_⟩
  intro tracked args oldHeap later calling events after step
  obtain ⟨call, kind, raw, types, active, name, arguments, issued, started, scan, _⟩ :=
    origins tracked args oldHeap later calling
  refine ⟨call, kind, raw, active, name, arguments, issued, started, ?_⟩
  exact exchange_initialization program policy tag a.solve.prepareFMI3.solve kind
    (FactoryValidation.locals kind raw true) types objects.instances objects.flags objects.capacity tracked
    raw.environment raw.logger raw.logging current ledger call
    (header_factory_scope header objects (pool.addresses firstBlock) kind raw) storage objects.bounded
    rfl rfl rfl rfl rfl rfl (library "atomic_exchange" _ rfl) fresh active scan calling step

end Rumoca.FMI3.StaticFactory.ClaimInitialization


namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CCalls CCalls.Events RuntimeLinkage FactoryControl

/-- One source-bound runtime and raw public history account for authored
static storage, computed physical reservations, observed publication origins,
and actual successful initialization. The same recorded invocation ledger
connects these facts; private-region interference and legal caller authority
remain explicit, separate obligations. -/
theorem source_creation_histories (compiled : compile input = .ok a)
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
          (∀ args before result after, effect.execute args before result after → CStorage.Preserves before after) →
          (∀ args before result after, effect.execute args before result after → CAtomicBoolean.Preserves before after) →
        ∃ program : Events.Program Invocation,
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs ∧
          (Logging.Capability.present logger environment hostName effect).Bound program ∧
          (∀ name fn, StaticRuntime.library tag rfl rfl rfl name = some fn → program.externals name = some fn) ∧
          program.externals "floor" = some (CMathCalls.floorExternal rfl) ∧
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl observed range) ∧
          ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
            (memory : Concurrent.State → Nat → Heap → Prop),
            (∀ state thread heap, memory state thread heap → CStorage.Preserves state.heap heap) →
            (∀ state thread heap, memory state thread heap → CAtomicBoolean.Preserves state.heap heap) →
            let policy := Host.publicPolicy sigs domain memory
            FactoryControl.AdmitsFactories policy →
            ∀ initialHeap, StaticStorage.Fresh objects initialHeap → ∀ trace current,
              let heap := StaticStorage.initial objects initialHeap
              Host.History program policy ⟨heap, fun _ => none⟩ trace current →
              CReadOnly.Preserves initialHeap heap ∧
              ∃ ledger ticks, ∃ publications : PublicationRegistry.State objects.capacity,
                Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                Transition.Events.Reaches (PublicationRegistry.Step program policy instances flags)
                  ⟨⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩, fun _ => none⟩ ticks
                  ⟨⟨current, ledger⟩, publications⟩ ∧
                SlotOwners.Represents flags current.heap (PublicationRegistry.reservations publications) ∧
                (∀ slot lease, PublicationRegistry.Published publications slot lease →
                  ∃ tick ∈ ticks, PublicationRegistry.Observed instances slot lease tick) ∧
                ∀ tracked args oldHeap later,
                  current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                  ∀ events after, Concurrent.Step program current tracked events after →
                    ∃ call kind raw, ledger.active tracked = some call ∧
                      call.name = (FactoryArguments.signature kind).name ∧
                      call.args = FactoryArguments.arguments kind raw ∧ call.serial < ledger.next ∧
                      (∃ tick ∈ ticks, Host.Recording.Started tracked call tick) ∧
                      Outcome program policy tag kind objects.instances objects.flags objects.capacity tracked
                        raw.environment raw.logger raw.logging current ledger call args events after := by
  obtain ⟨sigs, unique, _, rendered, _, functions, _, _, _, prepared, _, _, _,
    _, _, _, _, _, _, _, factories, _, _, _, _, _, _, _, _, _, _, _, _, covered⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp prepared
  refine ⟨compiled, contract.numerical, CapabilityMetadata.artifact _ _ contract.metadata,
    sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect callbackStorage callbackFlags
  let program := logged a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger effect
  obtain ⟨actual, callback, _, _, library, floor, rounding⟩ :=
    logged_contract a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl observed range logger environment effect
  refine ⟨program, actual, callback, library, floor, rounding, ?_⟩
  obtain ⟨expected, whitespace, expectedBound, whitespaceBound, _, _⟩ := Identity.constants_ready
    a.solve.prepareFMI3 sigs (FactoryArguments.signature .cs) (factories.member .cs) .cs rfl made
    (fun _ => none) firstBlock false
  intro domain memory memoryStorage memoryFlags admitted initialHeap freshStorage trace current path
  let heap := StaticStorage.initial objects initialHeap
  let policy := Host.publicPolicy sigs domain memory
  have heapEq : CAtomicBoolean.initial (StaticStorage.initialInstances objects initialHeap) flags objects.capacity = heap := by
    exact (CObject.initial_atomic (StaticStorage.initialInstances objects initialHeap) flags objects.capacity).symm
  obtain ⟨ledger, ticks, owners, erased, recorded, uniqueInvocations, registry, represented⟩ :=
    ReservationRegistry.logged_reservations header objects (pool.addresses firstBlock) flags rfl
      a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect callbackFlags
      domain memory memoryFlags admitted (StaticStorage.initialInstances objects initialHeap) trace current
      (by simpa only [heapEq] using path)
  rw [heapEq] at recorded registry
  obtain ⟨otherLedger, otherTicks, otherErased, otherRecorded, _, origins⟩ :=
    logged_host_atomic header objects (pool.addresses firstBlock) a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect
      domain memory admitted heap trace current path
  have same : otherLedger = ledger :=
    Host.Recording.history_same_ledger otherRecorded recorded (otherErased.trans erased.symm)
  subst otherLedger
  obtain ⟨publications, publicationHistory, projected⟩ :=
    PublicationRegistry.reservation_history_lift program policy instances flags registry (fun _ => none) rfl
  have observedPublications : ∀ slot lease, PublicationRegistry.Published publications slot lease →
      ∃ tick ∈ ticks, PublicationRegistry.Observed instances slot lease tick := by
    intro slot lease published
    rcases PublicationRegistry.history_publication_origin publicationHistory published with absent | observed
    · cases absent
    · exact observed
  have fresh := (Host.Recording.history_invariants recorded (Host.Recording.initial_aligned heap)
    Host.Recording.initial_fresh).2
  have storage := RuntimeStorage.logged_initial_slots a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
    observed range logger effect callbackStorage policy memoryStorage objects initialHeap path
  refine ⟨StaticStorage.initial_preserves freshStorage, ledger, ticks, publications, erased, recorded, uniqueInvocations,
    publicationHistory, by simpa only [projected] using represented, observedPublications, ?_⟩
  intro tracked args oldHeap later calling events after step
  obtain ⟨call, kind, raw, types, active, name, arguments, issued, _, scan, _⟩ :=
    origins tracked args oldHeap later calling
  have started : ∃ tick ∈ ticks, Host.Recording.Started tracked call tick := by
    rcases Host.Recording.history_origin recorded active with absent | found
    · contradiction
    · exact found
  refine ⟨call, kind, raw, active, name, arguments, issued, started, ?_⟩
  exact exchange_initialization program policy tag a.solve.prepareFMI3.solve kind
    (FactoryValidation.locals kind raw true) types objects.instances objects.flags objects.capacity tracked
    raw.environment raw.logger raw.logging current ledger call
    (header_factory_scope header objects (pool.addresses firstBlock) kind raw) storage objects.bounded
    rfl rfl rfl rfl rfl rfl (library "atomic_exchange" _ rfl) fresh active scan calling step

end Rumoca.FMI3.StaticFactory.ClaimInitialization
