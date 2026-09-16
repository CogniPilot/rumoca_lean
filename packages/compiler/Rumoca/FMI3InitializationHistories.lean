import Rumoca.FMI3PublicContracts
import RumocaFMI3.FactoryHistory
import RumocaFMI3.ExchangeInitialization

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CCalls CCalls.Events RuntimeLinkage FactoryControl

/-- Source-bound public histories derive the real factory caller and actual
exchange. Under typed instance storage and the explicit private-record frame,
successful creation initializes and returns that slot in the same generated
C program. Legal live-handle authority and native correspondence remain open. -/
theorem source_factory_initializations (compiled : compile input = .ok a)
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
            FactoryControl.AdmitsFactories policy →
            ∀ initialHeap trace current,
              Host.History program policy ⟨initialHeap, fun _ => none⟩ trace current →
              ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨initialHeap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                ∀ tracked args oldHeap later,
                  current.threads tracked = some (.calling "atomic_exchange" args oldHeap later) →
                  ∀ events after, Concurrent.Step program current tracked events after →
                    (∀ slot : Fin objects.capacity, InstanceSlot.Storage current.heap (objects.instances.index slot.val)) →
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
  obtain ⟨ledger, ticks, erased, recorded, uniqueInvocations, origins⟩ :=
    logged_host_atomic header objects (pool.addresses firstBlock) a.solve.prepareFMI3 sigs covered
      (fun kind => StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      expected whitespace expectedBound whitespaceBound tag observed range logger effect
      domain memory admitted initialHeap trace current path
  have fresh := (Host.Recording.history_invariants recorded (Host.Recording.initial_aligned initialHeap)
    Host.Recording.initial_fresh).2
  refine ⟨ledger, ticks, erased, recorded, uniqueInvocations, ?_⟩
  intro tracked args oldHeap later calling events after step storage
  obtain ⟨call, kind, raw, types, active, name, arguments, issued, started, scan, _⟩ :=
    origins tracked args oldHeap later calling
  refine ⟨call, kind, raw, active, name, arguments, issued, started, ?_⟩
  exact exchange_initialization program policy tag a.solve.prepareFMI3.solve kind
    (FactoryValidation.locals kind raw true) types objects.instances objects.flags objects.capacity tracked
    raw.environment raw.logger raw.logging current ledger call
    (header_factory_scope header objects (pool.addresses firstBlock) kind raw) storage objects.bounded
    rfl rfl rfl rfl rfl rfl (library "atomic_exchange" _ rfl) fresh active scan calling step

end Rumoca.FMI3.StaticFactory.ClaimInitialization
