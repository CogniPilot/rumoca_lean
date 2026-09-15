import Rumoca.FMI3PublicContracts
import RumocaFMI3.ReservationOriginRuntime
import RumocaC.Fenv

namespace Rumoca.FMI3.ReservationOrigin
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage

/-- The same actual source, adapter, public header and linked program
supply the computed invocation record for each reservation call. No later
enclosing-factory or lease annotation is a premise. This establishes origin
and fresh identity; publishing a concurrently created live handle and proving
its later release authority remain separate obligations. -/
theorem source_reservation_origins (compiled : compile input = .ok a)
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
            ∀ heap trace after,
            Host.History program (Host.publicPolicy sigs domain memory) ⟨heap, fun _ => none⟩ trace after →
            ∃ ledger ticks, Host.Recording.erase ticks = trace ∧
              Transition.Events.Reaches (Host.Recording.Step program (Host.publicPolicy sigs domain memory))
                ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨after, ledger⟩ ∧
              (Host.Recording.issued ticks).Nodup ∧
              ∀ thread name args savedHeap stack, after.threads thread = some (.calling name args savedHeap stack) →
                allowed name = false → ∃ call, ledger.active thread = some call ∧ factory call.name ∧
                  call.serial < ledger.next ∧ ∃ tick ∈ ticks, Host.Recording.Started thread call tick := by
  obtain ⟨sigs, rendered, functions, prepared, covered, _⟩ := adapter_public_contracts contract.adapter
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
  intro domain memory heap trace after path
  exact logged_host_origins a.solve.prepareFMI3 sigs covered tag rfl rfl rfl rfl
    observed range logger effect domain memory heap trace after path

end Rumoca.FMI3.ReservationOrigin
