import Rumoca.FMI3ReservationHistories
import RumocaFMI3.PublicationProjection

namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CCalls CCalls.Events RuntimeLinkage

/-- The actual source-bound runtime has a computed publication history that
projects to its proved physical reservation history. Every current published
lease has an observed return by its original factory in that same history.
This does not infer caller authority from a pointer or a publication bit. -/
theorem source_publication_histories (compiled : compile input = .ok a)
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
              ∃ ledger ticks, ∃ publications : State StaticStorage.deploymentCapacity,
                Host.Recording.erase ticks = trace ∧
                Transition.Events.Reaches (Host.Recording.Step program policy)
                  ⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩ ticks ⟨current, ledger⟩ ∧
                (Host.Recording.issued ticks).Nodup ∧
                Transition.Events.Reaches (Step program policy instances flags)
                  ⟨⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩, fun _ => none⟩ ticks
                  ⟨⟨current, ledger⟩, publications⟩ ∧
                SlotOwners.Represents flags current.heap (reservations publications) ∧
                (∀ slot lease, Published publications slot lease →
                  ∃ tick ∈ ticks, Observed instances slot lease tick) := by
  obtain ⟨compiled, numerical, metadata, sigs, pool, made, rendered, functions, covered, runtime⟩ :=
    ReservationRegistry.source_reservation_histories compiled contract
  refine ⟨compiled, numerical, metadata, sigs, pool, made, rendered, functions, covered, ?_⟩
  intro header instances flags separate firstBlock
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := header.interface (StaticFactory.executionInterface objects (pool.addresses firstBlock))
  dsimp only
  intro tag observed range logger environment effect callbackFrame
  obtain ⟨program, internal, callback, library, floor, rounding, histories⟩ :=
    runtime header instances flags separate firstBlock tag observed range logger environment effect callbackFrame
  refine ⟨program, internal, callback, library, floor, rounding, ?_⟩
  intro domain memory hostFrame admitted initialHeap trace current path
  obtain ⟨ledger, ticks, owners, erased, recorded, issued, registry, represented, _⟩ :=
    histories domain memory hostFrame admitted initialHeap trace current path
  obtain ⟨publications, publicationHistory, projected⟩ :=
    reservation_history_lift program _ instances flags registry (fun _ => none) rfl
  refine ⟨ledger, ticks, publications, erased, recorded, issued, publicationHistory,
    by simpa only [projected] using represented, ?_⟩
  intro slot lease published
  rcases history_publication_origin publicationHistory published with absent | observed
  · cases absent
  · exact observed

end Rumoca.FMI3.PublicationRegistry
