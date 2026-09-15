import RumocaFMI3.RuntimeLinkage
import Rumoca.FMI3PublicContracts
import RumocaFMI3.ReleaseConcurrentInvariant
import RumocaFMI3.ReleaseClaims
import RumocaC.Fenv

/-! Source-bound release address origin and current-lease atomic execution. -/
noncomputable section
namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCalls.Events RuntimeLinkage
open CCalls.Concurrent (BeforeReturn)
open StaticRelease.ConcurrentInvariant

/-- The actual source/adapter contract supplies the exact release definition,
public signature, pool and header bindings. Valid initial metadata and explicit
other-thread interference determine the release address throughout the public
invocation. A represented current lease then supplies the enabled atomic step.
No completed-call, argument-conversion or next-state annotation is a premise. -/
theorem source_release_bounds (compiled : compile input = .ok a)
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
          ∀ (before after : Concurrent.State) (tracked : Nat)
            (slot : Fin StaticStorage.deploymentCapacity) (savedHeap : Heap) (stack : Typed.Continuation),
            let p := objects.instances.index slot.val
            before.threads tracked = some (.calling StaticRelease.function.signature.name
              [.pointer (some p)] savedHeap stack) →
            load before.heap (p.member "slot") = some (.integer slot.val) →
            Transition.Reaches (fun a b => ∃ chosen events,
              Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen ∧
                EnvironmentFrame (some p) tracked a chosen b) before after →
            (∀ args heap later, after.threads tracked = some (.calling "atomic_store" args heap later) →
              args = [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value false]) ∧
            (∀ value heap, after.threads tracked = some (.returning value heap stack) → value = .void) ∧
            load after.heap (p.member "slot") = some (.integer slot.val) ∧
            (∀ args heap later, after.threads tracked = some (.calling "atomic_store" args heap later) →
              ∀ (owners : SlotOwners.State StaticStorage.deploymentCapacity) (lease : Nat),
                SlotOwners.Represents flags after.heap owners → owners slot = some lease →
                ∃ next : Concurrent.State,
                  (∀ effects target, Concurrent.Step program after tracked effects target ↔
                    effects = [tag (.write (AtomicSlots.address flags slot) false)] ∧ target = next) ∧
                  SlotOwners.release owners slot lease = some (SlotOwners.update owners slot none) ∧
                  SlotOwners.Represents flags next.heap (SlotOwners.update owners slot none) ∧
                  ScheduledStep program flags ⟨after, owners⟩
                    [⟨tracked, [tag (.write (AtomicSlots.address flags slot) false)], some (.release slot lease)⟩]
                    ⟨next, SlotOwners.update owners slot none⟩ ∧
                  next.threads tracked = some (Concurrent.control (.returning .void next.heap later)) ∧
                  (∀ other, other ≠ tracked → next.threads other = after.threads other)) := by
  obtain ⟨sigs, rendered, functions, prepared, covered, contracts⟩ := adapter_public_contracts contract.adapter
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
  have release : StaticRuntime.FunctionContract a.solve.prepareFMI3 sigs
      (StaticStorage.render StaticStorage.deploymentCapacity) := contracts .release
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact release.release_defined, rfl, rfl, rfl, rfl, rfl, rfl,
      statics "atomic_store" _ rfl⟩
  intro before after tracked slot savedHeap stack entry metadata path
  let p := objects.instances.index slot.val
  have initial : Metadata (some p) slot.val before.heap := by
    intro address same
    cases Option.some.inj same
    exact metadata
  obtain ⟨calls, returned, finalMetadata⟩ := call_prefix_origin program tag bindings rfl entry initial path
  have addresses : ∀ args heap later,
      after.threads tracked = some (.calling "atomic_store" args heap later) →
      args = [.pointer (some (AtomicSlots.address flags slot)), CAtomicBoolean.value false] := by
    intro args heap later calling
    simpa only [objects, StaticRuntime.objects, StaticFactory.Objects.flags, Address.index,
      Nat.zero_add, AtomicSlots.address] using (calls args heap later calling).2
  refine ⟨addresses, returned, finalMetadata p rfl, ?_⟩
  intro args heap later calling owners lease represented owned
  have converted := addresses args heap later calling
  subst args
  exact release_for_slot program tag rfl rfl (statics "atomic_store" _ rfl) calling represented owned

end Rumoca.FMI3.ConcurrentSlots
