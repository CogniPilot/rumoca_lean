import Rumoca.FMI3MEInitialization
import RumocaFMI3.MERelease

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Actual-adapter contracts compose the ME control history through release
with one definition table, object interface and original host lease. -/
theorem adapter_me_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        MEHistory.ReleaseContract objects program tag := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, runtime, termination, time, entries, completed, discrete, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program tag actual write
  have quiet : MEHistory.Quiet program :=
    ⟨(time.prepared pool made).quiet E objects firstBlock program actual,
      fun entry => ((entries entry).prepared pool made).quiet E objects firstBlock program actual,
      (completed.prepared pool made).quiet E objects firstBlock program actual,
      (discrete.prepared pool made).quiet E objects firstBlock program actual⟩
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  exact MEHistory.release_correct objects program tag quiet
    (Termination.terminate_release objects literals program tag
      ((termination.prepared pool made).quiet E objects firstBlock program actual) bindings)

end Rumoca.FMI3

namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- One actual adapter executes initialization, an arbitrary admitted ME
control history, termination and release. The original lease survives until
its proved discharge; the source IVP and all intermediate calls are retained.
This does not certify importer integration or validity after release. -/
theorem adapter_initialize_me_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (heap : Heap) (slot : Fin objects.capacity) (owners : SlotOwners.State objects.capacity)
          (owner : Nat) (args : Initialization.Arguments) (state : ModelExchange.State)
          (addresses : String → Address) (actions : List MEHistory.Action) (final : MEHistory.ReferenceState),
        let p := objects.instances.index slot.val
        args.Admissible → InitializationCalls.EntryStorage heap p →
        load heap (p.member "kind") = some (.integer 0) → StateProofs.Represents heap p state →
        MEHistory.Buffers heap addresses → MEHistory.Buffers.Outside p addresses →
        MEHistory.ReferenceTrace (MEHistory.ReferenceState.initial args.start args.stopTime) actions final →
        SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
        load heap (p.member "slot") = some (.integer slot.val) →
        let entered := InitializationEntry.finalHeap heap p args
        let exited := InitializationCalls.exitedHeap heap p args .me
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationCalls.signature.name
            (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
        ∃ after finalClock,
          MEHistory.Calls program p addresses exited actions after ∧
          MEHistory.Stored after p finalClock final state addresses ∧
          InitializationCalls.SourceInitialized a.parsed.ast after p args.start
            (Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast after p args.start candidate →
            candidate = Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) ∧
          let terminated := LifecycleBodies.writeMode after p .terminated
          let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
          SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
          SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
            behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
          (∀ query, MEHistory.Outside p addresses query → query ≠ p.member "stop" →
            query ≠ p.member "stopDefined" → query ≠ AtomicSlots.address objects.flagsBlock slot →
            released query = heap query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, runtime, termination, time, entries, completed, discrete, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program tag actual write heap slot owners owner args state addresses actions final
  let p := objects.instances.index slot.val
  dsimp only
  intro admissible storage kind model buffers outside admitted represented owned metadata
  have initQuiet : InitializationCalls.QuietExecutionContract program := by
    apply StaticInitialization.quiet_correct objects literals a.solve.prepareFMI3 program
    · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  have quiet : MEHistory.Quiet program :=
    ⟨(time.prepared pool made).quiet E objects firstBlock program actual,
      fun entry => ((entries entry).prepared pool made).quiet E objects firstBlock program actual,
      (completed.prepared pool made).quiet E objects firstBlock program actual,
      (discrete.prepared pool made).quiet E objects firstBlock program actual⟩
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := MEHistory.release_correct objects program tag quiet
    (Termination.terminate_release objects literals program tag
      ((termination.prepared pool made).quiet E objects firstBlock program actual) bindings)
  have ready := MEHistory.initialized_stored heap p args state addresses admissible kind model buffers outside
  obtain ⟨after, finalClock, called, storedAfter, terminated, discharged, ownersAfter, freed, framed⟩ :=
    finish (InitializationCalls.exitedHeap heap p args .me) slot owners owner (Time.Clock.initial args.start)
      (MEHistory.ReferenceState.initial args.start args.stopTime) final state addresses actions ready (Or.inl rfl)
      admitted (StaticInitialization.exited_owners objects heap slot args .me owners represented) owned
      ((StaticInitialization.exited_metadata heap p args .me).trans metadata)
  refine ⟨initQuiet.enter heap p args .me admissible storage kind,
    initQuiet.exit (InitializationEntry.finalHeap heap p args) p .me
      ((InitializationCalls.entered_kind heap p args).trans kind) (InitializationCalls.entered_mode heap p args),
    after, finalClock, called, storedAfter, ?_, ?_, terminated, discharged, ownersAfter, freed, ?_⟩
  · exact InitializationCalls.model_source_initialized a.parsed.ast after p args.start state
      a.solve.dae.flat.resolved storedAfter.modelStored
  · intro candidate initialized
    exact InitializationCalls.source_initialized_unique initialized storedAfter.modelStored
  · intro query separateFields stop stopDefined flag
    have decomposed := separateFields
    obtain ⟨time, mode, event, minimum, completed, _⟩ := decomposed
    exact (framed query separateFields flag).trans
      (InitializationCalls.exited_frame heap p query args .me time minimum event completed stop stopDefined mode)

end Rumoca.FMI3
