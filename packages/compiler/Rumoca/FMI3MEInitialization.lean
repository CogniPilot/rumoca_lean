import Rumoca.FMI3MEHistory
import Rumoca.FMI3InitializationCalls
import RumocaFMI3.MEInitialization
import RumocaFMI3.StaticInitialization

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Both public initialization calls and the subsequent ME control history
execute the actual adapter. Initialization supplies the event protocol state;
the resulting source IVP, all outputs and intermediate heaps are derived. -/
theorem adapter_initialize_me_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (args : Initialization.Arguments)
          (state : ModelExchange.State) (addresses : String → Address)
          (actions : List MEHistory.Action) (final : MEHistory.ReferenceState),
        args.Admissible → InitializationCalls.EntryStorage heap p →
        load heap (p.member "kind") = some (.integer 0) → StateProofs.Represents heap p state →
        MEHistory.Buffers heap addresses → MEHistory.Buffers.Outside p addresses →
        MEHistory.ReferenceTrace (MEHistory.ReferenceState.initial args.start args.stopTime) actions final →
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
          (∀ query, MEHistory.Outside p addresses query → after query = exited query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, time, entries, completed, discrete, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program actual heap p args state addresses actions final admissible storage kind model buffers outside admitted
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
  obtain ⟨entered, exited, after, finalClock, called, stored, framed⟩ :=
    MEHistory.initialize_trace program initQuiet quiet heap p args state addresses admissible storage
      kind model buffers outside admitted
  exact ⟨entered, exited, after, finalClock, called, stored,
    MEHistory.source_frame
      (InitializationCalls.exited_source_initialized a.solve.prepareFMI3 heap p args .me state model) outside framed,
    fun _ initialized => InitializationCalls.source_initialized_unique initialized stored.modelStored,
    framed⟩

end Rumoca.FMI3
