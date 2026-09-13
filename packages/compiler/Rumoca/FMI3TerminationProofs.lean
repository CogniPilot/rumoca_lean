import Rumoca.FMI3AdapterProofs
import Rumoca.FMI3InitializationCalls
import RumocaFMI3.StaticInitialization

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- The independently read adapter contains this exact public function and
supplies its complete call cases in the same static object environment. -/
theorem adapter_termination (contract : AdapterContract a adapter) :
    ∃ signatures pool before after,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      adapter = before ++ (Runtime.function a.solve.prepareFMI3 Termination.signature).render ++ after ∧
      Termination.FunctionContract a.solve.prepareFMI3 signatures
        (Runtime.function a.solve.prepareFMI3 Termination.signature).render ∧
      Termination.PreparedContract a.solve.prepareFMI3 signatures pool := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, termination, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
    Termination.signature termination.member
  exact ⟨signatures, pool, before, after, made, printed, printed ▸ located,
    termination, termination.prepared pool made⟩

/-- Changing only lifecycle mode preserves the source IVP selected by finite
instance storage. This does not add a source termination equation. -/
theorem Termination.source_frame
    (initialized : InitializationCalls.SourceInitialized source heap p start trajectory) :
    InitializationCalls.SourceInitialized source (LifecycleBodies.writeMode heap p .terminated)
      p start trajectory := by
  obtain ⟨valid, state, loaded, initial⟩ := initialized
  exact ⟨valid, state, LifecycleBodies.write_model (state := ⟨state⟩) loaded .terminated, initial⟩

/-- Both initialization calls and termination execute through their actual
shared table. Intermediate heaps, source meaning and unchanged finite state
are derived; no successful target execution is assumed. This sequence covers
initialization followed by termination, not arbitrary intervening simulation. -/
theorem adapter_initialize_terminate (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (args : Initialization.Arguments)
          (kind : Kind) (state : ModelExchange.State),
        Initialization.Arguments.Admissible args → InitializationCalls.EntryStorage heap p →
        load heap (p.member "kind") = some (.integer kind.code) → StateProofs.Represents heap p state →
        let entered := InitializationEntry.finalHeap heap p args
        let exited := InitializationCalls.exitedHeap heap p args kind
        let final := LifecycleBodies.writeMode exited p .terminated
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationCalls.signature.name
            (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling Termination.signature.name [.pointer (some p)] exited .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, final⟩) ∧
        HistoryProofs.Stored final p (Time.Clock.initial args.start) ∧
        StateProofs.Represents final p state ∧
        load final (p.member "mode") = some (.integer Mode.terminated.code) ∧
        InitializationCalls.SourceInitialized a.parsed.ast final p args.start
          (Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) ∧
        (∀ trajectory, InitializationCalls.SourceInitialized a.parsed.ast final p args.start trajectory →
          trajectory = Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) ∧
        (∀ query, ¬ p.InRecord query → final query = heap query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, termination, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program actual heap p args kind state admissible storage hk represented
  let entered := InitializationEntry.finalHeap heap p args
  let exited := InitializationCalls.exitedHeap heap p args kind
  have quiet : InitializationCalls.QuietExecutionContract program := by
    apply StaticInitialization.quiet_correct objects literals a.solve.prepareFMI3 program
    · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  have terminate := (termination.prepared pool made).quiet E objects firstBlock program actual
  have kindEntered := (InitializationCalls.entered_kind heap p args).trans hk
  have kindExited : load exited (p.member "kind") = some (.integer kind.code) := by
    simpa only [exited, InitializationCalls.exitedHeap, load,
      InitializationBodies.exit_frame (InitializationEntry.finalHeap heap p args) p
        (p.member "kind") kind (by simp)] using kindEntered
  have modeExited : exited (p.member "mode") =
      some ⟨.int32, true, some (.integer (nextMode .exitInitialization kind .initialization).code)⟩ := by
    simp [exited, InitializationCalls.exitedHeap, InitializationBodies.exitHeap]
  have allowed : Reference.Allowed .terminate kind (nextMode .exitInitialization kind .initialization) := by
    cases kind <;> simp [Reference.Allowed, me_initialization, cs_initialization]
  have modelExited := InitializationBodies.exit_model (InitializationEntry.model represented args) kind
  have modelFinal := LifecycleBodies.write_model modelExited .terminated
  refine ⟨quiet.enter heap p args kind admissible storage hk,
    quiet.exit entered p kind kindEntered (InitializationCalls.entered_mode heap p args),
    terminate.successful exited p kind _ kindExited modeExited allowed,
    LifecycleBodies.write_history (InitializationBodies.exit_history (InitializationCalls.stored heap p args) kind) .terminated,
    modelFinal, LifecycleBodies.write_mode exited p .terminated,
    Termination.source_frame (InitializationCalls.exited_source_initialized a.solve.prepareFMI3 heap p args kind state represented),
    fun _ initialized => InitializationCalls.source_initialized_unique initialized modelFinal, ?_⟩
  intro query outside
  have different (name : String) : query ≠ p.member name := by
    intro same
    subst query
    exact outside (p.member_in_record name)
  rw [LifecycleBodies.write_frame _ p query .terminated (different "mode")]
  exact InitializationCalls.exited_frame heap p query args kind (different "time")
    (different "timeMin") (different "eventTime") (different "lastCompleted")
    (different "stop") (different "stopDefined") (different "mode")

end Rumoca.FMI3
