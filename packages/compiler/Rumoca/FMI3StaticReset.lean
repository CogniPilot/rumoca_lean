import Rumoca.FMI3StaticInitialization
import Rumoca.FMI3ResetProofs
import RumocaFMI3.StaticReset

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Actual adapter text supplies reset's definition and all null/success
behaviors in the same static interface used by creation and initialization. -/
theorem adapter_static_reset (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        StaticReset.ExecutionContract program := by
  obtain ⟨signatures, unique, member, printed, _, _, _, _, _, poolReady, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  letI : CInterface := executionInterface objects (pool.addresses firstBlock)
  intro program actual
  apply StaticReset.execution_correct objects (pool.addresses firstBlock) a.solve.prepareFMI3 program
  rw [actual]
  exact LiteralPreparation.function_bound _ signatures unique _ member

/-- Reset selects the Solve default from arbitrary prior writable values,
then both actual initialization calls establish the corresponding source IVP.
Every intermediate heap is fixed explicitly; no successful target execution
or fresh allocation is supplied by the caller. Other live slots and leases
survive the sequence. General host histories and native ABI remain separate. -/
theorem adapter_static_reset_initialize (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (slot : Fin objects.capacity) (kind : Kind) (mode : Mode)
          (args : Initialization.Arguments),
        let p := objects.instances.index slot.val
        Reset.Storage heap p →
        load heap (p.member "kind") = some (.integer kind.code) →
        load heap (p.member "mode") = some (.integer mode.code) →
        Initialization.Arguments.Admissible args →
        let reset := Reset.finalHeap heap p
        let entered := InitializationEntry.finalHeap reset p args
        let exited := InitializationCalls.exitedHeap reset p args kind
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, reset⟩) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationCalls.signature.name
            (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) reset .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
        ResetSourceResult a p ⟨.integer 0, reset⟩ (Binary64.value args.start) ∧
        HistoryProofs.Stored exited p (Time.Clock.initial args.start) ∧
        load exited (p.member "mode") = some (.integer (nextMode .exitInitialization kind .initialization).code) ∧
        StateProofs.Represents exited p ⟨Binary64.positiveZero⟩ ∧
        InitializationCalls.SourceInitialized a.parsed.ast exited p args.start
          (Initialization.trajectory (Binary64.value args.start) (Binary64.value Binary64.positiveZero)) ∧
        (∀ trajectory, InitializationCalls.SourceInitialized a.parsed.ast exited p args.start trajectory →
          trajectory = Initialization.trajectory (Binary64.value args.start) (Binary64.value Binary64.positiveZero)) ∧
        load exited (p.member "slot") = load heap (p.member "slot") ∧
        (∀ (leases : SlotOwners.State objects.capacity), SlotOwners.Represents objects.flagsBlock heap leases →
          SlotOwners.Represents objects.flagsBlock exited leases) ∧
        (∀ (other : Fin objects.capacity) (query : Address), slot ≠ other →
          (objects.instances.index other.val).InRecord query → exited query = heap query) := by
  obtain ⟨signatures, unique, member, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface objects literals
  intro program actual heap slot kind mode args
  let p := objects.instances.index slot.val
  dsimp only
  intro storage hk hm admissible
  let reset := Reset.finalHeap heap p
  have quiet : InitializationCalls.QuietExecutionContract program := by
    apply StaticInitialization.quiet_correct objects literals a.solve.prepareFMI3 program
    · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  have kindLoaded := (StaticReset.kind_value heap p).trans hk
  have kept := InitializationBodies.exit_model (InitializationEntry.model (Reset.state heap p) args) kind
  refine ⟨StaticReset.call_behaviors objects literals a.solve.prepareFMI3 program heap p kind mode
    (by rw [actual]; exact LiteralPreparation.function_bound _ signatures unique _ member) storage hk hm,
    quiet.enter reset p args kind admissible (StaticReset.entry_storage heap p) kindLoaded,
    quiet.exit _ p kind ((InitializationCalls.entered_kind reset p args).trans kindLoaded)
      (InitializationCalls.entered_mode reset p args),
    reset_result a heap p (Binary64.value args.start),
    InitializationBodies.exit_history (InitializationCalls.stored reset p args) kind,
    InitializationBodies.exit_mode _ p kind, kept,
    InitializationCalls.exited_source_initialized a.solve.prepareFMI3 reset p args kind
      ⟨Binary64.positiveZero⟩ (Reset.state heap p),
    fun _ initialized => InitializationCalls.source_initialized_unique initialized kept,
    (StaticInitialization.exited_metadata reset p args kind).trans (StaticReset.metadata heap p),
    StaticReset.restarted_owners objects heap slot args kind, ?_⟩
  intro other query different inside
  exact StaticReset.restarted_other_instance heap objects.instances slot.val other.val args kind query
    (fun equal => different (Fin.ext equal)) inside

end Rumoca.FMI3
