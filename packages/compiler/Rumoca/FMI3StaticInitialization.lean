import Rumoca.FMI3StaticLifecycle
import Rumoca.FMI3InitializationCalls
import RumocaFMI3.StaticInitialization

/-! Compose creation and initialization in one actual object-aware program.
Source tokens, public definitions, writable storage, the initial finite value
and post-initialization ownership are derived from the same artifact/heap. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- The actual adapter supplies complete successful and null initialization
calls in the same execution interface used by static creation and release. -/
theorem adapter_static_initialization (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags) (firstBlock : Nat),
        letI : CInterface := executionInterface (StaticRuntime.objects instances flags separate) (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        InitializationCalls.QuietExecutionContract program := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, initialization, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate firstBlock
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  intro program actual
  apply StaticInitialization.quiet_correct storage literals a.solve.prepareFMI3 program
  · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  · rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember

/-- Creation followed by both initialization calls selects the source IVP
from the finite value actually stored by the Solve initializer. The created
object supplies all later storage/mode premises, and its lease survives.
This is a sequential prefix; arbitrary host histories and invalid subsequent
calls are separate obligations. -/
theorem adapter_static_create_initialize (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let storage := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := executionInterface storage literals
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap storage.instances storage.flags storage.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        (kind = .me ∨ FactoryEntry.unsupported args = false) →
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes →
        nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State storage.capacity),
        SlotOwners.Represents storage.flagsBlock heap owners →
        (∃ slot, owners slot = none) →
        ∀ (owner : Nat) (initArgs : Initialization.Arguments),
        Initialization.Arguments.Admissible initArgs →
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin storage.capacity,
        ∃ live initialized exited, ∃ (initial : Binary64.Value), ∃ trajectory,
          initialized = InitializationEntry.finalHeap live (storage.instances.index slot.val) initArgs ∧
          exited = InitializationCalls.exitedHeap live (storage.instances.index slot.val) initArgs kind ∧
          trace.length ≤ storage.capacity ∧
          Created live storage.instances storage.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner kind args.environment args.logger args.logging ∧
          SlotOwners.Represents storage.flagsBlock exited (SlotOwners.update owners slot (some owner)) ∧
          load exited ((storage.instances.index slot.val).member "slot") = some (.integer slot.val) ∧
          HistoryProofs.Stored exited (storage.instances.index slot.val) (Time.Clock.initial initArgs.start) ∧
          load exited ((storage.instances.index slot.val).member "mode") =
            some (.integer (nextMode .exitInitialization kind .initialization).code) ∧
          load exited (StateProofs.stateAddress (storage.instances.index slot.val)) = some (.finite initial) ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          InitializationCalls.SourceInitialized a.parsed.ast exited (storage.instances.index slot.val) initArgs.start trajectory ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited
            (storage.instances.index slot.val) initArgs.start candidate → candidate = trajectory) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some (storage.instances.index slot.val)), live⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationCalls.signature.name
              (InitializationCalls.arguments (some (storage.instances.index slot.val))
                (InitializationCalls.Raw.ofFinite initArgs)) live .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, initialized⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationExit.signature.name
              (InitializationExit.arguments (some (storage.instances.index slot.val))) initialized .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, exited⟩) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, initialization, _, factories, runtime, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange write kind args heap frame ready name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner initArgs admissible
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap frame
    kind args name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  obtain ⟨trace, slot, live, _, work, created, _, _, _, creation, _⟩ :=
    public_create_release storage literals program tag identity _ kind args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind))
      (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready reserveBindings releaseBindings
      owners represented available owner
  have quiet : InitializationCalls.QuietExecutionContract program := by
    apply StaticInitialization.quiet_correct storage literals a.solve.prepareFMI3 program
    · rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
    · rw [actual]
      exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  let p := storage.instances.index slot.val
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a (Binary64.value initArgs.start)
  have kept := InitializationBodies.exit_model (InitializationEntry.model (state := ⟨initial⟩) loaded initArgs) kind
  refine ⟨trace, slot, live, InitializationEntry.finalHeap live p initArgs,
    InitializationCalls.exitedHeap live p initArgs kind, initial,
    Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial),
    rfl, rfl, work, created, StaticInitialization.exited_owners storage live slot initArgs kind _ created.represented,
    (StaticInitialization.exited_metadata live p initArgs kind).trans created.metadata,
    InitializationBodies.exit_history (InitializationCalls.stored live p initArgs) kind,
    InitializationBodies.exit_mode (InitializationEntry.finalHeap live p initArgs) p kind,
    kept, agreement, ?_, ?_, creation,
    quiet.enter live p initArgs kind admissible (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue,
    quiet.exit _ p kind ((InitializationCalls.entered_kind live p initArgs).trans created.initialized.kindValue)
      (InitializationCalls.entered_mode live p initArgs)⟩
  · exact InitializationCalls.exited_source_initialized a.solve.prepareFMI3 live p initArgs kind ⟨initial⟩ loaded
  · intro candidate candidateSource
    exact InitializationCalls.source_initialized_unique candidateSource kept

end Rumoca.FMI3
