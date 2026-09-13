import Rumoca.FMI3StaticCreation
import Rumoca.Initialization

/-! Sequential actual-adapter creation and release, with source initialization
and reusable ownership on the same heap. Intervening public calls and native
concurrent histories still require their own composition. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- The numerical value established by creation agrees with the compiled
Solve plan and selects its unique completed source trajectory. The source
equation alone does not choose this fallback initial value. -/
theorem StaticFactory.Created.source_default (artifact : Artifact input)
    (created : Created heap base block owners slot owner kind environment logger logging) (t₀ : ℝ) :
    ∃ initial : Binary64.Value,
      load heap (StateProofs.stateAddress (base.index slot.val)) = some (.finite initial) ∧
      Binary64.value initial = (artifact.solve.initial.initial : ℝ) ∧
      Source.Initializes artifact.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value initial)) ∧
      ∀ candidate, Source.Initializes artifact.parsed.ast t₀ candidate →
        candidate t₀ = Binary64.value initial →
        candidate = Initialization.trajectory t₀ (Binary64.value initial) := by
  have zero : Binary64.value Binary64.positiveZero = 0 := by
    have units : Binary64.units Binary64.positiveZero = 0 := by decide +kernel
    simp only [Binary64.value, units, Int.cast_zero, zero_div]
  have agreement : Binary64.value Binary64.positiveZero = (artifact.solve.initial.initial : ℝ) := by
    rw [zero, artifact.solve.initial_default]
    exact Nat.cast_zero.symm
  refine ⟨Binary64.positiveZero, created.initialized.model, agreement, ?_, ?_⟩
  · rw [agreement]
    exact (artifact.solve.initialization_correct t₀).1
  · intro candidate source initial
    rw [agreement] at initial ⊢
    exact artifact.solve.initialized_solution_unique t₀ candidate source initial

/-- An available slot can be created and released through the actual public
functions, restoring the original owners and reusable storage. All initial
field values, including old instance values, may vary. The actual scan and
both complete C-call behaviors follow from readiness and availability. -/
theorem adapter_static_create_release (contract : AdapterContract a adapter) :
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
        (∃ slot, owners slot = none) → ∀ owner : Nat,
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin storage.capacity, ∃ live freed,
          trace.length ≤ storage.capacity ∧
          Created live storage.instances storage.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner kind args.environment args.logger args.logging ∧
          SlotOwners.Represents storage.flagsBlock freed owners ∧
          CreationStorage freed storage.instances storage.flags storage.capacity ∧
          CStorage.Preserves heap freed ∧
          (∀ t₀ : ℝ, ∃ initial : Binary64.Value,
            load live (StateProofs.stateAddress (storage.instances.index slot.val)) = some (.finite initial) ∧
            Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
            Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value initial)) ∧
            ∀ candidate, Source.Initializes a.parsed.ast t₀ candidate →
              candidate t₀ = Binary64.value initial →
              candidate = Initialization.trajectory t₀ (Binary64.value initial)) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some (storage.instances.index slot.val)), live⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling StaticRelease.function.signature.name [.pointer (some (storage.instances.index slot.val))] live .done) behavior ↔
            behavior = .terminates [tag (.write (AtomicSlots.address storage.flagsBlock slot) false)] ⟨.void, freed⟩) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady, _, _, _, _, _, _, _, _, _, _, factories, runtime, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E instances flags separate before firstBlock signed
  let storage := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange write kind args heap frame ready name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨request⟩ := prepared_static_identity a signatures (factories.member .cs) made before firstBlock signed heap frame
    kind args name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ signatures⟩
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  obtain ⟨trace, slot, live, freed, work, created, restored, reusable, preserved, creation, released⟩ :=
    public_create_release storage literals program tag identity _ kind args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ signatures unique kind (factories.member kind))
      (by rw [actual]; exact StaticRuntime.identity_bound _ signatures) ready reserveBindings releaseBindings
      owners represented available owner
  exact ⟨trace, slot, live, freed, work, created, restored, reusable, preserved,
    created.source_default a, creation, released⟩

/-- The actual public release ignores a null handle on every heap. No object
readiness, identity-library or atomic binding premise is needed. -/
theorem adapter_static_null_release (contract : AdapterContract a adapter) :
    ∃ signatures,
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags) (literals : CLiteralAddresses),
        letI : CInterface := executionInterface (StaticRuntime.objects instances flags separate) literals
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ heap behavior, (CCalls.Events.machine program).Behaves
          (.calling StaticRelease.function.signature.name [.pointer none] heap .done) behavior ↔
          behavior = .terminates [] ⟨.void, heap⟩ := by
  obtain ⟨signatures, printed, _, released⟩ := adapter_static_definitions contract
  refine ⟨signatures, printed, ?_⟩
  intro E instances flags separate literals
  letI : CInterface := executionInterface (StaticRuntime.objects instances flags separate) literals
  intro program actual heap behavior
  exact StaticRelease.null_behaviors program heap (by rw [actual]; exact released) rfl rfl rfl behavior

end Rumoca.FMI3
