import Rumoca.FMI3MENumericalHistory
import Rumoca.FMI3StaticLifecycle
import Rumoca.FMI3InitializationSemantics
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.CSCreationStorage
import RumocaFMI3.TerminationEnvironment
import RumocaFMI3.MENumericalLifecycle

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CLiteral CStringMemory StaticFactory

/-- Actual creation supplies the handle, source default and lease before the
importer chooses an admitted initialized numerical history. The initial caller
buffers belong to the pre-creation heap. Every later storage/ownership premise,
status and raw query result is derived; release restores the original owners.
The selected source IVP is recorded at initialization, separately from trial
states subsequently supplied by the importer. -/
theorem runtime_create_me_numerical_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (E : Type) (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (before : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        Identity.Bindings program →
        program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
        program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (args : FactoryArguments.Raw) (heap : Heap),
        CReadOnly.Preserves (pool.install before firstBlock signed) heap →
        CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
        args.name = some name → args.token = some supplied →
        Contents heap name nameBytes → Contents heap supplied tokenBytes → nameBytes.length < 2^64 →
        Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
          (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners → (∃ slot, owners slot = none) →
        ∀ owner : Nat,
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner .me args.environment args.logger args.logging ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling (FactoryArguments.signature .me).name (FactoryArguments.arguments .me args) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          (∀ (initArgs : Initialization.Arguments) (addresses : String → Address) (buffer : Address)
            (actions : List MENumericalHistory.Action) (final : MENumericalHistory.ReferenceState),
            initArgs.Admissible → MENumericalHistory.CallerStorage heap objects.instances addresses buffer →
            MENumericalHistory.ReferenceTrace (MENumericalHistory.ReferenceState.initial initArgs initial) actions final →
            let entered := InitializationEntry.finalHeap live p initArgs
            let exited := InitializationCalls.exitedHeap live p initArgs .me
            let trajectory := Initialization.trajectory (Binary64.value initArgs.start) (Binary64.value initial)
            (∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling InitializationCalls.signature.name
                (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite initArgs)) live .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
            (∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
            InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start trajectory ∧
            (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p initArgs.start candidate →
              candidate = trajectory) ∧
            ∃ after finalClock,
              MENumericalHistory.Calls program p addresses buffer exited actions
                (MENumericalHistory.observations a.solve.prepareFMI3
                  (MENumericalHistory.ReferenceState.initial initArgs initial) actions) after ∧
              MENumericalHistory.Stored after p finalClock final addresses buffer ∧
              CReadOnly.Preserves heap after ∧
              (∀ observed actualAfter,
                MENumericalHistory.Executed program p addresses buffer exited actions observed actualAfter →
                observed = (MENumericalHistory.observations a.solve.prepareFMI3
                  (MENumericalHistory.ReferenceState.initial initArgs initial) actions).map
                    MENumericalHistory.Observation.ok ∧ actualAfter = after ∧
                MENumericalHistory.DerivativeObservations a.parsed.ast actions observed) ∧
              let terminated := LifecycleBodies.writeMode after p .terminated
              let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
              (∀ behavior, (CCalls.Events.machine program).Behaves
                (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
                behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
              SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
              SlotOwners.Represents objects.flagsBlock released owners ∧
              (∀ behavior, (CCalls.Events.machine program).Behaves
                (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
                behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
              (∀ q, ¬ p.InRecord q → (∀ name ∈ DiscreteCalls.names, q ≠ addresses name) →
                q ≠ buffer → q ≠ AtomicSlots.address objects.flagsBlock slot → released q = heap q)) := by
  obtain ⟨sigs, unique, _, printed, _, functions, _, _, _, ready, _, _, _, _, states, derivative,
    _, _, initialization, _, factories, runtime, termination, time, entries, completed, discrete, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have prepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
        unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made⟩
  refine ⟨compiled, build.numerical, DerivativeMetadata.artifact_derivatives _ _ build.metadata,
    sigs, pool, made, printed, functions, prepared, ?_⟩
  intro E header instances flags separate before firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity exchange write args heap literalFrame storage name supplied nameBytes tokenBytes
    nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨request⟩ := prepared_static_identity a sigs (factories.member .cs) made before firstBlock signed heap
    literalFrame .me args name supplied nameBytes tokenBytes (Or.inl rfl)
    nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ sigs⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    FactoryEnvironment.create_owned header objects literals program tag identity _ .me args heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ sigs unique .me (factories.member .me))
      (by rw [actual]; exact StaticRuntime.identity_bound _ sigs) storage reserveBindings
      owners represented available owner
  let p := objects.instances.index slot.val
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have terminateQuiet : Termination.QuietContract program := by
    apply TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ termination.member
  have finish := TerminationEnvironment.release_correct header objects literals program tag terminateQuiet releaseBindings
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a 0
  have state := created.initialized.state_cell initial loaded
  refine ⟨trace, slot, live, initial, work, reserved, created, agreement, creation, ?_⟩
  intro initArgs addresses buffer actions final admissible callers admitted
  have outputs := (callers.storage_preserved preserved).at_index slot.val
  obtain ⟨entered, exited, after, finalClock, called, finalStored, readonly,
    terminated, discharged, ownersAfter, freed, frame⟩ :=
    MENumericalHistory.initialize_release header objects literals a.solve.prepareFMI3 program tag
      enterDefined exitDefined (prepared.quiet header E objects firstBlock program actual) finish
      live slot (SlotOwners.update owners slot (some owner)) owner initArgs initial addresses buffer actions final
      admissible (StaticInitialization.entry_storage created.initialized) created.initialized.kindValue state outputs
      admitted created.represented created.owned created.metadata
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 live p initArgs .me ⟨initial⟩ loaded
  have initialModel := InitializationBodies.exit_model (InitializationEntry.model loaded initArgs) .me
  have restored := SlotOwners.release_reserved_restore reserved
  rw [restored] at discharged ownersAfter
  refine ⟨entered, exited, initialized,
    fun _ given => InitializationCalls.source_initialized_unique given initialModel,
    after, finalClock, called, finalStored,
    (CCalls.Events.termination_preserves ((creation _).mpr rfl)).trans readonly,
    ?_, terminated, discharged, ownersAfter, freed, ?_⟩
  · intro observed actualAfter executed
    obtain ⟨values, finalHeap⟩ := called.determines executed
    refine ⟨values, finalHeap, ?_⟩
    rw [values]
    exact MENumericalHistory.observations_source a.solve (MENumericalHistory.ReferenceState.initial initArgs initial) actions
  · intro q notRecord notOutputs notBuffer notFlag
    have field (name : String) : q ≠ p.member name := by
      intro same
      exact notRecord (same ▸ p.member_in_record name)
    have stateOutside : q ≠ StateProofs.stateAddress p := by
      intro same
      exact notRecord (same ▸ (p.member_in_record "model").member "x")
    have outside : MENumericalHistory.Outside p addresses buffer q :=
      ⟨⟨field "time", field "mode", field "eventTime", field "timeMin", field "lastCompleted", notOutputs⟩,
        stateOutside, notBuffer⟩
    exact (frame q outside (field "stop") (field "stopDefined") notFlag).trans
      (createdFrame q notRecord notFlag)

end Rumoca.FMI3
end
