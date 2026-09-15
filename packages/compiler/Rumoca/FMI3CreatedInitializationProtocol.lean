import Rumoca.FMI3InitializationProtocol
import Rumoca.FMI3StaticLifecycle
import RumocaFMI3.InitializationProtocolCreation
import RumocaFMI3.InitializationProtocolEnvironment
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.CSRunEnvironment
import RumocaFMI3.MEEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CLiteral CStringMemory StaticFactory CCalls.Events

variable {source : AST.Model} {model : Solve.FMI3Model source}
variable {readers : ReadBank}

structure CreatedSourceContract [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (slot : Fin objects.capacity) (owner : Nat)
    (original literals live : Heap) (buffers : Float64Buffers.Layout) (kind : Kind)
    (actions : List Action) (final : State) (readers : ReadBank) : Prop where
  initialized : SourceContract model program objects retained (SlotOwners.update owners slot (some owner))
    original literals live (objects.instances.index slot.val) buffers kind State.reset final actions readers
  completed : ∀ observed after checkpoints,
    Completed program (objects.instances.index slot.val) buffers live actions observed after checkpoints →
    CReadOnly.Preserves original after ∧
    (final.phase.Finished →
      LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner kind
        (final.phase.mode kind) ∧
      SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
      SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot (final.phase.mode kind)) owners ∧
      ∀ q, Float64Rejection.Protected objects retained q →
        Untouched (objects.instances.index slot.val) buffers actions q →
        q ≠ AtomicSlots.address objects.flagsBlock slot →
        LifecycleRelease.releasedHeap after objects slot (final.phase.mode kind) q = original q)

theorem after_creation [interface : CInterface] {program : Program Invocation}
    (objects : Objects) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (owners : SlotOwners.State objects.capacity) (slot : Fin objects.capacity) (owner : Nat)
    (created : Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
      slot owner kind factoryArgs.environment factoryArgs.logger factoryArgs.logging)
    (reserved : SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)))
    (represented : SlotOwners.Represents objects.flagsBlock original owners)
    (storage : CStorage.Preserves original live) (readonly : CReadOnly.Preserves original live)
    (literalFrame : CReadOnly.Preserves literals original)
    (creationFrame : ∀ q, ¬ (objects.instances.index slot.val).InRecord q →
      q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q)
    (logging : FactoryLogPolicy program objects retained factoryArgs)
    (contract : ExecutionContract model program objects retained (SlotOwners.update owners slot (some owner))
      original literals (objects.instances.index slot.val) buffers kind readers)
    (reference : ReferenceTrace kind State.reset actions final)
    (prepared : ∀ action ∈ actions, action.Prepared objects retained original (objects.instances.index slot.val) buffers readers)
    (finish : Termination.ReleaseContract objects program tag) (release : StaticRelease.Bindings program tag)
    (flags : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨objects.flagsBlock, [], 0⟩))) :
    CreatedSourceContract model program objects tag retained owners slot owner original literals live buffers kind actions final readers := by
  have readerFrame := contract.resources.readerInputs.creation_frame represented
    contract.resources.readerGuarded creationFrame
  have invariant := Invariant.created objects created storage (literalFrame.trans readonly) logging readerFrame
  refine ⟨source_contract contract reference prepared invariant, ?_⟩
  intro observed after checkpoints executed
  obtain ⟨_, _, _, kept, _, frame⟩ := executed.correct contract reference prepared invariant
  refine ⟨readonly.trans kept, ?_⟩
  intro finished
  have released := executed.release objects tag slot contract reference prepared invariant finished finish release flags
    created.owned created.metadata
  have discharged := released.discharged
  have restored := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged restored
  refine ⟨released, discharged, restored, ?_⟩
  intro q guarded untouched notFlag
  have notMode : q ≠ (objects.instances.index slot.val).member "mode" :=
    fun same => untouched.1 (same ▸ (objects.instances.index slot.val).member_in_record "mode")
  exact (released.frame q notMode notFlag).trans ((frame q guarded untouched).trans (creationFrame q untouched.1 notFlag))

/-- Actual creation supplies the protocol's initial handle, state and storage.
Every request buffer is justified from the pre-creation heap. One prepared
source/artifact environment supplies creation, protocol calls and release. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧ Float64SetMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs → Identity.Bindings program →
          program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
          program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (kind : Kind) (factoryArgs : FactoryArguments.Raw) (heap : Heap),
          CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
          CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
          (kind = .me ∨ FactoryEntry.unsupported factoryArgs = false) →
          factoryArgs.name = some name → factoryArgs.token = some supplied →
          Contents heap name nameBytes → Contents heap supplied tokenBytes → nameBytes.length < 2^64 →
          Identity.accepted nameBytes (content " \t\n\r\u000c\u000b") tokenBytes
            (token a.solve.prepareFMI3).toUTF8.data.toList = true →
        ∀ (owners : SlotOwners.State objects.capacity), SlotOwners.Represents objects.flagsBlock heap owners →
          (∃ slot, owners slot = none) → ∀ owner : Nat,
          ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity, ∃ live, ∃ initial : Binary64.Value,
            let p := objects.instances.index slot.val
            trace.length ≤ objects.capacity ∧
            SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
            Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner kind
              factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
            load live (StateProofs.stateAddress p) = some (.finite initial) ∧
            Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
            CStorage.Preserves heap live ∧
            (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = heap q) ∧
            (∀ behavior, (machine program).Behaves
              (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind factoryArgs) heap .done) behavior ↔
              behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
            ∀ (retained : Address → Prop) (buffers : Float64Buffers.Layout) (actions : List Action) (final : State)
              (readers : ReadBank),
              Resources objects retained heap p buffers readers → FactoryLogPolicy program objects retained factoryArgs →
              ReferenceTrace kind State.reset actions final →
              (∀ action ∈ actions, action.Prepared objects retained heap p buffers readers) →
              CreatedSourceContract a.solve.prepareFMI3 program objects tag retained owners slot owner heap
                (pool.install baseHeap firstBlock signed) live buffers kind actions final readers := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, queries, ready, _, _, _, nominals, states, derivative, getter, setter,
    initialization, _, factories, runtime, termination, time, entries, completed, discrete, step, logging, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have getPrepared := Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made
  have setPrepared := Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made
  have countPrepared : ∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool := by
    letI : StaticLiterals := ⟨fun _ => none⟩
    exact fun events => (queries inferInstance events).prepared pool made
  have nominalPrepared := nominals.runtime pool made
  have loggingPrepared := logging.prepared pool made
  have runPrepared : CSRunEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨⟨LiteralPreparation.function_bound _ sigs unique _ resetMember,
      by rw [← InitializationCalls.function_eq a.solve.prepareFMI3]; exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember,
      LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember,
      LiteralPreparation.function_bound _ sigs unique _ termination.member, runtime.release_defined⟩, step.prepared pool made⟩
  have mePrepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made⟩
  refine ⟨compiled, build.numerical, Float64Metadata.artifact_variables _ _ build.metadata,
    Float64SetMetadata.artifact_state _ _ build.metadata, CountMetadata.artifact_counts _ _ build.metadata,
    NominalMetadata.artifact_nominals _ _ build.metadata,
    DebugLogging.artifact_category _ _ build.metadata,
    derivative_value_source a.solve,
    sigs, pool, made, printed, functions, ⟨getPrepared, setPrepared, countPrepared, nominalPrepared, loggingPrepared, runPrepared, mePrepared⟩, ?_⟩
  intro header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity exchange write kind factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨request⟩ := prepared_static_identity a sigs (factories.member .cs) made baseHeap firstBlock signed heap
    literalFrame kind factoryArgs name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ sigs⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    FactoryEnvironment.create_owned header objects literals program tag identity _ kind factoryArgs heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
      (by rw [actual]; exact StaticRuntime.identity_bound _ sigs) storage reserveBindings owners represented available owner
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have terminateQuiet : Termination.QuietContract program := by
    apply TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ termination.member
  have finish := TerminationEnvironment.release_correct header objects literals program tag terminateQuiet releaseBindings
  obtain ⟨initial, loaded, agreement, _, _⟩ := created.source_default a 0
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, ?_⟩
  intro retained buffers actions final readers resources logging reference prepared
  exact after_creation objects tag owners slot owner created reserved represented preserved (termination_preserves ((creation _).mpr rfl))
    literalFrame createdFrame logging
    (execution_contract header objects a.solve.prepareFMI3 sigs pool getPrepared setPrepared countPrepared nominalPrepared loggingPrepared runPrepared.toPreparedContract
      baseHeap firstBlock signed program actual identity.compareBinding retained (SlotOwners.update owners slot (some owner)) heap _ buffers kind readers resources)
    reference prepared finish releaseBindings rfl

end Rumoca.FMI3.InitializationProtocol
end
