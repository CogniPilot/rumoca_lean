import Rumoca.FMI3InitializationAccess
import Rumoca.FMI3StaticLifecycle
import RumocaFMI3.FactoryEnvironment
import RumocaFMI3.InitializationAccessStorage
import RumocaFMI3.CSRunEnvironment
import RumocaFMI3.MEEnvironment
import RumocaFMI3.CountEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationAccess
open CTree CMemory CLiteral CStringMemory StaticFactory Float64Access Float64Buffers CCalls.Events

/-- The actual source-bound factory establishes the handle, default and
storage for arbitrary accepted initialization access histories. Host writes
select the new source IVP; complete public-call observations, surviving caller
storage and release of the original lease follow from the initial heap.
No created or initialized heap or successful execution is a premise. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧
    Float64SetMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap CLiteral.functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      CSRunEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      (∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool) ∧
      ∀ (E : Type) (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        let literals := pool.addresses firstBlock
        letI : CInterface := RuntimeEnvironment.interface header objects literals
        ∀ (program : Program E) (tag : CAtomicBoolean.Calls.Event → E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
        Identity.Bindings program →
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
        ∀ (owners : SlotOwners.State objects.capacity),
        SlotOwners.Represents objects.flagsBlock heap owners → (∃ slot, owners slot = none) → ∀ owner : Nat,
        ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity,
        ∃ live, ∃ initial : Binary64.Value,
          let p := objects.instances.index slot.val
          trace.length ≤ objects.capacity ∧
          SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
          Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
            slot owner kind factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
          load live (StateProofs.stateAddress p) = some (.finite initial) ∧
          Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
          CStorage.Preserves heap live ∧
          (∀ q, ¬ p.InRecord q → q ≠ AtomicSlots.address objects.flagsBlock slot → live q = heap q) ∧
          (∀ behavior, (machine program).Behaves
            (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind factoryArgs) heap .done) behavior ↔
            behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
          ∀ (buffers : Layout) (args : Initialization.Arguments) (before during : List Request),
          Stored heap buffers → buffers.Separate objects.instances → args.Admissible →
          (∀ request ∈ before, request.Fits buffers) → (∀ request ∈ before, request.StartQuery) →
          (∀ request ∈ during, request.Fits buffers) → (∀ request ∈ during, request.Allowed kind .initialization) →
          ∃ beforeEntry atExit,
            Certificate a.solve.prepareFMI3 program p buffers args kind ⟨initial⟩ Binary64.positiveZero
              live before during beforeEntry atExit ∧
            Executed program p buffers args live before during
              (expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during)
              (InitializationBodies.exitHeap atExit p kind) ∧
            ∀ observation after, Executed program p buffers args live before during observation after →
              observation = expectedObservation a.solve.prepareFMI3 ⟨initial⟩ Binary64.positiveZero args before during ∧
              InitializationCalls.SourceInitialized a.parsed.ast after p args.start (trajectory ⟨initial⟩ args before during) ∧
              (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast after p args.start candidate →
                candidate = trajectory ⟨initial⟩ args before during) ∧
              CStorage.Preserves heap after ∧
              CReadOnly.Preserves heap after ∧
              SlotOwners.Represents objects.flagsBlock after (SlotOwners.update owners slot (some owner)) ∧
              LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner))
                owner kind (nextMode .exitInitialization kind .initialization) ∧
              SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
              SlotOwners.Represents objects.flagsBlock
                (LifecycleRelease.releasedHeap after objects slot (nextMode .exitInitialization kind .initialization)) owners ∧
              (∀ q, ¬ p.InRecord q → Outside buffers q → q ≠ AtomicSlots.address objects.flagsBlock slot →
                LifecycleRelease.releasedHeap after objects slot (nextMode .exitInitialization kind .initialization) q = heap q) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, queries, ready, _, _, _, _, states, derivative, getter, setter,
    initialization, _, factories, runtime, termination, time, entries, completed, discrete, step⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have countPrepared : ∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool := by
    letI : StaticLiterals := ⟨fun _ => none⟩
    exact fun events => (queries inferInstance events).prepared pool made
  have getPrepared := Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made
  have setPrepared := Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made
  have runPrepared : CSRunEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨⟨LiteralPreparation.function_bound _ sigs unique _ resetMember,
      by rw [← InitializationCalls.function_eq a.solve.prepareFMI3]; exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember,
      LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember,
      LiteralPreparation.function_bound _ sigs unique _ termination.member, runtime.release_defined⟩, step.prepared pool made⟩
  have mePrepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
        unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made⟩
  refine ⟨compiled, build.numerical, Float64Metadata.artifact_variables _ _ build.metadata,
    Float64SetMetadata.artifact_state _ _ build.metadata, sigs, pool, made, printed, functions, runPrepared, mePrepared, countPrepared, ?_⟩
  intro E header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  dsimp only
  intro program tag actual identity exchange write kind factoryArgs heap literalFrame storage name supplied nameBytes tokenBytes
    supported nameBound tokenBound nameStored tokenStored fits accepted owners represented available owner
  obtain ⟨request⟩ := prepared_static_identity a sigs (factories.member .cs) made baseHeap firstBlock signed heap
    literalFrame kind factoryArgs name supplied nameBytes tokenBytes supported
    nameBound tokenBound nameStored tokenStored fits accepted
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact StaticRuntime.reservation_bound _ sigs⟩
  obtain ⟨trace, slot, live, work, reserved, created, preserved, createdFrame, creation⟩ :=
    FactoryEnvironment.create_owned header objects literals program tag identity _ kind factoryArgs heap request
      (by rw [actual]; exact StaticRuntime.factory_bound _ sigs unique kind (factories.member kind))
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
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, createdFrame, creation, ?_⟩
  intro buffers args before during buffersStored buffersSeparate admissible beforeFits beforeAllowed duringFits duringAllowed
  obtain ⟨beforeEntry, atExit, certified⟩ := initialization_history program
    (InitializationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program enterDefined exitDefined)
    (getPrepared.quiet header E objects firstBlock program actual)
    (setPrepared.quiet header E objects firstBlock program actual)
    (created.initialized.access_instance initial loaded) (StaticInitialization.entry_storage created.initialized)
    (buffersStored.preserved preserved) (buffersSeparate.at_index slot.val)
    args admissible before during beforeFits beforeAllowed duringFits duringAllowed
  refine ⟨beforeEntry, atExit, certified, certified.executes, ?_⟩
  intro observation after executed
  obtain ⟨observed, initialized, uniqueSource⟩ := certified.completed_source executed
  obtain ⟨_, rfl⟩ := certified.determines executed
  have released := certified.release objects tag slot finish releaseBindings rfl created.represented created.owned created.metadata
  have restored := released.ownersAfter
  have discharged := released.discharged
  rw [SlotOwners.release_reserved_restore reserved] at restored discharged
  refine ⟨observed, initialized, uniqueSource, preserved.trans certified.storage,
    (termination_preserves ((creation _).mpr rfl)).trans certified.readonly,
    certified.owners created.represented, released, discharged, restored, ?_⟩
  intro q notRecord outside notFlag
  have field (name : String) : q ≠ p.member name := by
    intro same
    exact notRecord (same ▸ p.member_in_record name)
  have notState : q ≠ StateProofs.stateAddress p := by
    intro same
    exact notRecord (same ▸ (p.member_in_record "model").member "x")
  exact (released.frame q (field "mode") notFlag).trans
    ((certified.frame q ⟨outside, notState, fun name _ => field name⟩).trans (createdFrame q notRecord notFlag))

end Rumoca.FMI3.InitializationAccess
end
