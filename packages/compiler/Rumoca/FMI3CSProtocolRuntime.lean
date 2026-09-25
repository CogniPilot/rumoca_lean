import Rumoca.FMI3CSProtocol
import Rumoca.FMI3CreatedInitializationProtocol

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CTree CMemory CLiteral CStringMemory StaticFactory CCalls.Events

/-- The Co-Simulation lifetime of the actual emitted adapter table: source-bound
creation under an explicit slot owner, every admitted initialization/simulation
history with its exact statuses, readbacks and callback events, and release by
fmi3FreeInstance from any state or, where accepted, fmi3Terminate followed by
fmi3FreeInstance. The original owner map is restored; other instances, the
static pool and the literal pool are preserved outside the declared caller
regions. Creation, simulation and release share one prepared program. -/
abbrev Lifetime (a : Artifact input) (c description adapter metadata : String) : Prop :=
    Rumoca.ArtifactContract a c .internal ∧
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
      ∀ (header : CFenv.Header) (instances flags : Nat) (separate : instances ≠ flags)
        (baseHeap : Heap) (firstBlock : Nat) (signed : Bool),
        let objects := StaticRuntime.objects instances flags separate
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs → Identity.Bindings program →
          program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
          program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
          program.externals "floor" = some (CMathCalls.floorExternal rfl) →
        ∀ (factoryArgs : FactoryArguments.Raw) (heap : Heap),
          CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
          CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
          FactoryEntry.unsupported factoryArgs = false →
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
            Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner .cs
              factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
            load live (StateProofs.stateAddress p) = some (.finite initial) ∧
            Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
            (∀ behavior, (machine program).Behaves
              (.calling (FactoryArguments.signature .cs).name (FactoryArguments.arguments .cs factoryArgs) heap .done) behavior ↔
              behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
            ∀ (retained : Address → Prop) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (plan : Plan) (readers : InitializationProtocol.ReadBank),
              InitializationProtocol.Resources objects retained heap p access readers → StepArguments.Storage heap p buffers →
              InitializationProtocol.CSOutputsGuarded objects retained buffers →
              (∀ q, readers.Region q → CSRun.Outside p buffers q) →
              InitializationProtocol.FactoryLogPolicy program objects retained factoryArgs →
              Admitted header objects retained heap p access buffers readers plan →
              Contract a.solve.prepareFMI3 header program objects retained (SlotOwners.update owners slot (some owner)) heap
                (pool.install baseHeap firstBlock signed) live p access buffers plan readers ∧
              ∀ records after, Completed program p access live plan records after →
                SourceTrace a.solve.prepareFMI3 header p buffers plan records ∧ CReadOnly.Preserves heap after ∧
                InitializationProtocol.Retention plan.loggingUpdate p live after ∧
                load after (p.member "logging") = some (CBody.boolean (plan.loggingUpdate.getD factoryArgs.logging)) ∧
                SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
                InitializationProtocol.Freed objects program tag after slot (SlotOwners.update owners slot (some owner)) owner ∧
                SlotOwners.Represents objects.flagsBlock (InitializationProtocol.freedHeap after objects slot) owners ∧
                (∀ q, CSRun.Protected objects buffers q → plan.Outside p access buffers q →
                  q ≠ AtomicSlots.address objects.flagsBlock slot →
                  InitializationProtocol.freedHeap after objects slot q = heap q) ∧
                (∀ other : Fin objects.capacity, other ≠ slot → ∀ q, (objects.instances.index other.val).InRecord q →
                  plan.Outside p access buffers q → InitializationProtocol.freedHeap after objects slot q = heap q) ∧
                (plan.Finished →
                  LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner .cs plan.mode ∧
                  SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot plan.mode) owners ∧
                  (∀ q, CSRun.Protected objects buffers q → plan.Outside p access buffers q →
                    q ≠ AtomicSlots.address objects.flagsBlock slot →
                    LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q) ∧
                  (∀ other : Fin objects.capacity, other ≠ slot → ∀ q, (objects.instances.index other.val).InRecord q →
                    plan.Outside p access buffers q → LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q))

/-- Actual source-bound creation, repeated initialization/simulation cycles,
and final release share one prepared program and literal pool. Every resource
after creation is derived; callers supply only original storage and effects. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Lifetime a c description adapter metadata := by
  obtain ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, nominalMetadata, loggingMetadata, equation, sigs, pool, made, printed, functions,
    prepared, create⟩ := InitializationProtocol.runtime_create_release compiled build
  refine ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, nominalMetadata, loggingMetadata, equation, sigs, pool, made, printed, functions, ?_⟩
  intro header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  dsimp only
  intro program tag range actual identity exchange write rounding floorBound factoryArgs heap literalFrame storage
    name supplied nameBytes tokenBytes supported nameBound tokenBound nameStored tokenStored fits accepted
    owners represented available owner
  obtain ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, creationFrame, creation, _⟩ :=
    create header instances flags separate baseHeap firstBlock signed program tag actual identity exchange write .cs factoryArgs heap
      literalFrame storage name supplied nameBytes tokenBytes (Or.inr supported) nameBound tokenBound nameStored tokenStored fits accepted
      owners represented available owner
  let p := objects.instances.index slot.val
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, creation, ?_⟩
  intro retained access buffers plan readers resources outputs guarded readerOutside logging admitted
  have creationReadonly := termination_preserves ((creation _).mpr rfl)
  have readerFrame := resources.readerInputs.creation_frame represented resources.readerGuarded creationFrame
  have invariant := InitializationProtocol.Invariant.created objects created preserved (literalFrame.trans creationReadonly) logging readerFrame
  have initializeCalls := InitializationProtocol.execution_contract header objects a.solve.prepareFMI3 sigs pool
    prepared.getter prepared.setter prepared.counts prepared.nominals prepared.logging prepared.eventIndicators prepared.me.evaluation prepared.absent prepared.cs.toPreparedContract baseHeap firstBlock signed program actual identity.compareBinding retained
    (SlotOwners.update owners slot (some owner)) heap p access .cs readers resources
  have initialization : InitializationCompiler a.solve.prepareFMI3 program objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p access readers := by
    intro current actions state ready reference requests
    exact InitializationProtocol.source_contract initializeCalls reference requests ready
  have simulation : SimulationCompiler a.solve.prepareFMI3 program header objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p buffers readers := by
    intro current before final actions statuses persistent stored reference requests included regions readerSafe
    exact CSMixedRun.execution header objects a.solve.prepareFMI3 sigs pool prepared.cs prepared.logging
      ⟨prepared.getter, prepared.setter, prepared.absent⟩ baseHeap firstBlock signed
      program range actual rounding floorBound identity.compareBinding retained (SlotOwners.update owners slot (some owner)) heap current p buffers
      before final actions statuses readers persistent rfl guarded
      (fun q inside => ⟨(resources.readerGuarded q inside).1, readerOutside q inside⟩) stored reference requests included
      regions readerSafe
  obtain ⟨reset, _, _, termination, releaseDefined⟩ := prepared.cs.execution header objects firstBlock program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  have certified := correct initialization simulation reset outputs guarded (fun q inside => (resources.readerGuarded q inside).2.1) admitted invariant
  refine ⟨certified, ?_⟩
  intro records after completed
  obtain ⟨sourceTrace, freed, freedFrame⟩ := certified.freed objects tag slot releaseBindings rfl created.owned created.metadata completed
  have discharged := freed.discharged
  have freedOwners := freed.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged freedOwners
  refine ⟨sourceTrace, creationReadonly.trans (certified.completed _ _ completed).2.2.1,
    (certified.completed _ _ completed).2.2.2.1,
    (certified.completed _ _ completed).2.2.2.1.logging_value created.initialized.loggingValue,
    discharged, freed, freedOwners, ?_, ?_, ?_⟩
  · intro q inside outside notFlag
    exact (freedFrame q inside outside notFlag).trans (creationFrame q outside.not_record notFlag)
  · intro other different q inside outside
    obtain ⟨pooled, _, notFlag⟩ := InitializationProtocol.other_instance objects different inside
    exact (freedFrame q (Or.inl pooled) outside notFlag).trans (creationFrame q outside.not_record notFlag)
  intro finished
  obtain ⟨_, released, frame⟩ := certified.released objects tag slot finish releaseBindings rfl created.owned created.metadata
    (admitted.can_finish finished) completed
  have restored := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at restored
  refine ⟨released, restored, ?_, ?_⟩
  · intro q inside outside notFlag
    exact (frame q inside outside notFlag).trans (creationFrame q outside.not_record notFlag)
  · intro other different q inside outside
    obtain ⟨pooled, _, notFlag⟩ := InitializationProtocol.other_instance objects different inside
    exact (frame q (Or.inl pooled) outside notFlag).trans (creationFrame q outside.not_record notFlag)

end Rumoca.FMI3.CSProtocol
end
