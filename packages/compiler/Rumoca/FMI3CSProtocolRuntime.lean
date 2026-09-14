import Rumoca.FMI3CSProtocol
import Rumoca.FMI3CreatedInitializationProtocol

noncomputable section
namespace Rumoca.FMI3.CSProtocol
open CTree CMemory CLiteral CStringMemory StaticFactory CCalls.Events

/-- Actual source-bound creation, repeated initialization/simulation cycles,
and final release share one prepared program and literal pool. Every resource
after creation is derived; callers supply only original storage and effects. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧ Float64SetMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
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
            ∀ (retained : Address → Prop) (access : Float64Buffers.Layout) (buffers : StepEntry.Buffers) (plan : Plan),
              InitializationProtocol.Resources objects retained heap p access → StepArguments.Storage heap p buffers →
              InitializationProtocol.CSOutputsGuarded objects retained buffers →
              InitializationProtocol.FactoryLogPolicy program objects retained factoryArgs →
              Admitted header objects retained heap p access buffers plan →
              Contract a.solve.prepareFMI3 header program objects retained (SlotOwners.update owners slot (some owner)) heap
                (pool.install baseHeap firstBlock signed) live p access buffers plan ∧
              ∀ records after, Completed program p access live plan records after →
                SourceTrace a.solve.prepareFMI3 header p buffers plan records ∧ CReadOnly.Preserves heap after ∧
                LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner .cs plan.mode ∧
                SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
                SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot plan.mode) owners ∧
                (∀ q, CSRun.Protected objects buffers q → plan.Outside p access buffers q →
                  q ≠ AtomicSlots.address objects.flagsBlock slot →
                  LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q) := by
  obtain ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, equation, sigs, pool, made, printed, functions,
    prepared, create⟩ := InitializationProtocol.runtime_create_release compiled build
  refine ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, equation, sigs, pool, made, printed, functions, ?_⟩
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
  intro retained access buffers plan resources outputs guarded logging admitted
  have creationReadonly := termination_preserves ((creation _).mpr rfl)
  have invariant := InitializationProtocol.Invariant.created objects created preserved (literalFrame.trans creationReadonly) logging
  have initializeCalls := InitializationProtocol.execution_contract header objects a.solve.prepareFMI3 sigs pool
    prepared.getter prepared.setter prepared.counts prepared.cs.toPreparedContract baseHeap firstBlock signed program actual retained
    (SlotOwners.update owners slot (some owner)) heap p access .cs resources
  have initialization : InitializationCompiler a.solve.prepareFMI3 program objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p access := by
    intro current actions state ready reference requests
    exact InitializationProtocol.source_contract initializeCalls reference requests ready
  have simulation : SimulationCompiler a.solve.prepareFMI3 program header objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p buffers := by
    intro current before final actions statuses persistent stored reference
    exact InitializationProtocol.cs_execution header objects a.solve.prepareFMI3 sigs pool prepared.cs baseHeap firstBlock signed
      program range actual rounding floorBound retained (SlotOwners.update owners slot (some owner)) heap current p buffers
      before final actions statuses persistent rfl guarded stored reference
  obtain ⟨reset, _, _, termination, releaseDefined⟩ := prepared.cs.execution header objects firstBlock program actual
  have releaseBindings : StaticRelease.Bindings program tag := ⟨releaseDefined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have finish := TerminationEnvironment.release_correct header objects (pool.addresses firstBlock) program tag termination releaseBindings
  have certified := correct initialization simulation reset outputs guarded admitted invariant
  refine ⟨certified, ?_⟩
  intro records after completed
  obtain ⟨sourceTrace, released, frame⟩ := certified.released objects tag slot finish releaseBindings rfl created.owned created.metadata completed
  have discharged := released.discharged
  have restored := released.ownersAfter
  rw [SlotOwners.release_reserved_restore reserved] at discharged restored
  refine ⟨sourceTrace, creationReadonly.trans (certified.completed _ _ completed).2.2.1,
    released, discharged, restored, ?_⟩
  intro q inside outside notFlag
  exact (frame q inside outside notFlag).trans (creationFrame q outside.not_record notFlag)

end Rumoca.FMI3.CSProtocol
end
