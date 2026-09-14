import Rumoca.FMI3MEProtocol
import Rumoca.FMI3CreatedInitializationProtocol

noncomputable section
namespace Rumoca.FMI3.MEProtocol
open CTree CMemory CLiteral CStringMemory StaticFactory CCalls.Events

/-- Actual source-bound creation, repeated initialization/simulation cycles,
and final release share one prepared program and literal pool. Every resource
after creation is derived; callers supply only original storage and effects. -/
theorem runtime_create_release (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    Float64Metadata.Contract a.solve.prepareFMI3 metadata ∧ Float64SetMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
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
        ∀ (program : Program Invocation) (tag : CAtomicBoolean.Calls.Event → Invocation),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs → Identity.Bindings program →
          program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
          program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
        ∀ (factoryArgs : FactoryArguments.Raw) (heap : Heap),
          CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
          CreationStorage heap objects.instances objects.flags objects.capacity →
        ∀ (name supplied : Address) (nameBytes tokenBytes : List UInt8),
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
            Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner)) slot owner .me
              factoryArgs.environment factoryArgs.logger factoryArgs.logging ∧
            load live (StateProofs.stateAddress p) = some (.finite initial) ∧
            Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
            (∀ behavior, (machine program).Behaves
              (.calling (FactoryArguments.signature .me).name (FactoryArguments.arguments .me factoryArgs) heap .done) behavior ↔
              behavior = .terminates (trace.map tag) ⟨.pointer (some p), live⟩) ∧
            ∀ (retained : Address → Prop) (access : Float64Buffers.Layout) (addresses : String → Address) (buffer : Address) (plan : Plan),
              InitializationProtocol.Resources objects retained heap p access → MENumericalHistory.CallerStorage heap p addresses buffer →
              InitializationProtocol.MEOutputsGuarded objects retained addresses buffer →
              InitializationProtocol.FactoryLogPolicy program objects retained factoryArgs →
              Admitted objects retained heap p access addresses buffer plan →
              Contract a.solve program objects retained (SlotOwners.update owners slot (some owner)) heap
                (pool.install baseHeap firstBlock signed) live p access addresses buffer plan ∧
              ∀ records after, Completed program p access addresses buffer live plan records after →
                SourceTrace a.solve p plan records ∧ CReadOnly.Preserves heap after ∧
                LifecycleRelease.Released objects program tag after slot (SlotOwners.update owners slot (some owner)) owner .me plan.mode ∧
                SlotOwners.release (SlotOwners.update owners slot (some owner)) slot owner = some owners ∧
                SlotOwners.Represents objects.flagsBlock (LifecycleRelease.releasedHeap after objects slot plan.mode) owners ∧
                (∀ q, MEFailure.Protected objects addresses buffer q → plan.Outside p access addresses buffer q →
                  q ≠ AtomicSlots.address objects.flagsBlock slot →
                  LifecycleRelease.releasedHeap after objects slot plan.mode q = heap q) := by
  obtain ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, nominalMetadata, equation, sigs, pool, made, printed, functions,
    prepared, create⟩ := InitializationProtocol.runtime_create_release compiled build
  refine ⟨compiled, numerical, numericMetadata, writableMetadata, countMetadata, nominalMetadata, equation, sigs, pool, made, printed, functions, ?_⟩
  intro header instances flags separate baseHeap firstBlock signed
  let objects := StaticRuntime.objects instances flags separate
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  dsimp only
  intro program tag actual identity exchange write factoryArgs heap literalFrame storage
    name supplied nameBytes tokenBytes nameBound tokenBound nameStored tokenStored fits accepted
    owners represented available owner
  obtain ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, preserved, creationFrame, creation, _⟩ :=
    create header instances flags separate baseHeap firstBlock signed program tag actual identity exchange write .me factoryArgs heap
      literalFrame storage name supplied nameBytes tokenBytes (Or.inl rfl) nameBound tokenBound nameStored tokenStored fits accepted
      owners represented available owner
  let p := objects.instances.index slot.val
  refine ⟨trace, slot, live, initial, work, reserved, created, loaded, agreement, creation, ?_⟩
  intro retained access addresses buffer plan resources outputs guarded logging admitted
  have creationReadonly := termination_preserves ((creation _).mpr rfl)
  have invariant := InitializationProtocol.Invariant.created objects created preserved (literalFrame.trans creationReadonly) logging
  have initializeCalls := InitializationProtocol.execution_contract header objects a.solve.prepareFMI3 sigs pool
    prepared.getter prepared.setter prepared.counts prepared.nominals prepared.cs.toPreparedContract baseHeap firstBlock signed program actual retained
    (SlotOwners.update owners slot (some owner)) heap p access .me resources
  have initialization : InitializationCompiler a.solve program objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p access := by
    intro current actions state ready reference requests
    exact InitializationProtocol.source_contract initializeCalls reference requests ready
  have simulation : SimulationCompiler a.solve program objects retained
      (SlotOwners.update owners slot (some owner)) heap (pool.install baseHeap firstBlock signed) p addresses buffer := by
    intro current before final clock finalClock actions persistent stored storage reference requests regions
    exact InitializationProtocol.me_execution header objects a.solve.prepareFMI3 sigs pool prepared.me prepared.counts prepared.nominals
      prepared.cs.toPreparedContract baseHeap firstBlock signed program actual retained
      (SlotOwners.update owners slot (some owner)) heap current p addresses buffer before final clock finalClock actions
      persistent rfl guarded stored storage reference requests regions
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

end Rumoca.FMI3.MEProtocol
end
