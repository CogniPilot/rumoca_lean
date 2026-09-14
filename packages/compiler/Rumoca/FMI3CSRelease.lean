import Rumoca.FMI3CSInitialization
import RumocaFMI3.CSRelease
import RumocaFMI3.TerminationEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Actual initialization, accepted CS stepping, termination and release in
one program/interface. The original lease survives ordinary numerical writes
and is discharged by the actual atomic store. No post-initialization or
post-simulation heap/ownership is supplied as a host premise. -/
theorem adapter_initialize_cs_release (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (header : CFenv.Header) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
          program.externals "floor" = some (CMathCalls.floorExternal rfl) →
          program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
          ∀ (seed : Binary64.Value) (heap : Heap) (slot : Fin objects.capacity)
            (owners : SlotOwners.State objects.capacity) (owner : Nat) (args : Initialization.Arguments)
            (buffers : StepEntry.Buffers) (requests : List CSHistory.Request) (final : CSHistory.ReferenceState),
          let p := objects.instances.index slot.val
          args.Admissible → InitializationCalls.EntryStorage heap p →
          load heap (p.member "kind") = some (.integer 1) →
          heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩ →
          StepArguments.Storage heap p buffers →
          CSHistory.ReferenceTrace args.stopTime ⟨args.start, 0⟩ requests final →
          SlotOwners.Represents objects.flagsBlock heap owners → owners slot = some owner →
          load heap (p.member "slot") = some (.integer slot.val) →
          let entered := InitializationEntry.finalHeap heap p args
          let exited := InitializationCalls.exitedHeap heap p args .cs
          let trajectory := Initialization.trajectory (Binary64.value args.start) (Binary64.value seed)
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationCalls.signature.name
              (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
            behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
          InitializationCalls.SourceInitialized a.parsed.ast exited p args.start trajectory ∧
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p args.start candidate → candidate = trajectory) ∧
          ∃ after, CSHistory.Calls program p buffers exited ⟨args.start, 0⟩ requests after final ∧
            CSHistory.Stored a.solve seed after p buffers final args.stopTime ∧
            |Binary64.value (a.solve.run seed final.elapsed) - trajectory (Binary64.value final.time)| ≤
              (final.elapsed : ℝ) + |Binary64.value final.time - (Binary64.value args.start + (final.elapsed : ℝ))| ∧
            let terminated := LifecycleBodies.writeMode after p .terminated
            let released := replace terminated (AtomicSlots.address objects.flagsBlock slot) (CAtomicBoolean.cell false)
            (∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling Termination.signature.name [.pointer (some p)] after .done) behavior ↔
              behavior = .terminates [] ⟨.integer 0, terminated⟩) ∧
            SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
            SlotOwners.Represents objects.flagsBlock released (SlotOwners.update owners slot none) ∧
            (∀ behavior, (CCalls.Events.machine program).Behaves
              (.calling StaticRelease.function.signature.name [.pointer (some p)] terminated .done) behavior ↔
              behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, released⟩) ∧
            (∀ query, CSHistory.Outside p buffers query → query ≠ p.member "mode" →
              query ≠ p.member "timeMin" → query ≠ p.member "eventTime" → query ≠ p.member "lastCompleted" →
              query ≠ p.member "stop" → query ≠ p.member "stopDefined" →
              query ≠ AtomicSlots.address objects.flagsBlock slot → released query = heap query) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, runtime, termination, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E header objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program tag range actual rounding floorBound write seed heap slot owners owner args buffers requests final
  let p := objects.instances.index slot.val
  dsimp only
  intro admissible storage kind state outputs admitted represented owned metadata
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects literals a.solve.prepareFMI3
    program heap p args .cs enterDefined exitDefined admissible storage kind
  have initialStored := CSHistory.initialized_stored a.solve seed heap p args buffers admissible kind state outputs
  have initialValue : StateProofs.Represents heap p ⟨seed⟩ := by
    simp [p, StateProofs.Represents, load, state, convert, Value.finite]
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 heap p args .cs ⟨seed⟩ initialValue
  have uniqueInitial := InitializationBodies.exit_model (InitializationEntry.model initialValue args) .cs
  have bindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact runtime.release_defined, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  have terminateQuiet : Termination.QuietContract program := by
    apply TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ termination.member
  have finish := TerminationEnvironment.release_correct header objects literals program tag terminateQuiet bindings
  obtain ⟨after, calls, finalStored, atomic, frame⟩ := CSHistory.trace_atomic_frame header objects literals
    a.solve.prepareFMI3 signatures seed p buffers args.stopTime
    (fun reference request => ((step.prepared pool made).quiet
      (request.query header p buffers reference args.stopTime) objects firstBlock).2)
    program range actual rounding floorBound (InitializationCalls.exitedHeap heap p args .cs)
      ⟨args.start, 0⟩ final requests initialStored admitted
  have mode : InitializationCalls.exitedHeap heap p args .cs (p.member "mode") =
      some ⟨.int32, true, some (.integer 4)⟩ := by
    simp [InitializationCalls.exitedHeap, InitializationBodies.exitHeap, cs_initialization, Mode.code]
  obtain ⟨_, terminated, discharged, ownersAfter, freed, releasedFrame⟩ := CSHistory.release_history
    objects program tag finish a.solve seed (InitializationCalls.exitedHeap heap p args .cs) after
    slot buffers ⟨args.start, 0⟩ final args.stopTime requests owners owner initialStored mode calls finalStored atomic frame
    (StaticInitialization.exited_owners objects heap slot args .cs owners represented) owned
    ((StaticInitialization.exited_metadata heap p args .cs).trans metadata)
  refine ⟨entered, exited, initialized,
    fun _ given => InitializationCalls.source_initialized_unique given uniqueInitial,
    after, calls, finalStored,
    CSHistory.source_error a.solve seed args.start (InitializationCalls.exitedHeap heap p args .cs)
      p buffers args.stopTime initialized initialStored final,
    terminated, discharged, ownersAfter, freed, ?_⟩
  intro query outside outsideMode minimum event completed stop stopDefined flag
  exact (releasedFrame query outside outsideMode flag).trans
    (InitializationCalls.exited_frame heap p query args .cs outside.2.1 minimum event completed stop stopDefined outsideMode)

end Rumoca.FMI3
end
