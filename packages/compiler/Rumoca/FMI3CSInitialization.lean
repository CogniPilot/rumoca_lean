import Rumoca.FMI3CSHistory
import RumocaFMI3.InitializationEnvironment
import RumocaFMI3.CSInitialization

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- Both initialization calls and the finite CS history execute the actual
adapter in one header/object interface. The initialized source trajectory is
derived from original finite state, and each later numerical state is proved. -/
theorem adapter_initialize_cs_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (header : CFenv.Header) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
          program.externals "floor" = some (CMathCalls.floorExternal rfl) →
          ∀ (seed : Binary64.Value) (heap : Heap) (p : Address) (args : Initialization.Arguments)
            (buffers : StepEntry.Buffers) (requests : List CSHistory.Request) (final : CSHistory.ReferenceState),
          args.Admissible → InitializationCalls.EntryStorage heap p →
          load heap (p.member "kind") = some (.integer 1) →
          heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩ →
          StepArguments.Storage heap p buffers →
          CSHistory.ReferenceTrace args.stopTime ⟨args.start, 0⟩ requests final →
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
          (∀ candidate, InitializationCalls.SourceInitialized a.parsed.ast exited p args.start candidate →
            candidate = trajectory) ∧
          ∃ after, CSHistory.Calls program p buffers exited ⟨args.start, 0⟩ requests after final ∧
            CSHistory.Stored a.solve seed after p buffers final args.stopTime ∧
            (∀ query, CSHistory.Outside p buffers query → after query = exited query) ∧
            |Binary64.value (a.solve.run seed final.elapsed) - trajectory (Binary64.value final.time)| ≤
              (final.elapsed : ℝ) + |Binary64.value final.time - (Binary64.value args.start + (final.elapsed : ℝ))| := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E header objects firstBlock
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program range actual rounding floorBound seed heap p args buffers requests final admissible storage kind state outputs admitted
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
  have represented : StateProofs.Represents heap p ⟨seed⟩ := by
    simp [StateProofs.Represents, load, state, convert, Value.finite]
  have initialized := InitializationCalls.exited_source_initialized a.solve.prepareFMI3 heap p args .cs ⟨seed⟩ represented
  have initialValue := InitializationBodies.exit_model (InitializationEntry.model represented args) .cs
  obtain ⟨after, calls, finalStored, frame⟩ := CSHistory.trace_frame header objects literals
    a.solve.prepareFMI3 signatures seed p buffers args.stopTime
    (fun reference request => ((step.prepared pool made).quiet
      (request.query header p buffers reference args.stopTime) objects firstBlock).2)
    program range actual rounding floorBound (InitializationCalls.exitedHeap heap p args .cs)
      ⟨args.start, 0⟩ final requests initialStored admitted
  exact ⟨entered, exited, initialized,
    fun _ given => InitializationCalls.source_initialized_unique given initialValue,
    after, calls, finalStored, frame, CSHistory.source_error a.solve seed args.start
      (InitializationCalls.exitedHeap heap p args .cs) p buffers args.stopTime initialized initialStored final⟩

end Rumoca.FMI3
end
