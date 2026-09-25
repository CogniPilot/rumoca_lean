import Rumoca.FMI3CSMixedRecords
import RumocaFMI3.CSMixedExecution
import RumocaFMI3.CSMixedPrefixes
import Rumoca.FMI3BuildProofs
import RumocaFMI3.ResetEnvironment
import RumocaFMI3.DebugLoggingMetadata
import RumocaFMI3.InstanceQueryEnvironment
import RumocaFMI3.Float64Environment
import RumocaFMI3.Float64SetEnvironment

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody CLiteral StaticFactory CCalls.Events

theorem Trace.completed_source [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {model : Solve.Model source}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (completed : Completed program p heap actions observed events after) :
    ReferenceTrace header p buffers before actions final statuses ∧ CSRun.SourceSample source p final after :=
  ⟨certified.reference_of_completed completed, (certified.completed completed).2.1.source_sample⟩

theorem Trace.stopped_source [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {model : Solve.Model source}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (stored : CSRun.Stored model heap p buffers before)
    (configured : capability.Configured heap p enabled)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (stopped : Stopped program p heap actions) :
    ∃ left action rest observed events middle current expected remaining,
      actions = left ++ action :: rest ∧ Completed program p heap left observed events middle ∧
      Faulted program p middle action ∧ action.MayBlock ∧ statuses = expected ++ remaining ∧
      observed = expected.map Value.integer ∧ ReferenceTrace header p buffers before left current expected ∧
      CSRun.SourceSample source p current middle ∧
      capability.Configured middle p ((loggingUpdate left).getD enabled) ∧
      InitializationProtocol.Retention (loggingUpdate left) p heap middle ∧
      SlotOwners.Represents objects.flagsBlock middle owners ∧ CReadOnly.Preserves heap middle ∧
      (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → middle q = heap q) := by
  obtain ⟨left, action, rest, observed, events, middle, current, expected, remaining,
    same, completed, faulted, mayBlock, statusEq, values, reference, nextStored, nextConfig,
    retention, ownership, readonly, frame⟩ := certified.stopped_prefix stored configured represented stopped
  exact ⟨left, action, rest, observed, events, middle, current, expected, remaining,
    same, completed, faulted, mayBlock, statusEq, values, reference, nextStored.source_sample,
    nextConfig, retention, ownership, readonly, frame⟩

/-- The source compilation and actual artifact contract supply the same
prepared CS numerical functions, public logging setter, printer and XML category.
All later heaps and every raw returned status follow from those definitions. -/
theorem runtime_history (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DebugLogging.MetadataContract metadata "logStatus" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      StepCalls.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      DebugLogging.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (objects : Objects) (literalBase : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation) (capability : Logging.Capability) (enabled : Bool)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
          program.externals "floor" = some (CMathCalls.floorExternal rfl) →
          program.externals "strcmp" = some (CStringCalls.compareExternal rfl) → capability.Bound program →
          ∀ (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
            (before final : CSRun.Reference) (actions : List Action) (statuses : List Int)
            (owners : SlotOwners.State objects.capacity),
          capability.Requires (fun _ effect =>
            ∀ args before value after, effect.execute args before value after → CSRun.ProtectedFrame objects buffers before after) →
          capability.Configured heap p enabled → Reset.Writable heap (p.member "logging") .boolean →
          p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
          CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
          CSRun.Stored a.solve heap p buffers before → ReferenceTrace header p buffers before actions final statuses →
          (∀ action ∈ actions, action.Prepared objects buffers heap) →
          (∀ action ∈ actions, capability.Requires (fun _ effect =>
            ∀ args before value after, effect.execute args before value after →
              CStorage.PreservesOn action.CallerRegion before after)) →
          (∀ action ∈ actions, capability.Requires (fun _ effect =>
            ∀ args before value after, effect.execute args before value after →
              ∀ q, action.ReaderRegion q → after q = before q)) →
          (∀ action ∈ actions, ∀ q, action.ReaderRegion q → CSRun.Outside p buffers q) →
          (∀ writer ∈ actions, ∀ reader ∈ actions, ∀ q, reader.ReaderRegion q → ¬ writer.CallerRegion q) →
          Trace header objects owners a.solve capability program p buffers heap enabled before actions final statuses ∧
          (∀ observed events after, Completed program p heap actions observed events after →
            observed = statuses.map Value.integer ∧ CSRun.Stored a.solve after p buffers final ∧
            capability.Configured after p ((loggingUpdate actions).getD enabled) ∧
            InitializationProtocol.Retention (loggingUpdate actions) p heap after ∧
            SlotOwners.Represents objects.flagsBlock after owners ∧ CReadOnly.Preserves heap after ∧
            (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → after q = heap q) ∧
            ReferenceTrace header p buffers before actions final statuses ∧ CSRun.SourceSample a.parsed.ast p final after) ∧
          (∀ observed events after records, Recorded program p heap actions observed events after records →
            SourceTrace a.solve header p buffers heap before actions observed records after final) ∧
          ((∃ observed events after, Completed program p heap actions observed events after) ∨ Stopped program p heap actions) ∧
          (Stopped program p heap actions →
            ∃ left action rest observed events middle current expected remaining,
              actions = left ++ action :: rest ∧ Completed program p heap left observed events middle ∧
              Faulted program p middle action ∧ action.MayBlock ∧ statuses = expected ++ remaining ∧
              observed = expected.map Value.integer ∧ ReferenceTrace header p buffers before left current expected ∧
              CSRun.SourceSample a.parsed.ast p current middle ∧
              capability.Configured middle p ((loggingUpdate left).getD enabled) ∧
              InitializationProtocol.Retention (loggingUpdate left) p heap middle ∧
              SlotOwners.Represents objects.flagsBlock middle owners ∧ CReadOnly.Preserves heap middle ∧
              (∀ q, CSRun.Protected objects buffers q → CSRun.Outside p buffers q → middle q = heap q)) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, _, ready, _, _, _, _, _, _, getter, setter,
    initialization, _, _, _, termination, _, _, _, _, stepContract, loggingContract, _, _, absentContract, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have queries : InstanceQuery.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨Float64Environment.prepared_correct a.solve.prepareFMI3 sigs unique getter.member getter.numerical.fresh made,
      Float64SetEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique setter.member made,
      fun ty write => (absentContract ty write).prepared pool made⟩
  have step := stepContract.prepared pool made
  have logging := loggingContract.prepared pool made
  refine ⟨compiled, build.numerical, DebugLogging.artifact_category _ _ build.metadata,
    sigs, pool, made, printed, functions, step, logging, ?_⟩
  intro header objects literalBase firstBlock signed
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program capability enabled range actual rounding floorBound compare bound
    heap p buffers before final actions statuses owners required configured writable inPool represented
    readonly stored admitted requests storagePolicies policies guarded separate
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ resetMember
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ sigs unique _ initialization.exitMember
  have quietQuery := queries.quiet header objects firstBlock program actual
    (TerminationEnvironment.quiet_correct header objects literals a.solve.prepareFMI3 program
      (by rw [actual]; exact LiteralPreparation.function_bound _ sigs unique _ termination.member))
  have certified := trace_correct header objects a.solve.prepareFMI3 sigs pool step logging literalBase firstBlock signed p buffers
    inPool program capability enabled range actual rounding floorBound compare bound required reset quietQuery enterDefined
    exitDefined heap before final actions statuses owners readonly stored configured writable represented admitted requests
    storagePolicies policies guarded separate
  refine ⟨certified, ?_, (fun _ _ _ _ recorded => certified.recorded_source recorded), certified.progress, certified.stopped_source stored configured represented⟩
  intro observed events after completed
  obtain ⟨values, nextStored, nextConfig, retention, ownership, nextReadonly, frame⟩ := certified.completed completed
  exact ⟨values, nextStored, nextConfig, retention, ownership, nextReadonly, frame, certified.completed_source completed⟩

end Rumoca.FMI3.CSMixedRun
end
