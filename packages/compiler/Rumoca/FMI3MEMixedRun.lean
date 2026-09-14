import Rumoca.FMI3MENumericalRunObservations
import RumocaFMI3.MEMixedExecution
import RumocaFMI3.MEMixedInterrupted
import RumocaFMI3.ResetEnvironment
import RumocaFMI3.CountMetadata
import RumocaFMI3.NominalMetadata

noncomputable section
namespace Rumoca.FMI3.MEMixedRun
open CTree CMemory CBody CLiteral StaticFactory CCalls.Events

/-- Source observations retain each success status and derivative equation.
Rejected calls expose Error and callback events without validating failed outputs. -/
inductive SourceObservations (model : Solve.Model source) : List Action →
    List (MENumericalHistory.Observation Invocation) → Prop where
  | nil : SourceObservations model [] []
  | run : MENumericalRun.DerivativeObservations source [action] head →
      (∀ observed ∈ head, observed.status = .integer 0 ∧ observed.events = []) →
      SourceObservations model rest tail →
      SourceObservations model (.run action :: rest) (head ++ tail)
  | reject : SourceObservations model rest tail →
      SourceObservations model (.reject request input :: rest) (⟨events, .integer 3, none⟩ :: tail)
  | count : SourceObservations model rest tail →
      SourceObservations model (.counts (.get events output) :: rest)
        (MENumericalHistory.Observation.ok ((CountAccess.Request.get events output).expected model.prepareFMI3 0) :: tail)
  | countRejected : SourceObservations model rest tail →
      SourceObservations model (.counts (.reject which missing output) :: rest) (⟨events, .integer 3, none⟩ :: tail)
  | nominal : SourceObservations model rest tail →
      SourceObservations model (.nominals (.get output) :: rest)
        (MENumericalHistory.Observation.ok ((NominalAccess.Request.get output).expected model.prepareFMI3 0) :: tail)
  | nominalRejected : SourceObservations model rest tail →
      SourceObservations model (.nominals (.reject access output count) :: rest) (⟨events, .integer 3, none⟩ :: tail)

theorem ActionContract.epochs_source [CInterface] {source : AST.Model} {program : Program Invocation}
    (model : Solve.Model source) (certified : ActionContract program p addresses buffer heap action returns blocked)
    (performed : Performed program p addresses buffer heap action observed after epochs) :
    MENumericalRun.InitializedEpochs source p epochs := by
  cases performed with
  | run executed => cases certified with
    | run called =>
      obtain ⟨_, _, checkpoints⟩ := called.determines executed
      rw [checkpoints]
      exact called.epochs_source model
  | reject _ _ => intro epoch member; cases member
  | counts _ => intro epoch member; cases member
  | nominals _ => intro epoch member; cases member

/-- The actual completed script, including arbitrary observed statuses and
callback returns, inherits the source equations and every reset's source IVP. -/
theorem Trace.source [CInterface] {source : AST.Model} {program : Program Invocation}
    (model : Solve.Model source) {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model.prepareFMI3 objects owners config program p addresses buffer heap reference clock actions final finalClock)
    (completed : Completed program p addresses buffer heap actions observed after epochs) :
    SourceObservations model actions observed ∧ MENumericalRun.InitializedEpochs source p epochs := by
  induction completed generalizing reference clock final finalClock with
  | nil => exact ⟨.nil, fun _ member => by cases member⟩
  | @cons heap action head middle headEpochs rest tail after tailEpochs performed _ ih =>
    cases certified with
    | cons called returned following =>
      have outcome := called.returned performed
      have post := returned _ _ _ outcome
      obtain ⟨sourceTail, epochTail⟩ := ih (following _ _ _ outcome)
      have epochHead := called.epochs_source model performed
      refine ⟨?_, ?_⟩
      · cases action with
        | run command =>
          have values := post.observation
          change head = _ at values
          rw [values]
          refine .run (MENumericalRun.observations_source model reference [command]) ?_ sourceTail
          intro result member
          obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
          exact ⟨rfl, rfl⟩
        | reject request input =>
          obtain ⟨events, values⟩ := post.observation
          rw [values]
          exact .reject sourceTail
        | counts request =>
          cases request with
          | get which output =>
            have values : head = [MENumericalHistory.Observation.ok
                ((CountAccess.Request.get which output).expected model.prepareFMI3 0)] := post.observation
            rw [values]
            exact .count sourceTail
          | reject which missing output =>
            obtain ⟨events, values⟩ := post.observation
            rw [values]
            exact .countRejected sourceTail
        | nominals request =>
          cases request with
          | get output =>
            have values : head = [MENumericalHistory.Observation.ok
                ((NominalAccess.Request.get output).expected model.prepareFMI3 0)] := post.observation
            rw [values]
            exact .nominal sourceTail
          | reject access output count =>
            obtain ⟨events, values⟩ := post.observation
            rw [values]
            exact .nominalRejected sourceTail
      · intro epoch member
        rcases List.mem_append.mp member with member | member
        · exact epochHead epoch member
        · exact epochTail epoch member

/-- Returned observations and source initialization checkpoints before a
blocked action. ME trial states and clocks remain importer-selected. -/
structure SourcePrefix (model : Solve.Model source) (p : Address) (addresses : String → Address)
    (buffer : Address) (before : MENumericalHistory.ReferenceState) (clock : Time.Clock)
    (actions : List Action) (stop : StopRecord) : Prop where
  decomposition : actions = stop.done ++ stop.pending :: stop.rest
  observations : SourceObservations model stop.done stop.observed
  checkpoints : MENumericalRun.InitializedEpochs source p stop.epochs
  pending : ∃ middle middleClock,
    ReferenceTrace buffer before clock stop.done middle middleClock ∧
    MENumericalHistory.Stored stop.heap p middleClock middle addresses buffer ∧
    stop.pending.Allowed buffer middleClock middle ∧
    stop.pending.Rejection

theorem Trace.interrupted_source [CInterface] {source : AST.Model} {program : Program Invocation}
    (model : Solve.Model source) {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model.prepareFMI3 objects owners config program p addresses buffer heap before clock actions final finalClock)
    (stored : MENumericalHistory.Stored heap p clock before addresses buffer)
    (reset : Reset.Storage heap p) (configured : config.Stored heap p)
    (owned : SlotOwners.Represents objects.flagsBlock heap owners)
    (admitted : ReferenceTrace buffer before clock actions final finalClock)
    (interrupted : Interrupted program p addresses buffer heap actions stop) :
    SourcePrefix model p addresses buffer before clock actions stop := by
  obtain ⟨same, completed, faulted⟩ := interrupted
  rw [same] at certified admitted
  obtain ⟨middle, middleClock, first, last⟩ := admitted.split
  have initial := certified.take stored reset configured owned first
  obtain ⟨observations, checkpoints⟩ := initial.source model completed
  have finalStored := (initial.completed completed).1
  have suffix := certified.after_prefix first completed
  cases last with
  | cons allowed _ =>
    cases suffix with
    | cons called _ _ =>
      exact ⟨same, observations, checkpoints, middle, middleClock, first, finalStored,
        allowed, called.faulted_rejection faulted⟩

theorem Trace.stopped_source [CInterface] {source : AST.Model} {program : Program Invocation}
    (model : Solve.Model source) {objects : Objects}
    {owners : SlotOwners.State objects.capacity} {config : Configuration}
    (certified : Trace model.prepareFMI3 objects owners config program p addresses buffer heap before clock actions final finalClock)
    (stored : MENumericalHistory.Stored heap p clock before addresses buffer)
    (reset : Reset.Storage heap p) (configured : config.Stored heap p)
    (owned : SlotOwners.Represents objects.flagsBlock heap owners)
    (admitted : ReferenceTrace buffer before clock actions final finalClock)
    (stopped : Stopped program p addresses buffer heap actions) :
    ∃ stop, Interrupted program p addresses buffer heap actions stop ∧
      SourcePrefix model p addresses buffer before clock actions stop := by
  obtain ⟨stop, interrupted⟩ := stopped.interrupted
  exact ⟨stop, interrupted, certified.interrupted_source model stored reset configured owned admitted interrupted⟩

/-- Source compilation and its actual artifact contract supply the complete
branching ME history in one emitted table and literal pool. All later storage,
statuses, query values and actual initialization checkpoints are derived. -/
theorem runtime_history (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    NominalMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (objects : Objects) (literalBase : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : Program Invocation) (config : Configuration),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          ∀ heap p clock reference final finalClock addresses buffer actions (owners : SlotOwners.State objects.capacity),
          config.Valid program objects addresses buffer → config.Stored heap p →
          p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
          CReadOnly.Preserves (pool.install literalBase firstBlock signed) heap →
          MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
          ReferenceTrace buffer reference clock actions final finalClock →
          (∀ action ∈ actions, action.Prepared objects heap addresses buffer) →
          (∀ action ∈ actions, config.StoragePolicy action.CallerRegion) →
          Trace a.solve.prepareFMI3 objects owners config program p addresses buffer heap reference clock actions final finalClock ∧
          (∀ observed after epochs, Completed program p addresses buffer heap actions observed after epochs →
            MENumericalHistory.Stored after p finalClock final addresses buffer ∧ Reset.Storage after p ∧
            config.Stored after p ∧ SlotOwners.Represents objects.flagsBlock after owners ∧
            CReadOnly.Preserves heap after ∧
            (∀ q, MEFailure.Protected objects addresses buffer q → MENumericalRun.Outside p addresses buffer q → after q = heap q) ∧
            SourceObservations a.solve actions observed ∧ MENumericalRun.InitializedEpochs a.parsed.ast p epochs) ∧
          ((∃ observed after epochs, Completed program p addresses buffer heap actions observed after epochs) ∨
            Stopped program p addresses buffer heap actions) ∧
          (∀ stop, Interrupted program p addresses buffer heap actions stop →
            SourcePrefix a.solve p addresses buffer reference clock actions stop) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, queries, ready, _, _, _, nominalContract, states, derivative,
    _, _, initialization, _, _, _, _, time, entries, completed, discrete, _⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have counts : ∀ events, CountEnvironment.PreparedContract a.solve.prepareFMI3 sigs events pool := by
    letI : StaticLiterals := ⟨fun _ => none⟩
    exact fun events => (queries inferInstance events).prepared pool made
  have nominals := nominalContract.runtime pool made
  have prepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
        unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made⟩
  refine ⟨compiled, build.numerical, DerivativeMetadata.artifact_derivatives _ _ build.metadata,
    CountMetadata.artifact_counts _ _ build.metadata, NominalMetadata.artifact_nominals _ _ build.metadata, sigs, pool, made, printed, functions, prepared, ?_⟩
  intro header objects literalBase firstBlock signed
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program config actual heap p clock reference final finalClock addresses buffer actions owners
    valid configured inPool represented readonly stored storage admitted requests policies
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
  have certified := trace_correct header objects a.solve.prepareFMI3 sigs pool prepared counts nominals literalBase firstBlock signed
    program config actual reset enterDefined exitDefined heap p clock reference final finalClock addresses buffer actions owners
    valid configured inPool represented readonly stored storage admitted requests policies
  refine ⟨certified, ?_, certified.progress, ?_⟩
  · intro observed after epochs executed
    obtain ⟨nextStored, nextReset, nextConfig, nextOwners, nextReadonly, frame⟩ := certified.completed executed
    obtain ⟨observations, checkpoints⟩ := certified.source a.solve executed
    exact ⟨nextStored, nextReset, nextConfig, nextOwners, nextReadonly, frame, observations, checkpoints⟩
  · intro stop interrupted
    exact certified.interrupted_source a.solve stored storage configured represented admitted interrupted

end Rumoca.FMI3.MEMixedRun
end
