import Rumoca.FMI3MENumericalRunObservations
import RumocaFMI3.MEFailureContracts
import RumocaFMI3.MEFailureRecovery
import RumocaFMI3.ResetEnvironment

noncomputable section
namespace Rumoca.FMI3.MEFailure
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory

theorem Recovery.source [CInterface] {source : AST.Model} {program : CCalls.Events.Program E}
    (model : Solve.Model source) (certified : Recovery program heap p args addresses buffer) :
    MENumericalRun.InitializedEpochs source p [(args, MENumericalHistory.restarted heap p args)] :=
  certified.calls.epochs_source model

/-- The raw recovery execution determines statuses and the actual initialized
checkpoint, and transfers source initialization to that observed checkpoint. -/
theorem Recovery.executed_source [CInterface] {source : AST.Model} {program : CCalls.Events.Program E}
    (model : Solve.Model source) (certified : Recovery program heap p args addresses buffer)
    (executed : MENumericalRun.Executed program p addresses buffer heap [.restart args] observed after epochs) :
    observed = ([none, none, none].map MENumericalHistory.Observation.ok) ∧
    after = MENumericalHistory.restarted heap p args ∧ epochs = [(args, after)] ∧
    MENumericalRun.InitializedEpochs source p epochs := by
  obtain ⟨values, memory, checkpoints⟩ := certified.determines executed
  refine ⟨values, memory, checkpoints, ?_⟩
  rw [checkpoints, memory]
  exact certified.source model

/-- The post-error guarantee retains storage and ownership and derives every
later reset/initialization call. It does not assign meaning to failed outputs. -/
structure Returned [CInterface] (source : AST.Model) (program : CCalls.Events.Program Invocation)
    (objects : Objects) (owners : SlotOwners.State objects.capacity) (heap after : Heap) (p : Address)
    (clock : Time.Clock) (reference : MENumericalHistory.ReferenceState)
    (addresses : String → Address) (buffer : Address) : Prop where
  stored : MENumericalHistory.Stored after p clock reference.failed addresses buffer
  resetStorage : Reset.Storage after p
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  readonly : CReadOnly.Preserves heap after
  frame : ∀ q, Protected objects addresses buffer q → q ≠ p.member "mode" → after q = heap q
  recovery : ∀ (args : Initialization.Arguments), args.Admissible →
    Recovery program after p args addresses buffer ∧
    MENumericalRun.InitializedEpochs source p [(args, MENumericalHistory.restarted after p args)] ∧
    SlotOwners.Represents objects.flagsBlock (MENumericalHistory.restarted after p args) owners

/-- The compiled artifact supplies all represented numerical/control errors
and recovery in one actual table/pool. Observed statuses and callback arguments
are derived from arbitrary completed target calls. Every modeled callback
outcome is retained, with a universal external frame and no presumed return. -/
theorem runtime_recovery (compiled : compile input = .ok a)
    (build : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    DerivativeMetadata.Contract a.parsed.ast metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      ∀ (header : CFenv.Header) (objects : Objects) (before : Heap) (firstBlock : Nat) (signed : Bool),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program Invocation),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 sigs →
          ∀ (request : Request) (heap : Heap) (p : Address) (clock : Time.Clock)
            (reference : MENumericalHistory.ReferenceState) (addresses : String → Address)
            (buffer : Address) (owners : SlotOwners.State objects.capacity),
          CReadOnly.Preserves (pool.install before firstBlock signed) heap →
          MENumericalHistory.Stored heap p clock reference addresses buffer → Reset.Storage heap p →
          p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
          request.Condition heap p .me reference.control.mode →
          ∃ category message,
            pool.addresses firstBlock "logStatus" = some category ∧
            pool.addresses firstBlock request.message = some message ∧
            Stored signed heap category "logStatus" ∧ Stored signed heap message request.message ∧
            request.Suppressed program heap ∧ request.Logged program category message heap signed ∧
            (∀ (logger : Option Address) (logging : Bool),
              load heap (p.member "logger") = some (.pointer logger) →
              load heap (p.member "logging") = some (boolean logging) → (logger = none ∨ logging = false) →
              ∀ events status after,
                (CCalls.Events.machine program).Behaves
                  (.calling (request.call p).1 (request.call p).2 heap .done) (.terminates events ⟨status, after⟩) →
                events = [] ∧ status = .integer 3 ∧
                Returned a.parsed.ast program objects owners heap after p clock reference addresses buffer) ∧
            (∀ (logger : Address) (environment : Option Address) (name : String)
              (effect : ReturningEffect (Logging.signature name)),
              program.addresses logger = some name →
              program.externals name = some (External.observed (Logging.signature name) effect) →
              Respects effect objects addresses buffer →
              load heap (p.member "logger") = some (.pointer (some logger)) →
              load heap (p.member "logging") = some (.integer 1) →
              load heap (p.member "environment") = some (.pointer environment) →
              ∀ events status after,
                (CCalls.Events.machine program).Behaves
                  (.calling (request.call p).1 (request.call p).2 heap .done) (.terminates events ⟨status, after⟩) →
                events = [⟨name, Logging.arguments environment category message⟩] ∧ status = .integer 3 ∧
                Returned a.parsed.ast program objects owners heap after p clock reference addresses buffer) := by
  obtain ⟨sigs, unique, resetMember, printed, _, functions, _, _, _, ready,
    _, _, _, _, states, derivative, _, _, initialization, _, _, _, _, time, entries, completed, discrete, _, _, _, evaluationContract⟩ := build.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  have prepared : MEEnvironment.PreparedContract a.solve.prepareFMI3 sigs pool :=
    ⟨StateEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique states.member made,
      DerivativeEnvironment.prepared_correct a.solve.prepareFMI3 sigs unique derivative.member derivative.numerical.fresh made,
      MEControlEnvironment.TimeControl.prepared_correct a.solve.prepareFMI3 sigs unique time.member made,
      fun entry => MEControlEnvironment.EntryControl.prepared_correct a.solve.prepareFMI3 entry sigs
        unique (entries entry).member made,
      MEControlEnvironment.CompletedControl.prepared_correct a.solve.prepareFMI3 sigs unique completed.member made,
      MEControlEnvironment.DiscreteControl.prepared_correct a.solve.prepareFMI3 sigs unique discrete.member made,
      evaluationContract.prepared pool made⟩
  refine ⟨compiled, build.numerical, DerivativeMetadata.artifact_derivatives _ _ build.metadata,
    sigs, pool, made, printed, functions, prepared, ?_⟩
  intro header objects before firstBlock signed
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program actual request heap p clock reference addresses buffer owners literalsPreserved stored storage inPool represented condition
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
  obtain ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, suppressed, logged⟩ :=
    request.prepared prepared header before firstBlock signed objects heap literalsPreserved
  have silent := suppressed Invocation program actual
  have enabled := logged program actual
  have recover (after : Heap) (nextStored : MENumericalHistory.Stored after p clock reference.failed addresses buffer)
      (nextReset : Reset.Storage after p) (nextOwners : SlotOwners.Represents objects.flagsBlock after owners)
      (readonly : CReadOnly.Preserves heap after)
      (frame : ∀ q, Protected objects addresses buffer q → q ≠ p.member "mode" → after q = heap q) :
      Returned a.parsed.ast program objects owners heap after p clock reference addresses buffer := by
    refine ⟨nextStored, nextReset, nextOwners, readonly, frame, ?_⟩
    intro args admissible
    have certified := Recovery.correct header objects literals a.solve.prepareFMI3 program reset enterDefined exitDefined
      after p clock reference.failed addresses buffer args nextStored nextReset admissible
    exact ⟨certified, certified.source a.solve, certified.owners nextOwners⟩
  refine ⟨category, message, categoryBound, messageBound, categoryStored, messageStored, silent, enabled, ?_, ?_⟩
  · intro logger logging loggerStored loggingStored quiet events status after executed
    have called := silent p .me reference.control.mode logger logging stored.control.kind stored.control.mode
      condition loggerStored loggingStored quiet
    have same := (called _).mp executed
    cases same
    exact ⟨rfl, rfl, recover _ stored.failed (stored.failed_reset storage)
      (SlotOwners.ordinary_preserves represented stored.failed_atomic)
      (CCalls.Events.termination_preserves executed)
      (fun q _ other => LifecycleBodies.write_frame heap p q .terminated other)⟩
  · intro logger environment name effect address external policy loggerStored loggingStored environmentStored
      events status after executed
    have called := enabled p logger environment .me reference.control.mode name effect address external
      stored.control.kind stored.control.mode condition loggerStored loggingStored environmentStored
    rcases (called.1 _).mp executed with ⟨value, next, outcome, same⟩ | ⟨_, impossible⟩
    · cases same
      obtain ⟨nextStored, nextReset, nextOwners, frame⟩ := policy.returned stored storage inPool represented outcome
      exact ⟨rfl, rfl, recover _ nextStored nextReset nextOwners (CCalls.Events.termination_preserves executed) frame⟩
    · cases impossible

end Rumoca.FMI3.MEFailure
end
