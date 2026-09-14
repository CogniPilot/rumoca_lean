import Rumoca.FMI3Restart
import RumocaFMI3.StepRecovery

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory

/-- The actual required CS contract and reset/initialization definitions
jointly certify every suppressed rejection followed by recovery. The initial
heap supplies storage; no post-error heap or successful execution is assumed. -/
theorem adapter_suppressed_recovery (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (query : StepCases.Query) (objects : Objects) (before : Heap) (firstBlock : Nat)
        (signed : Bool) (heap : Heap),
      CReadOnly.Preserves (pool.install before firstBlock signed) heap →
      letI : CInterface := RuntimeEnvironment.interface query.header objects (pool.addresses firstBlock)
      ∀ (E : Type) (program : CCalls.Events.Program E) (reason : StepRejections.Reason)
        (p : Address) (flag : Bool) (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31)
        (logger : Option Address) (logging : Bool) (args : Initialization.Arguments),
      program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
      (reason.observesRounding = true → program.externals "fegetround" =
        some (CMathCalls.roundingExternal rfl query.observed range)) →
      (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
      query.handle = some p → StepRejections.Reads reason query heap p →
      StepCases.Condition query reason.outcome → Reset.Storage heap p →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → args.Admissible →
      (∀ behavior, (CCalls.Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
        behavior = .terminates [] ⟨.integer (StepRejections.status reason), StepRejections.afterHeap reason query heap p⟩) ∧
      Restarted a program (StepRejections.afterHeap reason query heap p) p query.kind args := by
  obtain ⟨signatures, unique, member, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro query objects before firstBlock signed heap literalFrame
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro E program reason p flag range logger logging args actual rounding floorBound
    handle reads selected storage loggerValue loggingValue suppressed admissible
  obtain ⟨_, _, _, _, _, _, rejected, _⟩ :=
    (step.prepared pool made).rejections query before firstBlock signed objects heap literalFrame
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct query.header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ member
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  exact ⟨rejected E program reason p flag range logger logging actual rounding floorBound handle reads selected
    (fun _ => storage.mode) loggerValue loggingValue suppressed,
    restart_correct a query.header objects literals program _ p query.kind (StepRejections.nextMode reason query.mode)
      args reset enterDefined exitDefined (StepRejections.after_reset_storage reason query heap p reads selected storage)
      (StepRejections.after_kind reason query heap p reads selected)
      (StepRejections.after_mode reason query heap p reads selected) admissible⟩

/-- Logging retains all modeled outcomes, including no returning outcome.
Recovery is derived for each returning callback that preserves the instance
record. This conditional frame is not a proof of native callback behavior. -/
theorem adapter_logged_recovery (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (query : StepCases.Query) (objects : Objects) (before : Heap) (firstBlock : Nat)
        (signed : Bool) (heap : Heap),
      CReadOnly.Preserves (pool.install before firstBlock signed) heap →
      ∃ (category : Address) (messages : StepRejections.Reason → Address),
      pool.addresses firstBlock "logStatus" = some category ∧
      (∀ reason : StepRejections.Reason, pool.addresses firstBlock reason.message = some (messages reason)) ∧
      letI : CInterface := RuntimeEnvironment.interface query.header objects (pool.addresses firstBlock)
      ∀ (program : CCalls.Events.Program CCalls.Events.Invocation) (reason : StepRejections.Reason)
        (p logger : Address) (flag : Bool) (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31)
        (environment : Option Address) (name : String)
        (effect : CCalls.Events.ReturningEffect (Logging.signature name)) (args : Initialization.Arguments),
      program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
      (reason.observesRounding = true → program.externals "fegetround" =
        some (CMathCalls.roundingExternal rfl query.observed range)) →
      (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
      program.addresses logger = some name →
      program.externals name = some (CCalls.Events.External.observed (Logging.signature name) effect) →
      query.handle = some p → StepRejections.Reads reason query heap p →
      StepCases.Condition query reason.outcome → Reset.Storage heap p →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → args.Admissible →
      (∀ behavior, (CCalls.Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
        (∃ value after, effect.execute (StepRejections.arguments reason environment category (messages reason))
          (StepRejections.afterHeap reason query heap p) value after ∧
          behavior = .terminates [⟨name, StepRejections.arguments reason environment category (messages reason)⟩]
            ⟨.integer (StepRejections.status reason), after⟩) ∨
        ((∀ value after, ¬ effect.execute (StepRejections.arguments reason environment category (messages reason))
          (StepRejections.afterHeap reason query heap p) value after) ∧ behavior = .wrong [])) ∧
      (∀ value after, effect.execute (StepRejections.arguments reason environment category (messages reason))
        (StepRejections.afterHeap reason query heap p) value after →
        (CLiteral.Stored signed after category "logStatus" ∧
          ∀ other : StepRejections.Reason, CLiteral.Stored signed after (messages other) other.message) ∧
        ((∀ address, p.InRecord address → after address = StepRejections.afterHeap reason query heap p address) →
          Restarted a program after p query.kind args)) := by
  obtain ⟨signatures, unique, member, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, initialization, _, _, _, _, _, _, _, _, step⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro query objects before firstBlock signed heap literalFrame
  let literals := pool.addresses firstBlock
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  obtain ⟨category, messages, categoryBound, messageBound, _, _, _, logged⟩ :=
    (step.prepared pool made).rejections query before firstBlock signed objects heap literalFrame
  refine ⟨category, messages, categoryBound, messageBound, ?_⟩
  intro program reason p logger flag range environment name effect args actual rounding floorBound
    address external handle reads selected storage loggerValue loggingValue environmentValue admissible
  have reset : StaticReset.ExecutionContract program := by
    apply ResetEnvironment.execution_correct query.header objects literals a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ member
  have enterDefined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) := by
    rw [actual, ← InitializationCalls.function_eq a.solve.prepareFMI3]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.enterMember
  have exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound _ signatures unique _ initialization.exitMember
  obtain ⟨called, immutable⟩ := logged program reason p logger flag range environment name effect actual rounding floorBound
    address external handle reads selected (fun _ => storage.mode) loggerValue loggingValue environmentValue
  refine ⟨called, ?_⟩
  intro value after executed
  refine ⟨immutable value after executed, ?_⟩
  intro callbackFrame
  have kindAfter : load after (p.member "kind") = some (.integer query.kind.code) := by
    simpa only [load, callbackFrame _ (p.member_in_record "kind")] using
      StepRejections.after_kind reason query heap p reads selected
  have modeAfter : load after (p.member "mode") = some (.integer (StepRejections.nextMode reason query.mode).code) := by
    simpa only [load, callbackFrame _ (p.member_in_record "mode")] using
      StepRejections.after_mode reason query heap p reads selected
  exact restart_correct a query.header objects literals program after p query.kind (StepRejections.nextMode reason query.mode)
    args reset enterDefined exitDefined
    ((StepRejections.after_reset_storage reason query heap p reads selected storage).record_preserved callbackFrame)
    kindAfter modeAfter admissible

end Rumoca.FMI3
end
