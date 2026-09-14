import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.StepEntry

/-! Complete public CS lifecycle rejection in each checked error context.
Other admission failures, discard paths and public histories remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StepErrors
open CTree CMemory CBody
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem types (context : ErrorContext literals) : @StepEntry.Types context.target := by
  letI : CInterface := context.target
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [← context.types] <;> rfl

/-- Rejected lifecycle calls reach failure before touching any output buffer.
Every raw numerical argument and nullable output pointer is covered. -/
theorem lifecycle_prefix (context : ErrorContext literals) (model : Solve.FMI3Model source)
    (heap : Heap) (p : Address) (point step : BitVec 64) (flag : Bool)
    (outputs : StepEntry.Outputs) (kind : Kind) (mode : Mode)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .doStep kind mode) :
    @GuardedCalls.FailurePrefix context.target (Runtime.function model StepEntry.signature)
      (StepEntry.arguments (some p) point step flag outputs) heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := context.target
  let env := StepEntry.parameters (some p) point step flag outputs
  let later := StepEntry.locals env p
  let rest := StepEntry.outputCode ++ StepEntry.inputGuard :: Runtime.doStep.drop 9
  have rejected : allowed .doStep kind mode = false :=
    Bool.eq_false_iff.mpr (fun admitted => denied ((allowed_correct .doStep kind mode).mp admitted))
  refine ⟨rfl, BodyEmbedding.body_closed model StepEntry.signature,
    env, later, rest, 3, StepEntry.parameters_bound (types context) _ _ _ _ _, ?_, ?_, ?_⟩
  · have ran := StepEntry.lifecycle_run (types context) env heap p kind mode rest
      (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [env, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    change run 3 (.running (Runtime.body model StepEntry.signature) env heap) = _
    rw [StepEntry.body, List.append_assoc]
    simpa only [rejected, Bool.false_eq_true, ↓reduceIte, List.singleton_append] using ran
  · simp [later, StepEntry.locals, env, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  · simp [later, StepEntry.locals, CBody.bind, resolve]

theorem lifecycle_suppressed {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message : Address)
      (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
      (kind : Kind) (mode : Mode) (logger : Option Address) (logging : Bool),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message →
      load heap (p.member "kind") = some (.integer kind.code) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      ¬ Reference.Allowed .doStep kind mode → (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := context.target
  intro program heap p message point step flag outputs kind mode logger logging
    defined helper messageBound kindValue modeCell loggerValue loggingValue denied suppressed behavior
  have modeValue : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, modeCell, convert, Mode.code]
  exact StaticErrors.prefix_suppressed_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message ErrorCalls.rejectionMessage
    _ logger logging
    (lifecycle_prefix context model heap p point step flag outputs kind mode kindValue modeValue denied)
    defined helper messageBound modeCell loggerValue loggingValue suppressed behavior

theorem lifecycle_logged {E : Type} (context : ErrorContext literals) (model : Solve.FMI3Model source) :
    letI : CInterface := context.target
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p message category logger : Address)
      (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
      (kind : Kind) (mode : Mode) (environment : Option Address) (name : String)
      (foreign : CCalls.Events.External E),
      program.internal.definitions StepEntry.signature.name =
        some (.tree (Runtime.function model StepEntry.signature)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals ErrorCalls.rejectionMessage = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap (p.member "kind") = some (.integer kind.code) →
      heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      ¬ Reference.Allowed .doStep kind mode → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after ∧
        behavior = .terminates events ⟨.integer 3, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category message)
        (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := context.target
  intro program heap p message category logger point step flag outputs kind mode environment name foreign
    defined helper messageBound categoryBound address external prototype kindValue modeCell
    loggerValue loggingValue environmentValue denied behavior
  have modeValue : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, modeCell, convert, Mode.code]
  exact StaticErrors.prefix_all_behaviors context program (Runtime.function model StepEntry.signature)
    (StepEntry.arguments (some p) point step flag outputs) heap heap p message category logger
    ErrorCalls.rejectionMessage name environment _ foreign
    (lifecycle_prefix context model heap p point step flag outputs kind mode kindValue modeValue denied)
    defined helper messageBound address external prototype categoryBound modeCell loggerValue
    loggingValue environmentValue behavior

end Rumoca.FMI3.StepErrors
end
