import RumocaFMI3.CSRunRestart

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

inductive Action where
  | step (request : CSHistory.Request) (outputs : StepEntry.Outputs)
  | restart (args : Initialization.Arguments)

/-- Source-level run progression and raw-call admission are stated without
any C heap or successful target execution. Restart denotes the three public
reset/enter-initialization/exit-initialization calls. -/
inductive Change (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Reference → Action → Reference → Int → Prop where
  | accepted {before : Reference} {request : CSHistory.Request} {after : CSHistory.ReferenceState} :
      before.mode = .step → CSHistory.Accepted before.stop before.current request after →
      Change header p buffers before (.step request buffers.outputs) (before.advance after) 0
  | rejected {before : Reference} {request : CSHistory.Request} {outputs : StepEntry.Outputs}
      (reason : StepRejections.Reason) : BufferSelection outputs buffers →
      StepCases.Condition (before.query header p request outputs header.nearest) reason.outcome →
      Change header p buffers before (.step request outputs) (before.reject reason) (StepRejections.status reason)
  | restart {before : Reference} {args : Initialization.Arguments} : args.Admissible →
      Change header p buffers before (.restart args) (Reference.restart args) 0

inductive ReferenceTrace (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Reference → List Action → Reference → List Int → Prop where
  | nil : ReferenceTrace header p buffers reference [] reference []
  | cons {before next final : Reference} {action : Action} {rest : List Action} {status : Int} {statuses : List Int} :
      Change header p buffers before action next status → ReferenceTrace header p buffers next rest final statuses →
      ReferenceTrace header p buffers before (action :: rest) final (status :: statuses)

/-- Successful DoStep exposes all four outputs to the importer. FMI leaves
error/discard outputs undefined; restart has no corresponding output buffers. -/
def Observation (buffers : StepEntry.Buffers) (reference : Reference) (action : Action)
    (status : Int) (heap : Heap) : Prop :=
  match action with
  | .step _ _ => status = 0 → CSHistory.Outputs heap buffers reference.current.time
  | .restart _ => True

theorem change_step_total (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (before : Reference) (request : CSHistory.Request) (outputs : StepEntry.Outputs)
    (selection : BufferSelection outputs buffers) :
    ∃ after status, Change header p buffers before (.step request outputs) after status := by
  rcases StepCalls.outcome_cases (before.query header p request outputs header.nearest) with invalid | accepted | ⟨reason, rejected⟩
  · simp [StepCases.Condition, Reference.query] at invalid
  · have mode : before.mode = .step := accepted.1.2.1.2
    have complete : outputs = buffers.outputs := selection.resolve_left accepted.1.2.2.1
    subst outputs
    have same : before.query header p request buffers.outputs header.nearest =
        request.query header p buffers before.current before.stop := by
      simp [Reference.query, CSHistory.Request.query, mode]
    rw [same] at accepted
    obtain ⟨after, next⟩ := CSHistory.accepted_of_case header p buffers accepted
    exact ⟨before.advance after, 0, .accepted mode next⟩
  · exact ⟨before.reject reason, StepRejections.status reason, .rejected reason selection rejected⟩

/-- These fields include logger configuration, callback environment and slot
metadata. Every admitted internal run action retains their exact cells. -/
def Retains (p : Address) (before after : Heap) : Prop :=
  ∀ name, name ∉ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"] →
    after (p.member name) = before (p.member name)

theorem Retains.trans (first : Retains p before middle) (second : Retains p middle after) :
    Retains p before after := fun name retained => (second name retained).trans (first name retained)

def Suppressed (heap : Heap) (p : Address) : Prop :=
  ∃ (logger : Option Address) (logging : Bool),
    load heap (p.member "logger") = some (.pointer logger) ∧
    load heap (p.member "logging") = some (boolean logging) ∧ (logger = none ∨ logging = false)

theorem Retains.suppressed (retains : Retains p before after) (quiet : Suppressed before p) : Suppressed after p := by
  obtain ⟨logger, logging, loggerValue, loggingValue, suppressed⟩ := quiet
  exact ⟨logger, logging, by simpa only [load, retains "logger" (by simp)] using loggerValue,
    by simpa only [load, retains "logging" (by simp)] using loggingValue, suppressed⟩

theorem advance_retains (stored : Stored model heap p buffers reference) (after : CSHistory.ReferenceState) :
    Retains p heap (CSHistory.written model reference.seed heap p buffers reference.current after) := by
  intro name retained
  exact CSHistory.written_frame model reference.seed heap p buffers reference.current after (p.member name)
    (CSHistory.field_outside stored.buffers name (by intro same; simp [same] at retained))

theorem reject_retains (stored : Stored model heap p buffers reference)
    (header : CFenv.Header) (request : CSHistory.Request) (outputs : StepEntry.Outputs)
    (observed : Int) (reason : StepRejections.Reason) (selection : BufferSelection outputs buffers)
    (selected : StepCases.Condition (reference.query header p request outputs observed) reason.outcome) :
    Retains p heap (StepRejections.afterHeap reason (reference.query header p request outputs observed) heap p) := by
  intro name retained
  exact StepRejections.after_frame reason _ heap p
    (stored.rejection_reads header request outputs observed reason selection selected) selected (p.member name) rfl
    (by intro same; have names := (Address.member_inj _ _ _).mp same; simp [names] at retained)

theorem restart_retains (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    Retains p heap (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) := by
  intro name retained
  have different (field : String) (member : field ∈ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]) :
      p.member name ≠ p.member field := by
    intro same
    have names := (Address.member_inj _ _ _).mp same
    exact retained (names ▸ member)
  exact (InitializationCalls.exited_frame _ p (p.member name) args .cs
    (different "time" (by simp)) (different "timeMin" (by simp))
    (different "eventTime" (by simp)) (different "lastCompleted" (by simp))
    (different "stop" (by simp)) (different "stopDefined" (by simp)) (different "mode" (by simp))).trans
    (Reset.retained_field heap p name retained)

/-- Every public invocation carries an all-behavior contract. The relation
retains exact intermediate reset/initialization heaps as well as step status. -/
inductive Executed [CInterface] (program : Events.Program E) (p : Address) :
    Heap → Action → Heap → Int → Prop where
  | step {before after : Heap} {request : CSHistory.Request} {outputs : StepEntry.Outputs} {status : Int} :
      (∀ behavior, (Events.machine program).Behaves
        (.calling StepEntry.signature.name (StepEntry.arguments (some p) request.point request.step request.flag outputs) before .done) behavior ↔
        behavior = .terminates [] ⟨.integer status, after⟩) →
      Executed program p before (.step request outputs) after status
  | restart {before : Heap} {args : Initialization.Arguments} :
      (∀ behavior, (Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer (some p)] before .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, Reset.finalHeap before p⟩) →
      (∀ behavior, (Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) (Reset.finalHeap before p) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap (Reset.finalHeap before p) p args⟩) →
      (∀ behavior, (Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p))
          (InitializationEntry.finalHeap (Reset.finalHeap before p) p args) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, InitializationCalls.exitedHeap (Reset.finalHeap before p) p args .cs⟩) →
      Executed program p before (.restart args) (InitializationCalls.exitedHeap (Reset.finalHeap before p) p args .cs) 0

theorem Executed.readonly {E : Type} [CInterface] {program : Events.Program E}
    (executed : Executed program p before action after status) :
    CReadOnly.Preserves before after := by
  cases executed with
  | step called => exact Events.termination_preserves ((called _).mpr rfl)
  | restart reset enter leave =>
    exact (Events.termination_preserves ((reset _).mpr rfl)).trans
      ((Events.termination_preserves ((enter _).mpr rfl)).trans
        (Events.termination_preserves ((leave _).mpr rfl)))

end Rumoca.FMI3.CSRun
end
