import RumocaFMI3.CSHistory
import RumocaFMI3.StepRecovery

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The active source epoch is separate from the rounded communication clock
and the discrete solver duration. A rejection changes only the lifecycle mode;
reset and reinitialization establish a new epoch. -/
structure Reference where
  seed : Binary64.Value
  start : Binary64.Value
  current : CSHistory.ReferenceState
  stop : Option Binary64.Value
  mode : Mode

def Reference.advance (reference : Reference) (after : CSHistory.ReferenceState) : Reference :=
  { reference with current := after }

def Reference.reject (reference : Reference) (reason : StepRejections.Reason) : Reference :=
  { reference with mode := StepRejections.nextMode reason reference.mode }

def Reference.restart (args : Initialization.Arguments) : Reference :=
  ⟨Binary64.positiveZero, args.start, ⟨args.start, 0⟩, args.stopTime, .step⟩

/-- Persistent instance and caller storage, including the cells needed by
reset after an error. The state remains meaningful even outside Step Mode. -/
structure Stored (model : Solve.Model source) (heap : Heap) (p : Address)
    (buffers : StepEntry.Buffers) (reference : Reference) : Prop where
  kind : load heap (p.member "kind") = some (.integer 1)
  mode : load heap (p.member "mode") = some (.integer reference.mode.code)
  clock : heap (p.member "time") = some ⟨.float64, true, some (.finite reference.current.time)⟩
  state : heap (StateProofs.stateAddress p) =
    some ⟨.float64, true, some (.finite (model.run reference.seed reference.current.elapsed))⟩
  stopDefined : load heap (p.member "stopDefined") = some (boolean reference.stop.isSome)
  stopValue : ∀ limit, reference.stop = some limit → load heap (p.member "stop") = some (.finite limit)
  reset : Reset.Storage heap p
  buffers : StepArguments.Storage heap p buffers

theorem Stored.step_mode {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference)
    (mode : reference.mode = .step) :
    CSHistory.Stored model reference.seed heap p buffers reference.current reference.stop :=
  ⟨stored.kind, by simpa only [mode, Mode.code] using stored.mode, stored.clock,
    stored.state, stored.stopDefined, stored.stopValue, stored.buffers⟩

/-- Numerical writes preserve all reset-only fields. This supplies recovery
storage after any number of accepted steps. -/
theorem Stored.advance {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference)
    (mode : reference.mode = .step) (after : CSHistory.ReferenceState) :
    Stored model (CSHistory.written model reference.seed heap p buffers reference.current after)
      p buffers (reference.advance after) := by
  have old := stored.step_mode mode
  obtain ⟨next, _⟩ := CSHistory.written_stored old after
  have field (name : String) (other : name ≠ "time") (type : CType)
      (writable : Reset.Writable heap (p.member name) type) :
      Reset.Writable (CSHistory.written model reference.seed heap p buffers reference.current after)
        (p.member name) type := by
    obtain ⟨value, found⟩ := writable
    exact ⟨value, (CSHistory.written_frame model reference.seed heap p buffers reference.current after (p.member name)
      (CSHistory.field_outside stored.buffers name other)).trans found⟩
  refine ⟨next.kind, ?_, next.clock, next.state, next.stopDefined, next.stopValue,
    ⟨⟨_, next.state⟩, ⟨_, next.clock⟩,
      field "timeMin" (by decide) _ stored.reset.minimum,
      field "eventTime" (by decide) _ stored.reset.event,
      field "lastCompleted" (by decide) _ stored.reset.completed,
      field "stop" (by decide) _ stored.reset.stop,
      field "stopDefined" (by decide) _ stored.reset.stopDefined,
      field "mode" (by decide) _ stored.reset.mode⟩, next.buffers⟩
  simpa only [Reference.advance, mode, Mode.code] using next.mode

/-- The caller may omit outputs to exercise the public missing-pointer path.
When all four are supplied they use the persistent typed buffer bank. -/
def BufferSelection (outputs : StepEntry.Outputs) (buffers : StepEntry.Buffers) : Prop :=
  StepArguments.MissingOutput outputs ∨ outputs = buffers.outputs

def Reference.query (reference : Reference) (header : CFenv.Header) (p : Address)
    (request : CSHistory.Request) (outputs : StepEntry.Outputs) (observed : Int) : StepCases.Query :=
  ⟨some p, .cs, reference.mode, outputs, request.point, request.step,
    reference.current.time, reference.stop, observed, header⟩

theorem Stored.rejection_reads {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference)
    (header : CFenv.Header) (request : CSHistory.Request) (outputs : StepEntry.Outputs)
    (observed : Int) (reason : StepRejections.Reason)
    (selection : BufferSelection outputs buffers)
    (selected : StepCases.Condition (reference.query header p request outputs observed) reason.outcome) :
    StepRejections.Reads reason (reference.query header p request outputs observed) heap p := by
  constructor
  · exact stored.kind
  · exact stored.mode
  · intro _
    simp [Reference.query, load, stored.clock, Value.finite, convert]
  · intro writes other chosen
    have same : outputs = buffers.outputs := selection.resolve_left (by
      intro missing
      obtain ⟨present, bound⟩ := StepRejections.buffers_present reason _ selected writes
      change outputs = present.outputs at bound
      simp [bound, StepArguments.MissingOutput, StepEntry.Buffers.outputs] at missing)
    have equal : buffers = other := by
      cases buffers
      cases other
      simpa [Reference.query, same, StepEntry.Buffers.outputs] using chosen
    subst other
    exact stored.buffers
  · intro _
    exact stored.stopDefined
  · intro _
    exact stored.stopValue

/-- Caller outputs retain their writable types after every classified
rejection, including Boolean aliases and the no-output-write branches. -/
theorem rejection_buffers (stored : StepArguments.Storage heap p buffers)
    (reason : StepRejections.Reason) (query : StepCases.Query)
    (selection : BufferSelection query.outputs buffers)
    (selected : StepCases.Condition query reason.outcome) :
    StepArguments.Storage (StepRejections.afterHeap reason query heap p) p buffers := by
  have before : StepArguments.Storage (StepRejections.beforeHeap reason query heap) p buffers := by
    by_cases writes : reason.writesOutputs = true
    · have same : query.outputs = buffers.outputs := selection.resolve_left (by
        intro missing
        obtain ⟨present, bound⟩ := StepRejections.buffers_present reason query selected writes
        simp [bound, StepArguments.MissingOutput, StepEntry.Buffers.outputs] at missing)
      obtain ⟨old, last⟩ := stored.last
      obtain ⟨event, terminate, early, output⟩ := StepEntry.output_values heap buffers query.time old
        stored.event stored.terminate stored.early last
      simp only [StepRejections.beforeHeap, writes, ↓reduceIte,
        StepRejections.outputHeap_of_buffers query heap buffers same]
      exact ⟨⟨_, event⟩, ⟨_, terminate⟩, ⟨_, early⟩, ⟨_, output⟩,
        stored.outsideEvent, stored.outsideTerminate, stored.outsideEarly, stored.outsideLast⟩
    · simpa only [StepRejections.beforeHeap, writes, Bool.false_eq_true, ↓reduceIte] using stored
  have kept (address : Address) (outside : address.block ≠ p.block) :
      StepRejections.afterHeap reason query heap p address = StepRejections.beforeHeap reason query heap address := by
    unfold StepRejections.afterHeap
    split
    · rfl
    · exact LifecycleBodies.write_frame _ p address .terminated (by
        intro same
        have blocks : address.block = (p.member "mode").block := congrArg Address.block same
        exact outside blocks)
  refine ⟨?_, ?_, ?_, ?_, stored.outsideEvent, stored.outsideTerminate, stored.outsideEarly, stored.outsideLast⟩
  · obtain ⟨value, found⟩ := before.event
    exact ⟨value, (kept _ stored.outsideEvent).trans found⟩
  · obtain ⟨value, found⟩ := before.terminate
    exact ⟨value, (kept _ stored.outsideTerminate).trans found⟩
  · obtain ⟨value, found⟩ := before.early
    exact ⟨value, (kept _ stored.outsideEarly).trans found⟩
  · obtain ⟨value, found⟩ := before.last
    exact ⟨value, (kept _ stored.outsideLast).trans found⟩

theorem Stored.reject {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference)
    (header : CFenv.Header) (request : CSHistory.Request) (outputs : StepEntry.Outputs)
    (observed : Int) (reason : StepRejections.Reason)
    (selection : BufferSelection outputs buffers)
    (selected : StepCases.Condition (reference.query header p request outputs observed) reason.outcome) :
    Stored model (StepRejections.afterHeap reason (reference.query header p request outputs observed) heap p)
      p buffers (reference.reject reason) := by
  have reads := stored.rejection_reads header request outputs observed reason selection selected
  have field (name : String) (other : name ≠ "mode") :
      load (StepRejections.afterHeap reason (reference.query header p request outputs observed) heap p)
        (p.member name) = load heap (p.member name) := by
    simp only [load, StepRejections.after_frame reason _ heap p reads selected (p.member name) rfl (by simpa using other)]
  exact ⟨StepRejections.after_kind reason _ heap p reads selected,
    StepRejections.after_mode reason _ heap p reads selected,
    (StepRejections.after_frame reason _ heap p reads selected (p.member "time") rfl (by simp)).trans stored.clock,
    (StepRejections.after_frame reason _ heap p reads selected (StateProofs.stateAddress p) rfl
      (HistoryBodies.state_ne_field p "mode")).trans stored.state,
    (field "stopDefined" (by decide)).trans stored.stopDefined,
    fun limit chosen => (field "stop" (by decide)).trans (stored.stopValue limit chosen),
    StepRejections.after_reset_storage reason _ heap p reads selected stored.reset,
    rejection_buffers stored.buffers reason _ selection selected⟩

end Rumoca.FMI3.CSRun
end
