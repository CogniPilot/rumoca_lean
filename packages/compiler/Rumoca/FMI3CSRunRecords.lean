import RumocaFMI3.CSRunRecordSemantics
import Rumoca.FMI3CSRun
import Rumoca.FMI3InitializationProtocol

noncomputable section
namespace Rumoca.FMI3.CSRun
open CMemory

variable {source : AST.Model} {model : Solve.Model source} {buffers : StepEntry.Buffers}

/-- A readable numerical sample and its bound against the unique source IVP
for this epoch. The time origin and selected initial value survive later resets. -/
structure SourceSample (source : AST.Model) (p : Address) (reference : Reference) (heap : Heap) : Prop where
  epoch : ∃! trajectory, SourceEpoch source reference trajectory
  sample : ∀ trajectory, SourceEpoch source reference trajectory →
    ∃ value : Binary64.Value, load heap (StateProofs.stateAddress p) = some (.finite value) ∧
      |Binary64.value value - trajectory (Binary64.value reference.current.time)| ≤
        (reference.current.elapsed : ℝ) +
          |Binary64.value reference.current.time -
            (Binary64.value reference.start + (reference.current.elapsed : ℝ))|

theorem Stored.source_sample {model : Solve.Model source}
    (stored : Stored model heap p buffers reference) : SourceSample source p reference heap :=
  ⟨source_epoch model reference, fun _ epoch => stored.source_observation epoch⟩

theorem Stored.restart_source_checkpoint {model : Solve.Model source}
    (stored : Stored model heap p buffers (.restart args)) :
    InitializationProtocol.SourceCheckpoint source p
      ⟨.initialized args, ⟨Binary64.positiveZero⟩, args.start⟩ heap := by
  have represented : StateProofs.Represents heap p ⟨Binary64.positiveZero⟩ := by
    simp [StateProofs.Represents, load, stored.state, Reference.restart, Solve.Model.run, Value.finite, convert]
  exact ⟨InitializationCalls.model_source_initialized source heap p args.start _
      model.dae.flat.resolved represented,
    fun _ initialized => InitializationCalls.source_initialized_unique initialized represented⟩

/-- Source observations annotate the very same returned call records. Only a
successful step promises public outputs. A restart retains all three returns
and its actual initialization-exit source checkpoint. -/
inductive SourceAction (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → Action → Int → List (CallRecord E) → Heap → Reference → Prop where
  | step {record : CallRecord E} : Change header p buffers before (.step request outputs) next record.status →
      SourceSample source p next record.heap → Observation buffers next (.step request outputs) record.status record.heap →
      SourceAction source header p buffers heap before (.step request outputs) record.status [record] record.heap next
  | restart {reset enter leave : CallRecord E} : args.Admissible →
      reset.status = 0 → enter.status = 0 → leave.status = 0 →
      reset.events = [] → enter.events = [] → leave.events = [] →
      InitializationProtocol.SourceCheckpoint source p
        ⟨.initialized args, ⟨Binary64.positiveZero⟩, args.start⟩ leave.heap →
      SourceSample source p (.restart args) leave.heap →
      SourceAction source header p buffers heap before (.restart args) leave.status
        [reset, enter, leave] leave.heap (.restart args)

inductive SourceTrace (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → List Action → List Int → List (CallRecord E) → Heap → Reference → Prop where
  | nil : SourceTrace source header p buffers heap reference [] [] [] heap reference
  | cons : SourceAction source header p buffers heap before action status records middle next →
      SourceTrace source header p buffers middle next rest statuses following after final →
      SourceTrace source header p buffers heap before (action :: rest) (status :: statuses) (records ++ following) after final

theorem SemanticAction.source_observations
    (semantic : SemanticAction model header p buffers heap before action status records after next) :
    SourceAction source header p buffers heap before action status records after next := by
  cases semantic with
  | step changed stored observed => exact .step changed stored.source_sample observed
  | restart admissible stored =>
    rename_i args
    refine SourceAction.restart
      (reset := ⟨0, [], Reset.finalHeap heap p⟩)
      (enter := ⟨0, [], InitializationEntry.finalHeap (Reset.finalHeap heap p) p args⟩)
      (leave := ⟨0, [], InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs⟩)
      admissible rfl rfl rfl rfl rfl rfl ?_ ?_
    · exact stored.restart_source_checkpoint
    · exact stored.source_sample

theorem SemanticTrace.source_observations
    (semantic : SemanticTrace model header p buffers heap before actions statuses records after final) :
    SourceTrace source header p buffers heap before actions statuses records after final := by
  induction semantic with
  | nil => exact .nil
  | cons action _ ih => exact .cons action.source_observations ih

end Rumoca.FMI3.CSRun
end
