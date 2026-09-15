import RumocaFMI3.CSMixedRecords
import Rumoca.FMI3CSRunRecords

noncomputable section
namespace Rumoca.FMI3.CSMixedRun
open CTree CMemory CBody StaticFactory CCalls.Events

/-- Source consequences annotate the exact mixed call records. The numerical
case reuses the established CS source actions and all three restart returns. -/
inductive SourceAction (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → CSRun.Reference → Action → Value → List CallRecord → Heap → CSRun.Reference → Prop where
  | run {before next : CSRun.Reference} : CSRun.SourceAction source header p buffers heap before action status records after next →
      SourceAction source header p buffers heap before (.run action) (.integer status) (records.map runRecord) after next
  | logging : CSLoggingCalls.CorrectObservation request events status →
      CSRun.SourceSample source p (CSLoggingCalls.next request before) after →
      InitializationProtocol.Retention request.loggingUpdate p heap after →
      SourceAction source header p buffers heap before (.logging request) status [(events, ⟨status, after⟩)]
        after (CSLoggingCalls.next request before)

inductive SourceTrace (source : AST.Model) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → CSRun.Reference → List Action → List Value → List CallRecord → Heap → CSRun.Reference → Prop where
  | nil : SourceTrace source header p buffers heap reference [] [] [] heap reference
  | cons {before next final : CSRun.Reference} :
      SourceAction source header p buffers heap before action status records middle next →
      SourceTrace source header p buffers middle next rest statuses following after final →
      SourceTrace source header p buffers heap before (action :: rest) (status :: statuses) (records ++ following) after final

theorem Trace.recorded_source [CInterface] {program : Program Invocation}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {capability : Logging.Capability}
    {model : Solve.Model source}
    (certified : Trace header objects owners model capability program p buffers heap enabled before actions final statuses)
    (recorded : Recorded program p heap actions observed events after records) :
    SourceTrace source header p buffers heap before actions observed records after final := by
  induction recorded generalizing enabled before final statuses with
  | nil => cases certified; exact .nil
  | cons head _ ih => cases certified with
    | cons changed called returned following =>
      have outcome := called.returned head.performed
      have post := returned _ _ _ outcome
      refine .cons ?_ (ih (following _ _ _ outcome))
      cases head with
      | run actual => cases changed with
        | run transition =>
          exact .run (called.run_recorded transition returned actual).source_observations
      | logging actual => cases changed with
        | logging => exact .logging post.observed.2 post.stored.source_sample post.retention

end Rumoca.FMI3.CSMixedRun
end
