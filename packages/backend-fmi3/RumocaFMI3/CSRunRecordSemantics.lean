import RumocaFMI3.CSRunRecords

noncomputable section
namespace Rumoca.FMI3.CSRun
open CMemory StaticFactory CCalls.Events

/-- Reference transitions and output contracts attached to the exact raw
call records. Restart records expose its real initialization exit checkpoint. -/
inductive SemanticAction (model : Solve.Model source) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → Action → Int → List (CallRecord E) → Heap → Reference → Prop where
  | step {record : CallRecord E} : Change header p buffers before (.step request outputs) next record.status →
      Stored model record.heap p buffers next → Observation buffers next (.step request outputs) record.status record.heap →
      SemanticAction model header p buffers heap before (.step request outputs) record.status [record] record.heap next
  | restart {heap : Heap} {args : Initialization.Arguments} : args.Admissible →
      Stored model (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) p buffers (.restart args) →
      SemanticAction model header p buffers heap before (.restart args) 0
        [⟨0, [], Reset.finalHeap heap p⟩,
          ⟨0, [], InitializationEntry.finalHeap (Reset.finalHeap heap p) p args⟩,
          ⟨0, [], InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs⟩]
        (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) (.restart args)

inductive SemanticTrace (model : Solve.Model source) (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers) :
    Heap → Reference → List Action → List Int → List (CallRecord E) → Heap → Reference → Prop where
  | nil : SemanticTrace model header p buffers heap reference [] [] [] heap reference
  | cons : SemanticAction model header p buffers heap before action status records middle next →
      SemanticTrace model header p buffers middle next rest statuses following after final →
      SemanticTrace model header p buffers heap before (action :: rest) (status :: statuses) (records ++ following) after final

theorem SemanticAction.change
    (semantic : SemanticAction model header p buffers heap before action status records after next) :
    Change header p buffers before action next status := by
  cases semantic with
  | step changed _ _ => exact changed
  | restart admissible _ => exact .restart admissible

theorem SemanticTrace.reference
    (semantic : SemanticTrace model header p buffers heap before actions statuses records after final) :
    ReferenceTrace header p buffers before actions final statuses := by
  induction semantic with
  | nil => exact .nil
  | cons action _ ih => exact .cons action.change ih

/-- Complete silent call contracts determine every recorded return, not just
the final heap. The reference/output proofs annotate those very records. -/
theorem Executed.recorded_correct [CInterface] {program : Program E}
    (certified : Executed program p heap action after status)
    (changed : Change header p buffers before action next status)
    (stored : Stored model after p buffers next)
    (observed : Observation buffers next action status after)
    (actual : RecordedAction program p heap action observedStatus events actualAfter records) :
    observedStatus = status ∧ events = [] ∧ actualAfter = after ∧
      SemanticAction model header p buffers heap before action observedStatus records actualAfter next := by
  cases actual with
  | step performed =>
    cases performed with
    | step called =>
      cases certified with
      | step expected =>
        cases (expected _).mp called
        exact ⟨rfl, rfl, rfl, .step (record := (⟨status, [], after⟩ : CallRecord E)) changed stored observed⟩
  | restart resetCall enterCall exitCall =>
    cases certified with
    | restart reset enter leave =>
      cases (reset _).mp resetCall
      cases (enter _).mp enterCall
      cases (leave _).mp exitCall
      cases changed with
      | restart admissible => exact ⟨rfl, rfl, rfl, .restart admissible stored⟩

end Rumoca.FMI3.CSRun
end
