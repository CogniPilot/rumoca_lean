import RumocaFMI3.CSRunTransition

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory CCalls

def Outside (p : Address) (buffers : StepEntry.Buffers) (query : Address) : Prop :=
  ¬ p.InRecord query ∧ query ≠ buffers.event ∧ query ≠ buffers.terminate ∧
    query ≠ buffers.early ∧ query ≠ buffers.last

theorem Outside.field (outside : Outside p buffers query) (name : String) : query ≠ p.member name := by
  intro same
  exact outside.1 (same ▸ p.member_in_record name)

theorem Outside.cs (outside : Outside p buffers query) : CSHistory.Outside p buffers query := by
  refine ⟨?_, outside.field "time", outside.2⟩
  intro same
  exact outside.1 (same ▸ (p.member_in_record "model").member "x")

theorem rejection_frame (reason : StepRejections.Reason) (query : StepCases.Query) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (selection : BufferSelection query.outputs buffers)
    (selected : StepCases.Condition query reason.outcome) (address : Address) (outside : Outside p buffers address) :
    StepRejections.afterHeap reason query heap p address = heap address := by
  have before : StepRejections.beforeHeap reason query heap address = heap address := by
    by_cases writes : reason.writesOutputs = true
    · have complete : query.outputs = buffers.outputs := selection.resolve_left (by
        intro missing
        obtain ⟨present, bound⟩ := StepRejections.buffers_present reason query selected writes
        simp [bound, StepArguments.MissingOutput, StepEntry.Buffers.outputs] at missing)
      simp only [StepRejections.beforeHeap, writes, ↓reduceIte,
        StepRejections.outputHeap_of_buffers query heap buffers complete]
      exact StepEntry.output_frame heap buffers query.time address outside.2.1 outside.2.2.1 outside.2.2.2.1 outside.2.2.2.2
    · simp [StepRejections.beforeHeap, writes]
  unfold StepRejections.afterHeap
  split
  · exact before
  · exact (LifecycleBodies.write_frame _ p address .terminated (outside.field "mode")).trans before

theorem initialize_frame (heap : Heap) (p query : Address) (args : Initialization.Arguments)
    (outside : ¬ p.InRecord query) : InitializationCalls.exitedHeap heap p args .cs query = heap query := by
  have different (name : String) : query ≠ p.member name := by
    intro same
    exact outside (same ▸ p.member_in_record name)
  exact InitializationCalls.exited_frame heap p query args .cs (different "time") (different "timeMin")
    (different "eventTime") (different "lastCompleted") (different "stop") (different "stopDefined") (different "mode")

theorem initialize_retains (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    Retains p heap (InitializationCalls.exitedHeap heap p args .cs) := by
  intro name retained
  have different (field : String) (member : field ∈ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]) :
      p.member name ≠ p.member field := by
    intro same
    have names := (Address.member_inj _ _ _).mp same
    exact retained (names ▸ member)
  exact InitializationCalls.exited_frame heap p (p.member name) args .cs
    (different "time" (by simp)) (different "timeMin" (by simp))
    (different "eventTime" (by simp)) (different "lastCompleted" (by simp))
    (different "stop" (by simp)) (different "stopDefined" (by simp)) (different "mode" (by simp))

end Rumoca.FMI3.CSRun
end
