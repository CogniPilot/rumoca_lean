import RumocaFMI3.CSHistory
import RumocaFMI3.InitializationComposition

noncomputable section
namespace Rumoca.FMI3.CSHistory
open CTree CMemory CBody

/-- Initialization establishes the successful-CS invariant from original
finite writable state and caller buffers. It supplies the clock and stop bound
and preserves the exact state cell, including its write permission. -/
theorem initialized_stored (model : Solve.Model source) (seed : Binary64.Value)
    (heap : Heap) (p : Address) (args : Initialization.Arguments) (buffers : StepEntry.Buffers)
    (admissible : args.Admissible)
    (kind : load heap (p.member "kind") = some (.integer 1))
    (state : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩)
    (outputStorage : StepArguments.Storage heap p buffers) :
    Stored model seed (InitializationCalls.exitedHeap heap p args .cs) p buffers ⟨args.start, 0⟩ args.stopTime := by
  let entered := InitializationEntry.finalHeap heap p args
  let exited := InitializationCalls.exitedHeap heap p args .cs
  have preserved (query : Address) (mode : query ≠ p.member "mode") :
      exited query = entered query := InitializationBodies.exit_frame entered p query .cs mode
  have outside (query : Address) (separate : query.block ≠ p.block) : exited query = heap query := by
    have different (name : String) : query ≠ p.member name := by
      intro same
      have blocks : query.block = (p.member name).block := congrArg Address.block same
      exact separate blocks
    exact InitializationCalls.exited_frame heap p query args .cs (different "time") (different "timeMin")
      (different "eventTime") (different "lastCompleted") (different "stop") (different "stopDefined") (different "mode")
  constructor
  · change load exited (p.member "kind") = _
    simpa only [load, preserved (p.member "kind") (by simp)] using
      (InitializationCalls.entered_kind heap p args).trans kind
  · simpa only [Mode.code, nextMode] using InitializationBodies.exit_mode entered p .cs
  · exact (InitializationBodies.exit_history (InitializationCalls.stored heap p args) .cs).time
  · have different (name : String) : StateProofs.stateAddress p ≠ p.member name := by
      intro same
      have lengths := congrArg (fun address : Address => address.members.length) same
      simp [StateProofs.stateAddress, Address.member] at lengths
    exact (InitializationCalls.exited_frame heap p (StateProofs.stateAddress p) args .cs
      (different "time") (different "timeMin") (different "eventTime") (different "lastCompleted")
      (different "stop") (different "stopDefined") (different "mode")).trans state
  · rw [show load exited (p.member "stopDefined") = load entered (p.member "stopDefined") by
      simp only [load, preserved (p.member "stopDefined") (by simp)]]
    simpa only [Initialization.stopTime_defined args admissible] using (InitializationEntry.stop heap p args).2
  · intro limit selected
    have bits := Initialization.stopTime_bits args admissible limit selected
    rw [show load exited (p.member "stop") = load entered (p.member "stop") by
      simp only [load, preserved (p.member "stop") (by simp)]]
    simpa only [Value.finite, bits] using (InitializationEntry.stop heap p args).1
  · refine ⟨?_, ?_, ?_, ?_, outputStorage.outsideEvent, outputStorage.outsideTerminate,
      outputStorage.outsideEarly, outputStorage.outsideLast⟩
    · obtain ⟨old, cell⟩ := outputStorage.event
      exact ⟨old, (outside _ outputStorage.outsideEvent).trans cell⟩
    · obtain ⟨old, cell⟩ := outputStorage.terminate
      exact ⟨old, (outside _ outputStorage.outsideTerminate).trans cell⟩
    · obtain ⟨old, cell⟩ := outputStorage.early
      exact ⟨old, (outside _ outputStorage.outsideEarly).trans cell⟩
    · obtain ⟨old, cell⟩ := outputStorage.last
      exact ⟨old, (outside _ outputStorage.outsideLast).trans cell⟩

end Rumoca.FMI3.CSHistory
end
