import RumocaFMI3.StepEntry

/-! Exact successful-step observations, composed from initialized-buffer
facts and the numerical tail's residual frames. Profile execution contracts
retain their caller-storage, arithmetic and runtime-linking premises. -/
noncomputable section
namespace Rumoca.FMI3.StepEntry
open CMemory
set_option autoImplicit false

/-- The three false output flags and exact preservation of the selected mode.
The final time and state observations remain in the profile execution contract. -/
structure SuccessState (before after : Heap) (p : Address) (buffers : Buffers) : Prop where
  eventFalse : after buffers.event = some ⟨.boolean, true, some (.integer 0)⟩
  terminateFalse : after buffers.terminate = some ⟨.boolean, true, some (.integer 0)⟩
  earlyFalse : after buffers.early = some ⟨.boolean, true, some (.integer 0)⟩
  modePreserved : after (p.member "mode") = before (p.member "mode")

/-- Reuse initialization facts and the actual numerical tail's frames.
Boolean buffers may alias each other. Float/Boolean separation follows from
existing initial storage types, with no extra caller premise. -/
theorem success_of_frames (heap finalHeap : Heap) (p : Address)
    (buffers : Buffers) (time : Binary64.Value) (old : Option Value)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, old⟩)
    (outsideEvent : buffers.event.block ≠ p.block)
    (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block)
    (outsideLast : buffers.last.block ≠ p.block)
    (outside : ∀ q, q.block ≠ p.block → q ≠ buffers.last →
      finalHeap q = outputHeap heap buffers time q)
    (mode : finalHeap (p.member "mode") = outputHeap heap buffers time (p.member "mode")) :
    SuccessState heap finalHeap p buffers := by
  obtain ⟨eventZero, terminateZero, earlyZero, _⟩ :=
    output_values heap buffers time old event terminate early last
  exact ⟨(outside _ outsideEvent (float_ne_boolean heap _ _ old last event).symm).trans eventZero,
    (outside _ outsideTerminate (float_ne_boolean heap _ _ old last terminate).symm).trans terminateZero,
    (outside _ outsideEarly (float_ne_boolean heap _ _ old last early).symm).trans earlyZero,
    mode.trans (output_instance heap buffers time p _ outsideEvent outsideTerminate
      outsideEarly outsideLast rfl)⟩

end Rumoca.FMI3.StepEntry
