import RumocaC.StoreRunInvariant
import RumocaC.AtomicFrame
import RumocaFMI3.Float64Access

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory Float64Buffers

theorem Request.host_atomic {request : Request} {heap after : Heap}
    (executed : request.hostRun heap buffers = some after) : CAtomicBoolean.Preserves heap after := by
  cases request <;>
    simp only [Request.hostRun, Option.bind_eq_bind, Option.bind_eq_some_iff] at executed
  · obtain ⟨prior, references, result⟩ := executed
    cases Option.some.inj result
    exact CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) references
  · obtain ⟨prior, references, values⟩ := executed
    exact (CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) references).trans
      (CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) values)

theorem assigned_atomic (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (state : ModelExchange.State)
    (cell : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) :
    CAtomicBoolean.Preserves heap (Float64Set.assigned heap p values shape.volume) := by
  by_cases nonempty : 0 < shape.volume
  · rw [assigned_final heap p values nonempty]
    exact CAtomicBoolean.ordinary_store_preserves
      (store_float64 heap (StateProofs.stateAddress p) (some (.finite state.x))
        (Binary64.toBits values[shape.volume - 1]).val cell)
  · have empty : shape.volume = 0 := by omega
    simpa only [empty, Float64Set.assigned] using CAtomicBoolean.Preserves.refl heap

/-- Typed ordinary access cannot alter an atomic reservation cell, even
when caller buffers share its enclosing block. No extra block-separation
premise is needed to preserve leases. -/
theorem Request.after_atomic (model : Solve.FMI3Model source) (request : Request)
    (stored : Instance heap p kind mode state time) (buffersStored : Stored heap buffers)
    (fits : request.Fits buffers) (separate : buffers.Separate p) :
    CAtomicBoolean.Preserves heap (request.after model heap p buffers state time) := by
  obtain ⟨host, preparedBuffers, _, _⟩ := request.prepare_correct buffersStored fits
  have prepared := request.prepared_instance stored fits separate
  have first := Request.host_atomic host
  cases request with
  | get shape references =>
    let outputs := Float64Calls.outputValues model state time shape (fun i => Float64Calls.selectReference (references i))
    have writable : TensorView.Writable ((Request.get shape references).prepare heap buffers) buffers.values shape.volume :=
      fun i hi => preparedBuffers.values i (Nat.lt_of_lt_of_le hi fits)
    exact first.trans (CStoreInvariant.array_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b)
      (values_run _ buffers.values outputs writable))
  | set values => exact first.trans (assigned_atomic _ p values state prepared.state)

end Rumoca.FMI3.Float64Access
end
