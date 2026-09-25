import RumocaFMI3.InitializationProtocolRejection
import RumocaFMI3.MEEnvironment

/-! Model Exchange continuous-state and derivative reads in Initialization
Mode and after an initialization error (FMI 3.0.2 §§2.3.3, 2.3.8). Each read
writes one caller float cell and leaves the instance record unchanged. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CTree CMemory CBody StaticFactory CCalls.Events

variable {objects : Objects} {owners : SlotOwners.State objects.capacity}

theorem output_memory (heap : Heap) (p buffer : Address) (bits : BitVec 64)
    (objects : Objects) (owners : SlotOwners.State objects.capacity) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩)
    (instanceStored : Float64Access.Instance heap p kind mode state time)
    (reset : Reset.Storage heap p)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (outside : ¬ p.InRecord buffer) :
    Float64Access.Instance (StateProofs.written heap buffer bits) p kind mode state time ∧
    Reset.Storage (StateProofs.written heap buffer bits) p ∧
    SlotOwners.Represents objects.flagsBlock (StateProofs.written heap buffer bits) owners ∧
    CStorage.Preserves heap (StateProofs.written heap buffer bits) ∧
    CReadOnly.Preserves heap (StateProofs.written heap buffer bits) ∧
    (∀ q, q ≠ buffer → StateProofs.written heap buffer bits q = heap q) := by
  have executed := store_float64 heap buffer old bits storage
  have kept := CStorage.store_preserves executed
  have atomic := CAtomicBoolean.ordinary_store_preserves executed
  have frame (q : Address) (different : q ≠ buffer) := StateProofs.written_frame heap buffer q bits different
  exact ⟨instanceStored.record_preserved (fun q inside => frame q (fun same => outside (same ▸ inside))),
    reset.preserved kept, SlotOwners.ordinary_preserves ownership atomic, kept, CReadOnly.store_preserves executed, frame⟩

theorem output_result (stored : Stored heap p kind state) (action : Action) (next : action.next state = state)
    (logging : action.loggingUpdate = none) (buffer : Address) (bits : BitVec 64) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩) (separate : ¬ p.InRecord buffer)
    (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (actionOutside : ∀ q, action.Outside q → q ≠ buffer) :
    Result objects retained owners p buffers heap (StateProofs.written heap buffer bits) kind state action := by
  obtain ⟨instanceAfter, resetAfter, ownersAfter, preserved, readonly, frame⟩ :=
    output_memory heap p buffer bits objects owners old storage stored.instanceStored stored.reset ownership separate
  have record (q : Address) (inside : p.InRecord q) : StateProofs.written heap buffer bits q = heap q :=
    frame q (fun same => separate (same ▸ inside))
  refine ⟨?_, ownersAfter, CallerStorage.ordinary preserved, readonly, ?_,
    fun q _ _ _ outside => frame q (actionOutside q outside)⟩
  · rw [next]
    exact ⟨instanceAfter, resetAfter, stored.configured.framed (fun name _ => record _ (p.member_in_record name))⟩
  · rw [logging]
    exact Retention.of_retains (fun name _ => record _ (p.member_in_record name))

theorem states_call [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (quiet : ∀ heap, StateCalls.QuietExecutionContract program heap)
    (stored : Stored heap p kind state) (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (buffer : Address) (old : Option Value) (storage : heap buffer = some ⟨.float64, true, old⟩)
    (separate : ¬ p.InRecord buffer) (allowed : (Action.states buffer).Allowed kind state) :
    CallContract model program objects retained owners p buffers heap kind state (.states buffer) := by
  obtain ⟨me, permitted⟩ := allowed
  subst me
  have called := (quiet heap).get p buffer (state.phase.mode .me) state.value old
    (by simpa [Kind.code] using stored.instanceStored.kind) stored.instanceStored.mode_loaded permitted
    stored.instanceStored.represented storage
  refine CallContract.quiet rfl called ?_
    (output_result stored _ rfl rfl buffer _ old storage separate ownership (fun _ outside => outside))
  simp [Action.Observed, Action.readback, StateProofs.written, load, convert, Value.finite,
    Float64Access.Observation.ok]

theorem derivatives_call [CInterface] (model : Solve.FMI3Model source) (program : Program Invocation)
    (quiet : ∀ heap, DerivativeCalls.QuietExecutionContract model program heap)
    (stored : Stored heap p kind state) (ownership : SlotOwners.Represents objects.flagsBlock heap owners)
    (buffer : Address) (old : Option Value) (storage : heap buffer = some ⟨.float64, true, old⟩)
    (separate : ¬ p.InRecord buffer) (allowed : (Action.derivatives buffer).Allowed kind state) :
    CallContract model program objects retained owners p buffers heap kind state (.derivatives buffer) := by
  obtain ⟨me, permitted⟩ := allowed
  subst me
  have called := (quiet heap).get p buffer (state.phase.mode .me) state.value old
    (by simpa [Kind.code] using stored.instanceStored.kind) stored.instanceStored.mode_loaded permitted storage
  refine CallContract.quiet rfl called ?_
    (output_result stored _ rfl rfl buffer _ old storage separate ownership (fun _ outside => outside))
  simp [Action.Observed, Action.readback, StateProofs.written, load, convert, Value.finite,
    Float64Access.Observation.ok]

end Rumoca.FMI3.InitializationProtocol
end
