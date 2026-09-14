import RumocaFMI3.MENumericalInitialization
import RumocaFMI3.StaticReset

noncomputable section
namespace Rumoca.FMI3.MENumericalHistory
open CTree CMemory StaticFactory

/-- Recovery requires writable stop fields even when no stop value is active.
The remaining writable fields are already supplied by the numerical invariant. -/
theorem Stored.reset_storage (stored : Stored heap p clock reference addresses buffer)
    (stop : Reset.Writable heap (p.member "stop") .float64)
    (stopDefined : Reset.Writable heap (p.member "stopDefined") .boolean) : Reset.Storage heap p :=
  ⟨⟨_, stored.stateCell⟩, ⟨_, stored.control.clockStored.time⟩,
    ⟨_, stored.control.clockStored.minimum⟩, ⟨_, stored.control.clockStored.eventTime⟩,
    ⟨_, stored.control.clockStored.lastCompleted⟩, stop, stopDefined, ⟨_, stored.control.mode⟩⟩

theorem Stored.stop_outside (stored : Stored heap p clock reference addresses buffer)
    (name : String) (selected : name = "stop" ∨ name = "stopDefined") :
    Outside p addresses buffer (p.member name) := by
  have outputs : ∀ label ∈ DiscreteCalls.names, p.member name ≠ addresses label := by
    intro label member same
    exact stored.control.outside label member (by simpa using (congrArg Address.block same).symm)
  refine ⟨?_, Ne.symm (HistoryBodies.state_ne_field p name), stored.field_ne_buffer name⟩
  rcases selected with rfl | rfl <;>
    exact ⟨by simp, by simp, by simp, by simp, by simp, outputs⟩

/-- Any admitted numerical operation preserves the storage needed for a later
reset. Stop-field permissions are retained even when their values are inactive. -/
theorem step_reset_storage (model : Solve.FMI3Model source) (action : Action)
    (stored : Stored heap p clock reference addresses buffer)
    (afterStored : Stored (action.after model heap p clock reference addresses buffer) p
      (action.clock clock) (action.next reference) addresses buffer)
    (reset : Reset.Storage heap p) :
    Reset.Storage (action.after model heap p clock reference addresses buffer) p := by
  apply afterStored.reset_storage
  · obtain ⟨old, cell⟩ := reset.stop
    exact ⟨old, (action.frame model heap p clock reference addresses buffer _
      (stored.stop_outside "stop" (Or.inl rfl))).trans cell⟩
  · obtain ⟨old, cell⟩ := reset.stopDefined
    exact ⟨old, (action.frame model heap p clock reference addresses buffer _
      (stored.stop_outside "stopDefined" (Or.inr rfl))).trans cell⟩

theorem CallerStorage.reset (stored : CallerStorage heap p addresses buffer) :
    CallerStorage (Reset.finalHeap heap p) p addresses buffer := by
  have controls := stored.controls.transport (fun layout member =>
    StaticReset.record_frame heap p (addresses layout.1)
      (fun inside => stored.outside layout.1 (List.mem_map.mpr ⟨layout, member, rfl⟩) inside.1))
  obtain ⟨old, cell⟩ := stored.bufferCell
  exact ⟨controls, stored.outside,
    ⟨old, (StaticReset.record_frame heap p buffer (fun inside => stored.bufferOutside inside.1)).trans cell⟩,
    stored.bufferOutside, stored.bufferSeparate⟩

theorem reset_state_cell (heap : Heap) (p : Address) :
    Reset.finalHeap heap p (StateProofs.stateAddress p) =
      some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ := by
  have different (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  simp [Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
    HistoryProofs.write, LifecycleBodies.writeMode, StateProofs.stateAddress, replace, different]

theorem initialized_reset_storage (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (seed : Binary64.Value)
    (state : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩) :
    Reset.Storage (InitializationCalls.exitedHeap heap p args .me) p := by
  have different (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  constructor <;>
    simp [Reset.Writable, InitializationCalls.exitedHeap, InitializationBodies.exitHeap,
      InitializationEntry.finalHeap, HistoryProofs.initialHeap, HistoryProofs.write,
      HistoryProofs.cell, StateProofs.stateAddress,
      replace, Mode.code, nextMode, different] at *
  exact ⟨_, state⟩

def restarted (heap : Heap) (p : Address) (args : Initialization.Arguments) : Heap :=
  InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .me

def ReferenceState.restart (args : Initialization.Arguments) : ReferenceState :=
  .initial args Binary64.positiveZero

theorem Stored.restart (stored : Stored heap p clock reference addresses buffer)
    (args : Initialization.Arguments) (admissible : args.Admissible) :
    Stored (restarted heap p args) p (Time.Clock.initial args.start)
      (ReferenceState.restart args) addresses buffer :=
  initialized_stored _ p args Binary64.positiveZero addresses buffer admissible
    ((StaticReset.kind_value heap p).trans stored.control.kind) (reset_state_cell heap p) stored.callers.reset

/-- A reset starts a new initialized epoch while preserving every existing
atomic reservation. This is independent of whether an old stop value was active. -/
theorem restart_atomic (stored : Reset.Storage heap p) (args : Initialization.Arguments) :
    CAtomicBoolean.Preserves heap (restarted heap p args) := by
  intro address busy atomic
  have different (target : Address) (type : CType) (nonatomic : type ≠ .atomicBoolean)
      (writable : Reset.Writable heap target type) : address ≠ target := by
    obtain ⟨value, found⟩ := writable
    intro same
    rw [same] at atomic
    exact nonatomic (congrArg Cell.type (Option.some.inj (atomic.symm.trans found))).symm
  have state := different _ _ (by intro h; cases h) stored.state
  have time := different _ _ (by intro h; cases h) stored.time
  have minimum := different _ _ (by intro h; cases h) stored.minimum
  have event := different _ _ (by intro h; cases h) stored.event
  have completed := different _ _ (by intro h; cases h) stored.completed
  have stop := different _ _ (by intro h; cases h) stored.stop
  have flag := different _ _ (by intro h; cases h) stored.stopDefined
  have mode := different _ _ (by intro h; cases h) stored.mode
  exact (InitializationCalls.exited_frame _ p address args .me time minimum event completed stop flag mode).trans
    ((Reset.frame heap p address state time minimum event completed stop flag mode).trans atomic)

end Rumoca.FMI3.MENumericalHistory
end
