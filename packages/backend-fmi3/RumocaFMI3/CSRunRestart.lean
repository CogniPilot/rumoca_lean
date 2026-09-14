import RumocaFMI3.CSRunState
import RumocaFMI3.CSInitialization
import RumocaFMI3.CSRelease

noncomputable section
namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory

/-- The constructed reset/initialization heap has every writable cell needed
by subsequent recovery. Executing those writes still requires original storage. -/
theorem restart_storage (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    Reset.Storage (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) p := by
  have different (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  constructor <;>
    simp [Reset.Writable, InitializationCalls.exitedHeap, InitializationBodies.exitHeap,
      InitializationEntry.finalHeap, Reset.finalHeap, CInitialization.written,
      HistoryProofs.initialHeap, HistoryProofs.write, HistoryProofs.cell,
      LifecycleBodies.writeMode, StateProofs.stateAddress, replace, Mode.code, nextMode, different]

theorem restart_buffers (stored : StepArguments.Storage heap p buffers) (args : Initialization.Arguments) :
    StepArguments.Storage (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) p buffers := by
  have kept (address : Address) (outside : address.block ≠ p.block) :
      InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs address = heap address :=
    StaticReset.restarted_frame heap p address args .cs (fun inside => outside inside.1)
  refine ⟨?_, ?_, ?_, ?_, stored.outsideEvent, stored.outsideTerminate, stored.outsideEarly, stored.outsideLast⟩
  · obtain ⟨value, found⟩ := stored.event
    exact ⟨value, (kept _ stored.outsideEvent).trans found⟩
  · obtain ⟨value, found⟩ := stored.terminate
    exact ⟨value, (kept _ stored.outsideTerminate).trans found⟩
  · obtain ⟨value, found⟩ := stored.early
    exact ⟨value, (kept _ stored.outsideEarly).trans found⟩
  · obtain ⟨value, found⟩ := stored.last
    exact ⟨value, (kept _ stored.outsideLast).trans found⟩

theorem Stored.restart {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference)
    (args : Initialization.Arguments) (admissible : args.Admissible) :
    Stored model (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs)
      p buffers (Reference.restart args) := by
  have state : Reset.finalHeap heap p (StateProofs.stateAddress p) =
      some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ := by
    have different (name : String) : (p.member "model").member "x" ≠ p.member name :=
      HistoryBodies.state_ne_field p name
    simp [Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, LifecycleBodies.writeMode,
      StateProofs.stateAddress, replace, different]
  have outputs : StepArguments.Storage (Reset.finalHeap heap p) p buffers := by
    have kept (address : Address) (outside : address.block ≠ p.block) :
        Reset.finalHeap heap p address = heap address :=
      StaticReset.record_frame heap p address (fun inside => outside inside.1)
    refine ⟨?_, ?_, ?_, ?_, stored.buffers.outsideEvent, stored.buffers.outsideTerminate,
      stored.buffers.outsideEarly, stored.buffers.outsideLast⟩
    · obtain ⟨value, found⟩ := stored.buffers.event
      exact ⟨value, (kept _ stored.buffers.outsideEvent).trans found⟩
    · obtain ⟨value, found⟩ := stored.buffers.terminate
      exact ⟨value, (kept _ stored.buffers.outsideTerminate).trans found⟩
    · obtain ⟨value, found⟩ := stored.buffers.early
      exact ⟨value, (kept _ stored.buffers.outsideEarly).trans found⟩
    · obtain ⟨value, found⟩ := stored.buffers.last
      exact ⟨value, (kept _ stored.buffers.outsideLast).trans found⟩
  have next := CSHistory.initialized_stored model Binary64.positiveZero (Reset.finalHeap heap p) p args buffers
    admissible ((StaticReset.kind_value heap p).trans stored.kind) state outputs
  exact ⟨next.kind, next.mode, next.clock, next.state, next.stopDefined, next.stopValue,
    restart_storage heap p args, next.buffers⟩

/-- Callback recovery and history composition require actual cell contents,
not just writable types. This frame preserves the instance and caller buffers;
leases and unrelated callback effects remain separate conditions. -/
def Frame (p : Address) (buffers : StepEntry.Buffers) (before after : Heap) : Prop :=
  (∀ address, p.InRecord address → after address = before address) ∧
  after buffers.event = before buffers.event ∧ after buffers.terminate = before buffers.terminate ∧
  after buffers.early = before buffers.early ∧ after buffers.last = before buffers.last

theorem Stored.framed {buffers : StepEntry.Buffers} (stored : Stored model heap p buffers reference) (frame : Frame p buffers heap after) :
    Stored model after p buffers reference := by
  have field (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, frame.1 _ (p.member_in_record name)]
  refine ⟨(field "kind").trans stored.kind, (field "mode").trans stored.mode,
    (frame.1 _ (p.member_in_record "time")).trans stored.clock,
    (frame.1 _ ((p.member_in_record "model").member "x")).trans stored.state,
    (field "stopDefined").trans stored.stopDefined,
    fun limit chosen => (field "stop").trans (stored.stopValue limit chosen),
    stored.reset.record_preserved frame.1,
    ⟨?_, ?_, ?_, ?_, stored.buffers.outsideEvent, stored.buffers.outsideTerminate,
      stored.buffers.outsideEarly, stored.buffers.outsideLast⟩⟩
  · obtain ⟨value, found⟩ := stored.buffers.event
    exact ⟨value, frame.2.1.trans found⟩
  · obtain ⟨value, found⟩ := stored.buffers.terminate
    exact ⟨value, frame.2.2.1.trans found⟩
  · obtain ⟨value, found⟩ := stored.buffers.early
    exact ⟨value, frame.2.2.2.1.trans found⟩
  · obtain ⟨value, found⟩ := stored.buffers.last
    exact ⟨value, frame.2.2.2.2.trans found⟩

end Rumoca.FMI3.CSRun

namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory

/-- Original writable non-atomic fields exclude aliasing with any existing
reservation. Reset and reinitialization therefore preserve every atomic lease. -/
theorem restart_atomic (stored : Reset.Storage heap p) (args : Initialization.Arguments) :
    CAtomicBoolean.Preserves heap (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args .cs) := by
  intro address busy atomic
  have different (target : Address) (type : CType) (nonatomic : type ≠ .atomicBoolean)
      (writable : Reset.Writable heap target type) : address ≠ target := by
    obtain ⟨value, found⟩ := writable
    intro same
    rw [same] at atomic
    exact nonatomic (congrArg Cell.type (Option.some.inj (atomic.symm.trans found))).symm
  have state := different _ _ (by intro h; cases h) stored.state
  have clock := different _ _ (by intro h; cases h) stored.time
  have minimum := different _ _ (by intro h; cases h) stored.minimum
  have event := different _ _ (by intro h; cases h) stored.event
  have completed := different _ _ (by intro h; cases h) stored.completed
  have stop := different _ _ (by intro h; cases h) stored.stop
  have stopDefined := different _ _ (by intro h; cases h) stored.stopDefined
  have mode := different _ _ (by intro h; cases h) stored.mode
  exact (InitializationCalls.exited_frame _ p address args .cs clock minimum event completed stop stopDefined mode).trans
    ((Reset.frame heap p address state clock minimum event completed stop stopDefined mode).trans atomic)

theorem advance_atomic (stored : Stored model heap p buffers reference) (mode : reference.mode = .step)
    (after : CSHistory.ReferenceState) :
    CAtomicBoolean.Preserves heap (CSHistory.written model reference.seed heap p buffers reference.current after) := by
  intro address busy atomic
  exact (CSHistory.written_frame model reference.seed heap p buffers reference.current after address
    ((stored.step_mode mode).atomic_outside address busy atomic)).trans atomic

end Rumoca.FMI3.CSRun

namespace Rumoca.FMI3.CSRun
open CTree CMemory CBody StaticFactory

/-- Public initialization provides the stronger invariant needed by mixed
histories, from the original finite state and caller buffers. -/
theorem Stored.initialized (model : Solve.Model source) (seed : Binary64.Value)
    (heap : Heap) (p : Address) (args : Initialization.Arguments) (buffers : StepEntry.Buffers)
    (admissible : args.Admissible) (kind : load heap (p.member "kind") = some (.integer 1))
    (state : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite seed)⟩)
    (outputs : StepArguments.Storage heap p buffers) :
    Stored model (InitializationCalls.exitedHeap heap p args .cs) p buffers
      ⟨seed, args.start, ⟨args.start, 0⟩, args.stopTime, .step⟩ := by
  have stored := CSHistory.initialized_stored model seed heap p args buffers admissible kind state outputs
  refine ⟨stored.kind, stored.mode, stored.clock, stored.state, stored.stopDefined, stored.stopValue,
    ⟨⟨_, stored.state⟩, ⟨_, stored.clock⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, stored.buffers⟩
  all_goals
    simp [Reset.Writable, InitializationCalls.exitedHeap, InitializationBodies.exitHeap,
      InitializationEntry.finalHeap, HistoryProofs.initialHeap, HistoryProofs.write,
      HistoryProofs.cell, replace]

end Rumoca.FMI3.CSRun
end
