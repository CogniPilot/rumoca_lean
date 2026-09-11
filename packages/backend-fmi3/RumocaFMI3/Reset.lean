import RumocaFMI3.BodyEmbedding
import RumocaFMI3.InitializationEntry
import RumocaC.InitializationOriginProofs
import RumocaCore.Solve.FMI3OriginProofs

/-! Reset of the existing ME/CS unit instance. All writable cells may contain
arbitrary old values. The actual body restores the prepared model default,
clock fields, stop policy and lifecycle mode, retaining unrelated storage.
Allocation, native ABI and complete adapter-text binding remain separate. -/
namespace Rumoca.FMI3.Reset
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def Writable (heap : Heap) (address : Address) (type : CType) : Prop :=
  ∃ old, heap address = some ⟨type, true, old⟩

structure Storage (heap : Heap) (p : Address) : Prop where
  state : Writable heap (StateProofs.stateAddress p) .float64
  time : Writable heap (p.member "time") .float64
  minimum : Writable heap (p.member "timeMin") .float64
  event : Writable heap (p.member "eventTime") .float64
  completed : Writable heap (p.member "lastCompleted") .float64
  stop : Writable heap (p.member "stop") .float64
  stopDefined : Writable heap (p.member "stopDefined") .boolean
  mode : Writable heap (p.member "mode") .int32

def finalHeap (heap : Heap) (p : Address) : Heap :=
  LifecycleBodies.writeMode
    (replace
      (CInitialization.written
        (HistoryProofs.initialHeap (CInitialization.written heap (StateProofs.stateAddress p))
          p Binary64.positiveZero) (p.member "stop"))
      (p.member "stopDefined") ⟨.boolean, true, some (boolean false)⟩)
    p .instantiated

def tail : List Stmt := [
  Runtime.put "time" (Runtime.n 0), Runtime.put "timeMin" (Runtime.n 0),
  Runtime.put "eventTime" (Runtime.n 0), Runtime.put "lastCompleted" (Runtime.n 0),
  Runtime.put "stop" (Runtime.n 0), Runtime.put "stopDefined" (Runtime.n 0),
  Runtime.setMode .instantiated, Runtime.ok]

def locals (p : Address) : Locals :=
  bind (HistoryBodies.parameters p) "m" (.pointer (some p))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem tail_run (heap : Heap) (p : Address) (storage : Storage heap p) :
    run 8 (.running tail (locals p)
      (CInitialization.written heap (StateProofs.stateAddress p))) =
      some (.returned ⟨.integer 0, finalHeap heap p⟩) := by
  rcases storage with ⟨hx, ⟨time, ht⟩, ⟨minimum, hn⟩, ⟨event, he⟩,
    ⟨completed, hl⟩, ⟨stop, hs⟩, ⟨flag, hf⟩, ⟨mode, hm⟩⟩
  have distinct (name : String) : p.member name ≠ (p.member "model").member "x" :=
    Ne.symm (HistoryBodies.state_ne_field p name)
  simp [tail, Runtime.put, Runtime.field, Runtime.v, Runtime.n, Runtime.setMode,
    Runtime.mode, Runtime.ok, Runtime.ret, Mode.code, run, next, eval, lvalue,
    locals, HistoryBodies.parameters, CBody.bind, resolve, constants,
    Value.address, Value.finite, store, convert, boolean, Value.truth, distinct,
    finalHeap, CInitialization.written, LifecycleBodies.writeMode,
    HistoryProofs.initialHeap, HistoryProofs.write, HistoryProofs.cell,
    StateProofs.stateAddress, replace, ht, hn, he, hl, hs, hf, hm]

/-- The complete successful body works from every declared lifecycle mode in
both interfaces. Reset does not inspect the old model/time/stop values. -/
theorem body_run (m : Solve.FMI3Model source) (sig : Signature)
    (name : sig.name = "fmi3Reset") (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (storage : Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    run 12 (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap) =
      some (.returned ⟨.integer 0, finalHeap heap p⟩) := by
  have guarded := LifecycleGuard.accept (HistoryBodies.parameters p) heap p .reset kind mode
    ((CInitialization.emit m.solve Runtime.x).statement :: tail)
    (by simp [HistoryBodies.parameters]) (by simp [HistoryBodies.parameters]) hk hm trivial
  obtain ⟨old, hx⟩ := storage.state
  have initialized := CInitialization.write_step m.solve Runtime.x (locals p) heap
    (StateProofs.stateAddress p) old (by simp)
    (by simp [lvalue, eval, Runtime.x, Runtime.field, Runtime.v, locals,
      CBody.bind, resolve, constants, Value.address, StateProofs.stateAddress]) hx tail
  have body : Runtime.body m sig = Runtime.require .reset ++
      (CInitialization.emit m.solve Runtime.x).statement :: tail := by
    simp [Runtime.body, name, tail]
  rw [body, show 12 = 3 + 9 from rfl, run_add, guarded]
  change (do run 8 (← next (.running
    ((CInitialization.emit m.solve Runtime.x).statement :: tail) (locals p) heap))) = _
  rw [initialized]
  exact tail_run heap p storage

omit static in
theorem frame (heap : Heap) (p q : Address)
    (hx : q ≠ StateProofs.stateAddress p)
    (ht : q ≠ p.member "time") (hn : q ≠ p.member "timeMin")
    (he : q ≠ p.member "eventTime") (hl : q ≠ p.member "lastCompleted")
    (hs : q ≠ p.member "stop") (hd : q ≠ p.member "stopDefined") (hm : q ≠ p.member "mode") :
    finalHeap heap p q = heap q := by
  simp only [finalHeap, LifecycleBodies.write_frame _ _ _ _ hm,
    replace_other _ _ _ _ hd, CInitialization.written_frame _ _ _ hs,
    HistoryProofs.initial_frame _ _ _ _ ht hn he hl,
    CInitialization.written_frame _ _ _ hx]

omit static in
theorem state (heap : Heap) (p : Address) :
    StateProofs.Represents (finalHeap heap p) p ⟨Binary64.positiveZero⟩ := by
  have distinct (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  simp [StateProofs.Represents, StateProofs.stateAddress, finalHeap,
    CInitialization.written, HistoryProofs.initialHeap, HistoryProofs.write,
    LifecycleBodies.writeMode, load, replace, convert, Value.finite, distinct]

omit static in
theorem history (heap : Heap) (p : Address) :
    HistoryProofs.Stored (finalHeap heap p) p (Time.Clock.initial Binary64.positiveZero) := by
  constructor <;>
    simp [finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, HistoryProofs.cell, LifecycleBodies.writeMode,
      Time.Clock.initial, replace]

omit static in
theorem lifecycle (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) :
    load (finalHeap heap p) (p.member "mode") = some (.integer (nextMode .reset kind mode).code) := by
  rw [reset_recovers]
  exact LifecycleBodies.write_mode _ _ _

omit static in
theorem stop (heap : Heap) (p : Address) :
    load (finalHeap heap p) (p.member "stop") = some (.finite Binary64.positiveZero) ∧
    load (finalHeap heap p) (p.member "stopDefined") = some (boolean false) := by
  simp [finalHeap, CInitialization.written, LifecycleBodies.writeMode, load, replace, convert,
    boolean, Value.truth, Value.finite]

omit static in
theorem other_instance (heap : Heap) (p q : Address) (different : q.block ≠ p.block) :
    finalHeap heap p q = heap q := by
  apply frame
  all_goals
    intro same
    apply different
    simpa [StateProofs.stateAddress, Address.member] using congrArg Address.block same

omit static in
theorem retained_field (heap : Heap) (p : Address) (name : String)
    (outside : name ∉ ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]) :
    finalHeap heap p (p.member name) = heap (p.member name) := by
  apply frame
  · exact Ne.symm (HistoryBodies.state_ne_field p name)
  all_goals
    intro same
    have names := (Address.member_inj _ _ _).mp same
    apply outside
    simp [names]

end Rumoca.FMI3.Reset
