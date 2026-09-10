import RumocaCore.GALEC.UnitProfile

/-! Authored reference for the no-input/no-parameter specialization of eFMI
1.0.0 Beta 1 §3.2.3's lifecycle diagram. Calls are explicit enter/complete pairs;
an output read cannot interleave with a method. A clock tick enters DoStep
exactly once. Physical scheduling, uninitialized C storage and the public ABI
are separate obligations, not consequences of this reference model. -/
namespace Rumoca.GALEC.Protocol
open UnitProfile

inductive Phase where
  | running (method : Method)
  | idle
  | stopped
  deriving Repr, BEq, DecidableEq

inductive Event where
  | complete
  | recalibrate
  | tick
  | readOutput
  | shutdown
  deriving Repr, BEq, DecidableEq

structure Configuration (α : Type) where
  phase : Phase
  values : State α
  samples : Nat

/-- Initial memory is unobservable until Startup completes. The unit Startup
theorem makes its resulting values independent of this arbitrary old state. -/
def initial (old : State α) : Configuration α := ⟨.running .startup, old, 0⟩

inductive Step (execute : Method → State α → State α) :
    Configuration α → Event → Configuration α → Prop where
  | complete (method values samples) : Step execute ⟨.running method, values, samples⟩ .complete
      ⟨.idle, execute method values, samples + (if method = .doStep then 1 else 0)⟩
  | recalibrate (values samples) : Step execute ⟨.idle, values, samples⟩ .recalibrate
      ⟨.running .recalibrate, values, samples⟩
  | tick (values samples) : Step execute ⟨.idle, values, samples⟩ .tick
      ⟨.running .doStep, values, samples⟩
  | readOutput (values samples) : Step execute ⟨.idle, values, samples⟩ .readOutput
      ⟨.idle, values, samples⟩
  | shutdown (values samples) : Step execute ⟨.idle, values, samples⟩ .shutdown
      ⟨.stopped, values, samples⟩

inductive Trace (execute : Method → State α → State α) :
    Configuration α → List Event → Configuration α → Prop where
  | nil (state) : Trace execute state [] state
  | cons : Step execute before event middle → Trace execute middle events after →
      Trace execute before (event :: events) after

theorem read_only_idle {executor : Method → State α → State α}
    (h : Step executor before .readOutput after) :
    before.phase = .idle ∧ after = before := by
  cases h
  exact ⟨rfl, rfl⟩

theorem tick_enters_once {executor : Method → State α → State α}
    (h : Step executor before .tick after) :
    before.phase = .idle ∧ after.phase = .running .doStep ∧
      after.values = before.values ∧ after.samples = before.samples := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem stopped_terminal {executor : Method → State α → State α}
    (h : before.phase = .stopped) :
    ¬ Step executor before event after := by
  intro step
  cases step <;> cases h

/-- General method refinement lifts to the complete permitted interaction
trace, including visible state and the count of completed sampling calls. -/
theorem trace_congr (h : ∀ method state, execute₁ method state = execute₂ method state) :
    Trace execute₁ before events after ↔ Trace execute₂ before events after := by
  have he : execute₁ = execute₂ := funext fun method => funext (h method)
  rw [he]

theorem lower_trace_correct (block : GALEC.Block Rumoca.Tensor.scalar)
    (zero one : α) (add : α → α → α)
    (before after : Configuration α) (events : List Event) :
    Trace (solveExecute (Solve.Algorithm.lower block) zero one add) before events after ↔
      Trace (execute block zero one add) before events after :=
  trace_congr (UnitProfile.lower_correct block zero one add)

end Rumoca.GALEC.Protocol
