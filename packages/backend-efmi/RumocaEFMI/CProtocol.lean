import RumocaEFMI.CInterface
import RumocaEFMI.ProductionProofs
import RumocaCore.GALEC.Protocol

/-! Serial block-interface interactions with the generated C bodies. The host
supplies legal method entries; this relation does not claim that the C API
contains a scheduler or dynamically checks the host's lifecycle discipline. -/
noncomputable section
namespace Rumoca.EFMI.CProtocol
private local instance targetInterface : CInterface := cInterface
open CMemory GALEC.Protocol

structure Configuration where
  phase : Phase
  heap : Heap
  samples : Nat

inductive Step (module : Production.Module) (p : Address) :
    Configuration → Event → Configuration → Prop where
  | complete (method heap heap' samples) :
      CArithmetic.machine.Behaves
        (.running (module.method method).body (Production.parameters p) heap)
        (.terminates ⟨.integer 0, heap'⟩) →
      Step module p ⟨.running method, heap, samples⟩ .complete
        ⟨.idle, heap', samples + (if method = .doStep then 1 else 0)⟩
  | recalibrate (heap samples) : Step module p ⟨.idle, heap, samples⟩ .recalibrate
      ⟨.running .recalibrate, heap, samples⟩
  | tick (heap samples) : Step module p ⟨.idle, heap, samples⟩ .tick
      ⟨.running .doStep, heap, samples⟩
  | readOutput (heap samples) : Step module p ⟨.idle, heap, samples⟩ .readOutput
      ⟨.idle, heap, samples⟩
  | shutdown (heap samples) : Step module p ⟨.idle, heap, samples⟩ .shutdown
      ⟨.stopped, heap, samples⟩

inductive Trace (module : Production.Module) (p : Address) :
    Configuration → List Event → Configuration → Prop where
  | nil (state) : Trace module p state [] state
  | cons : Step module p before event middle → Trace module p middle events after →
      Trace module p before (event :: events) after

def Related (p : Address) (c : Configuration) (s : GALEC.Protocol.Configuration Binary64.Value) : Prop :=
  c.phase = s.phase ∧ c.samples = s.samples ∧ Production.Represents c.heap p s.values

def execute (model : Solve.Algorithm.Model source) :=
  GALEC.UnitProfile.solveExecute model.block Binary64.positiveZero Binary64.one GALEC.roundedAdd

theorem step_sound (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (p : Address)
    (s : GALEC.Protocol.Configuration Binary64.Value)
    (related : Related p before s) (step : Step module p before event after) :
    ∃ s', GALEC.Protocol.Step (execute model) s event s' ∧ Related p after s' := by
  rcases s with ⟨phase, values, count⟩
  cases step with
  | complete method heap heap' samples done =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    have correct := Production.method_correct model module lowered method heap p values memory
    have eq := (correct.1 _).mp done
    injection eq with eq
    have heaps := congrArg CBody.Result.heap eq
    dsimp only at heaps
    subst heap'
    exact ⟨_, .complete _ _ _, rfl, rfl, correct.2.1⟩
  | recalibrate heap samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .recalibrate _ _, rfl, rfl, memory⟩
  | tick heap samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .tick _ _, rfl, rfl, memory⟩
  | readOutput heap samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .readOutput _ _, rfl, rfl, memory⟩
  | shutdown heap samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .shutdown _ _, rfl, rfl, memory⟩

theorem step_complete (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (p : Address)
    (c : Configuration) (related : Related p c before)
    (step : GALEC.Protocol.Step (execute model) before event after) :
    ∃ c', Step module p c event c' ∧ Related p c' after := by
  rcases c with ⟨phase, heap, count⟩
  cases step with
  | complete method values samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    have correct := Production.method_correct model module lowered method heap p values memory
    exact ⟨_, .complete _ _ _ _ ((correct.1 _).mpr rfl), rfl, rfl, correct.2.1⟩
  | recalibrate values samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .recalibrate _ _, rfl, rfl, memory⟩
  | tick values samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .tick _ _, rfl, rfl, memory⟩
  | readOutput values samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .readOutput _ _, rfl, rfl, memory⟩
  | shutdown values samples =>
    dsimp only [Related] at related
    rcases related with ⟨rfl, rfl, memory⟩
    exact ⟨_, .shutdown _ _, rfl, rfl, memory⟩

theorem trace_sound (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (p : Address)
    (s : GALEC.Protocol.Configuration Binary64.Value)
    (related : Related p before s) (trace : Trace module p before events after) :
    ∃ s', GALEC.Protocol.Trace (execute model) s events s' ∧ Related p after s' := by
  induction trace generalizing s with
  | nil => exact ⟨s, .nil _, related⟩
  | cons step trace ih =>
    obtain ⟨middle, stepped, related'⟩ := step_sound model module lowered p s related step
    obtain ⟨last, traced, related''⟩ := ih middle related'
    exact ⟨last, .cons stepped traced, related''⟩

theorem trace_complete (model : Solve.Algorithm.Model source) (module : Production.Module)
    (lowered : Production.lower model = .ok module) (p : Address)
    (c : Configuration) (related : Related p c before)
    (trace : GALEC.Protocol.Trace (execute model) before events after) :
    ∃ c', Trace module p c events c' ∧ Related p c' after := by
  induction trace generalizing c with
  | nil => exact ⟨c, .nil _, related⟩
  | cons step trace ih =>
    obtain ⟨middle, stepped, related'⟩ := step_complete model module lowered p c related step
    obtain ⟨last, traced, related''⟩ := ih middle related'
    exact ⟨last, .cons stepped traced, related''⟩

end Rumoca.EFMI.CProtocol
