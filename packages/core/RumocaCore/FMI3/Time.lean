import RumocaCore.Real.Comparison

/-! The reference ME time window, separate from its C representation. FMI
3.0.2 §3.2.1 permits time backtracking down to the start time, second-last
completed step and last event-mode entry. An optional experiment stop bounds
this unit runtime's accepted interval above. Maintaining these history fields
through initialization/completion/event calls requires separate body proofs. -/
namespace Rumoca.FMI3.Time
open Binary64

structure Window where
  startTime : Binary64.Value
  secondLastCompleted : Binary64.Value
  lastEvent : Binary64.Value
  stopTime : Option Binary64.Value

def Window.Admissible (window : Window) (time : Binary64.Value) : Prop :=
  value window.startTime ≤ value time ∧
  value window.secondLastCompleted ≤ value time ∧
  value window.lastEvent ≤ value time ∧
  ∀ stop, window.stopTime = some stop → value time ≤ value stop

def Window.RepresentsLower (window : Window) (minimum : Binary64.Value) : Prop :=
  value minimum = max (value window.startTime)
    (max (value window.secondLastCompleted) (value window.lastEvent))

theorem admissible_iff (window : Window) (minimum time : Binary64.Value)
    (h : window.RepresentsLower minimum) :
    window.Admissible time ↔ value minimum ≤ value time ∧
      ∀ stop, window.stopTime = some stop → value time ≤ value stop := by
  rw [show value minimum = _ from h]
  simp [Window.Admissible, and_assoc]

def Window.initial (start : Binary64.Value) (stop : Option Binary64.Value) : Window :=
  ⟨start, start, start, stop⟩

theorem initial_lower (start : Binary64.Value) (stop : Option Binary64.Value) :
    (Window.initial start stop).RepresentsLower start := by
  simp [Window.initial, Window.RepresentsLower]

end Rumoca.FMI3.Time
