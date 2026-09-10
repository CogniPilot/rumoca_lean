import RumocaCore.FMI3.Time

/-! Reference ME history and its compact cached representation. Completed
timestamps are retained by position, not by a monotonicity assumption. The
event floor is retained separately so an obsolete completion can be dropped. -/
namespace Rumoca.FMI3.Time
open Binary64

def maximum (a b : Binary64.Value) : Binary64.Value :=
  if units a < units b then b else a

theorem maximum_value (a b : Binary64.Value) :
    value (maximum a b) = max (value a) (value b) := by
  unfold maximum
  split <;> rename_i h
  · exact (max_eq_right (le_of_lt ((Rumoca.Float64.value_lt_iff a b).mpr h))).symm
  · exact (max_eq_left ((Rumoca.Float64.value_le_iff b a).mpr (Int.le_of_not_gt h))).symm

structure History where
  window : Window
  time : Binary64.Value
  lastCompleted : Binary64.Value

def History.initial (start : Binary64.Value) (stop : Option Binary64.Value) : History :=
  ⟨Window.initial start stop, start, start⟩
def History.setTime (h : History) (time : Binary64.Value) : History := { h with time }
def History.completed (h : History) : History :=
  { h with window.secondLastCompleted := h.lastCompleted, lastCompleted := h.time }
def History.event (h : History) : History := { h with window.lastEvent := h.time }

/-- Trial time can retreat past the last completion, but not the start or
last event. Completion does not change these two persistent bounds. -/
def History.Stable (h : History) : Prop :=
  value h.window.startTime ≤ value h.window.lastEvent ∧ value h.window.lastEvent ≤ value h.time

structure Clock where
  time : Binary64.Value
  minimum : Binary64.Value
  eventTime : Binary64.Value
  lastCompleted : Binary64.Value

def Clock.initial (start : Binary64.Value) : Clock := ⟨start, start, start, start⟩
def Clock.setTime (c : Clock) (time : Binary64.Value) : Clock := { c with time }
def Clock.completed (c : Clock) : Clock :=
  { c with minimum := maximum c.eventTime c.lastCompleted, lastCompleted := c.time }
def Clock.event (c : Clock) : Clock :=
  { c with minimum := maximum c.minimum c.time, eventTime := c.time }

structure Represents (h : History) (c : Clock) : Prop where
  time : c.time = h.time
  completed : c.lastCompleted = h.lastCompleted
  eventTime : c.eventTime = h.window.lastEvent
  minimum : h.window.RepresentsLower c.minimum
  stable : h.Stable

theorem initial_represents (start : Binary64.Value) (stop : Option Binary64.Value) :
    Represents (History.initial start stop) (Clock.initial start) := by
  exact ⟨rfl, rfl, rfl, initial_lower start stop, ⟨le_refl _, le_refl _⟩⟩

theorem setTime_represents (hr : Represents h c) (ha : h.window.Admissible time) :
    Represents (h.setTime time) (c.setTime time) := by
  exact ⟨rfl, hr.completed, hr.eventTime, hr.minimum, ⟨hr.stable.1, ha.2.2.1⟩⟩

theorem completed_represents (hr : Represents h c) :
    Represents h.completed c.completed := by
  refine ⟨hr.time, hr.time, hr.eventTime, ?_, hr.stable⟩
  change value (maximum c.eventTime c.lastCompleted) =
    max (value h.window.startTime) (max (value h.lastCompleted) (value h.window.lastEvent))
  rw [maximum_value, hr.eventTime, hr.completed, max_comm]
  exact (max_eq_right (le_trans hr.stable.1 (le_max_right _ _))).symm

theorem event_represents (hr : Represents h c) :
    Represents h.event c.event := by
  refine ⟨hr.time, hr.completed, hr.time, ?_, ?_⟩
  · change value (maximum c.minimum c.time) =
      max (value h.window.startTime) (max (value h.window.secondLastCompleted) (value h.time))
    rw [maximum_value, hr.time, show value c.minimum = _ from hr.minimum,
      max_assoc, max_assoc, max_eq_right hr.stable.2]
  · exact ⟨le_trans hr.stable.1 hr.stable.2, le_refl _⟩

inductive Action where
  | setTime (time : Binary64.Value)
  | completed
  | event

inductive Step : History → Action → History → Prop where
  | setTime (ha : h.window.Admissible time) : Step h (.setTime time) (h.setTime time)
  | completed : Step h .completed h.completed
  | event : Step h .event h.event

def Clock.apply (c : Clock) : Action → Clock
  | .setTime time => c.setTime time
  | .completed => c.completed
  | .event => c.event

theorem step_represents (hr : Represents h c) (hs : Step h action h') :
    Represents h' (c.apply action) := by
  cases hs with
  | setTime ha => exact setTime_represents hr ha
  | completed => exact completed_represents hr
  | event => exact event_represents hr

inductive Trace : History → List Action → History → Prop where
  | nil : Trace h [] h
  | cons : Step h action h' → Trace h' actions h'' → Trace h (action :: actions) h''

/-- Every reference-admitted history sequence preserves the cached window.
The C bodies must separately implement these same clock updates. -/
theorem trace_represents (hr : Represents h c) (hs : Trace h actions h') :
    Represents h' (actions.foldl Clock.apply c) := by
  induction hs generalizing c with
  | nil => exact hr
  | cons head _ ih => exact ih (step_represents hr head)

end Rumoca.FMI3.Time
