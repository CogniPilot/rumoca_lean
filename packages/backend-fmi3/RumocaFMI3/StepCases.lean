import RumocaCore.Real.Decoding
import RumocaFMI3.StepDiscard

/-! Exhaustive and disjoint public CS admission for arbitrary raw inputs.
Accepted cases derive the finite values and numerical premises of the complete
successful call. This reference partition alone is not an artifact contract. -/
noncomputable section
namespace Rumoca.FMI3.StepCases
open CMemory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

theorem input_values (point step : BitVec 64) (time : Binary64.Value)
    (valid : StepEntry.InputsValid point step time) :
    ∃ current duration : Binary64.Value,
      point = (Binary64.toBits current).val ∧ step = (Binary64.toBits duration).val ∧
      Binary64.value current = Binary64.value time ∧ 0 < Binary64.value duration := by
  cases current : Float64.decode point <;>
    cases duration : Float64.decode step <;>
    simp only [StepEntry.InputsValid, current, duration] at valid
  exact ⟨_, _, Float64.finite_encoding current, Float64.finite_encoding duration, valid⟩

structure Query where
  handle : Option Address
  kind : Kind
  mode : Mode
  outputs : StepEntry.Outputs
  point : BitVec 64
  step : BitVec 64
  time : Binary64.Value
  stop : Option Binary64.Value
  observed : Int
  header : CFenv.Header

inductive Outcome where
  | null | lifecycle | outputs | input | rounding | stop | discard | accepted
  deriving DecidableEq

def Ready (query : Query) : Prop :=
  query.handle ≠ none ∧ Reference.Allowed .doStep query.kind query.mode ∧
    ¬ StepArguments.MissingOutput query.outputs ∧
    StepEntry.InputsValid query.point query.step query.time

def nextTime (query : Query) : Float64.Number :=
  match Float64.decode query.step with
  | .finite duration => Binary64.addResult query.time duration
  | _ => .nan

def Duration (query : Query) : Prop :=
  match Float64.decode query.step with
  | .finite duration => StepAdmission.AdmittedDuration duration
  | _ => False

/-- A disjoint reference partition of raw public inputs, respecting the
specified lifecycle and the established numerical admission policy. -/
def Condition (query : Query) : Outcome → Prop
  | .null => query.handle = none
  | .lifecycle => query.handle ≠ none ∧ ¬ Reference.Allowed .doStep query.kind query.mode
  | .outputs => query.handle ≠ none ∧ Reference.Allowed .doStep query.kind query.mode ∧
      StepArguments.MissingOutput query.outputs
  | .input => query.handle ≠ none ∧ Reference.Allowed .doStep query.kind query.mode ∧
      ¬ StepArguments.MissingOutput query.outputs ∧ ¬ StepEntry.InputsValid query.point query.step query.time
  | .rounding => Ready query ∧ query.observed ≠ query.header.nearest
  | .stop => Ready query ∧ query.observed = query.header.nearest ∧
      StepGuards.AboveStop (nextTime query) query.stop
  | .discard => Ready query ∧ query.observed = query.header.nearest ∧
      ¬ StepGuards.AboveStop (nextTime query) query.stop ∧
      (¬ StepGuards.Progress query.time (nextTime query) ∨ ¬ Duration query)
  | .accepted => Ready query ∧ query.observed = query.header.nearest ∧
      ¬ StepGuards.AboveStop (nextTime query) query.stop ∧
      StepGuards.Progress query.time (nextTime query) ∧ Duration query

theorem complete (query : Query) : ∃ outcome, Condition query outcome := by
  classical
  by_cases handle : query.handle = none
  · exact ⟨.null, handle⟩
  by_cases allowed : Reference.Allowed .doStep query.kind query.mode
  · by_cases outputs : StepArguments.MissingOutput query.outputs
    · exact ⟨.outputs, handle, allowed, outputs⟩
    by_cases valid : StepEntry.InputsValid query.point query.step query.time
    · have ready : Ready query := ⟨handle, allowed, outputs, valid⟩
      by_cases rounding : query.observed = query.header.nearest
      · by_cases stop : StepGuards.AboveStop (nextTime query) query.stop
        · exact ⟨.stop, ready, rounding, stop⟩
        by_cases progress : StepGuards.Progress query.time (nextTime query)
        · by_cases duration : Duration query
          · exact ⟨.accepted, ready, rounding, stop, progress, duration⟩
          · exact ⟨.discard, ready, rounding, stop, Or.inr duration⟩
        · exact ⟨.discard, ready, rounding, stop, Or.inl progress⟩
      · exact ⟨.rounding, ready, rounding⟩
    · exact ⟨.input, handle, allowed, outputs, valid⟩
  · exact ⟨.lifecycle, handle, allowed⟩

theorem unique (first : Condition query a) (second : Condition query b) : a = b := by
  cases a <;> cases b <;> simp only [Condition, Ready] at first second <;> first | rfl | tauto

theorem partition (query : Query) : ∃! outcome, Condition query outcome := by
  obtain ⟨outcome, valid⟩ := complete query
  exact ⟨outcome, valid, fun _ other => unique other valid⟩


/-- Valid raw inputs supply exact values and nonnull buffers. Storage remains
an independent premise of target execution, not a parser/classifier assumption. -/
theorem ready_values (query : Query) (ready : Ready query) :
    ∃ p buffers current duration,
      query.handle = some p ∧ query.outputs = StepEntry.Buffers.outputs buffers ∧
      query.kind = .cs ∧ query.mode = .step ∧
      query.point = (Binary64.toBits current).val ∧ query.step = (Binary64.toBits duration).val ∧
      Binary64.value current = Binary64.value query.time ∧ 0 < Binary64.value duration := by
  obtain ⟨nonnull, allowed, present, valid⟩ := ready
  have handle : ∃ p, query.handle = some p := by
    cases found : query.handle with
    | none => exact False.elim (nonnull found)
    | some p => exact ⟨p, rfl⟩
  obtain ⟨p, handle⟩ := handle
  obtain ⟨buffers, outputs⟩ := (StepArguments.output_cases query.outputs).resolve_left present
  obtain ⟨current, duration, point, step, same, positive⟩ := input_values query.point query.step query.time valid
  exact ⟨p, buffers, current, duration, handle, outputs, allowed.1, allowed.2, point, step, same, positive⟩

/-- An accepted raw case derives every numerical admission premise required
by the existing complete successful call, including finite nonoverflowing
addition, clock progress and the inclusive stop bound. -/
theorem accepted_values (query : Query) (accepted : Condition query .accepted) :
    ∃ p buffers current duration,
      query.handle = some p ∧ query.outputs = StepEntry.Buffers.outputs buffers ∧
      query.kind = .cs ∧ query.mode = .step ∧
      query.point = (Binary64.toBits current).val ∧ query.step = (Binary64.toBits duration).val ∧
      Binary64.value current = Binary64.value query.time ∧ StepAdmission.AdmittedDuration duration ∧
      query.observed = query.header.nearest ∧
      Binary64.value query.time < Binary64.value (Binary64.roundedAdd query.time duration) ∧
      (∀ stop, query.stop = some stop →
        Binary64.value (Binary64.roundedAdd query.time duration) ≤ Binary64.value stop) := by
  obtain ⟨ready, rounding, noStop, progress, duration⟩ := accepted
  obtain ⟨p, buffers, current, step, handle, outputs, kind, mode, point, encoded, same, positive⟩ :=
    ready_values query ready
  have admitted : StepAdmission.AdmittedDuration step := by
    simpa only [Duration, encoded, Float64.decode_finite] using duration
  have sum := StepAdmission.duration_sum query.time step admitted
  have advancing : Binary64.value query.time < Binary64.value (Binary64.roundedAdd query.time step) := by
    simpa only [nextTime, encoded, Float64.decode_finite, sum, StepGuards.Progress] using progress
  refine ⟨p, buffers, current, step, handle, outputs, kind, mode, point, encoded, same,
    admitted, rounding, advancing, ?_⟩
  intro stop chosen
  have within : ¬ Binary64.value stop < Binary64.value (Binary64.roundedAdd query.time step) := by
    simpa only [nextTime, encoded, Float64.decode_finite, sum, chosen, StepGuards.AboveStop] using noStop
  exact le_of_not_gt within

end Rumoca.FMI3.StepCases
end
