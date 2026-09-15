import RumocaFMI3.InitializationAccess
import RumocaFMI3.LoggingCapability

/-! Exact control-field effects compose alongside the numerical reference
state. The unchanged case recovers the existing full field-retention contract;
a setter records its precise replacement of the logging cell. -/
noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CBody

def Retains (p : Address) (before after : Heap) : Prop :=
  ∀ name, name ∉ InitializationAccess.writtenFields → after (p.member name) = before (p.member name)

def loggingCell (update : Option Bool) (previous : Option Cell) : Option Cell :=
  match update with
  | none => previous
  | some enabled => some ⟨.boolean, true, some (boolean enabled)⟩

structure Retention (update : Option Bool) (p : Address) (before after : Heap) : Prop where
  fields : ∀ name, name ∉ InitializationAccess.writtenFields → name ≠ "logging" →
    after (p.member name) = before (p.member name)
  logging : after (p.member "logging") = loggingCell update (before (p.member "logging"))

theorem Retention.of_retains (kept : Retains p before after) : Retention none p before after :=
  ⟨fun name outside _ => kept name outside, kept "logging" (by decide)⟩

theorem Retention.to_retains (kept : Retention none p before after) : Retains p before after := by
  intro name outside
  by_cases logging : name = "logging"
  · subst name
    exact kept.logging
  · exact kept.fields name outside logging

theorem Retention.refl (heap : Heap) (p : Address) : Retention none p heap heap :=
  ⟨fun _ _ _ => rfl, rfl⟩

theorem Retention.trans (first : Retention left p before middle)
    (second : Retention right p middle after) :
    Retention (right.orElse fun _ => left) p before after := by
  refine ⟨fun name outside different =>
    (second.fields name outside different).trans (first.fields name outside different), ?_⟩
  cases right with
  | none => exact second.logging.trans first.logging
  | some enabled => exact second.logging

theorem Retention.writable (kept : Retention update p before after)
    (stored : Reset.Writable before (p.member "logging") .boolean) :
    Reset.Writable after (p.member "logging") .boolean := by
  cases update with
  | none =>
    obtain ⟨old, cell⟩ := stored
    exact ⟨old, kept.logging.trans cell⟩
  | some enabled => exact ⟨some (boolean enabled), kept.logging⟩

theorem Retention.logging_value (kept : Retention update p before after)
    (stored : load before (p.member "logging") = some (boolean enabled)) :
    load after (p.member "logging") = some (boolean (update.getD enabled)) := by
  cases update with
  | none => simpa only [load, kept.logging, loggingCell, Option.getD_none] using stored
  | some flag =>
    cases flag <;> simp [load, kept.logging, loggingCell, boolean, convert, Value.truth]

theorem Retention.configured [CInterface] {capability : Logging.Capability}
    (kept : Retention update p before after) (configured : capability.Configured before p enabled) :
    capability.Configured after p (update.getD enabled) := by
  refine ⟨configured.1.framed ?_, kept.logging_value configured.2⟩
  intro name member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals exact kept.fields _ (by decide) (by decide)

theorem Retention.logging_written (heap : Heap) (p : Address) (enabled : Bool) :
    Retention (some enabled) p heap (DebugLogging.written heap p enabled) := by
  refine ⟨fun name _ different => DebugLogging.written_frame heap p enabled _ (by simpa using different), ?_⟩
  simp [DebugLogging.written, replace, loggingCell]

end Rumoca.FMI3.InitializationProtocol
end
