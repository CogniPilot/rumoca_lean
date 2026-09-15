import RumocaFMI3.PublicAPI
import Lean

/-! Proof-producing coverage for a concrete public signature list. This
macro performs no file I/O or native classification. Every selected witness
and every generic-catalog membership is checked by the Lean kernel. -/
namespace Rumoca.FMI3.PublicAPI

macro "fmi_public_coverage" : tactic =>
  `(tactic| (
    simp only [Covered, List.forall_mem_cons, List.forall_mem_nil]
    repeat' apply And.intro
    all_goals first
      | exact True.intro
      | exact fun _ impossible => False.elim (List.not_mem_nil impossible)
      | exact ⟨(.version : Entry), rfl⟩
      | exact ⟨(.debugLogging : Entry), rfl⟩
      | exact ⟨(.factory .me : Entry), rfl⟩
      | exact ⟨(.factory .cs : Entry), rfl⟩
      | exact ⟨(.scheduled : Entry), rfl⟩
      | exact ⟨(.release : Entry), rfl⟩
      | exact ⟨(.initialization true : Entry), rfl⟩
      | exact ⟨(.initialization false : Entry), rfl⟩
      | exact ⟨(.reset : Entry), rfl⟩
      | exact ⟨(.counts false : Entry), rfl⟩
      | exact ⟨(.counts true : Entry), rfl⟩
      | exact ⟨(.nominals : Entry), rfl⟩
      | exact ⟨(.states false : Entry), rfl⟩
      | exact ⟨(.states true : Entry), rfl⟩
      | exact ⟨(.derivatives : Entry), rfl⟩
      | exact ⟨(.float64 false : Entry), rfl⟩
      | exact ⟨(.float64 true : Entry), rfl⟩
      | exact ⟨(.terminate : Entry), rfl⟩
      | exact ⟨(.time : Entry), rfl⟩
      | exact ⟨(.entry .event : Entry), rfl⟩
      | exact ⟨(.entry .continuous : Entry), rfl⟩
      | exact ⟨(.completed : Entry), rfl⟩
      | exact ⟨(.discrete : Entry), rfl⟩
      | exact ⟨(.step : Entry), rfl⟩
      | exact ⟨(.eventIndicators : Entry), rfl⟩
      | exact ⟨(.evaluation : Entry), rfl⟩
      | exact ⟨(.absent .float32 false : Entry), rfl⟩
      | exact ⟨(.absent .float32 true : Entry), rfl⟩
      | exact ⟨(.absent .int8 false : Entry), rfl⟩
      | exact ⟨(.absent .int8 true : Entry), rfl⟩
      | exact ⟨(.absent .uint8 false : Entry), rfl⟩
      | exact ⟨(.absent .uint8 true : Entry), rfl⟩
      | exact ⟨(.absent .int16 false : Entry), rfl⟩
      | exact ⟨(.absent .int16 true : Entry), rfl⟩
      | exact ⟨(.absent .uint16 false : Entry), rfl⟩
      | exact ⟨(.absent .uint16 true : Entry), rfl⟩
      | exact ⟨(.absent .int32 false : Entry), rfl⟩
      | exact ⟨(.absent .int32 true : Entry), rfl⟩
      | exact ⟨(.absent .uint32 false : Entry), rfl⟩
      | exact ⟨(.absent .uint32 true : Entry), rfl⟩
      | exact ⟨(.absent .int64 false : Entry), rfl⟩
      | exact ⟨(.absent .int64 true : Entry), rfl⟩
      | exact ⟨(.absent .uint64 false : Entry), rfl⟩
      | exact ⟨(.absent .uint64 true : Entry), rfl⟩
      | exact ⟨(.absent .boolean false : Entry), rfl⟩
      | exact ⟨(.absent .boolean true : Entry), rfl⟩
      | exact ⟨(.absent .string false : Entry), rfl⟩
      | exact ⟨(.absent .string true : Entry), rfl⟩
      | exact ⟨(.absent .binary false : Entry), rfl⟩
      | exact ⟨(.absent .binary true : Entry), rfl⟩
      | (refine ⟨Entry.capability _ ?_, rfl⟩
         simp [CapabilityRejection.signatures])))

end Rumoca.FMI3.PublicAPI
