import RumocaFMI3.DebugLoggingRuntime
import RumocaFMI3.DebugLoggingMetadata

/-! The legal-request predicate is stated independently of C validation and
uses the XML category names. The complete public contract entails successful
configuration, an exact flag update and preservation of every other cell. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody
open scoped Classical
variable [CInterface]

theorem legal_behaviors (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (failures)
    (contract : RequestContract program heap p kind mode failures)
    (pointer : Option Address) (count : UInt64) (enabled : Bool) (old : Option Value)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (caller : pointer.isSome = true → Entries heap pointer count.toNat selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (legal : LegalRequest pointer count.toNat selected bytes ["logStatus"]) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩ := by
  have readable : count.toNat = 0 ∨ pointer.isSome = true := by
    by_cases zero : count.toNat = 0
    · exact Or.inl zero
    · exact Or.inr (legal.2.1 (Nat.pos_of_ne_zero zero))
  have result := contract pointer count enabled old selected bytes hk hm caller storage behavior
  simpa only [Responses, if_pos readable, if_pos (legal_single_accepted legal)] using result

theorem legal_returned (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode) (failures)
    (contract : RequestContract program heap p kind mode failures)
    (pointer : Option Address) (count : UInt64) (enabled : Bool) (old : Option Value)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (caller : pointer.isSome = true → Entries heap pointer count.toNat selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (legal : LegalRequest pointer count.toNat selected bytes ["logStatus"])
    (events : List E) (result : CBody.Result)
    (executed : (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done)
      (.terminates events result)) :
    events = [] ∧ result.value = .integer 0 ∧
    load result.heap (p.member "logging") = some (boolean enabled) ∧
    CStorage.Preserves heap result.heap ∧ CReadOnly.Preserves heap result.heap ∧
    ∀ address, address ≠ p.member "logging" → result.heap address = heap address := by
  have same := (legal_behaviors program heap p kind mode failures contract pointer count enabled old
    selected bytes hk hm caller storage legal _).mp executed
  injection same with eventsEqual resultEqual
  subst events
  subst result
  exact ⟨rfl, rfl, written_flag heap p enabled, (written_storage heap p enabled old storage).1,
    (written_storage heap p enabled old storage).2, written_frame heap p enabled⟩

end Rumoca.FMI3.DebugLogging
end
