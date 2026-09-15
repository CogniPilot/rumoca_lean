import RumocaFMI3.DebugLoggingEntry

/-! Public logging behavior under ordinary typed argument binding. The exact
function table definition, library semantics and original caller resources
determine the result; no expected return or future heap is a premise. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CStringMemory
open scoped Classical
variable [interface : CInterface]

theorem call_behaviors (types : EntryTypes) (program : CCalls.Events.Program E)
    (library : Library program) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (count : UInt64) (enabled : Bool) (old : Option Value) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (selected : Nat → Option Address) (bytes : Nat → List UInt8) (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (caller : pointer.isSome = true → Entries heap pointer count.toNat selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (missingOutcomes unknownOutcomes : Transition.Events.Observation E CBody.Result → Prop)
    (missingContract : FailureContract program heap p "Missing log categories" missingOutcomes)
    (unknownContract : FailureContract program heap p "Unknown log category" unknownOutcomes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done) behavior ↔
    (if count.toNat = 0 ∨ pointer.isSome = true then
      if ∀ i < count.toNat, Accepted (selected i) (bytes i) expectedBytes then
        behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩
      else unknownOutcomes behavior
     else missingOutcomes behavior) := by
  obtain ⟨localTypes, entered⟩ := public_prefix types program heap p enabled count pointer kind mode
    defined kindValue modeValue
  exact (CCalls.Events.internal_prefix_behaviors program entered behavior).trans
    (code_behaviors program library (locals p enabled count pointer) localTypes heap p expected pointer
      count.toNat enabled old (public_scope p enabled count pointer) count.toNat_lt_size selected bytes
      expectedBytes literal expectedStored caller storage missingOutcomes unknownOutcomes
      missingContract unknownContract behavior)

theorem call_success_behaviors (types : EntryTypes) (program : CCalls.Events.Program E)
    (library : Library program) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (count : UInt64) (enabled : Bool) (old : Option Value) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (selected : Nat → Option Address) (bytes : Nat → List UInt8) (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer count.toNat selected bytes)
    (valid : ∀ i < count.toNat, Accepted (selected i) (bytes i) expectedBytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩ := by
  obtain ⟨localTypes, entered⟩ := public_prefix types program heap p enabled count pointer kind mode
    defined kindValue modeValue
  exact (CCalls.Events.internal_prefix_behaviors program entered behavior).trans
    (code_success_behaviors program library (locals p enabled count pointer) localTypes heap p expected
      pointer count.toNat enabled old (public_scope p enabled count pointer) count.toNat_lt_size
      selected bytes expectedBytes literal expectedStored entries valid storage behavior)

omit interface in
theorem written_flag (heap : Heap) (p : Address) (enabled : Bool) :
    load (written heap p enabled) (p.member "logging") = some (boolean enabled) := by
  cases enabled <;> simp [load, written, replace, boolean, convert, Value.truth]

theorem call_success_returned (types : EntryTypes) (program : CCalls.Events.Program E)
    (library : Library program) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (count : UInt64) (enabled : Bool) (old : Option Value) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (selected : Nat → Option Address) (bytes : Nat → List UInt8) (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer count.toNat selected bytes)
    (valid : ∀ i < count.toNat, Accepted (selected i) (bytes i) expectedBytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (observed : List E) (result : CBody.Result)
    (executed : (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) enabled count pointer) heap .done)
      (.terminates observed result)) :
    observed = [] ∧ result.value = .integer 0 ∧
    load result.heap (p.member "logging") = some (boolean enabled) ∧
    CStorage.Preserves heap result.heap ∧ CReadOnly.Preserves heap result.heap ∧
    ∀ address, address ≠ p.member "logging" → result.heap address = heap address := by
  have same := (call_success_behaviors types program library heap p expected pointer count enabled old
    kind mode defined kindValue modeValue selected bytes expectedBytes literal expectedStored entries
    valid storage _).mp executed
  injection same with eventsEqual resultEqual
  subst observed
  subst result
  exact ⟨rfl, rfl, written_flag heap p enabled, (written_storage heap p enabled old storage).1,
    (written_storage heap p enabled old storage).2, written_frame heap p enabled⟩

end Rumoca.FMI3.DebugLogging
end
