import RumocaFMI3.DiscreteContract

noncomputable section
namespace Rumoca.FMI3.DiscreteCalls
open CTree CMemory CBody StaticFactory CLiteral.Interface

/-- Non-null arguments on the actual parameter list have a total address
representation; values assigned to unrelated names do not affect the call. -/
theorem nonnull_arguments (handle : Option Address) (addresses : String → Option Address)
    (present : ∀ name ∈ names, (addresses name).isSome = true) :
    ∃ actual : String → Address,
      arguments handle addresses = arguments handle (fun name => some (actual name)) := by
  let actual := fun name => (addresses name).getD ⟨0, [], 0⟩
  refine ⟨actual, congrArg (List.cons (Value.pointer handle)) ?_⟩
  apply List.map_congr_left
  intro name member
  have valid := present name member
  cases selected : addresses name with
  | none => simp [selected] at valid
  | some address => simp [actual, selected]

theorem outputs_compatible
    (writable : ∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) :
    COutputAssignments.Compatible (outputs addresses) := by
  have value : ∀ entry ∈ outputs addresses, entry.value = zeroValue entry.type := by
    intro entry member
    obtain ⟨layout, _, rfl⟩ := List.mem_map.mp member
    rfl
  intro a ha b hb same
  obtain ⟨old, first⟩ := writable a ha
  obtain ⟨previous, second⟩ := writable b hb
  rw [same] at first
  have types : a.type = b.type := congrArg Cell.type (Option.some.inj (first.symm.trans second))
  exact ⟨types, by rw [value a ha, value b hb, types]⟩

theorem returned_outputs
    (writable : ∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) :
    ∀ layout ∈ layouts,
      load (COutputAssignments.after heap (outputs addresses)) (addresses layout.1) = some (zeroValue layout.2) := by
  intro layout member
  have stored := COutputAssignments.outputs_stored (heap := heap) (outputs_compatible writable)
    (output addresses layout) (List.mem_map.mpr ⟨layout, member, rfl⟩)
  change COutputAssignments.after heap (outputs addresses) (addresses layout.1) =
    some ⟨layout.2, true, some (zeroValue layout.2)⟩ at stored
  simp only [layouts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [load, stored, zeroValue, convert, Value.truth, Value.finite]

theorem frame (heap : Heap) (addresses : String → Address) (query : Address)
    (outside : ∀ name ∈ names, query ≠ addresses name) :
    COutputAssignments.after heap (outputs addresses) query = heap query := by
  apply COutputAssignments.frame
  intro entry member
  obtain ⟨layout, declared, rfl⟩ := List.mem_map.mp member
  exact outside layout.1 (List.mem_map.mpr ⟨layout, declared, rfl⟩)

theorem instance_frame (heap : Heap) (p : Address) (addresses : String → Address) (query : Address)
    (outputsOutside : ∀ name ∈ names, (addresses name).block ≠ p.block)
    (sameBlock : query.block = p.block) :
    COutputAssignments.after heap (outputs addresses) query = heap query := by
  apply frame
  intro name member equal
  exact outputsOutside name member ((congrArg Address.block equal).symm.trans sameBlock)

/-- The no-event unit adapter finishes its public discrete update, retains
all instance state/history and returns the prepared output values. This is
the call result needed to discharge event-iteration readiness in ME traces. -/
theorem history_call [interface : CInterface] (program : CCalls.Events.Program E)
    (quiet : QuietContract program) (heap : Heap) (p : Address) (addresses : String → Address)
    (clock : Time.Clock) (history : Time.History) (state : ModelExchange.State)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 2)⟩)
    (clockStored : HistoryProofs.Stored heap p clock) (historyStored : Time.Represents history clock)
    (stateStored : StateProofs.Represents heap p state)
    (stopDefined : load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome))
    (stopValue : ∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop))
    (writable : ∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry)
    (outputsOutside : ∀ name ∈ names, (addresses name).block ≠ p.block) :
    let after := COutputAssignments.after heap (outputs addresses)
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (fun name => some (addresses name))) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, after⟩) ∧
    HistoryProofs.Stored after p clock ∧ Time.Represents history clock ∧
    StateProofs.Represents after p state ∧
    after (p.member "mode") = some ⟨.int32, true, some (.integer 2)⟩ ∧
    TimeCalls.Bounds after p history.window clock.minimum ∧
    (∀ layout ∈ layouts, load after (addresses layout.1) = some (zeroValue layout.2)) ∧
    (∀ query, query.block = p.block → after query = heap query) := by
  have framed := instance_frame heap p addresses
  have fieldFrame (name : String) := framed (p.member name) outputsOutside rfl
  have clockAfter : HistoryProofs.Stored (COutputAssignments.after heap (outputs addresses)) p clock := by
    exact ⟨(fieldFrame "time").trans clockStored.time, (fieldFrame "timeMin").trans clockStored.minimum,
      (fieldFrame "eventTime").trans clockStored.eventTime, (fieldFrame "lastCompleted").trans clockStored.lastCompleted⟩
  have stateAfter : StateProofs.Represents (COutputAssignments.after heap (outputs addresses)) p state := by
    simpa only [StateProofs.Represents, load,
      framed (StateProofs.stateAddress p) outputsOutside rfl] using stateStored
  have modeLoaded : load heap (p.member "mode") = some (.integer 2) := by simp [load, hm, convert]
  refine ⟨quiet.successful heap p addresses hk modeLoaded writable, clockAfter, historyStored,
    stateAfter, (fieldFrame "mode").trans hm, ?_, returned_outputs writable,
    fun query sameBlock => framed query outputsOutside sameBlock⟩
  refine ⟨historyStored.minimum, HistoryProofs.load_cell clockAfter.minimum, ?_, ?_⟩
  · simpa only [load, fieldFrame] using stopDefined
  · intro stop selected
    simpa only [load, fieldFrame] using stopValue stop selected

end Rumoca.FMI3.DiscreteCalls
