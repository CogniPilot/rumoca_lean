import RumocaFMI3.StepArguments
import RumocaFMI3.StaticFactoryOwnership

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory

theorem StepArguments.Storage.storage_preserved (stored : StepArguments.Storage before p buffers)
    (preserved : CStorage.Preserves before after) : StepArguments.Storage after p buffers := by
  refine ⟨?_, ?_, ?_, ?_, stored.outsideEvent, stored.outsideTerminate, stored.outsideEarly, stored.outsideLast⟩
  · obtain ⟨old, found⟩ := stored.event
    exact preserved.cell found
  · obtain ⟨old, found⟩ := stored.terminate
    exact preserved.cell found
  · obtain ⟨old, found⟩ := stored.early
    exact preserved.cell found
  · obtain ⟨old, found⟩ := stored.last
    exact preserved.cell found

theorem StepArguments.Storage.at_index (stored : StepArguments.Storage heap p buffers) (slot : Nat) :
    StepArguments.Storage heap (p.index slot) buffers :=
  ⟨stored.event, stored.terminate, stored.early, stored.last,
    stored.outsideEvent, stored.outsideTerminate, stored.outsideEarly, stored.outsideLast⟩

theorem InstanceInitialization.Initialized.state_cell
    (initialized : InstanceInitialization.Initialized heap p kind environment logger logging)
    (initial : Binary64.Value) (loaded : load heap (StateProofs.stateAddress p) = some (.finite initial)) :
    heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite initial)⟩ := by
  obtain ⟨old, stored⟩ := initialized.storage.state
  cases old with
  | none => simp [load, stored] at loaded
  | some value =>
    have same : value = Value.finite initial := by
      simp only [load, stored] at loaded
      change ((convert .float64 value).bind fun checked =>
        if checked = value then some value else none) = some (.finite initial) at loaded
      obtain ⟨checked, _, returned⟩ := Option.bind_eq_some_iff.mp loaded
      split at returned
      · exact Option.some.inj returned
      · contradiction
    simpa only [same] using stored

end Rumoca.FMI3
end
