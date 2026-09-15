import RumocaFMI3.InitializationProtocolRunFrames

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory StaticFactory CCalls.Events
variable {readers : ReadBank}

/-- Reset establishes the protocol's fresh state from the actual simulation
storage. No pre-reset finite payload or initialization phase is assumed. -/
theorem Stored.reset_from {kind : Kind} {mode : Mode} (model : Solve.FMI3Model source) (storage : Reset.Storage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code)) :
    Stored (Reset.finalHeap heap p) p kind State.reset := by
  refine ⟨⟨(StaticReset.kind_value heap p).trans kindValue, ?_, ?_, ?_⟩,
    storage.preserved (Reset.preserves model heap p kind mode storage kindValue modeValue).1, trivial⟩
  · simp [State.reset, Phase.mode, Reset.finalHeap, LifecycleBodies.writeMode]
  · exact MENumericalHistory.reset_state_cell heap p
  · simp [State.reset, load, (Reset.history heap p).time, convert, Value.finite, Time.Clock.initial, HistoryProofs.cell]

theorem reset_invariant [CInterface] {program : Program Invocation}
    {kind : Kind} {mode : Mode}
    {objects : Objects} {owners : SlotOwners.State objects.capacity}
    (model : Solve.FMI3Model source) (reset : StaticReset.ExecutionContract program)
    (storage : Reset.Storage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (caller : CallerStorage objects retained original heap)
    (literals : CReadOnly.Preserves literalHeap heap)
    (logging : LogPolicy program objects retained heap p)
    (readerFrame : readers.Frame original heap)
    (readerOutside : ∀ q, readers.Region q → ¬ p.InRecord q) :
    (∀ behavior, (machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩) ∧
    Invariant program objects retained owners original literalHeap (Reset.finalHeap heap p) p kind State.reset readers ∧
    CReadOnly.Preserves heap (Reset.finalHeap heap p) ∧ Retains p heap (Reset.finalHeap heap p) := by
  have called := reset.successful heap p kind mode storage kindValue modeValue
  have memory := Reset.preserves model heap p kind mode storage kindValue modeValue
  have readonly := termination_preserves ((called _).mpr rfl)
  have retains := Reset.retained_field heap p
  exact ⟨called, ⟨Stored.reset_from model storage kindValue modeValue,
    SlotOwners.ordinary_preserves represented memory.2, caller.trans (CallerStorage.ordinary memory.1),
    literals.trans readonly, logging.framed retains,
    readerFrame.trans (fun q inside => StaticReset.record_frame heap p q (readerOutside q inside))⟩, readonly, retains⟩

end Rumoca.FMI3.InitializationProtocol
end
