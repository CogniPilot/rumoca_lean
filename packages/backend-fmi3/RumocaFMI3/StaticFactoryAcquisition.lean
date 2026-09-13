import RumocaFMI3.StaticFactoryAdmission

noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody

/-- Public creation retains its reservation result, storage invariant and
memory frame so later lifecycle calls can consume them on the same heap. -/
theorem public_create_owned {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_request : IdentityRequest literals model kind args before true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_storage : CreationStorage before objects.instances objects.flags objects.capacity)
    (_bindings : ReservationBindings program tag)
    (owners : SlotOwners.State objects.capacity)
    (_represented : SlotOwners.Represents objects.flagsBlock before owners)
    (_available : ∃ slot, owners slot = none) (owner : Nat),
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity, ∃ live,
      trace.length ≤ objects.capacity ∧
      SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
        slot owner kind args.environment args.logger args.logging ∧
      CStorage.Preserves before live ∧
      (∀ query, ¬ (objects.instances.index slot.val).InRecord query →
        query ≠ AtomicSlots.address objects.flagsBlock slot → live query = before query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) before .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot.val)), live⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program tag identity model kind args before request defined helper storage bindings
    owners represented available owner
  obtain ⟨types, scope, admission⟩ := public_admission objects literals program identity model kind args before .done
    request defined helper
  obtain ⟨trace, index, after, outcome⟩ := CAtomicScan.outcome_exists storage.flagsReady (Nat.zero_le objects.capacity)
  have bounds := CAtomicScan.outcome_bounds outcome
  have selected : index < objects.capacity := by
    by_contra outside
    have exhausted : index = objects.capacity := by omega
    rw [exhausted] at outcome
    obtain ⟨slot, vacant⟩ := available
    have busy := (AtomicSlots.scan_exhausted represented outcome).2 slot
    simp [SlotOwners.occupied, vacant] at busy
  obtain ⟨reserved, created, preserved, framed, creation⟩ := successful_owned program tag
    model.solve kind (FactoryValidation.locals kind args true) types before after objects.instances
    objects.flagsBlock objects.capacity args.environment args.logger args.logging scope storage bindings
    ⟨rfl, rfl, rfl⟩ owners represented owner ⟨index, selected⟩ outcome
  exact ⟨trace, ⟨index, selected⟩, _, by simpa using bounds.2.2,
    reserved, created, preserved, framed, fun behavior => (admission behavior).trans (creation behavior)⟩

end Rumoca.FMI3.StaticFactory

namespace Rumoca.FMI3.SlotOwners

theorem release_reserved_restore (reserved : reserve owners slot owner = some (update owners slot (some owner))) :
    update (update owners slot (some owner)) slot none = owners := by
  have vacant := (reserve_iff.mp reserved).1
  funext other
  by_cases same : other = slot
  · subst other
    simp [update, vacant]
  · simp [update, same]

end Rumoca.FMI3.SlotOwners
