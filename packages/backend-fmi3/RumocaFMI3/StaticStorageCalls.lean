import RumocaFMI3.StaticStorage
import RumocaFMI3.StaticFactoryAdmission

/-! Static declarations establish the complete factory's storage premises.
The public entry executes identity validation, reservation, initialization and
return; release uses that same returned handle. There is no assumed writable
instance heap, successful scan/call, vacant owner state, or callback result.
The target profile, identity buffers and external routine bindings remain
explicit. This is a sequential history, not a native concurrent ABI theorem. -/
noncomputable section
namespace Rumoca.FMI3.StaticStorage
open CMemory StaticFactory

theorem initial_create_release {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_fresh : Fresh objects before)
    (_request : IdentityRequest literals model kind args (initial objects before) true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (StaticFactory.function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_bindings : ReservationBindings program tag) (_releaseBindings : StaticRelease.Bindings program tag)
    (owner : Nat),
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity, ∃ live freed,
      trace.length ≤ objects.capacity ∧
      Created live objects.instances objects.flagsBlock
        (SlotOwners.update (fun _ => none) slot (some owner)) slot owner kind
        args.environment args.logger args.logging ∧
      SlotOwners.Represents objects.flagsBlock freed (fun _ : Fin objects.capacity => none) ∧
      CreationStorage freed objects.instances objects.flags objects.capacity ∧
      CStorage.Preserves (initial objects before) freed ∧
      CReadOnly.Preserves before (initial objects before) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args)
          (initial objects before) .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot.val)), live⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (objects.instances.index slot.val))] live .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, freed⟩) := by
  letI : CInterface := executionInterface objects literals
  intro program tag identity model kind args before fresh request defined helper bindings releaseBindings owner
  have positive : 0 < objects.capacity := lt_of_lt_of_le (by decide +kernel : 0 < 2) objects.multiple
  obtain ⟨trace, slot, live, freed, work, created, owners, storage, preserved, creation, released⟩ :=
    public_create_release objects literals program tag identity model kind args (initial objects before)
      request defined helper (initial_ready objects before) bindings releaseBindings (fun _ => none)
      (initial_owners objects before) ⟨⟨0, positive⟩, rfl⟩ owner
  exact ⟨trace, slot, live, freed, work, created, owners, storage, preserved,
    initial_preserves fresh, creation, released⟩

end Rumoca.FMI3.StaticStorage
