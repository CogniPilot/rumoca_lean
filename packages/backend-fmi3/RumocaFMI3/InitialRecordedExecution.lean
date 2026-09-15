import RumocaFMI3.StaticRuntimeContract
import RumocaC.InvocationExecution

namespace Rumoca.FMI3.StaticRuntime
open CTree CMemory StaticFactory CCalls
noncomputable section

/-- The existing initial-storage contract, now in the host recording model.
The successful factory lease is its invocation serial. Release is a different
invocation and retains the factory lease as its ownership authority. This is
an exact sequential witness; arbitrary concurrent lifecycle composition is open. -/
def InitialRecordedExecution (model : Solve.FMI3Model source) (sigs : List Signature) : Prop :=
  ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags) (literals : CLiteralAddresses),
    let storage := objects instances flags separate
    letI : CInterface := executionInterface storage literals
    ∀ (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
    program.internal = LiteralPreparation.program model sigs →
    Identity.Bindings program →
    program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
    program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
    ∀ (kind : Kind) (args : FactoryArguments.Raw) (before : Heap),
    StaticStorage.Fresh storage before →
    IdentityRequest literals model kind args (StaticStorage.initial storage before) true →
    ∀ (serial thread : Nat) (policy : Host.Policy),
    policy.admit ⟨StaticStorage.initial storage before, fun _ => none⟩ thread
      (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) →
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin storage.capacity, ∃ live freed,
      trace.length ≤ storage.capacity ∧
      Created live storage.instances storage.flagsBlock
        (SlotOwners.update (fun _ => none) slot (some serial)) slot serial kind
        args.environment args.logger args.logging ∧
      SlotOwners.Represents storage.flagsBlock freed (fun _ : Fin storage.capacity => none) ∧
      CreationStorage freed storage.instances storage.flags storage.capacity ∧
      CStorage.Preserves (StaticStorage.initial storage before) freed ∧
      CReadOnly.Preserves before (StaticStorage.initial storage before) ∧
      (∃ chunks : List (List E), chunks.flatten = trace.map tag ∧
        Transition.Events.Reaches (Host.Recording.Step program policy)
          ⟨⟨StaticStorage.initial storage before, fun _ => none⟩, ⟨serial, fun _ => none⟩⟩
          (Host.Recording.callTrace ⟨serial, fun _ => none⟩ thread
            (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) chunks
            (.pointer (some (storage.instances.index slot.val))))
          ⟨⟨live, fun _ => none⟩, ⟨serial + 1, fun _ => none⟩⟩) ∧
      (policy.admit ⟨live, fun _ => none⟩ thread StaticRelease.function.signature.name
          [.pointer (some (storage.instances.index slot.val))] →
        ∃ chunks : List (List E), chunks.flatten = [tag (.write (AtomicSlots.address storage.flagsBlock slot) false)] ∧
          Transition.Events.Reaches (Host.Recording.Step program policy)
            ⟨⟨live, fun _ => none⟩, ⟨serial + 1, fun _ => none⟩⟩
            (Host.Recording.callTrace ⟨serial + 1, fun _ => none⟩ thread StaticRelease.function.signature.name
              [.pointer (some (storage.instances.index slot.val))] chunks .void)
            ⟨⟨freed, fun _ => none⟩, ⟨serial + 2, fun _ => none⟩⟩)

/-- Derive complete host calls, returned-handle provenance and ownership from
the existing actual C contract. No successful scan, call or release is a premise. -/
theorem initial_recorded (execution : InitialExecution model sigs) : InitialRecordedExecution model sigs := by
  intro E instances flags separate literals
  let storage := objects instances flags separate
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange write kind args before fresh request serial thread policy admitted
  obtain ⟨trace, slot, live, freed, bounded, created, restored, ready, preserved, readonly, creation, release⟩ :=
    execution E instances flags separate literals program tag actual identity exchange write kind args before fresh request serial
  have createdRun : Transition.Events.Reaches (Events.machine program).step
      (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args)
        (StaticStorage.initial storage before) .done)
      (trace.map tag) (.halted ⟨.pointer (some (storage.instances.index slot.val)), live⟩) :=
    Events.terminating_path ((creation _).mpr rfl)
  have aligned : Host.Recording.Aligned ⟨StaticStorage.initial storage before, fun _ => none⟩
      ⟨serial, fun _ => none⟩ := by intro thread; simp
  obtain ⟨chunks, flattened, recorded⟩ := Host.Recording.call_recorded program policy
    ⟨serial, fun _ => none⟩ aligned rfl admitted createdRun
  refine ⟨trace, slot, live, freed, bounded, created, restored, ready, preserved, readonly,
    ⟨chunks, flattened, recorded⟩, ?_⟩
  intro releaseAdmitted
  have releaseRun : Transition.Events.Reaches (Events.machine program).step
      (.calling StaticRelease.function.signature.name [.pointer (some (storage.instances.index slot.val))] live .done)
      [tag (.write (AtomicSlots.address storage.flagsBlock slot) false)] (.halted ⟨.void, freed⟩) :=
    Events.terminating_path ((release _).mpr rfl)
  have releaseAligned : Host.Recording.Aligned ⟨live, fun _ => none⟩ ⟨serial + 1, fun _ => none⟩ := by
    intro thread; simp
  exact Host.Recording.call_recorded program policy ⟨serial + 1, fun _ => none⟩ releaseAligned rfl releaseAdmitted releaseRun

end
end Rumoca.FMI3.StaticRuntime
