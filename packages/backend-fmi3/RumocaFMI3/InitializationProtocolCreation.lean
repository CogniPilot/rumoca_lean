import RumocaFMI3.InitializationProtocolLifetime

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CBody StaticFactory CCalls.Events

/-- The actual factory frame preserves every original borrowed read cell.
Readable arrays and strings cannot alias its atomic reservation flag. -/
theorem ReadBank.Stored.creation_frame {objects : Objects} {owners : SlotOwners.State objects.capacity}
    {readers : ReadBank} {slot : Fin objects.capacity}
    (stored : readers.Stored original)
    (represented : SlotOwners.Represents objects.flagsBlock original owners)
    (guarded : readers.Guarded objects retained (objects.instances.index slot.val) buffers)
    (frame : ∀ q, ¬ (objects.instances.index slot.val).InRecord q →
      q ≠ AtomicSlots.address objects.flagsBlock slot → live q = original q) :
    readers.Frame original live := by
  intro q inside
  exact frame q (guarded q inside).2.1 (stored.not_flag represented inside slot)

/-- Requirements on the host's factory arguments and optional external
logger, before an instance exists. No future field value is a premise. -/
def FactoryLogPolicy [CInterface] (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (args : FactoryArguments.Raw) : Prop :=
  ∃ capability : Logging.Capability,
    (args.logger = capability.logger ∧ args.environment = capability.environment) ∧
    capability.Bound program ∧
    capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained)

theorem LogPolicy.created [CInterface] {program : Program Invocation}
    (initialized : InstanceInitialization.Initialized heap p kind args.environment args.logger args.logging)
    (policy : FactoryLogPolicy program objects retained args) : LogPolicy program objects retained heap p := by
  obtain ⟨capability, described, bound, required⟩ := policy
  refine ⟨capability, args.logging, ⟨⟨?_, ?_⟩, initialized.loggingValue⟩,
    bound, required, initialized.storage.logging⟩
  · simpa only [described.1] using initialized.loggerValue
  · simpa only [described.2] using initialized.environmentValue

theorem Invariant.created [CInterface] {program : Program Invocation}
    (objects : Objects) {owners : SlotOwners.State objects.capacity} {slot : Fin objects.capacity} {readers : ReadBank}
    (created : Created live objects.instances objects.flagsBlock owners slot owner kind
      args.environment args.logger args.logging)
    (storage : CStorage.Preserves original live) (readonly : CReadOnly.Preserves literals live)
    (logging : FactoryLogPolicy program objects retained args)
    (readerFrame : readers.Frame original live) :
    Invariant program objects retained owners original literals live (objects.instances.index slot.val) kind State.reset readers :=
  ⟨Stored.created created.initialized, created.represented, CallerStorage.ordinary storage,
    readonly, LogPolicy.created created.initialized logging, readerFrame⟩

end Rumoca.FMI3.InitializationProtocol
end
