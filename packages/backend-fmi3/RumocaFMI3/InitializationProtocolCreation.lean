import RumocaFMI3.InitializationProtocolLifetime

noncomputable section
namespace Rumoca.FMI3.InitializationProtocol
open CMemory CBody StaticFactory CCalls.Events

/-- Requirements on the host's factory arguments and optional external
logger, before an instance exists. No future field value is a premise. -/
def FactoryLogPolicy [CInterface] (program : Program Invocation) (objects : Objects)
    (retained : Address → Prop) (args : FactoryArguments.Raw) : Prop :=
  (args.logger = none ∨ args.logging = false) ∨
  ∃ (logger : Address) (name : String) (effect : ReturningEffect (Logging.signature name)),
    args.logger = some logger ∧ args.logging = true ∧
    program.addresses logger = some name ∧
    program.externals name = some (External.observed (Logging.signature name) effect) ∧
    Float64Rejection.Respects effect objects retained

theorem LogPolicy.created [CInterface] {program : Program Invocation}
    (initialized : InstanceInitialization.Initialized heap p kind args.environment args.logger args.logging)
    (policy : FactoryLogPolicy program objects retained args) : LogPolicy program objects retained heap p := by
  rcases policy with suppressed | ⟨logger, name, effect, loggerBound, loggingBound, address, external, respects⟩
  · exact Or.inl ⟨args.logger, args.logging, initialized.loggerValue, initialized.loggingValue, suppressed⟩
  · exact Or.inr ⟨logger, args.environment, name, effect,
      by simpa only [loggerBound] using initialized.loggerValue,
      by simpa only [loggingBound, boolean] using initialized.loggingValue,
      initialized.environmentValue, address, external, respects⟩

theorem Invariant.created [CInterface] {program : Program Invocation}
    (objects : Objects) {owners : SlotOwners.State objects.capacity} {slot : Fin objects.capacity}
    (created : Created live objects.instances objects.flagsBlock owners slot owner kind
      args.environment args.logger args.logging)
    (storage : CStorage.Preserves original live) (readonly : CReadOnly.Preserves literals live)
    (logging : FactoryLogPolicy program objects retained args) :
    Invariant program objects retained owners original literals live (objects.instances.index slot.val) kind State.reset :=
  ⟨Stored.created created.initialized, created.represented, CallerStorage.ordinary storage,
    readonly, LogPolicy.created created.initialized logging⟩

end Rumoca.FMI3.InitializationProtocol
end
