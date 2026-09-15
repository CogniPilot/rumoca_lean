import RumocaFMI3.LoggingCapabilityLifetime
import RumocaFMI3.InitializationProtocolCreation

/-! The persistent callback is supplied by the original factory arguments.
Its binding and universal host policy do not disappear when the original
logging flag is false. No initialized instance or future callback is assumed. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CMemory CBody StaticFactory CCalls.Events
variable [CInterface]

def Capability.Describes (capability : Capability) (args : FactoryArguments.Raw) : Prop :=
  args.logger = capability.logger ∧ args.environment = capability.environment

theorem Capability.factory_policy {capability : Capability}
    (describes : capability.Describes args) (bound : capability.Bound program)
    (required : capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained)) :
    InitializationProtocol.FactoryLogPolicy program objects retained args :=
  ⟨capability, describes, bound, required⟩

theorem Capability.created {capability : Capability}
    {objects : Objects} {owners : SlotOwners.State objects.capacity} {slot : Fin objects.capacity}
    (describes : capability.Describes args)
    (created : Created live objects.instances objects.flagsBlock owners slot owner kind
      args.environment args.logger args.logging) :
    capability.Configured live (objects.instances.index slot.val) args.logging := by
  apply capability.initialized
  simpa only [describes.1, describes.2] using created.initialized

theorem Capability.created_invariant {capability : Capability}
    (objects : Objects) {owners : SlotOwners.State objects.capacity} {slot : Fin objects.capacity}
    {readers : InitializationProtocol.ReadBank}
    (created : Created live objects.instances objects.flagsBlock owners slot owner kind
      args.environment args.logger args.logging)
    (storage : CStorage.Preserves original live) (readonly : CReadOnly.Preserves literals live)
    (describes : capability.Describes args) (bound : capability.Bound program)
    (required : capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained))
    (readerFrame : readers.Frame original live) :
    InitializationProtocol.Invariant program objects retained owners original literals live
      (objects.instances.index slot.val) kind InitializationProtocol.State.reset readers ∧
    capability.Configured live (objects.instances.index slot.val) args.logging ∧
    capability.Bound program ∧
    capability.Requires (fun _ effect => Float64Rejection.Respects effect objects retained) :=
  ⟨InitializationProtocol.Invariant.created objects created storage readonly
      (Capability.factory_policy describes bound required) readerFrame,
    Capability.created describes created, bound, required⟩

end Rumoca.FMI3.Logging
end
