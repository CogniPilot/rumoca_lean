import RumocaFMI3.PublicAPI
import RumocaFMI3.ReservationOriginPolicy

namespace Rumoca.FMI3.PublicAPI
open CTree

/-- Instance methods borrow an existing handle. Factories, version inquiry,
unsupported Scheduled Execution creation and instance destruction have their
separate ownership rules. Classification uses the existing API index. -/
def Entry.ordinary : Entry → Bool
  | .version | .factory _ | .scheduled | .release => false
  | _ => true

def InstanceMethod (signature : Signature) : Prop :=
  signature.parameters.head? = some ⟨"fmi3Instance", "instance", false⟩ ∧
  signature.result = "fmi3Status" ∧
  signature.name ≠ StaticRelease.function.signature.name ∧
  ¬ ReservationOrigin.factory signature.name

private local instance factoryDecidable (name : String) : Decidable (ReservationOrigin.factory name) := by
  unfold ReservationOrigin.factory
  infer_instance

private theorem capability_methods : ∀ sig ∈ CapabilityRejection.signatures, InstanceMethod sig := by
  simp only [CapabilityRejection.signatures, List.forall_mem_cons]
  repeat' constructor
  all_goals first | (intro x impossible; cases impossible) | decide +kernel

/-- Every indexed ordinary public method takes the instance as its first
argument. The exact emitted signature also excludes factory/release routing. -/
theorem ordinary_signature (api : Entry) (ordinary : api.ordinary = true) : InstanceMethod api.signature := by
  cases api with
  | version | factory | scheduled | release => simp [Entry.ordinary] at ordinary
  | capability sig member => exact capability_methods sig member
  | absent ty write => cases ty <;> cases write <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | initialization enter => cases enter <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | counts events => cases events <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | states write => cases write <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | float64 write => cases write <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | entry which => cases which <;> exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩
  | _ => exact ⟨rfl, rfl, by decide +kernel, by decide +kernel⟩

/-- The handle-method classifier is exhaustive for the emitted API index. -/
theorem ordinary_iff (api : Entry) : api.ordinary = true ↔ InstanceMethod api.signature := by
  constructor
  · exact ordinary_signature api
  · intro method
    cases api with
    | release => exact False.elim (method.2.2.1 rfl)
    | version | scheduled => simpa [InstanceMethod, Entry.signature, Version.signature,
        ScheduledCreation.signature, StaticRelease.function] using method.1
    | factory kind => cases kind <;> simp [InstanceMethod, Entry.signature, FactoryArguments.signature] at method
    | _ => rfl

end Rumoca.FMI3.PublicAPI
