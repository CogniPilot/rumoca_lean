import RumocaFMI3.TensorFunctions
import RumocaFMI3.FamilyContracts

/-! The two unsupported/absent-type function families over the tensor adapter
list. The family execution bodies are identical to the scalar renderer's; only
the surrounding function list (`TensorFunctions.functions`) and its literal pool
differ. The model-agnostic execution core is proved once over the profile-generic
`AdapterFamily`; the tensor family is `tensorFamily`, the tensor `AdapterFamily`
value, and every tensor family contract is that generic contract instantiated at
`tensorFamily`. No family execution proof is duplicated.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and neither the scalar renderer, the families nor any
existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface
open TensorFunctions (tensorFunction functions program prepare)

variable {source : AST.Model} {shape : Rumoca.Tensor.Shape}

/-! ### Bridging lemmas: fallthrough signatures render the scalar body -/

/-- Every absent-type family signature falls through the tensor dispatch to the
scalar body. -/
theorem absent_function (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (ty : AbsentVariables.VariableType) (write : Bool) :
    tensorFunction model m (AbsentVariables.signature ty write)
      = Runtime.function model (AbsentVariables.signature ty write) := by
  cases ty <;> cases write <;> rfl

/-- Every unsupported-capability signature falls through the tensor dispatch to
the scalar body. -/
theorem capability_function (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) :
    ∀ sig ∈ CapabilityRejection.signatures, tensorFunction model m sig = Runtime.function model sig := by
  intro sig member
  fin_cases member <;> rfl

/-- `fmi3InstantiateScheduledExecution` falls through the tensor dispatch to the
scalar body. -/
theorem scheduled_function (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) :
    tensorFunction model m ScheduledCreation.signature
      = Runtime.function model ScheduledCreation.signature := rfl

/-- Definition-table fact for any signature that renders the scalar body. -/
theorem scalar_bound (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ sigs)
    (routed : tensorFunction model m sig = Runtime.function model sig) :
    (program model m sigs).definitions sig.name = some (.tree (Runtime.function model sig)) := by
  rw [← routed]; exact TensorFunctions.function_bound model m sigs unique sig member

/-- List membership of a scalar body rendered by the tensor list. -/
theorem scalar_member (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs)
    (routed : tensorFunction model m sig = Runtime.function model sig) :
    Runtime.function model sig ∈ functions model m sigs := by
  rw [← routed]; exact List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩)

/-- The tensor adapter as a profile-generic `AdapterFamily`: the tensor dispatched
function, helper prefix, emitted list, definition table, literal pool, render and
the tensor definition-table/pool facts, with the tensor fallthrough routing of
every family signature to the scalar body. -/
def tensorFamily (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape) :
    AdapterFamily source where
  model := model
  pick := TensorFunctions.tensorFunction model m
  helpers := TensorFunctions.helpers
  functions := TensorFunctions.functions model m
  functions_def := fun _ => rfl
  fail_mem := by simp [TensorFunctions.helpers]
  program := TensorFunctions.program model m
  render := TensorFunctions.render model m
  function_bound := TensorFunctions.function_bound model m
  helpers_bound := TensorFunctions.helpers_bound model m
  prepare := TensorFunctions.prepare model m
  text_bound := TensorFunctions.text_bound model m
  rendered_member := TensorFunctions.rendered_member model m
  absent_routes := absent_function model m
  capability_routes := capability_function model m

/-! ### Absent-type variable family over the tensor list -/

namespace TensorAbsentVariables
open AbsentVariables

/-- The absent-type prepared contract over the tensor adapter definition table
and literal pool: the generic absent-type prepared contract at `tensorFamily`. -/
abbrev PreparedContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop :=
  AbsentFamily.PreparedContract (tensorFamily model m) sigs ty write pool

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs ty write pool :=
  AbsentFamily.prepared_correct (tensorFamily model m) sigs ty write unique member made

abbrev FunctionContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (ty : VariableType) (write : Bool) (text : String) : Prop :=
  AbsentFamily.FunctionContract (tensorFamily model m) sigs ty write text

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs) :
    FunctionContract model m sigs ty write (Runtime.function model (signature ty write)).render :=
  AbsentFamily.rendered_contract (tensorFamily model m) sigs ty write unique member

/-- The absent-type family contract over the tensor adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) : Prop :=
  AbsentFamily.FamilyContract (tensorFamily model m) sigs

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ ty write, signature ty write ∈ sigs) : FamilyContract model m sigs :=
  AbsentFamily.family_correct (tensorFamily model m) sigs unique members

end TensorAbsentVariables

/-! ### Unsupported-capability family over the tensor list -/

namespace TensorCapabilityRejection
open CapabilityRejection

abbrev PreparedContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop :=
  CapabilityFamily.PreparedContract (tensorFamily model m) sigs sig tail pool

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : tensorFunction model m sig = Runtime.function model sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs sig tail pool :=
  CapabilityFamily.prepared_correct (tensorFamily model m) sigs profile routed fallthrough unique member made

abbrev FunctionContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter) (text : String) : Prop :=
  CapabilityFamily.FunctionContract (tensorFamily model m) sigs sig tail text

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : tensorFunction model m sig = Runtime.function model sig)
    (printable : Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs) :
    FunctionContract model m sigs sig tail (Runtime.function model sig).render :=
  CapabilityFamily.rendered_contract (tensorFamily model m) sigs profile routed fallthrough printable unique member

/-- The unsupported-capability family contract over the tensor adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature) : Prop :=
  CapabilityFamily.FamilyContract (tensorFamily model m) sigs

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.TensorFMI3Model shape)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs) : FamilyContract model m sigs :=
  CapabilityFamily.family_correct (tensorFamily model m) sigs unique members

end TensorCapabilityRejection

end Rumoca.FMI3
end
