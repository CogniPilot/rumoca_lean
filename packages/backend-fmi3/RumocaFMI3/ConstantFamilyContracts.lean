import RumocaFMI3.ConstantFunctions
import RumocaFMI3.FamilyContracts

/-! The two unsupported/absent-type function families over the constant adapter
list. The family execution bodies are identical to the scalar renderer's; only
the surrounding function list (`ConstantFunctions.functions`) and its literal pool
differ. The model-agnostic execution core is proved once over the profile-generic
`AdapterFamily`; the constant family is `constantFamily`, the constant
`AdapterFamily` value, and every constant family contract is that generic contract
instantiated at `constantFamily`. No family execution proof is duplicated.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and neither the scalar renderer, the families nor any
existing contract changes. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory CLiteral.Interface
open ConstantFunctions (constantFunction functions program prepare)

variable {source : AST.Model} {n : Nat}

/-! ### Bridging lemmas: fallthrough signatures render the scalar body -/

/-- Every absent-type family signature falls through the tensor dispatch to the
scalar body. -/
theorem constant_absent_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (ty : AbsentVariables.VariableType) (write : Bool) :
    constantFunction model m (AbsentVariables.signature ty write)
      = Runtime.function model (AbsentVariables.signature ty write) := by
  cases ty <;> cases write <;> rfl

/-- Every unsupported-capability signature falls through the tensor dispatch to
the scalar body. -/
theorem constant_capability_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    ∀ sig ∈ CapabilityRejection.signatures, constantFunction model m sig = Runtime.function model sig := by
  intro sig member
  fin_cases member <;> rfl

/-- `fmi3InstantiateScheduledExecution` falls through the tensor dispatch to the
scalar body. -/
theorem constant_scheduled_function (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    constantFunction model m ScheduledCreation.signature
      = Runtime.function model ScheduledCreation.signature := rfl

/-- Definition-table fact for any signature that renders the scalar body. -/
theorem constant_scalar_bound (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (sig : Signature) (member : sig ∈ sigs)
    (routed : constantFunction model m sig = Runtime.function model sig) :
    (program model m sigs).definitions sig.name = some (.tree (Runtime.function model sig)) := by
  rw [← routed]; exact ConstantFunctions.function_bound model m sigs unique sig member

/-- List membership of a scalar body rendered by the constant adapter list. -/
theorem constant_scalar_member (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (member : sig ∈ sigs)
    (routed : constantFunction model m sig = Runtime.function model sig) :
    Runtime.function model sig ∈ functions model m sigs := by
  rw [← routed]; exact List.mem_append_right _ (List.mem_map.mpr ⟨sig, member, rfl⟩)

/-- The constant adapter as a profile-generic `AdapterFamily`: the constant
dispatched function, helper prefix, emitted list, definition table, literal pool,
render and the constant definition-table/pool facts, with the constant fallthrough
routing of every family signature to the scalar body. -/
def constantFamily (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n) :
    AdapterFamily source where
  model := model
  pick := ConstantFunctions.constantFunction model m
  helpers := ConstantFunctions.helpers
  functions := ConstantFunctions.functions model m
  functions_def := fun _ => rfl
  fail_mem := by simp [ConstantFunctions.helpers, TensorFunctions.helpers]
  program := ConstantFunctions.program model m
  render := ConstantFunctions.render model m
  function_bound := ConstantFunctions.function_bound model m
  helpers_bound := ConstantFunctions.helpers_bound model m
  prepare := ConstantFunctions.prepare model m
  text_bound := ConstantFunctions.text_bound model m
  rendered_member := ConstantFunctions.rendered_member model m
  absent_routes := constant_absent_function model m
  capability_routes := constant_capability_function model m

/-! ### Absent-type variable family over the constant adapter list -/

namespace ConstantAbsentVariables
open AbsentVariables

/-- The absent-type prepared contract over the constant adapter definition table
and literal pool: the generic absent-type prepared contract at `constantFamily`. -/
abbrev PreparedContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop :=
  AbsentFamily.PreparedContract (constantFamily model m) sigs ty write pool

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs ty write pool :=
  AbsentFamily.prepared_correct (constantFamily model m) sigs ty write unique member made

abbrev FunctionContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool) (text : String) : Prop :=
  AbsentFamily.FunctionContract (constantFamily model m) sigs ty write text

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (ty : VariableType) (write : Bool)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : signature ty write ∈ sigs) :
    FunctionContract model m sigs ty write (Runtime.function model (signature ty write)).render :=
  AbsentFamily.rendered_contract (constantFamily model m) sigs ty write unique member

/-- The absent-type family contract over the constant adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) : Prop :=
  AbsentFamily.FamilyContract (constantFamily model m) sigs

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ ty write, signature ty write ∈ sigs) : FamilyContract model m sigs :=
  AbsentFamily.family_correct (constantFamily model m) sigs unique members

end ConstantAbsentVariables

/-! ### Unsupported-capability family over the constant adapter list -/

namespace ConstantCapabilityRejection
open CapabilityRejection

abbrev PreparedContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter)
    (pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)) : Prop :=
  CapabilityFamily.PreparedContract (constantFamily model m) sigs sig tail pool

theorem prepared_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : constantFunction model m sig = Runtime.function model sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs)
    {pool : Pool (LiteralPreparation.excluded ++ (functions model m sigs).flatMap functionNames)}
    (made : prepare model m sigs = some pool) : PreparedContract model m sigs sig tail pool :=
  CapabilityFamily.prepared_correct (constantFamily model m) sigs profile routed fallthrough unique member made

abbrev FunctionContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (sig : Signature) (tail : List Parameter) (text : String) : Prop :=
  CapabilityFamily.FunctionContract (constantFamily model m) sigs sig tail text

theorem rendered_contract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) (profile : Profile sig tail) (routed : Runtime.body model sig = CapabilityRejection.code)
    (fallthrough : constantFunction model m sig = Runtime.function model sig)
    (printable : Printer.SignaturePrintable RuntimePrinter.typedefs sig)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (member : sig ∈ sigs) :
    FunctionContract model m sigs sig tail (Runtime.function model sig).render :=
  CapabilityFamily.rendered_contract (constantFamily model m) sigs profile routed fallthrough printable unique member

/-- The unsupported-capability family contract over the constant adapter list. -/
def FamilyContract (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature) : Prop :=
  CapabilityFamily.FamilyContract (constantFamily model m) sigs

theorem family_correct (model : Solve.FMI3Model source) (m : Solve.ConstantFMI3Model n)
    (sigs : List Signature)
    (unique : ((functions model m sigs).map (fun fn => fn.signature.name)).Nodup)
    (members : ∀ sig ∈ CapabilityRejection.signatures, sig ∈ sigs) : FamilyContract model m sigs :=
  CapabilityFamily.family_correct (constantFamily model m) sigs unique members

end ConstantCapabilityRejection

end Rumoca.FMI3
end
