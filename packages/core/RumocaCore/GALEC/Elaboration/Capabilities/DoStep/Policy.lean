import RumocaCore.GALEC.Elaboration.Layout.Base
import RumocaCore.GALEC.Elaboration.Targets

/-! A restricted DoStep capability policy for the current Real declaration IR.
It captures the pinned eFMI control-input assignment prohibition and DoStep
constant preservation. It is not complete declaration/method legality, ranged
variable limitation, Startup policy or a claim about parameter kinds absent
from this IR. Roles are derived before typed storage construction, never in C. -/
namespace Rumoca.GALEC.Elaboration.Capabilities.DoStep
open Rumoca.Tensor Rumoca.Solve.Tensor

/-- Independent writable-state condition, not an invocation of the classifier. -/
def Writable (declaration : Declarations.Real.Descriptor) : Prop :=
  declaration.variability = .variable ∧ declaration.direction ≠ .input

def role (declaration : Declarations.Real.Descriptor) : Layout.Role :=
  match declaration.direction, declaration.variability with
  | .input, _ | _, .constant => .readOnly
  | _, .variable => .writable

theorem role_writable_iff (declaration : Declarations.Real.Descriptor) :
    role declaration = .writable ↔ Writable declaration := by
  obtain ⟨name, visibility, direction, variability, shape⟩ := declaration
  cases direction <;> cases variability <;> simp [role, Writable]

theorem role_readOnly_iff (declaration : Declarations.Real.Descriptor) :
    role declaration = .readOnly ↔
      declaration.direction = .input ∨ declaration.variability = .constant := by
  obtain ⟨name, visibility, direction, variability, shape⟩ := declaration
  cases direction <;> cases variability <;> simp [role]

def fields (declarations : List Declarations.Real.Descriptor) : List Layout.Field :=
  declarations.map fun declaration => ⟨declaration, role declaration⟩

theorem fields_declarations (declarations : List Declarations.Real.Descriptor) :
    (fields declarations).map Layout.Field.declaration = declarations := by
  simp [fields, List.map_map, Function.comp_def]

theorem resolves_member (resolved : BindingTable.Resolves table key value) :
    (key, value) ∈ table := by
  induction resolved with
  | here => simp
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Every actual typed binding retains its originating whole-shaped descriptor
and the capability computed from that descriptor, even before uniqueness checks. -/
theorem resolved_metadata
    (resolved : BindingTable.Resolves (Layout.bindings (fields declarations)) key value) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      value.1 = declaration.shape ∧ Layout.roleOf value = role declaration := by
  have member : (key, value.1, Layout.roleOf value) ∈ Layout.describe (Layout.bindings (fields declarations)) :=
    List.mem_map.mpr ⟨(key, value), resolves_member resolved, rfl⟩
  rw [Layout.describe_bindings] at member
  obtain ⟨field, member, equal⟩ := List.mem_map.mp member
  obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
  have keyEq := congrArg Prod.fst equal
  have shapeEq := congrArg (fun x => x.2.1) equal
  have roleEq := congrArg (fun x => x.2.2) equal
  exact ⟨declaration, present, keyEq.symm, shapeEq.symm, roleEq.symm⟩

theorem resolved_writable
    (resolved : BindingTable.Resolves (Layout.bindings (fields declarations)) key ⟨shape, .writable ref⟩) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      shape = declaration.shape ∧ Writable declaration := by
  obtain ⟨declaration, present, keyEq, shapeEq, roleEq⟩ := resolved_metadata resolved
  exact ⟨declaration, present, keyEq, shapeEq,
    (role_writable_iff declaration).mp roleEq.symm⟩

/-- An independently typed assignment target cannot name a control input or
constant. The theorem traces the actual source path, not just its final role. -/
theorem target_writable
    (typed : TargetLowering.Elaborates (Layout.bindings (fields declarations)) names source target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Writable declaration := by
  cases typed with
  | writable read =>
    cases read with
    | indexed spelling binding indices =>
      obtain ⟨declaration, present, keyEq, shapeEq, writable⟩ := resolved_writable binding
      exact ⟨declaration, present, _, keyEq ▸ spelling, shapeEq, writable⟩

theorem target_lowered_writable
    (lowered : TargetLowering.lower (Layout.bindings (fields declarations)) names source = some target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Writable declaration :=
  target_writable ((TargetLowering.lower_iff _ _ _ _).mp lowered)

end Rumoca.GALEC.Elaboration.Capabilities.DoStep
