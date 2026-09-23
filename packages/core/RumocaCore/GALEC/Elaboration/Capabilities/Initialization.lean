import RumocaCore.GALEC.Elaboration.Capabilities.Generic

/-! RESTRICTED non-input-write initialization profile. Non-input constants may
be initialized. This does not establish normative Startup legality or resolve
the pinned input-initialization versus assignment-ban conflict. -/
namespace Rumoca.GALEC.Elaboration.Capabilities.Initialization
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

def Writable (declaration : Declarations.Real.Descriptor) : Prop :=
  declaration.direction ≠ .input

def role (declaration : Declarations.Real.Descriptor) : Layout.Role :=
  match declaration.direction with
  | .input => .readOnly
  | _ => .writable

theorem role_writable_iff (declaration : Declarations.Real.Descriptor) :
    role declaration = .writable ↔ Writable declaration := by
  obtain ⟨name, visibility, direction, variability, shape⟩ := declaration
  cases direction <;> simp [role, Writable]

theorem role_readOnly_iff (declaration : Declarations.Real.Descriptor) :
    role declaration = .readOnly ↔ declaration.direction = .input := by
  obtain ⟨name, visibility, direction, variability, shape⟩ := declaration
  cases direction <;> simp [role]

def fields (declarations : List Declarations.Real.Descriptor) : List Layout.Field :=
  Capabilities.Generic.fields role declarations

theorem fields_declarations (declarations : List Declarations.Real.Descriptor) :
    (fields declarations).map Layout.Field.declaration = declarations :=
  Capabilities.Generic.fields_declarations role declarations

theorem resolved_metadata
    (resolved : BindingTable.Resolves (Layout.bindings (fields declarations)) key value) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      value.1 = declaration.shape ∧ Layout.roleOf value = role declaration :=
  Capabilities.Generic.resolved_metadata resolved

theorem resolved_writable
    (resolved : BindingTable.Resolves (Layout.bindings (fields declarations)) key ⟨shape, .writable ref⟩) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      shape = declaration.shape ∧ Writable declaration :=
  Capabilities.Generic.resolved_writable role_writable_iff resolved

theorem target_writable
    (typed : TargetLowering.Elaborates (Layout.bindings (fields declarations)) names source target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Writable declaration :=
  Capabilities.Generic.target_writable role_writable_iff typed

theorem target_lowered_writable
    (lowered : TargetLowering.lower (Layout.bindings (fields declarations)) names source = some target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Writable declaration :=
  Capabilities.Generic.target_lowered_writable role_writable_iff lowered

abbrev StatementWrites := Capabilities.Generic.StatementWrites Writable
abbrev BodyWrites := Capabilities.Generic.BodyWrites Writable

theorem statement_writes
    (typed : Bodies.StatementElaborates (Layout.bindings (fields declarations))
      HasShape ceiling names source stmt) : StatementWrites declarations source :=
  Capabilities.Generic.statement_writes role_writable_iff typed

theorem body_writes
    (typed : Bodies.BodyElaborates (Layout.bindings (fields declarations))
      HasShape ceiling names sources stmt) : BodyWrites declarations sources :=
  Capabilities.Generic.body_writes role_writable_iff typed

theorem lowered_body_writes
    (lowered : Bodies.statements (Layout.bindings (fields declarations))
      lookupShape ceiling names sources = some stmt) : BodyWrites declarations sources :=
  Capabilities.Generic.lowered_body_writes role_writable_iff lowered

end Rumoca.GALEC.Elaboration.Capabilities.Initialization
