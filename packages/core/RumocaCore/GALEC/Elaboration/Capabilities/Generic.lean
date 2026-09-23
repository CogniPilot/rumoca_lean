import RumocaCore.GALEC.Elaboration.Layout.Base
import RumocaCore.GALEC.Elaboration.Bodies.Lowering

/-! Role-parametric metadata tracing and independent recursive write policy.
Roles are compiler preparation parameters, not callbacks stored in target IR.
No particular method, declaration validity or normative permission is assumed. -/
namespace Rumoca.GALEC.Elaboration.Capabilities.Generic
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

variable {Allowed : Declarations.Real.Descriptor → Prop}

def fields (role : Declarations.Real.Descriptor → Layout.Role)
    (declarations : List Declarations.Real.Descriptor) : List Layout.Field :=
  declarations.map fun declaration => ⟨declaration, role declaration⟩

theorem fields_declarations (role : Declarations.Real.Descriptor → Layout.Role)
    (declarations : List Declarations.Real.Descriptor) :
    (fields role declarations).map Layout.Field.declaration = declarations := by
  simp [fields, List.map_map, Function.comp_def]

theorem resolves_member (resolved : BindingTable.Resolves table key value) :
    (key, value) ∈ table := by
  induction resolved with
  | here => simp
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

/-- The actual resolved slot has an originating descriptor with identical key,
whole shape and supplied role, even before source uniqueness is established. -/
theorem resolved_metadata
    (resolved : BindingTable.Resolves (Layout.bindings (fields role declarations)) key value) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      value.1 = declaration.shape ∧ Layout.roleOf value = role declaration := by
  have member : (key, value.1, Layout.roleOf value) ∈
      Layout.describe (Layout.bindings (fields role declarations)) :=
    List.mem_map.mpr ⟨(key, value), resolves_member resolved, rfl⟩
  rw [Layout.describe_bindings] at member
  obtain ⟨field, member, equal⟩ := List.mem_map.mp member
  obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
  have keyEq := congrArg Prod.fst equal
  have shapeEq := congrArg (fun x => x.2.1) equal
  have roleEq := congrArg (fun x => x.2.2) equal
  exact ⟨declaration, present, keyEq.symm, shapeEq.symm, roleEq.symm⟩

theorem resolved_writable
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (resolved : BindingTable.Resolves (Layout.bindings (fields role declarations))
      key ⟨shape, .writable ref⟩) :
    ∃ declaration ∈ declarations, key = [declaration.name] ∧
      shape = declaration.shape ∧ Allowed declaration := by
  obtain ⟨declaration, present, keyEq, shapeEq, roleEq⟩ := resolved_metadata resolved
  exact ⟨declaration, present, keyEq, shapeEq, (correct declaration).mp roleEq.symm⟩

/-- Trace the original path and its original index expressions, retaining
the typed target's full shape; do not infer permissions from a backend name. -/
theorem target_writable
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (typed : TargetLowering.Elaborates (Layout.bindings (fields role declarations))
      names source target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Allowed declaration := by
  cases typed with
  | writable read =>
    cases read with
    | indexed spelling binding indices =>
      obtain ⟨declaration, present, keyEq, shapeEq, writable⟩ := resolved_writable correct binding
      exact ⟨declaration, present, _, keyEq ▸ spelling, shapeEq, writable⟩

theorem target_lowered_writable
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (lowered : TargetLowering.lower (Layout.bindings (fields role declarations))
      names source = some target) :
    ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface source [declaration.name] indices ∧
      target.shape = declaration.shape ∧ Allowed declaration :=
  target_writable correct ((TargetLowering.lower_iff _ _ _ _).mp lowered)

mutual
/-- Source-only write-side condition; neither role classification, lowering,
nor target execution defines this judgment. Index expressions are retained. -/
inductive StatementWrites (Allowed : Declarations.Real.Descriptor → Prop)
    (declarations : List Declarations.Real.Descriptor) : AST.Statement → Prop where
  | assign (allowed : ∃ declaration ∈ declarations, ∃ indices,
      Path.Surface target [declaration.name] indices ∧ Allowed declaration) :
      StatementWrites Allowed declarations (.assign target value)
  | loop : BodyWrites Allowed declarations body →
      StatementWrites Allowed declarations (.forLoop binder start stride stop body)

inductive BodyWrites (Allowed : Declarations.Real.Descriptor → Prop)
    (declarations : List Declarations.Real.Descriptor) : List AST.Statement → Prop where
  | nil : BodyWrites Allowed declarations []
  | cons : StatementWrites Allowed declarations source → BodyWrites Allowed declarations rest →
      BodyWrites Allowed declarations (source :: rest)
end

mutual
theorem statement_writes
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (typed : Bodies.StatementElaborates (Layout.bindings (fields role declarations))
      HasShape ceiling names source stmt) : StatementWrites Allowed declarations source := by
  cases typed with
  | assign assignment =>
    cases assignment with
    | assign target value =>
      obtain ⟨declaration, present, indices, spelling, _, writable⟩ := target_writable correct target
      exact .assign ⟨declaration, present, indices, spelling, writable⟩
  | loop _ body => exact .loop (body_writes correct body)
termination_by sizeOf source

theorem body_writes
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (typed : Bodies.BodyElaborates (Layout.bindings (fields role declarations))
      HasShape ceiling names sources stmt) : BodyWrites Allowed declarations sources := by
  cases typed with
  | nil => exact .nil
  | cons first rest => exact .cons (statement_writes correct first) (body_writes correct rest)
termination_by sizeOf sources
end

/-- Shape lookup is used only to recover existing typing from successful
lowering. The write-side conclusion does not invent source-shape semantics. -/
theorem lowered_body_writes
    (correct : ∀ declaration, role declaration = .writable ↔ Allowed declaration)
    (lowered : Bodies.statements (Layout.bindings (fields role declarations))
      lookupShape ceiling names sources = some stmt) : BodyWrites Allowed declarations sources :=
  body_writes correct (Bodies.statements_sound _ lookupShape
    (fun key shape => lookupShape key = some shape) (fun _ _ => Iff.rfl)
    ceiling names sources stmt lowered)

end Rumoca.GALEC.Elaboration.Capabilities.Generic
