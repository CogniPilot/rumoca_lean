import RumocaCore.GALEC.Elaboration.Declarations.Real
import RumocaCore.GALEC.Elaboration.Bindings

/-! Ordered typed storage preparation. The supplied role is a method-specific
capability decision, NOT inferred here from direction/variability metadata.
Construction allocates one existing shaped reference per declared field; no
tensor cells, native addresses or replacement storage IR are introduced. -/
namespace Rumoca.GALEC.Elaboration.Layout
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor

inductive Role where
  | readOnly | writable
  deriving Repr, DecidableEq

structure Field where
  declaration : Declarations.Real.Descriptor
  role : Role
  deriving Repr, DecidableEq

def inputShapes : List Field → List Shape
  | [] => []
  | ⟨declaration, .readOnly⟩ :: rest => declaration.shape :: inputShapes rest
  | ⟨_, .writable⟩ :: rest => inputShapes rest

def outputShapes : List Field → List Shape
  | [] => []
  | ⟨_, .readOnly⟩ :: rest => outputShapes rest
  | ⟨declaration, .writable⟩ :: rest => declaration.shape :: outputShapes rest

def shiftInput (added : Shape) : BindingValue inputs outputs → BindingValue (added :: inputs) outputs
  | ⟨shape, .readOnly ref⟩ => ⟨shape, .readOnly (.there ref)⟩
  | ⟨shape, .writable ref⟩ => ⟨shape, .writable ref⟩

def shiftOutput (added : Shape) : BindingValue inputs outputs → BindingValue inputs (added :: outputs)
  | ⟨shape, .readOnly ref⟩ => ⟨shape, .readOnly ref⟩
  | ⟨shape, .writable ref⟩ => ⟨shape, .writable (.there ref)⟩

def mapBindings (f : BindingValue inputs outputs → BindingValue newInputs newOutputs)
    (table : BindingTable inputs outputs) : BindingTable newInputs newOutputs :=
  table.map fun (key, value) => (key, f value)

def bindings : (fields : List Field) → BindingTable (inputShapes fields) (outputShapes fields)
  | [] => []
  | ⟨declaration, .readOnly⟩ :: rest =>
      ([declaration.name], ⟨declaration.shape, .readOnly .here⟩) ::
        mapBindings (shiftInput declaration.shape) (bindings rest)
  | ⟨declaration, .writable⟩ :: rest =>
      ([declaration.name], ⟨declaration.shape, .writable .here⟩) ::
        mapBindings (shiftOutput declaration.shape) (bindings rest)

theorem lookup_map (f : BindingValue inputs outputs → BindingValue newInputs newOutputs)
    (table : BindingTable inputs outputs) (key : List String) :
    BindingTable.lookup (mapBindings f table) key = (BindingTable.lookup table key).map f := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨head, value⟩ := entry
    by_cases same : key = head
    · simp [mapBindings, BindingTable.lookup, same]
    · simpa only [mapBindings, List.map_cons, BindingTable.lookup, if_neg same] using ih

def roleOf : BindingValue inputs outputs → Role
  | ⟨_, .readOnly _⟩ => .readOnly
  | ⟨_, .writable _⟩ => .writable

theorem shiftInput_shape (added : Shape) (value : BindingValue inputs outputs) :
    (shiftInput added value).1 = value.1 := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

theorem shiftOutput_shape (added : Shape) (value : BindingValue inputs outputs) :
    (shiftOutput added value).1 = value.1 := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

theorem shiftInput_role (added : Shape) (value : BindingValue inputs outputs) :
    roleOf (shiftInput added value) = roleOf value := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

theorem shiftOutput_role (added : Shape) (value : BindingValue inputs outputs) :
    roleOf (shiftOutput added value) = roleOf value := by
  obtain ⟨shape, access⟩ := value
  cases access <;> rfl

/-- A declaration-level summary only; actual addresses remain typed refs in
the binding table. This projection is not used to reconstruct target storage. -/
def describe (table : BindingTable inputs outputs) : List (List String × Shape × Role) :=
  table.map fun (key, value) => (key, value.1, roleOf value)

theorem describe_map (f : BindingValue inputs outputs → BindingValue newInputs newOutputs)
    (preservesShape : ∀ value, (f value).1 = value.1)
    (preservesRole : ∀ value, roleOf (f value) = roleOf value)
    (table : BindingTable inputs outputs) : describe (mapBindings f table) = describe table := by
  simp only [describe, mapBindings, List.map_map]
  apply List.map_congr_left
  intro entry _
  obtain ⟨key, value⟩ := entry
  simp [preservesShape, preservesRole]

theorem describe_bindings (fields : List Field) :
    describe (bindings fields) = fields.map fun field =>
      ([field.declaration.name], field.declaration.shape, field.role) := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    cases role with
    | readOnly =>
      simp only [bindings, describe, List.map_cons]
      change _ :: describe (mapBindings (shiftInput declaration.shape) (bindings rest)) = _
      rw [describe_map _ (shiftInput_shape _) (shiftInput_role _), ih]
      rfl
    | writable =>
      simp only [bindings, describe, List.map_cons]
      change _ :: describe (mapBindings (shiftOutput declaration.shape) (bindings rest)) = _
      rw [describe_map _ (shiftOutput_shape _) (shiftOutput_role _), ih]
      rfl

end Rumoca.GALEC.Elaboration.Layout
