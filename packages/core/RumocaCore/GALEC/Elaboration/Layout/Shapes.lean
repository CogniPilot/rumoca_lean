import RumocaCore.GALEC.Elaboration.Layout.Base
import RumocaCore.GALEC.Elaboration.Declarations.ShapeLookup

/-! Shape lookup from actual typed storage agrees with validated declarations.
The equality holds even before name validation; the source judgment bridge
requires the existing duplicate-rejecting declaration semantics. -/
namespace Rumoca.GALEC.Elaboration.Layout
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor
open Elaboration.Static

theorem bindingShape_map
    (f : BindingValue inputs outputs → BindingValue newInputs newOutputs)
    (preservesShape : ∀ value, (f value).1 = value.1)
    (table : BindingTable inputs outputs) (key : List String) :
    Dimensions.bindingShape (mapBindings f table) key =
      Dimensions.bindingShape table key := by
  simp only [Dimensions.bindingShape, lookup_map]
  cases BindingTable.lookup table key with
  | none => rfl
  | some value => simp only [Option.map_some, preservesShape]

theorem declaration_shape_cons (declaration : Declarations.Real.Descriptor)
    (rest : List Declarations.Real.Descriptor) (key : List String) :
    Declarations.ShapeLookup.read (declaration :: rest) key =
      if key = [declaration.name] then some declaration.shape
      else Declarations.ShapeLookup.read rest key := by
  cases key with
  | nil => simp [Declarations.ShapeLookup.read]
  | cons name tail =>
    cases tail with
    | nil =>
      by_cases same : name = declaration.name
      · simp [Declarations.ShapeLookup.read, Declarations.NamedLookup.lookup, same]
      · simp [Declarations.ShapeLookup.read, Declarations.NamedLookup.lookup, same]
    | cons next rest => simp [Declarations.ShapeLookup.read]

theorem bindingShape_eq_declarations (fields : List Field) (key : List String) :
    Dimensions.bindingShape (bindings fields) key =
      Declarations.ShapeLookup.read (fields.map Field.declaration) key := by
  induction fields with
  | nil =>
    cases key with
    | nil => rfl
    | cons first rest => cases rest <;> rfl
  | cons field rest ih =>
    obtain ⟨declaration, role⟩ := field
    rw [List.map_cons, declaration_shape_cons]
    cases role with
    | readOnly =>
      change (BindingTable.lookup
        (([declaration.name], ⟨declaration.shape, .readOnly .here⟩) ::
          mapBindings (shiftInput declaration.shape) (bindings rest)) key).map Sigma.fst = _
      by_cases same : key = [declaration.name]
      · simp [BindingTable.lookup, same]
      · simp only [BindingTable.lookup, if_neg same]
        change Dimensions.bindingShape (mapBindings (shiftInput declaration.shape) (bindings rest)) key = _
        rw [bindingShape_map _ (shiftInput_shape _), ih]
    | writable =>
      change (BindingTable.lookup
        (([declaration.name], ⟨declaration.shape, .writable .here⟩) ::
          mapBindings (shiftOutput declaration.shape) (bindings rest)) key).map Sigma.fst = _
      by_cases same : key = [declaration.name]
      · simp [BindingTable.lookup, same]
      · simp only [BindingTable.lookup, if_neg same]
        change Dimensions.bindingShape (mapBindings (shiftOutput declaration.shape) (bindings rest)) key = _
        rw [bindingShape_map _ (shiftOutput_shape _), ih]

/-- The shape-provider premise for nested body elaboration now follows from
the actual declarations and the same table used for expression execution. -/
theorem bindingShape_iff_source (fields : List Field)
    (declared : Declarations.Real.DeclaresAll ceiling sources (fields.map Field.declaration))
    (key : List String) (shape : Shape) :
    Dimensions.bindingShape (bindings fields) key = some shape ↔
      Declarations.ShapeLookup.HasShape ceiling sources key shape := by
  rw [bindingShape_eq_declarations]
  exact Declarations.ShapeLookup.read_iff declared key shape

theorem dimension_read_iff_source (fields : List Field)
    (declared : Declarations.Real.DeclaresAll ceiling sources (fields.map Field.declaration))
    (source : AST.Reference) (axis extent : Nat) :
    Dimensions.read (Dimensions.bindingShape (bindings fields)) source axis = some extent ↔
      Dimensions.Denotes (Declarations.ShapeLookup.HasShape ceiling sources) source axis extent :=
  Dimensions.read_iff _ _ (bindingShape_iff_source fields declared) source axis extent

theorem bounded_read_iff_source (fields : List Field)
    (declared : Declarations.Real.DeclaresAll ceiling sources (fields.map Field.declaration))
    (source : AST.Expr) (value : Nat) :
    Bounded.read (Dimensions.bindingShape (bindings fields)) ceiling source = some value ↔
      Bounded.Evaluates (Declarations.ShapeLookup.HasShape ceiling sources) ceiling source value :=
  Bounded.read_iff _ _ (bindingShape_iff_source fields declared) ceiling source value

end Rumoca.GALEC.Elaboration.Layout
