import RumocaC.DeclaredMembers
import RumocaEFMI.TensorProductionCode
import RumocaEFMI.CInterface

/-! The tensor eFMI header selects the reusable declared-member metadata.
No new header bytes, pointer-cell assumptions or whole-method theorem. -/
namespace Rumoca.EFMI.TensorArrayMembers
open CTree CMemory CDeclaredMembers
open TensorProduction

def arrayField (v : ArrayVar) : CDeclaredMembers.Field :=
  ⟨v.name, realAlias, .float64, some ⟨v.dims⟩⟩

def clockField : CDeclaredMembers.Field := ⟨clockName, realAlias, .float64, none⟩
def statusField : CDeclaredMembers.Field := ⟨statusName, statusAlias, .int32, none⟩

def record : CDeclaredMembers.Record :=
  ⟨"Model", modelVars.map arrayField ++ [clockField, statusField]⟩

private theorem foldl_product (dims : List Nat) (start : Nat) :
    dims.foldl (· * ·) start = start * dims.foldr (· * ·) 1 := by
  induction dims generalizing start with
  | nil => simp
  | cons n rest ih => simp [List.foldl_cons, List.foldr_cons, ih, Nat.mul_assoc]

theorem array_volume (v : ArrayVar) : (Tensor.Shape.mk v.dims).volume = v.volume := by
  simp [Tensor.Shape.volume, ArrayVar.volume, foldl_product]

theorem array_member_render (v : ArrayVar) :
    (arrayField v).render = TensorProduction.memberDecl v := by
  simp [arrayField, Field.render, TensorProduction.memberDecl, array_volume, String.append_assoc]

/-- The declaration nodes rendered here are EXACTLY the existing header. -/
theorem header_exact :
    "typedef double " ++ realAlias ++ ";\n" ++
    "typedef int32_t " ++ statusAlias ++ ";\n" ++ record.render = TensorProduction.header := rfl

theorem unique_fields : (record.fields.map CDeclaredMembers.Field.name).Nodup := by
  decide +kernel

/-- Array/scalar metadata uses the actual alias meanings, not arbitrary types. -/
theorem header_types : record.Typed EFMI.cInterface := by
  intro field member
  simp only [record, modelVars, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rfl

def declarations (name : String) : Option (List CDeclaredMembers.Field) :=
  if name = record.name then some record.fields else none

theorem metadata_bound : declarations record.name = some record.fields := by simp [declarations]

theorem array_member (v : ArrayVar) (member : v ∈ modelVars) :
    arrayField v ∈ record.fields :=
  List.mem_append_left _ (List.mem_map.mpr ⟨v, member, rfl⟩)

/-- Rank and extents are kept, although the actual C declaration is flat. -/
theorem array_shape (v : ArrayVar) : (arrayField v).array = some ⟨v.dims⟩ := rfl

theorem jacobian_rank : (arrayField jacobianVar).array = some ⟨[2, 2]⟩ := rfl

theorem represents (objects : Objects) (heap : Heap) (base : Address)
    (typedObject : objects base = some record.name)
    (storage : ∀ field ∈ record.fields, field.Storage heap base) :
    Represents declarations objects record heap base :=
  ⟨typedObject, metadata_bound, unique_fields, storage⟩

section
variable [interface : CInterface]

/-- Any actual declared tensor field supplies its own first-element address
and allocated element storage; there is no heap pointer cell at that address. -/
theorem array_argument (rep : Represents declarations objects record heap base)
    (v : ArrayVar) (member : v ∈ modelVars)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env heap (selfField v.name) =
      some (.pointer (some (base.member v.name))) ∧
    ArrayStorage heap (base.member v.name) .float64 ⟨v.dims⟩ :=
  field_decay rep (arrayField v) (array_member v member) rfl bound

theorem array_argument_after_store (rep : Represents declarations objects record before base)
    (stored : store before destination value = some after)
    (v : ArrayVar) (member : v ∈ modelVars)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env after (selfField v.name) =
      some (.pointer (some (base.member v.name))) ∧
    ArrayStorage after (base.member v.name) .float64 ⟨v.dims⟩ :=
  array_argument (rep.after_store stored) v member bound

/-- Scalar fields inside this ARRAY-containing record still use the old load. -/
theorem clock_scalar (rep : Represents declarations objects record heap base)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env heap (selfField clockName) =
      CBody.eval env heap (selfField clockName) :=
  scalar_field_eval rep clockField (by simp [record]) rfl bound

theorem status_scalar (rep : Represents declarations objects record heap base)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env heap (selfField statusName) =
      CBody.eval env heap (selfField statusName) :=
  scalar_field_eval rep statusField (by simp [record]) rfl bound

end
end Rumoca.EFMI.TensorArrayMembers
