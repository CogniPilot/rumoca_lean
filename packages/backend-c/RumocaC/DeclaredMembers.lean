import RumocaC.Body
import RumocaC.TensorMemory
import RumocaC.Subobjects
import RumocaC.LiteralPointers

/-! Storage/representation proofs for declaration-selected flat C array members.
Evaluation aliases the canonical CBody evaluator; there is no second recursion.
Logical shape is retained and no pointer cell represents the array object. -/
namespace Rumoca.CDeclaredMembers
open CTree CMemory

/-- Allocated element cells, possibly uninitialized or read-only. Logical rank
and extents remain in the shape parameter; physical C storage is flat. -/
def ArrayStorage (heap : Heap) (base : Address) (element : CType) (shape : Tensor.Shape) : Prop :=
  0 < shape.volume ∧ ∀ i : Fin shape.volume, ∃ cell,
    heap (base.index i.val) = some cell ∧ cell.type = element

def Field.Storage (field : Field) (heap : Heap) (base : Address) : Prop :=
  match field.array with
  | none => ∃ cell, heap (base.member field.name) = some cell ∧ cell.type = field.element
  | some shape => ArrayStorage heap (base.member field.name) field.element shape

/-- Binds a particular live modeled object to the same declared record used for
evaluation, with storage for every declared field. No native allocator/layout claim. -/
structure Represents (declarations : Declarations) (objects : Objects)
    (record : Record) (heap : Heap) (base : Address) : Prop where
  object : objects base = some record.name
  declaration : declarations record.name = some record.fields
  unique : (record.fields.map Field.name).Nodup
  storage : ∀ field ∈ record.fields, field.Storage heap base

theorem field_lookup (fields : List Field) (field : Field)
    (unique : (fields.map Field.name).Nodup) (member : field ∈ fields) :
    fields.find? (fun f => f.name == field.name) = some field := by
  induction fields with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : head.name ≠ field.name := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨field, member, same.symm⟩)
        simpa [different] using ih unique.2 member

theorem Represents.field_bound (rep : Represents declarations objects record heap base)
    (field : Field) (member : field ∈ record.fields) :
    fieldAt declarations objects base field.name = some field := by
  simp only [fieldAt, rep.object, bind, Option.bind, rep.declaration]
  exact field_lookup record.fields field rep.unique member

theorem scalar_member (absent : arrayAt declarations objects base name = none) :
    memberValue declarations objects heap base name = load heap (base.member name) := by
  simp [memberValue, absent]

theorem declared_array (rep : Represents declarations objects record heap base)
    (field : Field) (member : field ∈ record.fields) (array : field.array = some shape) :
    memberValue declarations objects heap base field.name = some (.pointer (some (base.member field.name))) ∧
      ArrayStorage heap (base.member field.name) field.element shape := by
  constructor
  · simp [memberValue, arrayAt, rep.field_bound field member, array]
  · simpa only [Field.Storage, array] using rep.storage field member

theorem declared_scalar (rep : Represents declarations objects record heap base)
    (field : Field) (member : field ∈ record.fields) (scalar : field.array = none) :
    memberValue declarations objects heap base field.name = load heap (base.member field.name) := by
  apply scalar_member
  simp [arrayAt, rep.field_bound field member, scalar]

/-- Type/allocation preservation is sufficient for array decay after writes.
Contents preservation is a DIFFERENT, stronger obligation. -/
def TypesPreserved (before after : Heap) : Prop :=
  ∀ address cell, before address = some cell →
    ∃ newCell, after address = some newCell ∧ newCell.type = cell.type

theorem store_types (stored : store before address value = some after) :
    TypesPreserved before after := by
  unfold store at stored
  cases found : before address with
  | none => simp [found] at stored
  | some cell =>
      simp only [found, bind, Option.bind] at stored
      split at stored
      · contradiction
      · cases converted : convert cell.type value with
        | none => simp [converted] at stored
        | some result =>
            simp only [converted, pure, Option.some.injEq] at stored
            subst after
            intro query old present
            by_cases same : query = address
            · subst query
              have eq : old = cell := Option.some.inj (present.symm.trans found)
              subst old
              exact ⟨_, replace_at _ _ _, rfl⟩
            · exact ⟨old, (replace_other _ _ _ _ same).trans present, rfl⟩

theorem ArrayStorage.preserved (stored : ArrayStorage before base element shape)
    (frame : TypesPreserved before after) : ArrayStorage after base element shape := by
  refine ⟨stored.1, ?_⟩
  intro i
  obtain ⟨cell, found, typed⟩ := stored.2 i
  obtain ⟨newCell, present, same⟩ := frame _ cell found
  exact ⟨newCell, present, same.trans typed⟩

theorem Represents.preserved (rep : Represents declarations objects record before base)
    (frame : TypesPreserved before after) : Represents declarations objects record after base := by
  refine ⟨rep.object, rep.declaration, rep.unique, ?_⟩
  intro field member
  have h := rep.storage field member
  cases shape : field.array with
  | none =>
      simp only [Field.Storage, shape] at h ⊢
      obtain ⟨cell, found, typed⟩ := h
      obtain ⟨newCell, present, same⟩ := frame _ cell found
      exact ⟨newCell, present, same.trans typed⟩
  | some shape' =>
      simp only [Field.Storage, shape] at h ⊢
      exact h.preserved frame

theorem Represents.after_store (rep : Represents declarations objects record before base)
    (stored : store before address value = some after) :
    Represents declarations objects record after base :=
  rep.preserved (store_types stored)

/-- Output tensor writability supplies real float cells, not a pointer marker. -/
theorem array_of_writable (positive : 0 < shape.volume)
    (writable : TensorView.Writable heap base shape.volume) :
    ArrayStorage heap base .float64 shape := by
  refine ⟨positive, ?_⟩
  intro i
  obtain ⟨old, found⟩ := writable i.val i.isLt
  exact ⟨_, found, rfl⟩

/-- A symbolic uninitialized member-array installation; no allocation execution.
Other field paths and blocks are untouched. -/
def installArray (heap : Heap) (record : Address) (field : Field) (shape : Tensor.Shape)
    (writable : Bool) : Heap := fun address =>
  if address.block = record.block ∧
      address.members = (record.member field.name).members ∧ address.offset < shape.volume then
    some ⟨field.element, writable, none⟩
  else heap address

theorem installed (positive : 0 < shape.volume) :
    ArrayStorage (installArray heap record field shape writable)
      (record.member field.name) field.element shape := by
  refine ⟨positive, ?_⟩
  intro i
  exact ⟨⟨field.element, writable, none⟩,
    by simp [installArray, Address.index, Address.member, i.isLt], rfl⟩

/-- The first element may be uninitialized: representing an array requires no
readable value (and in particular no fabricated pointer) in that cell. -/
theorem installed_first_uninitialized (positive : 0 < shape.volume) :
    load (installArray heap record field shape writable) (record.member field.name) = none := by
  simp [installArray, Address.member, positive, load]

theorem install_other_field (different : name ≠ field.name) :
    installArray heap record field shape writable ((record.member name).index i) =
      heap ((record.member name).index i) := by
  have differentPath : ((record.member name).index i).members ≠ (record.member field.name).members := by
    simp [Address.index, Address.member, different]
  simp [installArray, differentPath]

section Evaluation
variable [interface : CInterface]

omit interface in
private theorem empty_member (heap : Heap) (base : Address) (name : String) :
    memberValue (fun _ => none) (fun _ => none) heap base name = load heap (base.member name) := rfl

/-- Compatibility names over the single canonical recursive evaluator. -/
noncomputable abbrev eval (declarations : Declarations) (objects : Objects)
    (env : CBody.Locals) (heap : Heap) : Expr → Option Value :=
  CBody.evalWith declarations objects env heap
noncomputable abbrev lvalue (declarations : Declarations) (objects : Objects)
    (env : CBody.Locals) (heap : Heap) : Expr → Option Address :=
  CBody.lvalueWith declarations objects env heap

private theorem other_call (fn a : Expr) (other : fn ≠ .id "isfinite") :
    eval declarations objects env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [eval, CBody.evalWith]

private theorem old_other_call (fn a : Expr) (other : fn ≠ .id "isfinite") :
    CBody.eval env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [CBody.eval, CBody.evalWith]

/-- Full expression/lvalue agreement, including failures and short-circuiting,
when the metadata selects no array fields. No successful execution is assumed. -/
theorem scalar_agreement (declarations : Declarations) (objects : Objects)
    (scalar : ∀ base name, arrayAt declarations objects base name = none)
    (env : CBody.Locals) (heap : Heap) (e : Expr) :
    eval declarations objects env heap e = CBody.eval env heap e ∧
    lvalue declarations objects env heap e = CBody.lvalue env heap e := by
  induction e using Expr.rec (motive_2 := fun args => ∀ a ∈ args,
      eval declarations objects env heap a = CBody.eval env heap a ∧
      lvalue declarations objects env heap a = CBody.lvalue env heap a) with
  | id | nat | decimal | str | sizeof => simp [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue]
  | bin op a b ha hb => cases op <;> simp [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, ha.1, hb.1]
  | index a b ha hb =>
      simp only [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, ha.1, ha.2, hb.1]
      constructor <;> trivial
  | not a ha | deref a ha | address a ha | cast type a ha =>
      simp [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, ha.1, ha.2]
  | field a name pointer ha =>
      have values (base : Address) := scalar_member (heap := heap) (scalar base name)
      simp [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue,
        ha.1, ha.2, values, empty_member]
  | call fn args hfn hargs =>
      refine ⟨?_, by simp [lvalue, CBody.lvalueWith, CBody.lvalue]⟩
      cases args with
      | nil => cases fn <;> simp [eval, CBody.evalWith, CBody.eval]
      | cons a rest =>
          cases rest with
          | cons b rest => cases fn <;> simp [eval, CBody.evalWith, CBody.eval]
          | nil =>
              have same := hargs a (by simp)
              by_cases intrinsic : fn = .id "isfinite"
              · subst fn; simp [eval, CBody.evalWith, CBody.eval, same.1]
              · rw [other_call fn a intrinsic, old_other_call fn a intrinsic]
  | nil => simp_all
  | cons a rest ha hr =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      · exact hr value member

theorem empty_agreement (env : CBody.Locals) (heap : Heap) (e : Expr) :
    eval (fun _ => none) objects env heap e = CBody.eval env heap e ∧
    lvalue (fun _ => none) objects env heap e = CBody.lvalue env heap e := by
  apply scalar_agreement
  intro base name
  simp [arrayAt, fieldAt]

theorem field_decay (rep : Represents declarations objects record heap base)
    (field : Field) (member : field ∈ record.fields) (array : field.array = some shape)
    (bound : env self = some (.pointer (some base))) :
    eval declarations objects env heap (.field (.id self) field.name true) =
      some (.pointer (some (base.member field.name))) ∧
      ArrayStorage heap (base.member field.name) field.element shape := by
  have result := declared_array rep field member array
  refine ⟨?_, result.2⟩
  simpa [eval, CBody.evalWith, CBody.resolve, bound, Value.address] using result.1

theorem scalar_field_eval (rep : Represents declarations objects record heap base)
    (field : Field) (member : field ∈ record.fields) (scalar : field.array = none)
    (bound : env self = some (.pointer (some base))) :
    eval declarations objects env heap (.field (.id self) field.name true) =
      CBody.eval env heap (.field (.id self) field.name true) := by
  simp [eval, CBody.evalWith, CBody.eval, CBody.resolve, bound, Value.address,
    declared_scalar rep field member scalar, empty_member]

/-- Address-of remains an lvalue operation; no array element is read. -/
theorem address_field (bound : env self = some (.pointer (some base))) :
    eval declarations objects env heap (.address (.field (.id self) name true)) =
      some (.pointer (some (base.member name))) := by
  simp [eval, CBody.evalWith, CBody.lvalueWith, CBody.resolve, bound, Value.address]

/-- The flat C subscript reads the indexed tensor element; the index retains
the declaration's logical shape and its extent bound. -/
theorem field_index_read (values : TensorView.Values shape) (i : Fin shape.volume)
    (bound : env self = some (.pointer (some base)))
    (reads : TensorView.Reads heap (base.member name) values) :
    eval declarations objects env heap (.index (.field (.id self) name true) (.nat i.val)) =
      some (.finite values[i]) := by
  simpa [eval, CBody.evalWith, lvalue, CBody.lvalueWith, CBody.resolve, bound, Value.address] using reads i

/-- Existing character-literal address selection is unchanged. -/
theorem literal_pointer (bound : interface.literals source = some base) :
    eval declarations objects env heap (.str source) = some (.pointer (some base)) := by
  simp [eval, CBody.evalWith, bound]

theorem literal_index (stored : CLiteral.Stored signed heap base source)
    (bound : interface.literals source = some base)
    (atByte : (CLiteral.bytes source)[index]? = some byte) :
    eval declarations objects env heap (.index (.str source) (.nat index)) =
      some (.integer (CCharacter.value signed byte)) := by
  simp [eval, CBody.evalWith, CBody.lvalueWith, bound, Value.address, stored.load atByte]

end Evaluation
end Rumoca.CDeclaredMembers
