import RumocaC.DeclaredStorage
import RumocaEFMI.TensorArrayMembers

/-! Actual tensor public storage: allocated-only base, then the original finite
input refinement. Canonical representation/status proofs occur only in the base.
No evaluator, scheduler, record layout or numerical implementation is duplicated. -/
namespace Rumoca.EFMI.TensorPublicStorage
open CTree CMemory CDeclaredMembers CDeclaredMembers.MemberStorage
open TensorProduction TensorArrayMembers

abbrev inputShape : Tensor.Shape := ⟨inputVar.dims⟩
abbrev squareShape : Tensor.Shape := ⟨squareVar.dims⟩
abbrev jacobianShape : Tensor.Shape := ⟨jacobianVar.dims⟩

def cleared (heap : Heap) (base : Address) : Heap :=
  replace heap (base.member statusName) ⟨.int32, true, some (.integer 0)⟩

theorem cleared_status :
    cleared heap base (base.member statusName) = some ⟨.int32, true, some (.integer 0)⟩ := by
  simp [cleared]

theorem cleared_status_reads : load (cleared heap base) (base.member statusName) = some (.integer 0) := by
  simp [load, cleared_status, convert]

theorem cleared_other (different : address ≠ base.member statusName) :
    cleared heap base address = heap address :=
  replace_other _ _ _ _ different

theorem method_prefix (name : String) (body : List Stmt) :
    (method name body).body =
      .assign (selfField statusName) (.nat 0) :: (body ++ [.ret (some (selfField statusName))]) := rfl

/-- Input allocation may be uninitialized/read-only; scalar old values are arbitrary. -/
structure AllocatedStorage (objects : Objects) (heap : Heap) (base : Address) : Prop where
  object : objects base = some record.name
  input : ArrayStorage heap (base.member inputVar.name) .float64 inputShape
  square : TensorView.Writable heap (base.member squareVar.name) squareShape.volume
  jacobian : TensorView.Writable heap (base.member jacobianVar.name) jacobianShape.volume
  clock : ScalarWritable heap (base.member clockName) .float64
  status : ScalarWritable heap (base.member statusName) .int32

theorem AllocatedStorage.represents (storage : AllocatedStorage objects heap base) :
    Represents declarations objects record heap base := by
  apply TensorArrayMembers.represents objects heap base storage.object
  intro field member
  simp only [record, modelVars, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact storage.input
  · exact array_of_writable (by decide +kernel) storage.square
  · exact array_of_writable (by decide +kernel) storage.jacobian
  · obtain ⟨old, found⟩ := storage.clock
    exact ⟨_, found, rfl⟩
  · obtain ⟨old, found⟩ := storage.status
    exact ⟨_, found, rfl⟩

theorem AllocatedStorage.declared_header (storage : AllocatedStorage objects heap base) :
    Represents declarations objects record heap base ∧ record.Typed EFMI.cInterface ∧
    "typedef double " ++ realAlias ++ ";\n" ++
      "typedef int32_t " ++ statusAlias ++ ";\n" ++ record.render = TensorProduction.header :=
  ⟨storage.represents, header_types, header_exact⟩

theorem clear_of_status {heap : Heap} {base : Address}
    (status : ScalarWritable heap (base.member statusName) .int32) :
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) := by
  obtain ⟨old, found⟩ := status
  simp [store, found, convert, cleared]

theorem AllocatedStorage.clear_store (storage : AllocatedStorage objects heap base) :
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) :=
  clear_of_status storage.status

theorem AllocatedStorage.clear_member (storage : AllocatedStorage objects heap base)
    (name : String) (different : name ≠ statusName) (i : Nat) :
    cleared heap base ((base.member name).index i) = heap ((base.member name).index i) :=
  member_frame storage.clear_store different i

theorem AllocatedStorage.after_clear (storage : AllocatedStorage objects heap base) :
    AllocatedStorage objects (cleared heap base) base := by
  refine ⟨storage.object, storage.input.preserved (store_types storage.clear_store), ?_, ?_, ?_, ?_⟩
  · exact writable_framed storage.square (storage.clear_member squareVar.name (by decide +kernel))
  · exact writable_framed storage.jacobian (storage.clear_member jacobianVar.name (by decide +kernel))
  · apply storage.clock.framed
    simpa only [Address.index_zero] using storage.clear_member clockName (by decide +kernel) 0
  · exact ⟨some (.integer 0), cleared_status⟩

theorem AllocatedStorage.input_frame (storage : AllocatedStorage objects heap base) (i : Nat) :
    cleared heap base ((base.member inputVar.name).index i) =
      heap ((base.member inputVar.name).index i) :=
  storage.clear_member inputVar.name (by decide +kernel) i

theorem AllocatedStorage.clock_frame (storage : AllocatedStorage objects heap base) :
    cleared heap base (base.member clockName) = heap (base.member clockName) ∧
    load (cleared heap base) (base.member clockName) = load heap (base.member clockName) := by
  have frame := storage.clear_member clockName (by decide +kernel) 0
  simp only [Address.index_zero] at frame
  exact ⟨frame, by simp only [load, frame]⟩

theorem AllocatedStorage.array_reads_frame (storage : AllocatedStorage objects heap base)
    (v : ArrayVar) (member : v ∈ modelVars)
    (values : TensorView.Values (Tensor.Shape.mk v.dims))
    (reads : TensorView.Reads heap (base.member v.name) values) :
    TensorView.Reads (cleared heap base) (base.member v.name) values := by
  apply reads_framed reads
  apply storage.clear_member v.name
  simp only [modelVars, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

theorem AllocatedStorage.clear_spec (storage : AllocatedStorage objects heap base) :
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) ∧
    AllocatedStorage objects (cleared heap base) base ∧
    Represents declarations objects record (cleared heap base) base ∧
    ArrayStorage (cleared heap base) (base.member inputVar.name) .float64 inputShape ∧
    TensorView.Writable (cleared heap base) (base.member squareVar.name) squareShape.volume ∧
    TensorView.Writable (cleared heap base) (base.member jacobianVar.name) jacobianShape.volume ∧
    load (cleared heap base) (base.member statusName) = some (.integer 0) :=
  ⟨storage.clear_store, storage.after_clear, storage.after_clear.represents,
    storage.after_clear.input, storage.after_clear.square, storage.after_clear.jacobian,
    cleared_status_reads⟩

section
variable [interface : CInterface]

theorem AllocatedStorage.status_assignment (storage : AllocatedStorage objects heap base)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.lvalue declarations objects env heap (selfField statusName) =
      some (base.member statusName) ∧
    CDeclaredMembers.eval declarations objects env heap (.nat 0) = some (.integer 0) ∧
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) := by
  refine ⟨?_, rfl, storage.clear_store⟩
  simp [selfField, CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.evalWith, CBody.resolve, bound, Value.address]

theorem AllocatedStorage.array_arguments_after_clear (storage : AllocatedStorage objects heap base)
    (v : ArrayVar) (member : v ∈ modelVars)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env (cleared heap base) (selfField v.name) =
      some (.pointer (some (base.member v.name))) ∧
    ArrayStorage (cleared heap base) (base.member v.name) .float64 ⟨v.dims⟩ :=
  array_argument storage.after_clear.represents v member bound

end

/-- Source-facing fields/constructor retained; proofs use the allocated base. -/
structure Storage (objects : Objects) (heap : Heap) (base : Address)
    (input : TensorView.Values inputShape) : Prop where
  object : objects base = some record.name
  inputCells : FiniteCells heap (base.member inputVar.name) input
  square : TensorView.Writable heap (base.member squareVar.name) squareShape.volume
  jacobian : TensorView.Writable heap (base.member jacobianVar.name) jacobianShape.volume
  clock : ScalarWritable heap (base.member clockName) .float64
  status : ScalarWritable heap (base.member statusName) .int32

variable {input : TensorView.Values inputShape}

theorem Storage.input_reads (storage : Storage objects heap base input) :
    TensorView.Reads heap (base.member inputVar.name) input :=
  storage.inputCells.reads

theorem Storage.input_allocated (storage : Storage objects heap base input) :
    ArrayStorage heap (base.member inputVar.name) .float64 inputShape :=
  storage.inputCells.allocated (by decide +kernel)

theorem Storage.toAllocated (storage : Storage objects heap base input) :
    AllocatedStorage objects heap base :=
  ⟨storage.object, storage.input_allocated, storage.square, storage.jacobian,
    storage.clock, storage.status⟩

theorem AllocatedStorage.with_input (storage : AllocatedStorage objects heap base)
    (inputCells : FiniteCells heap (base.member inputVar.name) input) :
    Storage objects heap base input :=
  ⟨storage.object, inputCells, storage.square, storage.jacobian, storage.clock, storage.status⟩

theorem storage_iff_allocated :
    Storage objects heap base input ↔
      AllocatedStorage objects heap base ∧ FiniteCells heap (base.member inputVar.name) input :=
  ⟨fun storage => ⟨storage.toAllocated, storage.inputCells⟩,
    fun ⟨storage, inputCells⟩ => storage.with_input inputCells⟩

theorem Storage.square_allocated (storage : Storage objects heap base input) :
    ArrayStorage heap (base.member squareVar.name) .float64 squareShape :=
  array_of_writable (by decide +kernel) storage.square

theorem Storage.jacobian_allocated (storage : Storage objects heap base input) :
    ArrayStorage heap (base.member jacobianVar.name) .float64 jacobianShape :=
  array_of_writable (by decide +kernel) storage.jacobian

theorem Storage.represents (storage : Storage objects heap base input) :
    Represents declarations objects record heap base :=
  storage.toAllocated.represents

theorem Storage.declared_header (storage : Storage objects heap base input) :
    Represents declarations objects record heap base ∧ record.Typed EFMI.cInterface ∧
    "typedef double " ++ realAlias ++ ";\n" ++
      "typedef int32_t " ++ statusAlias ++ ";\n" ++ record.render = TensorProduction.header :=
  storage.toAllocated.declared_header

theorem Storage.clear_store (storage : Storage objects heap base input) :
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) :=
  storage.toAllocated.clear_store

theorem Storage.clear_member (storage : Storage objects heap base input)
    (name : String) (different : name ≠ statusName) (i : Nat) :
    cleared heap base ((base.member name).index i) = heap ((base.member name).index i) :=
  storage.toAllocated.clear_member name different i

theorem Storage.after_clear (storage : Storage objects heap base input) :
    Storage objects (cleared heap base) base input :=
  storage.toAllocated.after_clear.with_input
    (storage.inputCells.framed storage.toAllocated.input_frame)

theorem Storage.input_writable_after_clear (storage : Storage objects heap base input)
    (writable : TensorView.Writable heap (base.member inputVar.name) inputShape.volume) :
    TensorView.Writable (cleared heap base) (base.member inputVar.name) inputShape.volume :=
  writable_framed writable (storage.clear_member inputVar.name (by decide +kernel))

theorem Storage.output_reads_after_clear (storage : Storage objects heap base input)
    (v : ArrayVar) (output : v = squareVar ∨ v = jacobianVar)
    (values : TensorView.Values (Tensor.Shape.mk v.dims))
    (reads : TensorView.Reads heap (base.member v.name) values) :
    TensorView.Reads (cleared heap base) (base.member v.name) values := by
  apply storage.toAllocated.array_reads_frame v ?_ values reads
  rcases output with rfl | rfl <;> simp [modelVars]

theorem Storage.clock_after_clear (storage : Storage objects heap base input) :
    cleared heap base (base.member clockName) = heap (base.member clockName) ∧
    load (cleared heap base) (base.member clockName) = load heap (base.member clockName) ∧
    ScalarWritable (cleared heap base) (base.member clockName) .float64 :=
  ⟨storage.toAllocated.clock_frame.1, storage.toAllocated.clock_frame.2, storage.after_clear.clock⟩

theorem Storage.clear_spec (storage : Storage objects heap base input) :
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) ∧
    Storage objects (cleared heap base) base input ∧
    Represents declarations objects record (cleared heap base) base ∧
    TensorView.Reads (cleared heap base) (base.member inputVar.name) input ∧
    TensorView.Writable (cleared heap base) (base.member squareVar.name) squareShape.volume ∧
    TensorView.Writable (cleared heap base) (base.member jacobianVar.name) jacobianShape.volume ∧
    load (cleared heap base) (base.member statusName) = some (.integer 0) :=
  ⟨storage.clear_store, storage.after_clear, storage.after_clear.represents,
    storage.after_clear.input_reads, storage.after_clear.square, storage.after_clear.jacobian,
    cleared_status_reads⟩

theorem Storage.represents_via_allocated (storage : Storage objects heap base input) :
    Represents declarations objects record heap base :=
  storage.represents

theorem Storage.after_clear_via_allocated (storage : Storage objects heap base input) :
    Storage objects (cleared heap base) base input :=
  storage.after_clear

section
variable [interface : CInterface]

theorem Storage.status_assignment (storage : Storage objects heap base input)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.lvalue declarations objects env heap (selfField statusName) =
      some (base.member statusName) ∧
    CDeclaredMembers.eval declarations objects env heap (.nat 0) = some (.integer 0) ∧
    store heap (base.member statusName) (.integer 0) = some (cleared heap base) :=
  storage.toAllocated.status_assignment bound

theorem Storage.array_arguments_after_clear (storage : Storage objects heap base input)
    (v : ArrayVar) (member : v ∈ modelVars)
    (bound : env "self" = some (.pointer (some base))) :
    CDeclaredMembers.eval declarations objects env (cleared heap base) (selfField v.name) =
      some (.pointer (some (base.member v.name))) ∧
    ArrayStorage (cleared heap base) (base.member v.name) .float64 ⟨v.dims⟩ :=
  storage.toAllocated.array_arguments_after_clear v member bound

end
end Rumoca.EFMI.TensorPublicStorage
