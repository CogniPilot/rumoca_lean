import RumocaC.DeclaredMembers

/-! Typed input/scalar storage and pointwise member frames. No backend-specific
metadata, numerical emission or evaluator/scheduler implementation. -/
namespace Rumoca.CDeclaredMembers.MemberStorage
open CMemory

/-- Input cells contain finite encodings; each cell's write permission is free. -/
def FiniteCells (heap : Heap) (base : Address) (values : TensorView.Values shape) : Prop :=
  ∀ i : Fin shape.volume, ∃ writable,
    heap (base.index i.val) = some ⟨.float64, writable, some (.finite values[i])⟩

/-- Allocated writable scalar, with no requirement to read/convert the old value. -/
def ScalarWritable (heap : Heap) (address : Address) (type : CType) : Prop :=
  ∃ old, heap address = some ⟨type, true, old⟩

variable {shape : Tensor.Shape} {values : TensorView.Values shape}
  {heap before after : Heap} {base address : Address}
  {destination name : String} {value : Value} {type : CType} {count : Nat}

theorem FiniteCells.reads (cells : FiniteCells heap base values) :
    TensorView.Reads heap base values := by
  intro i
  obtain ⟨writable, found⟩ := cells i
  simp [load, found, convert, Value.finite]

theorem FiniteCells.allocated (cells : FiniteCells heap base values)
    (positive : 0 < shape.volume) :
    ArrayStorage heap base .float64 shape := by
  refine ⟨positive, ?_⟩
  intro i
  obtain ⟨writable, found⟩ := cells i
  exact ⟨_, found, rfl⟩

/-- Distinct member names separate every indexed cell, even outside array bounds.
Bounds and native layout remain separate from this symbolic address fact. -/
theorem member_frame (stored : store before (base.member destination) value = some after)
    (different : name ≠ destination) (i : Nat) :
    after ((base.member name).index i) = before ((base.member name).index i) := by
  apply store_frame before (base.member destination) value after stored
  simpa only [Address.index_zero] using Address.fields_separate base name destination different i 0

theorem FiniteCells.framed (cells : FiniteCells before base values)
    (frame : ∀ i, after (base.index i) = before (base.index i)) :
    FiniteCells after base values := by
  intro i
  obtain ⟨writable, found⟩ := cells i
  exact ⟨writable, (frame i.val).trans found⟩

theorem writable_framed (cells : TensorView.Writable before base count)
    (frame : ∀ i, after (base.index i) = before (base.index i)) :
    TensorView.Writable after base count := by
  intro i bound
  obtain ⟨old, found⟩ := cells i bound
  exact ⟨old, (frame i).trans found⟩

theorem reads_framed (reads : TensorView.Reads before base values)
    (frame : ∀ i, after (base.index i) = before (base.index i)) :
    TensorView.Reads after base values := by
  intro i
  simpa only [load, frame i.val] using reads i

theorem ScalarWritable.framed (cells : ScalarWritable before address type)
    (frame : after address = before address) : ScalarWritable after address type := by
  obtain ⟨old, found⟩ := cells
  exact ⟨old, frame.trans found⟩

end Rumoca.CDeclaredMembers.MemberStorage
