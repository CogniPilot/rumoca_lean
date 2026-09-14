import RumocaC.ArrayStore
import RumocaC.UnsignedMemory
import RumocaFMI3.Float64SetContract
import RumocaFMI3.Float64Contract

noncomputable section
namespace Rumoca.FMI3.Float64Buffers
open CMemory

/-- Reusable caller-owned buffers. Their capacity bounds only host requests;
the compiler retains tensor operations in its IRs. -/
structure Layout where
  references : Address
  values : Address
  capacity : UInt64

structure Layout.Separate (buffers : Layout) (p : Address) : Prop where
  references : buffers.references.block ≠ p.block
  values : buffers.values.block ≠ p.block
  eachOther : buffers.references.block ≠ buffers.values.block

structure Stored (heap : Heap) (buffers : Layout) : Prop where
  references : ArrayStore.Writable heap buffers.references (.unsigned 32) buffers.capacity.toNat
  values : TensorView.Writable heap buffers.values buffers.capacity.toNat

theorem Stored.preserved (stored : Stored before buffers) (frame : CStorage.Preserves before after) :
    Stored after buffers := by
  constructor
  · intro i hi
    obtain ⟨old, cell⟩ := stored.references i hi
    exact frame.cell cell
  · intro i hi
    obtain ⟨old, cell⟩ := stored.values i hi
    exact frame.cell cell

theorem different_blocks (a b : Address) (different : a.block ≠ b.block) : a ≠ b :=
  fun same => different (congrArg Address.block same)

def referenceValues (shape : Tensor.Shape) (references : Nat → UInt32) : Fin shape.volume → Value :=
  fun i => .integer (references i.val).toNat

def prepareReferences (heap : Heap) (buffers : Layout) (shape : Tensor.Shape)
    (references : Nat → UInt32) : Heap :=
  ArrayStore.written heap buffers.references (.unsigned 32) (referenceValues shape references) shape.volume

theorem reference_converts (value : UInt32) :
    convert (.unsigned 32) (.integer value.toNat) = some (.integer value.toNat) := by
  apply convert_unsigned_in_range (by omega)
  have bound := value.toNat_lt_size
  change value.toNat < 4294967296 at bound
  change (value.toNat : Int) < 4294967296
  omega

theorem references_run (stored : Stored heap buffers) (shape : Tensor.Shape)
    (references : Nat → UInt32) (fits : shape.volume ≤ buffers.capacity.toNat) :
    ArrayStore.run heap buffers.references (referenceValues shape references) shape.volume =
      some (prepareReferences heap buffers shape references) := by
  exact ArrayStore.run_written _ _ _ _ _ (by omega)
    (fun i hi => stored.references i (by omega)) (by decide)
    (fun i => reference_converts (references i.val))

theorem references_read (heap : Heap) (buffers : Layout) (shape : Tensor.Shape)
    (references : Nat → UInt32) :
    Float64Calls.References (prepareReferences heap buffers shape references)
      (some buffers.references) shape.volume references := by
  intro i hi
  exact ⟨buffers.references, rfl, ArrayStore.written_reads heap buffers.references (.unsigned 32)
    (referenceValues shape references) (by decide) (fun j => reference_converts (references j.val)) ⟨i, hi⟩⟩

theorem references_frame (heap : Heap) (buffers : Layout) (shape : Tensor.Shape)
    (references : Nat → UInt32) (query : Address)
    (outside : ∀ i < shape.volume, query ≠ buffers.references.index i) :
    prepareReferences heap buffers shape references query = heap query :=
  ArrayStore.frame _ _ _ _ _ query (fun i => outside i.val i.isLt)

theorem references_preserve (stored : Stored heap buffers) (shape : Tensor.Shape)
    (references : Nat → UInt32) (fits : shape.volume ≤ buffers.capacity.toNat) :
    CStorage.Preserves heap (prepareReferences heap buffers shape references) ∧
      CReadOnly.Preserves heap (prepareReferences heap buffers shape references) :=
  ArrayStore.run_preserves (references_run stored shape references fits)

def finiteValues (values : TensorView.Values shape) : Fin shape.volume → Value := fun i => .finite values[i]

theorem finite_written (heap : Heap) (base : Address) (values : TensorView.Values shape) (k : Nat) :
    ArrayStore.written heap base .float64 (finiteValues values) k = TensorView.written heap base values k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ArrayStore.written, TensorView.written, ih, finiteValues]
    rfl

theorem values_run (heap : Heap) (base : Address) (values : TensorView.Values shape)
    (stored : TensorView.Writable heap base shape.volume) :
    ArrayStore.run heap base (finiteValues values) shape.volume =
      some (TensorView.written heap base values shape.volume) := by
  rw [← finite_written]
  exact ArrayStore.run_written _ _ _ _ _ (by omega) stored (by decide) (fun _ => rfl)

theorem values_preserve (heap : Heap) (base : Address) (values : TensorView.Values shape)
    (stored : TensorView.Writable heap base shape.volume) :
    CStorage.Preserves heap (TensorView.written heap base values shape.volume) ∧
      CReadOnly.Preserves heap (TensorView.written heap base values shape.volume) :=
  ArrayStore.run_preserves (values_run heap base values stored)

end Rumoca.FMI3.Float64Buffers
end
