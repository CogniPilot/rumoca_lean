import RumocaC.Memory

/-! The unsigned value relation in the authored target's conversion and object
store. Width selection and object-layout correspondence belong to the adapter;
float-to-integer and pointer-to-integer casts remain unsupported. -/
namespace Rumoca.CMemory

theorem convert_unsigned_iff (width : Nat) (input output : Int) :
    convert (.unsigned width) (.integer input) = some (.integer output) ↔
      CUnsigned.Converts width input output := by
  simp only [convert, Option.some.injEq, Value.integer.injEq]
  constructor
  · intro same
    exact same ▸ CUnsigned.value_correct width input
  · intro valid
    exact (CUnsigned.value_unique valid).symm

theorem convert_unsigned_bits (width : Nat) (input : Int) :
    convert (.unsigned width) (.integer input) =
      some (.integer ((BitVec.ofInt width input).toNat : Int)) := by
  rw [convert, CUnsigned.value_bits]

theorem convert_unsigned_in_range (nonnegative : 0 ≤ input)
    (bound : input < CUnsigned.modulus width) :
    convert (.unsigned width) (.integer input) = some (.integer input) := by
  rw [convert, CUnsigned.value_in_range nonnegative bound]

theorem store_unsigned (heap : Heap) (address : Address) (old : Option Value)
    (width : Nat) (input : Int)
    (storage : heap address = some ⟨.unsigned width, true, old⟩) :
    store heap address (.integer input) = some
      (replace heap address ⟨.unsigned width, true, some (.integer (CUnsigned.value width input))⟩) := by
  simp [store, storage, convert]

theorem load_unsigned_written (heap : Heap) (address : Address) (width : Nat) (input : Int) :
    load (replace heap address
      ⟨.unsigned width, true, some (.integer (CUnsigned.value width input))⟩) address =
      some (.integer (CUnsigned.value width input)) := by
  simp [load, convert, CUnsigned.value_idempotent]

end Rumoca.CMemory
