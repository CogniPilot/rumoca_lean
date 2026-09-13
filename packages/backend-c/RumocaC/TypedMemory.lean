import RumocaC.Memory

/-! Compose ordinary typed cell access with a separately checked conversion.
Keeping conversions abstract avoids unfolding numerical encodings during
unrelated memory proofs. Atomic cells still require their dedicated operations. -/
namespace Rumoca.CMemory

theorem store_converted (heap : Heap) (address : Address) (type : CType) (old : Option Value)
    (input output : Value) (found : heap address = some ⟨type, true, old⟩)
    (ordinary : type ≠ .atomicBoolean) (converted : convert type input = some output) :
    store heap address input = some (replace heap address ⟨type, true, some output⟩) := by
  simp [store, found, ordinary, converted]

theorem load_converted (heap : Heap) (address : Address) (type : CType) (writable : Bool)
    (value : Value) (found : heap address = some ⟨type, writable, some value⟩)
    (ordinary : type ≠ .atomicBoolean) (converted : convert type value = some value) :
    load heap address = some value := by
  simp [load, found, ordinary, converted]

end Rumoca.CMemory
