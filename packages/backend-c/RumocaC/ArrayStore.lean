import RumocaC.TensorMemory
import RumocaC.StorageTransfer

/-! Indexed typed host transfers through the ordinary C cell store.
The construction describes caller buffer preparation, not compiler lowering
or a new emitted array representation. -/
namespace Rumoca.CMemory.ArrayStore

def Writable (heap : Heap) (base : Address) (type : CType) (count : Nat) : Prop :=
  ∀ i < count, ∃ old, heap (base.index i) = some ⟨type, true, old⟩

def written (heap : Heap) (base : Address) (type : CType) (values : Fin count → Value) : Nat → Heap
  | 0 => heap
  | k + 1 => if inside : k < count then
      replace (written heap base type values k) (base.index k) ⟨type, true, some (values ⟨k, inside⟩)⟩
    else written heap base type values k

/-- Each requested write goes through conversion and the existing cell's
type/permissions. An out-of-range count or failed store is rejected. -/
def run (heap : Heap) (base : Address) (values : Fin count → Value) : Nat → Option Heap
  | 0 => some heap
  | k + 1 => do
      let prior ← run heap base values k
      if inside : k < count then store prior (base.index k) (values ⟨k, inside⟩) else none

theorem written_at (heap : Heap) (base : Address) (type : CType) (values : Fin count → Value)
    (k : Nat) (bounded : k ≤ count) (i : Fin count) :
    written heap base type values k (base.index i.val) =
      if i.val < k then some ⟨type, true, some (values i)⟩ else heap (base.index i.val) := by
  induction k with
  | zero => simp [written]
  | succ k ih =>
    have inside : k < count := by omega
    rw [written, dif_pos inside]
    by_cases same : i.val = k
    · have sameIndex : i = ⟨k, inside⟩ := Fin.ext same
      subst i
      simp [replace]
    · have distinct : base.index i.val ≠ base.index k := fun equal => same (TensorView.index_injective base equal)
      rw [replace_other _ _ _ _ distinct, ih (by omega)]
      have condition : i.val < k + 1 ↔ i.val < k := by omega
      simp only [condition]

theorem frame (heap : Heap) (base : Address) (type : CType) (values : Fin count → Value)
    (k : Nat) (query : Address) (outside : ∀ i : Fin count, query ≠ base.index i.val) :
    written heap base type values k query = heap query := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [written]
    split
    · rw [replace_other _ _ _ _ (outside ⟨k, ‹_›⟩), ih]
    · exact ih

theorem run_written (heap : Heap) (base : Address) (type : CType) (values : Fin count → Value)
    (k : Nat) (bounded : k ≤ count) (storage : Writable heap base type count)
    (nonatomic : type ≠ .atomicBoolean)
    (converted : ∀ i, convert type (values i) = some (values i)) :
    run heap base values k = some (written heap base type values k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have inside : k < count := by omega
    obtain ⟨old, stored⟩ := storage k inside
    have current := written_at heap base type values k (by omega) ⟨k, inside⟩
    simp only [lt_self_iff_false, if_false] at current
    simp [run, ih (by omega), inside, store, current.trans stored, nonatomic, converted, written]

/-- All successful transfers preserve the existing object domain, types,
permissions and read-only contents, including transfers whose inputs convert. -/
theorem run_preserves (executed : run heap base values k = some after) :
    CStorage.Preserves heap after ∧ CReadOnly.Preserves heap after := by
  induction k generalizing after with
  | zero =>
    cases Option.some.inj executed
    exact ⟨.refl _, .refl _⟩
  | succ k ih =>
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at executed
    obtain ⟨prior, priorRun, final⟩ := executed
    split at final
    · obtain ⟨stored, readonly⟩ := ih priorRun
      exact ⟨stored.trans (CStorage.store_preserves final), readonly.trans (CReadOnly.store_preserves final)⟩
    · contradiction

theorem written_reads (heap : Heap) (base : Address) (type : CType) (values : Fin count → Value)
    (nonatomic : type ≠ .atomicBoolean)
    (converted : ∀ i, convert type (values i) = some (values i)) :
    ∀ i, load (written heap base type values count) (base.index i.val) = some (values i) := by
  intro i
  have found := written_at heap base type values count (by omega) i
  rw [if_pos i.isLt] at found
  simp [load, found, nonatomic, converted]

end Rumoca.CMemory.ArrayStore
