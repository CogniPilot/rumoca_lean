import RumocaC.Memory
import Mathlib.Data.Set.Function

/-! Typed memory operations depend only on their addressed cell. Heap agreement
uses mathlib's `Set.EqOn`, preserving values as well as cell descriptors. -/
namespace Rumoca.CMemory.Footprint

theorem load_eq (agreement : Set.EqOn before other region) (inside : address ∈ region) :
    load before address = load other address := by
  simp only [load, agreement inside]

theorem replace_eq (agreement : Set.EqOn before other region) (address : Address) (cell : Cell) :
    Set.EqOn (replace before address cell) (replace other address cell) region := by
  intro query inside
  by_cases same : query = address
  · simp [replace, same]
  · simpa [replace, same] using agreement inside

/-- Transport the actual successful store across heaps with the same addressed
cell. The written cell is derived from the original store's conversion. -/
theorem store_transport (same : before address = other address)
    (stored : store before address value = some after) :
    ∃ cell, after = replace before address cell ∧
      store other address value = some (replace other address cell) := by
  unfold store at stored
  cases found : before address with
  | none => simp [found] at stored
  | some cell =>
    simp only [found, bind, Option.bind] at stored
    split at stored
    · contradiction
    next writable =>
      cases converted : convert cell.type value with
      | none => simp [converted] at stored
      | some datum =>
        simp only [converted, pure, Option.some.injEq] at stored
        subst after
        refine ⟨{cell with value := some datum}, rfl, ?_⟩
        simpa [store, ← same, found, converted] using writable

/-- A successful store can be replayed after interference outside its region.
The resulting heaps agree throughout the region; the other heap's exterior
is retained, rather than replaced by a stale full-heap snapshot. -/
theorem store_region (agreement : Set.EqOn before other region) (inside : address ∈ region)
    (stored : store before address value = some after) :
    ∃ following, store other address value = some following ∧
      Set.EqOn after following region ∧
      ∀ query, query ≠ address → following query = other query := by
  obtain ⟨cell, rfl, transported⟩ := store_transport (agreement inside) stored
  exact ⟨_, transported, replace_eq agreement address cell,
    fun query different => replace_other _ _ query _ different⟩

/-- A store outside a protected region leaves every cell value in it intact. -/
theorem store_outside (stored : store before address value = some after)
    (outside : address ∉ region) : Set.EqOn after before region := by
  intro query inside
  exact store_frame before address value after stored query (fun same => outside (same ▸ inside))

end Rumoca.CMemory.Footprint
