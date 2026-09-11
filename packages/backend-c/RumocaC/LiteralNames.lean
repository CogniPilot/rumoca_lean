import RumocaC.LiteralPoolStorage

/-! Naming facts about the actual checked constructor. These establish its
fixed non-reserved prefix and identifier significance bound. Complete header
macro/type exclusions and native linkage still require the target's inputs. -/
namespace Rumoca.CLiteral
variable {reserved : List String}

theorem Pool.make_spelling (made : Pool.make reserved texts = some pool)
    (member : entry ∈ pool.entries) :
    ∃ index : Nat, entry.name = "rumoca_literal_" ++ toString index := by
  rw [Pool.make_entries made] at member
  unfold candidates at member
  obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp member
  exact ⟨index, rfl⟩

/-- The generated names begin with a lowercase letter, exclude the supplied
reserved names/keywords, and fit C11's 63 significant internal characters.
This theorem is about `make`; an arbitrary checked pool need not use its prefix. -/
theorem Pool.make_name_conditions (made : Pool.make reserved texts = some pool)
    (member : entry ∈ pool.entries) :
    CIdentifier.valid ("isfinite" :: reserved) entry.name = true ∧
      entry.name.toList.head? = some 'r' ∧ entry.name.length ≤ 63 := by
  obtain ⟨index, spelling⟩ := Pool.make_spelling made member
  refine ⟨(pool.entry_valid member).1, ?_, (pool.entry_valid member).2⟩
  simp [spelling, String.toList_append]

/-- Discharge the authored constant-dictionary freshness premise from the
same explicit exclusions supplied to the checked pool constructor. -/
theorem Pool.headerFresh_of_reserved (pool : Pool reserved) (header : CInterface)
    (covered : ∀ name value, header.constants name = some value → name ∈ reserved) :
    pool.HeaderFresh header := by
  intro entry member
  cases found : header.constants entry.name with
  | none => rfl
  | some value =>
      exact False.elim ((pool.entry_fresh member).2 (covered entry.name value found))

end Rumoca.CLiteral
