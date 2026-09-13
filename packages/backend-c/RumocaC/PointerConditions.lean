import RumocaC.Body

namespace Rumoca.CPointerConditions
open CTree CMemory CBody

def missing (names : List String) : Expr :=
  (names.map fun name => Expr.not (.id name)).foldr (Expr.bin .or) (.nat 0)

/-- A nullable-output guard reads pointer arguments, not the pointed-to memory. -/
theorem missing_eval [interface : CInterface] (env : Locals) (heap : Heap)
    (names : List String) (addresses : String → Option Address)
    (bound : ∀ name ∈ names, resolve env name = some (.pointer (addresses name))) :
    eval env heap (missing names) = some (boolean (names.any fun name => (addresses name).isNone)) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    have head := bound name (by simp)
    have tail := ih (fun next member => bound next (by simp [member]))
    unfold missing at tail
    cases pointer : addresses name <;>
      cases rest : names.any (fun name => (addresses name).isNone) <;>
      simp [missing, List.any_cons, eval, head, pointer, tail, rest, boolean, Value.truth]

theorem missing_iff (names : List String) (addresses : String → Option Address) :
    (names.any fun name => (addresses name).isNone) = true ↔ ∃ name ∈ names, addresses name = none := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨name, member, missing⟩
    exact ⟨name, member, Option.isNone_iff_eq_none.mp missing⟩
  · rintro ⟨name, member, missing⟩
    exact ⟨name, member, Option.isNone_iff_eq_none.mpr missing⟩

end Rumoca.CPointerConditions
