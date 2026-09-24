import RumocaC.NullComparison
import RumocaC.BooleanProofs

namespace Rumoca.CPointerConditions
open CTree CMemory CBody

def missing (names : List String) : Expr :=
  Expr.disjunction (names.map fun name => Expr.not (.id name))

/-- A nullable-output guard reads pointer arguments, not the pointed-to memory. -/
theorem missing_eval [interface : CInterface] (env : Locals) (heap : Heap)
    (names : List String) (addresses : String → Option Address)
    (bound : ∀ name ∈ names, resolve env name = some (.pointer (addresses name))) :
    eval env heap (missing names) = some (boolean (names.any fun name => (addresses name).isNone)) := by
  apply BoolProofs.eval_disjunction
  intro name member
  have head := bound name member
  cases pointer : addresses name <;>
    simp [eval, evalWith, head, pointer, boolean, Value.truth]

theorem missing_iff (names : List String) (addresses : String → Option Address) :
    (names.any fun name => (addresses name).isNone) = true ↔ ∃ name ∈ names, addresses name = none := by
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨name, member, missing⟩
    exact ⟨name, member, Option.isNone_iff_eq_none.mp missing⟩
  · rintro ⟨name, member, missing⟩
    exact ⟨name, member, Option.isNone_iff_eq_none.mpr missing⟩


/-- Same ordered lazy guard with explicit pointer-to-null comparisons. -/
def explicitMissing (names : List String) : Expr :=
  Expr.disjunction (names.map fun name => Expr.bin .eq (.id name) Expr.nullPointer)

theorem explicit_missing_eq [interface : CInterface] (env : Locals) (heap : Heap)
    (names : List String) (addresses : String → Option Address)
    (bound : ∀ name ∈ names, resolve env name = some (.pointer (addresses name)))
    (nullType : interface.types "void *" = some .pointer) :
    eval env heap (explicitMissing names) = eval env heap (missing names) := by
  induction names with
  | nil => rfl
  | cons name names ih =>
    have head := CNull.equal_eval (.id name) Expr.nullPointer env heap (addresses name)
      (bound name (by simp)) (CNull.literal_eval nullType env heap)
    cases names with
    | nil => exact head
    | cons next rest =>
      have tail := ih (fun n member => bound n (List.mem_cons_of_mem _ member))
      change ((eval env heap (.bin .eq (.id name) Expr.nullPointer)).bind fun a =>
        a.truth.bind fun b => if b then some (boolean true) else
          (eval env heap (explicitMissing (next :: rest))).bind fun c =>
            c.truth.bind fun d => some (boolean d)) =
        ((eval env heap (.not (.id name))).bind fun a =>
        a.truth.bind fun b => if b then some (boolean true) else
          (eval env heap (missing (next :: rest))).bind fun c =>
            c.truth.bind fun d => some (boolean d))
      rw [head, tail]

theorem explicit_missing_eval [interface : CInterface] (env : Locals) (heap : Heap)
    (names : List String) (addresses : String → Option Address)
    (bound : ∀ name ∈ names, resolve env name = some (.pointer (addresses name)))
    (nullType : interface.types "void *" = some .pointer) :
    eval env heap (explicitMissing names) = some (boolean (names.any fun name => (addresses name).isNone)) := by
  rw [explicit_missing_eq env heap names addresses bound nullType]
  exact missing_eval env heap names addresses bound

end Rumoca.CPointerConditions
