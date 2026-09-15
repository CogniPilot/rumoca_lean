import RumocaC.Storage

namespace Rumoca.CStorage
open CMemory

/-- An atomic cell remains unreadable by ordinary loads across any transition
that preserves storage descriptions, independently of its payload. -/
theorem Preserves.atomic_unreadable {cell : Cell} (preserved : Preserves before after)
    (found : after p = some cell) (atomic : cell.type = .atomicBoolean) :
    load before p = none := by
  cases original : before p with
  | none => simp [load, original]
  | some prior =>
    have same := preserved p
    simp only [description, found, original, Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
    have typeSame : prior.type = .atomicBoolean := same.1.symm.trans atomic
    simp [load, original, typeSame]

end Rumoca.CStorage
