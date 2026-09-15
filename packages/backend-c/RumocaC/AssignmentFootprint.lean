import RumocaC.MemoryFootprint
import RumocaC.HeapFreeExpressions

namespace Rumoca.CLoops.Footprint
open CTree CMemory CBody.Footprint
variable [CInterface]

theorem assignment_next (notLocal : ∀ name, target ≠ Expr.id name) :
    next (.running (.assign target expr :: rest) env types heap) =
      (do
        let value ← eval env types heap expr
        let address ← CBody.lvalue env heap target
        let following ← store heap address value
        return .running rest env types following) := by
  cases target <;> try rfl
  exact False.elim (notLocal _ rfl)

/-- Transport the actual memory-assignment step after changes outside its
write region. The address and converted written value come from the original
step; no later heap snapshot or next control is supplied. -/
theorem assignment_region (addressFree : heapFreeAddress target = true)
    (valueFree : heapFreeValue expr = true)
    (inside : ∀ address, CBody.lvalue env before target = some address → address ∈ region)
    (agreement : Set.EqOn before other region)
    (step : next (.running (.assign target expr :: rest) env types before) = some finish) :
    ∃ after following, finish = .running rest env types after ∧
      next (.running (.assign target expr :: rest) env types other) =
        some (.running rest env types following) ∧
      Set.EqOn after following region ∧
      ∀ query, query ∉ region → following query = other query := by
  have notLocal : ∀ name, target ≠ Expr.id name := by
    intro name same
    subst target
    contradiction
  rw [assignment_next notLocal] at step
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at step
  obtain ⟨value, evaluated, address, selected, after, stored, returned⟩ := step
  cases Option.some.inj returned
  obtain ⟨following, transported, agreed, frame⟩ :=
    CMemory.Footprint.store_region agreement (inside address selected) stored
  refine ⟨after, following, rfl, ?_, agreed, ?_⟩
  · rw [assignment_next notLocal]
    rw [← loop_heap_free valueFree env types before other,
      ← (heap_free target).2 addressFree env before other]
    simp [evaluated, selected, transported]
  · intro query outside
    exact frame query (fun same => outside (same ▸ inside address selected))

end Rumoca.CLoops.Footprint

namespace Rumoca.CLoops.Footprint
open CTree CMemory CBody.Footprint
variable [CInterface]

/-- A fixed-local assignment certificate, independent of heap contents.
Its region is a set of symbolic addresses, not an enumerated tensor buffer. -/
def AssignsWithin (env : CBody.Locals) (region : Set Address) : Stmt → Prop
  | .assign target value => heapFreeAddress target = true ∧ heapFreeValue value = true ∧
      ∀ heap address, CBody.lvalue env heap target = some address → address ∈ region
  | _ => False

end Rumoca.CLoops.Footprint
