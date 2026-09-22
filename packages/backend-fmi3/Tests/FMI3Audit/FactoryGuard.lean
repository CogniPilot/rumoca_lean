import RumocaFMI3.StaticFactoryInitialization
import ProofAudit.Audit

noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

/-- The equality guard alone accepts an index above capacity. Actual factory
composition excludes this state using the scan's separate bounds theorem. -/
theorem exhaustion_guard_not_range_check (capacity : Nat) (heap : Heap)
    (types : CLoops.Types) (rest : List Stmt) :
    ∃ env : Locals,
      resolve env "slot" = some (.integer (capacity + 1)) ∧
      resolve env "rumoca_instance_capacity" = some (.integer capacity) ∧
      capacity < capacity + 1 ∧
      CLoops.next (.running (guard :: rest) env types heap) =
        some (.running rest env types heap) := by
  let env := bind (bind (fun _ => none) "slot" (.integer (capacity + 1)))
    "rumoca_instance_capacity" (.integer capacity)
  have selected : resolve env "slot" = some (.integer (capacity + 1)) := by
    simp [env, CBody.bind, CBody.resolve]
  have count : resolve env "rumoca_instance_capacity" = some (.integer capacity) := by
    simp [env, CBody.bind, CBody.resolve]
  refine ⟨env, selected, count, by omega, ?_⟩
  have different : capacity + 1 ≠ capacity := by omega
  simpa only [if_neg different, List.nil_append] using
    guard_step env types heap (capacity + 1) capacity rest selected count

#audit axioms exhaustion_guard_not_range_check

end Rumoca.FMI3.StaticFactory
