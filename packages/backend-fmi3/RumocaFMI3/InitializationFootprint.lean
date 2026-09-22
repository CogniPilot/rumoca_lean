import RumocaC.AssignmentFootprint
import RumocaFMI3.InstanceSlot

namespace Rumoca.FMI3.InstanceInitialization
open CTree CMemory CBody CBody.Footprint CLoops.Footprint
variable [CInterface]

theorem field_assignment_footprint (instanceBound : resolve env "m" = some (.pointer (some p)))
    (name : String) (free : heapFreeValue value = true) :
    AssignsWithin env {q | p.InRecord q} (put name value) := by
  refine ⟨rfl, free, ?_⟩
  intro heap address selected
  have same : some (p.member name) = some address := by
    simpa [put, field, lvalue, lvalueWith, eval, evalWith, instanceBound, Value.address] using selected
  cases Option.some.inj same
  exact p.member_in_record name

/-- All stores in the actual initializer use only bound locals/constants and
write the selected record, including its nested prepared Solve state. -/
theorem initialization_footprint (model : Solve.Model source) (kind : Kind)
    (instanceBound : resolve env "m" = some (.pointer (some p))) :
    ∀ stmt ∈ code model kind, AssignsWithin env {q | p.InRecord q} stmt := by
  intro stmt member
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨rfl, rfl, ?_⟩
    intro heap address selected
    have same : some ((p.member "model").member "x") = some address := by
      simpa [CInitialization.Emission.statement, state, field, lvalue, lvalueWith, eval, evalWith,
        instanceBound, Value.address] using selected
    cases Option.some.inj same
    exact (p.member_in_record "model").member "x"
  all_goals exact field_assignment_footprint instanceBound _ rfl

/-- Slot metadata has the same region discipline as the payload; returning
the handle does not read object memory. -/
theorem slot_initialization_footprint (model : Solve.Model source) (kind : Kind)
    (instanceBound : resolve env "m" = some (.pointer (some p))) :
    (∀ stmt ∈ InstanceSlot.statement :: code model kind,
      AssignsWithin env {q | p.InRecord q} stmt) ∧
      heapFreeValue (.cast "fmi3Instance" (.id "m")) = true := by
  refine ⟨?_, rfl⟩
  intro stmt member
  rcases List.mem_cons.mp member with rfl | rest
  · exact field_assignment_footprint instanceBound "slot" rfl
  · exact initialization_footprint model kind instanceBound stmt rest

end Rumoca.FMI3.InstanceInitialization
