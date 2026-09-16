import RumocaFMI3.InitializationFootprint
import RumocaC.InitializationProgress

namespace Rumoca.FMI3.InstanceSlot
open CMemory CCalls CCalls.InitializationRegion
variable [interface : CInterface] {E : Type}

/-- An actual initializer step in one array element preserves every cell of
any distinct element, at arbitrary member depth. The caller does not supply
a frame for this generated C step. -/
theorem initialization_other_instance (program : Events.Program E)
    (base : Address) (i j : Nat) (different : i ≠ j)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (ready : CompleteReady {q | (base.index i).InRecord q} env types
      (.cast "fmi3Instance" (.id "m")) "fmi3Instance"
      ⟨.pointer (some (base.index i)), expectedHeap⟩ (.pointer (some (base.index i))) before)
    (step : Events.Step program before events after) :
    Set.EqOn (CReadOnly.typedHeap before) (CReadOnly.typedHeap after) {q | (base.index j).InRecord q} := by
  have cast : returnCast "fmi3Instance" (.pointer (some (base.index i))) =
      some (.pointer (some (base.index i))) := by
    simp [returnCast, CBody.cast, handle, convert]
  have frame := complete_step_frame program rfl cast ready step
  intro query inside
  exact (frame (fun own => Address.records_separate base i j different own inside rfl)).symm

end Rumoca.FMI3.InstanceSlot
