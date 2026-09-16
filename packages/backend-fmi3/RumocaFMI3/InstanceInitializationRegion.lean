import RumocaFMI3.InitializationFootprint
import RumocaC.InitializationCompletion

namespace Rumoca.FMI3.InstanceSlot
open CTree CMemory CBody CCalls.InitializationRegion
variable [interface : CInterface]

/-- The actual slot store and existing prepared initializer execute in the
same loop machine used by the public concurrent C runtime. -/
theorem run_return (model : Solve.Model source) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    CLoops.run 14 (.running (code model kind) env types heap) =
      some (.returned ⟨.pointer (some p), finalHeap heap p slot kind environment logger logging⟩) := by
  have stored := store_index heap p slot storage.index bounded
  obtain ⟨types', executed, _⟩ := CBodyEmbedding.run_refines 13 _ _ types
    (by simp [CBodyEmbedding.safe, InstanceInitialization.code, InstanceInitialization.put,
      InstanceInitialization.returnHandle, CInitialization.Emission.statement, CBodyEmbedding.closedBlocks])
    (InstanceInitialization.run_return model kind env (written heap p slot) p environment logger logging
      (storage.fields.preserved (CStorage.store_preserves stored)) bound double handle)
  change (CLoops.next (.running (code model kind) env types heap)).bind (CLoops.run 13) = _
  rw [show code model kind = statement ::
    (InstanceInitialization.code model kind ++ [InstanceInitialization.returnHandle]) from rfl,
    step env types heap p slot _ bound.instanceBound selected storage.index bounded]
  exact executed

/-- Instantiate the generic private-store invariant with every actual store
in the emitted initializer, including metadata and nested model state. -/
theorem initialization_ready (model : Solve.Model source) (kind : Kind)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    CompleteReady {q | p.InRecord q} env types (.cast "fmi3Instance" (.id "m")) "fmi3Instance"
      ⟨.pointer (some p), finalHeap heap p slot kind environment logger logging⟩ (.pointer (some p))
      (.body (.running (code model kind) env types heap) "fmi3Instance" .done) := by
  refine .inl (.running (statement :: InstanceInitialization.code model kind) heap heap
    (InstanceInitialization.slot_initialization_footprint model kind bound.instanceBound).1 ?_ ?_)
  · exact run_return model kind env types heap p slot environment logger logging storage bound selected bounded double handle
  · intro query inside
    rfl

end Rumoca.FMI3.InstanceSlot
