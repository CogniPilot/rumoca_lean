import RumocaFMI3.InstanceInitialization
import RumocaC.BodyEvents
import RumocaC.Storage

/-! Initialization and handle return in the observable C call machine.
This is the successful factory suffix; slot reservation, public argument entry
and the complete actual factory certificate must compose with it separately. -/
noncomputable section
namespace Rumoca.FMI3.InstanceInitialization
open CTree CMemory CBody
variable [interface : CInterface]

structure Bindings (env : Locals) (p : Address)
    (environment logger : Option Address) (logging : Bool) : Prop where
  instanceBound : resolve env "m" = some (.pointer (some p))
  environmentBound : resolve env "instanceEnvironment" = some (.pointer environment)
  loggerBound : resolve env "logMessage" = some (.pointer logger)
  loggingBound : resolve env "loggingOn" = some (boolean logging)

theorem run_return (model : Solve.Model source) (kind : Kind)
    (env : Locals) (heap : Heap) (p : Address) (environment logger : Option Address)
    (logging : Bool) (storage : Storage heap p) (bound : Bindings env p environment logger logging)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    run 13 (.running (code model kind ++ [returnHandle]) env heap) =
      some (.returned ⟨.pointer (some p), finalHeap heap p kind environment logger logging⟩) := by
  rw [show 13 = 12 + 1 from rfl, run_add,
    run_initialization model kind env heap p environment logger logging [returnHandle]
      storage double bound.instanceBound bound.environmentBound bound.loggerBound bound.loggingBound]
  simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, returnHandle, CBody.eval, CBody.evalWith, bound.instanceBound, CBody.cast, handle, convert]

/-- The suffix terminates and returns its initialized handle in every caller
continuation. No successful execution, zero-filled object or foreign-call result
is a premise. Unused foreign bindings cannot affect this block. -/
theorem return_reaches (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address)
    (environment logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation)
    (storage : Storage heap p) (bound : Bindings env p environment logger logging)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (code model kind ++ [returnHandle]) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some p)) (finalHeap heap p kind environment logger logging) stack) := by
  obtain ⟨types', executed, _⟩ := CBodyEmbedding.run_refines 13 _ _ types
    (by simp [CBodyEmbedding.safe, code, put, returnHandle, CInitialization.Emission.statement,
      CBodyEmbedding.closedBlocks])
    (run_return model kind env heap p environment logger logging storage bound double handle)
  refine (CCalls.Events.body_reaches program (CLoops.run_reaches executed) "fmi3Instance" stack).trans ?_
  exact .next (by simp [CBodyEmbedding.lift, CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
    CCalls.returnCast, CBody.cast, handle, convert]) (.refl _)

theorem complete (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : Bindings env p environment logger logging)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code model kind ++ [returnHandle]) env types heap) "fmi3Instance" .done) behavior ↔
      behavior = .terminates [] ⟨.pointer (some p), finalHeap heap p kind environment logger logging⟩) ∧
    CStorage.Preserves heap (finalHeap heap p kind environment logger logging) ∧
    Initialized (finalHeap heap p kind environment logger logging) p kind environment logger logging ∧
    (∀ query, ¬ p.InRecord query → finalHeap heap p kind environment logger logging query = heap query) := by
  have path := return_reaches program model kind env types heap p environment logger logging .done
    storage bound double handle
  refine ⟨?_, CStorage.internal_reaches program path,
    initialized heap p kind environment logger logging,
    fun query outside => frame heap p query kind environment logger logging outside⟩
  exact (CCalls.Events.internal_prefix program
    path
    (CCalls.Events.return_forced program (.pointer (some p))
      (finalHeap heap p kind environment logger logging))).behaviors

end Rumoca.FMI3.InstanceInitialization
