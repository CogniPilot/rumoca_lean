import RumocaFMI3.DebugLoggingFailureLoop
import RumocaC.StorageRegion

/-! The logging configuration write follows complete category validation. The
typed write preserves every other cell and the original storage permissions. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops

def working (env : Locals) (i : Nat) : Locals :=
  counterEnv (CBody.bind env "difference" (.integer 0)) "k" i

def workingTypes (types : Types) : Types :=
  bindType (bindType types "difference" .int32) "k" .size

def written (heap : Heap) (p : Address) (enabled : Bool) : Heap :=
  replace heap (p.member "logging") ⟨.boolean, true, some (boolean enabled)⟩

theorem written_store (heap : Heap) (p : Address) (enabled : Bool) (old : Option Value)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) :
    store heap (p.member "logging") (boolean enabled) = some (written heap p enabled) := by
  cases enabled <;> simp [store, storage, convert, boolean, Value.truth]
  all_goals rfl

theorem written_frame (heap : Heap) (p : Address) (enabled : Bool) (address : Address)
    (outside : address ≠ p.member "logging") :
    written heap p enabled address = heap address := by
  simp [DebugLogging.written, replace, outside]

theorem written_storage (heap : Heap) (p : Address) (enabled : Bool) (old : Option Value)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) :
    CStorage.Preserves heap (written heap p enabled) ∧
    CReadOnly.Preserves heap (written heap p enabled) := by
  have stored := written_store heap p enabled old storage
  exact ⟨CStorage.store_preserves stored, CReadOnly.store_preserves stored⟩

variable [interface : CInterface]

theorem missing_step (env : Locals) (types : Types) (heap : Heap)
    (pointer : Option Address) (n : Nat) (rest : List Stmt)
    (count : env "nCategories" = some (.integer n))
    (array : env "categories" = some (.pointer pointer)) :
    CLoops.next (.running (missing :: rest) env types heap) =
      some (.running (if n = 0 ∨ pointer.isSome = true then rest else
        failure "Missing log categories" :: rest) env types heap) := by
  cases pointer <;> by_cases zero : n = 0 <;>
    simp [missing, failure, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, noDeclarations, CLoops.evalWith, CBody.eval, CBody.evalWith,
      resolve, count, array, boolean, Value.truth, zero]

theorem declarations_reaches (program : CCalls.Events.Program E) (env : Locals)
    (types : Types) (heap : Heap) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation)
    (differenceFresh : env "difference" = none) (counterFresh : env "k" = none)
    (integer : interface.types "int" = some .int32) (sizeType : interface.types "size_t" = some .size) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (.declare "int" "difference" (.nat 0) ::
        .declare "size_t" "k" (.nat 0) :: rest) env types heap) resultType stack)
      (.body (.running rest (working env 0) (workingTypes types) heap) resultType stack) := by
  have first := CLoops.declare_local env types heap "int" "difference" (.nat 0)
    (.declare "size_t" "k" (.nat 0) :: rest) .int32 (.integer 0) (.integer 0)
    integer differenceFresh rfl (by decide)
  have second := CLoops.counter_initialize (CBody.bind env "difference" (.integer 0))
    (bindType types "difference" .int32) heap "k" rest
    (by simp [CBody.bind, counterFresh]) sizeType
  exact .next (CCalls.Events.body_step program first resultType stack)
    (.next (CCalls.Events.body_step program second resultType stack) (.refl _))

theorem write_logging_step (env : Locals) (types : Types) (heap : Heap) (p : Address)
    (enabled : Bool) (old : Option Value) (rest : List Stmt)
    (handle : env "m" = some (.pointer (some p)))
    (flag : env "loggingOn" = some (boolean enabled))
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) :
    CLoops.next (.running (writeLogging :: rest) env types heap) =
      some (.running rest env types (written heap p enabled)) := by
  have stored := written_store heap p enabled old storage
  simp [writeLogging, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, CLoops.evalWith, CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith,
    resolve, handle, flag, Value.address, stored]

theorem finish_reaches (program : CCalls.Events.Program E) (env : Locals)
    (types : Types) (heap : Heap) (p : Address) (enabled : Bool) (old : Option Value)
    (stack : CCalls.Typed.Continuation)
    (handle : env "m" = some (.pointer (some p)))
    (flag : env "loggingOn" = some (boolean enabled))
    (ok : resolve env "fmi3OK" = some (.integer 0))
    (status : CCalls.returnCast "fmi3Status" (.integer 0) = some (.integer 0))
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running finish env types heap) "fmi3Status" stack)
      (.returning (.integer 0) (written heap p enabled) stack) := by
  refine .next (CCalls.Events.body_step program
    (write_logging_step env types heap p enabled old [.ret (some (.id "fmi3OK"))]
      handle flag storage) "fmi3Status" stack) ?_
  exact CCalls.Events.expression_return program env types (written heap p enabled)
    (.id "fmi3OK") [] "fmi3Status" stack (.integer 0) (.integer 0) ok status

end Rumoca.FMI3.DebugLogging
end
