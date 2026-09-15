import RumocaFMI3.DebugLoggingCode
import RumocaC.StringCompareAssignment
import RumocaC.LoopBehavior

/-! Category validation follows null-terminated caller memory and the shared
strcmp semantics. The universal loop proof does not enumerate categories or
assume a fixed bound such as one entry. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops CStringMemory CStringOperations
variable [interface : CInterface]

omit interface in
theorem iteration_closed : iteration.all noDeclarations = true := by
  simp [iteration, rejectNull, rejectDifference, comparison, failure, noDeclarations]

theorem category_eval (env : Locals) (heap : Heap) (base : Address) (i : Nat)
    (value : Option Address)
    (pointer : resolve env "categories" = some (.pointer (some base)))
    (counter : resolve env "k" = some (.integer i))
    (loaded : load heap (base.index i) = some (.pointer value)) :
    CBody.eval env heap category = some (.pointer value) := by
  simp [category, CBody.eval, pointer, counter, Value.address, loaded]

theorem null_category_step (env : Locals) (types : Types) (heap : Heap)
    (value : Option Address) (rest : List Stmt)
    (loaded : CBody.eval env heap category = some (.pointer value)) :
    CLoops.next (.running (rejectNull :: rest) env types heap) =
      some (.running (if value.isNone then failure "Unknown log category" :: rest else rest)
        env types heap) := by
  cases value <;>
    simp [rejectNull, failure, CLoops.next, noDeclarations, CLoops.eval,
      CBody.eval, loaded, Value.truth, boolean]

theorem difference_step (env : Locals) (types : Types) (heap : Heap)
    (value : Int) (rest : List Stmt)
    (loaded : env "difference" = some (.integer value)) :
    CLoops.next (.running (rejectDifference :: rest) env types heap) =
      some (.running (if value = 0 then rest else failure "Unknown log category" :: rest)
        env types heap) := by
  by_cases zero : value = 0 <;>
    simp [rejectDifference, failure, CLoops.next, noDeclarations, CLoops.eval,
      CBody.eval, resolve, loaded, CBody.comparison, boolean, Value.truth, zero]

theorem iteration_valid_equivalence (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (selected expected : Address)
    (bytes : List UInt8) (old : Value) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation)
    (pointer : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (present : env "difference" = some old) (typed : types "difference" = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (bound : program.externals "strcmp" = some (CStringCalls.compareExternal integer))
    (loaded : CBody.eval env heap category = some (.pointer (some selected)))
    (literal : interface.literals "logStatus" = some expected)
    (selectedStored : Contents heap selected bytes) (expectedStored : Contents heap expected bytes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (iteration ++ rest) env types heap) resultType stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest (CBody.bind env "difference" (.integer 0)) types heap) resultType stack) behavior := by
  have first := null_category_step env types heap (some selected)
    (comparison :: rejectDifference :: rest) loaded
  simp only [Option.isNone_some, Bool.false_eq_true, if_false] at first
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program first resultType stack) (.refl _)) behavior).trans
  apply CStringCalls.compare_assignment_equivalence program env types heap "difference"
    [category, .str "logStatus"] (rejectDifference :: rest) resultType stack old selected expected bytes bytes
    pointer integer present typed unshadowed named bound
    (by simp [CCalls.arguments, loaded, CBody.eval, literal]) selectedStored expectedStored
  intro value range compared observed
  have zero : value = 0 := (comparison_zero compared).mpr rfl
  subst value
  have step := difference_step (CBody.bind env "difference" (.integer 0)) types heap 0 rest
    (by simp [CBody.bind])
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program step resultType stack) (.refl _)) observed

end Rumoca.FMI3.DebugLogging
end
