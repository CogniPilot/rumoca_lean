import RumocaFMI3.LifecycleGuard
import RumocaFMI3.Runtime

noncomputable section
namespace Rumoca.FMI3.ScalarAccess
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

theorem invalid_run (env : Locals) (heap : Heap) (arrayName countName : String)
    (buffer : Option Address) (count : UInt64) (tail : List Stmt)
    (arrayBound : resolve env arrayName = some (.pointer buffer))
    (countBound : resolve env countName = some (.integer count.toNat))
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    run 1 (.running (Runtime.scalarAccessCheck arrayName countName ++ tail) env heap) =
      some (.running (Runtime.fail "Expected one continuous state" :: tail) env heap) := by
  rcases invalid with bad | rfl
  · simp [Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch, Runtime.either, Runtime.nev,
      Runtime.negate, Runtime.v, Runtime.n, run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, countBound, arrayBound,
      comparison, boolean, Value.truth, bad]
  · simp [Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch, Runtime.either, Runtime.nev,
      Runtime.negate, Runtime.v, Runtime.n, run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, countBound, arrayBound,
      comparison, boolean, Value.truth]

theorem valid_run (env : Locals) (heap : Heap) (arrayName countName : String)
    (buffer : Address) (tail : List Stmt)
    (arrayBound : resolve env arrayName = some (.pointer (some buffer)))
    (countBound : resolve env countName = some (.integer 1)) :
    run 1 (.running (Runtime.scalarAccessCheck arrayName countName ++ tail) env heap) =
      some (.running tail env heap) := by
  simp [Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch, Runtime.either, Runtime.nev,
    Runtime.negate, Runtime.v, Runtime.n, run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, countBound, arrayBound,
    comparison, boolean, Value.truth]

end Rumoca.FMI3.ScalarAccess
