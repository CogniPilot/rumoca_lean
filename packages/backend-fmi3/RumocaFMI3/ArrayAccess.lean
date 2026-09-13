import RumocaFMI3.ScalarAccess

/-! Reusable equal-length/nonempty-buffer validation. Empty
queries may have null arrays. The complete public getter contract composes this shared guard with
its typed loops, nested numerical calls and actual-file binding. -/
noncomputable section
namespace Rumoca.FMI3.ArrayAccess
open CTree CMemory CBody

def Valid (left right : Option Address) (n m : UInt64) : Prop :=
  n.toNat = m.toNat ∧ (n.toNat = 0 ∨ left ≠ none) ∧ (m.toNat = 0 ∨ right ≠ none)

instance (left right : Option Address) (n m : UInt64) : Decidable (Valid left right n m) :=
  inferInstanceAs (Decidable (n.toNat = m.toNat ∧
    (n.toNat = 0 ∨ left ≠ none) ∧ (m.toNat = 0 ∨ right ≠ none)))

def guard (left right leftCount rightCount message : String) : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v leftCount) (Runtime.v rightCount),
    Runtime.both (Runtime.v leftCount) (Runtime.negate (Runtime.v left)),
    Runtime.both (Runtime.v rightCount) (Runtime.negate (Runtime.v right))]) message

def float64Guard : Stmt := guard "valueReferences" "values" "nValueReferences" "nValues"
  "Invalid Float64 array lengths or pointers"

theorem getter_guard : (Runtime.getFloat64.drop (Runtime.require .get).length).head? = some float64Guard := rfl
theorem setter_guard : Runtime.setFloat64Values.head? = some float64Guard := rfl

variable [interface : CInterface]

set_option maxHeartbeats 2000000 in
theorem run_guard (env : Locals) (heap : Heap) (left right leftCount rightCount message : String)
    (lp rp : Option Address) (n m : UInt64) (tail : List Stmt)
    (leftBound : resolve env left = some (.pointer lp))
    (rightBound : resolve env right = some (.pointer rp))
    (nBound : resolve env leftCount = some (.integer n.toNat))
    (mBound : resolve env rightCount = some (.integer m.toNat)) :
    run 1 (.running (guard left right leftCount rightCount message :: tail) env heap) =
      some (.running (if Valid lp rp n m then tail else Runtime.fail message :: tail) env heap) := by
  classical
  by_cases same : n.toNat = m.toNat <;>
    by_cases nz : n.toNat = 0 <;> by_cases mz : m.toNat = 0 <;>
    cases lp <;> cases rp <;>
    simp_all [guard, Valid, Runtime.reject, Runtime.branch, Runtime.any,
      Runtime.either, Runtime.both, Runtime.nev, Runtime.negate, Runtime.v, Runtime.n,
      run, next, eval, comparison, boolean, Value.truth]
  all_goals have nonzero : (0 : Int) ≠ m.toNat := by omega
  all_goals simp [nonzero]

end Rumoca.FMI3.ArrayAccess
