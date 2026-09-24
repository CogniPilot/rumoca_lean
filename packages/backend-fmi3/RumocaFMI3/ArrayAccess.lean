import RumocaFMI3.ScalarAccess
import RumocaC.NullComparison
import RumocaC.CountConditions

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
  Runtime.arrayAccessGuardWith Expr.not left right leftCount rightCount message

/-- Explicit-null variant; the generic legacy guard remains available without
requiring a null-pointer type binding. -/
def explicitGuard (left right leftCount rightCount message : String) : Stmt :=
  Runtime.arrayAccessGuardWith (fun p => Expr.bin .eq p Expr.nullPointer)
    left right leftCount rightCount message

/-- Actual count-and-pointer specialization; the two old guards remain unchanged. -/
def countGuard (left right leftCount rightCount message : String) : Stmt :=
  Runtime.arrayAccessGuardWithConditions CCountConditions.nonzero
    (fun p => Expr.bin .eq p Expr.nullPointer) left right leftCount rightCount message

def float64Guard : Stmt := countGuard "valueReferences" "values" "nValueReferences" "nValues"
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
    simp_all [guard, Runtime.arrayAccessGuardWith, Runtime.arrayAccessGuardWithConditions, id_eq, Valid, Runtime.reject, Runtime.branch, Runtime.any,
      Runtime.either, Runtime.both, Runtime.nev, Runtime.v, Runtime.n,
      run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, comparison, boolean, Value.truth]
  all_goals have nonzero : (0 : Int) ≠ m.toNat := by omega
  all_goals simp [nonzero]


/-- The explicit variant has the same full validity/heap/continuation contract.
Only this new generic helper requires the null type; concrete FMI callers
derive it from their existing interface. -/
theorem run_explicit_guard (env : Locals) (heap : Heap) (left right leftCount rightCount message : String)
    (lp rp : Option Address) (n m : UInt64) (tail : List Stmt)
    (leftBound : resolve env left = some (.pointer lp))
    (rightBound : resolve env right = some (.pointer rp))
    (nBound : resolve env leftCount = some (.integer n.toNat))
    (mBound : resolve env rightCount = some (.integer m.toNat))
    (nullType : interface.types "void *" = some .pointer) :
    run 1 (.running (explicitGuard left right leftCount rightCount message :: tail) env heap) =
      some (.running (if Valid lp rp n m then tail else Runtime.fail message :: tail) env heap) := by
  have hl := CNull.equal_eval (.id left) Expr.nullPointer env heap lp leftBound
    (CNull.literal_eval nullType env heap)
  have hr := CNull.equal_eval (.id right) Expr.nullPointer env heap rp rightBound
    (CNull.literal_eval nullType env heap)
  simp only [eval, evalWith] at hl hr
  have same :
      run 1 (.running (explicitGuard left right leftCount rightCount message :: tail) env heap) =
      run 1 (.running (guard left right leftCount rightCount message :: tail) env heap) := by
    simp only [explicitGuard, guard, Runtime.arrayAccessGuardWith, Runtime.arrayAccessGuardWithConditions, id_eq, Runtime.reject, Runtime.branch,
      Runtime.any, Runtime.nev, Runtime.v, Runtime.both, Runtime.either, Runtime.n,
      List.foldr_cons, List.foldr_nil, run, next, nextWith, legacyExpressions, eval, evalWith, hl, hr]
  rw [same]
  exact run_guard env heap left right leftCount rightCount message lp rp n m tail
    leftBound rightBound nBound mBound

/-- Empty queries skip both pointer leaves. Neither pointer bindings nor a
null-type lookup is needed, and the entire heap and continuation are retained. -/
theorem run_explicit_guard_zero (env : Locals) (heap : Heap)
    (left right leftCount rightCount message : String) (tail : List Stmt)
    (nBound : resolve env leftCount = some (.integer 0))
    (mBound : resolve env rightCount = some (.integer 0)) :
    run 1 (.running (explicitGuard left right leftCount rightCount message :: tail) env heap) =
      some (.running tail env heap) := by
  simp [explicitGuard, Runtime.arrayAccessGuardWith, Runtime.arrayAccessGuardWithConditions, id_eq, Runtime.reject, Runtime.branch,
    Runtime.any, Runtime.nev, Runtime.v, Runtime.both, Runtime.either, Runtime.n,
    run, next, nextWith, legacyExpressions, eval, evalWith, nBound, mBound,
    comparison, Value.truth, boolean]

/-- Canonical full condition equality. Pointer operands may fail or be skipped;
no pointer binding, storage or null-type premise is needed for count rewriting. -/
theorem count_condition_eval (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (env : Locals) (heap : Heap)
    (pointerMissing : Expr → Expr) (left right leftCount rightCount : String)
    (sizeType : interface.types "size_t" = some .size)
    (nInteger : CCountConditions.IntegerResult
      (evalWith declarations objects env heap (.id leftCount)))
    (mInteger : CCountConditions.IntegerResult
      (evalWith declarations objects env heap (.id rightCount))) :
    evalWith declarations objects env heap
      (Runtime.any [Runtime.nev (.id leftCount) (.id rightCount),
        Runtime.both (CCountConditions.nonzero (.id leftCount)) (pointerMissing (.id left)),
        Runtime.both (CCountConditions.nonzero (.id rightCount)) (pointerMissing (.id right))]) =
    evalWith declarations objects env heap
      (Runtime.any [Runtime.nev (.id leftCount) (.id rightCount),
        Runtime.both (.id leftCount) (pointerMissing (.id left)),
        Runtime.both (.id rightCount) (pointerMissing (.id right))]) := by
  have hl := CCountConditions.and_nonzero_eval declarations objects env heap
    (.id leftCount) (pointerMissing (.id left)) sizeType nInteger
  have hr := CCountConditions.and_nonzero_eval declarations objects env heap
    (.id rightCount) (pointerMissing (.id right)) sizeType mInteger
  exact CCountConditions.or_eval_congr declarations objects env heap _ _ _ _ rfl
    (CCountConditions.or_eval_congr declarations objects env heap _ _ _ _ hl
      (CCountConditions.or_eval_congr declarations objects env heap _ _ _ _ hr rfl))

/-- Complete optional body successor, with the existing count-first order,
arbitrary suffix and unchanged full locals/heap. -/
theorem count_guard_next (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (env : Locals) (heap : Heap)
    (pointerMissing : Expr → Expr) (left right leftCount rightCount message : String)
    (tail : List Stmt) (sizeType : interface.types "size_t" = some .size)
    (nInteger : CCountConditions.IntegerResult
      (evalWith declarations objects env heap (.id leftCount)))
    (mInteger : CCountConditions.IntegerResult
      (evalWith declarations objects env heap (.id rightCount))) :
    nextWith (declaredExpressions declarations objects)
      (.running (Runtime.arrayAccessGuardWithConditions CCountConditions.nonzero pointerMissing
        left right leftCount rightCount message :: tail) env heap) =
    nextWith (declaredExpressions declarations objects)
      (.running (Runtime.arrayAccessGuardWith pointerMissing
        left right leftCount rightCount message :: tail) env heap) := by
  have same := count_condition_eval declarations objects env heap pointerMissing
    left right leftCount rightCount sizeType nInteger mInteger
  simpa only [Runtime.arrayAccessGuardWithConditions, Runtime.arrayAccessGuardWith,
    id_eq, Runtime.reject, Runtime.branch, Runtime.v, nextWith, declaredExpressions] using
    congrArg (fun result : Option Value => do
      let takeYes ← (← result).truth
      return State.running ((if takeYes then [Runtime.fail message] else []) ++ tail) env heap) same

/-- Actual scalar-array guard; the old helper keeps its smaller interface domain. -/
theorem run_count_guard (env : Locals) (heap : Heap) (left right leftCount rightCount message : String)
    (lp rp : Option Address) (n m : UInt64) (tail : List Stmt)
    (leftBound : resolve env left = some (.pointer lp))
    (rightBound : resolve env right = some (.pointer rp))
    (nBound : resolve env leftCount = some (.integer n.toNat))
    (mBound : resolve env rightCount = some (.integer m.toNat))
    (nullType : interface.types "void *" = some .pointer)
    (sizeType : interface.types "size_t" = some .size) :
    run 1 (.running (countGuard left right leftCount rightCount message :: tail) env heap) =
      some (.running (if Valid lp rp n m then tail else Runtime.fail message :: tail) env heap) := by
  have step := count_guard_next (fun _ => none) (fun _ => none) env heap
    (fun p => Expr.bin .eq p Expr.nullPointer) left right leftCount rightCount message tail sizeType
    (Or.inr ⟨n.toNat, nBound⟩) (Or.inr ⟨m.toNat, mBound⟩)
  have same :
      run 1 (.running (countGuard left right leftCount rightCount message :: tail) env heap) =
      run 1 (.running (explicitGuard left right leftCount rightCount message :: tail) env heap) :=
    congrArg (fun result : Option State => result.bind (run 0)) step
  exact same.trans (run_explicit_guard env heap left right leftCount rightCount message
    lp rp n m tail leftBound rightBound nBound mBound nullType)

/-- Actual zero path: size typing is required for the new cast, but neither
pointer binding, null typing nor storage is required. -/
theorem run_count_guard_zero (env : Locals) (heap : Heap)
    (left right leftCount rightCount message : String) (tail : List Stmt)
    (nBound : resolve env leftCount = some (.integer 0))
    (mBound : resolve env rightCount = some (.integer 0))
    (sizeType : interface.types "size_t" = some .size) :
    run 1 (.running (countGuard left right leftCount rightCount message :: tail) env heap) =
      some (.running tail env heap) := by
  have step := count_guard_next (fun _ => none) (fun _ => none) env heap
    (fun p => Expr.bin .eq p Expr.nullPointer) left right leftCount rightCount message tail sizeType
    (Or.inr ⟨0, nBound⟩) (Or.inr ⟨0, mBound⟩)
  have same :
      run 1 (.running (countGuard left right leftCount rightCount message :: tail) env heap) =
      run 1 (.running (explicitGuard left right leftCount rightCount message :: tail) env heap) :=
    congrArg (fun result : Option State => result.bind (run 0)) step
  exact same.trans (run_explicit_guard_zero env heap left right leftCount rightCount message tail nBound mBound)

end Rumoca.FMI3.ArrayAccess
