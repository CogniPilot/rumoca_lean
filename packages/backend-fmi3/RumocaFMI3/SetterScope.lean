import RumocaCore.Transition.Prefix
import RumocaFMI3.BodyEmbedding

/-! Instance-declaration hoisting and the emitted Float64 setter's entry paths.
The algebraic law compares two statement prefixes with an arbitrary shared
continuation; only the hoisted form is emitted. It preserves all behaviors in
CCalls, including error and divergence, under represented entry bindings.
The emitted empty/null paths also terminate with unchanged memory in the typed
C machine. Public parameter binding, nonempty value-loop correctness, enabled
callbacks and printed adapter bytes remain separate obligations. -/
namespace Rumoca.FMI3.SetterScope
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def empty : Expr := Runtime.both
  (Runtime.eqv (Runtime.v "nValueReferences") (Runtime.n 0))
  (Runtime.eqv (Runtime.v "nValues") (Runtime.n 0))
def nested (tail : List Stmt) : List Stmt :=
  [Runtime.branch empty (Runtime.require .get ++ [Runtime.ok])] ++ Runtime.require .setStart ++ tail
def hoisted (tail : List Stmt) : List Stmt := Runtime.instancePrefix ++
  [Runtime.branch empty [Runtime.modeGuard .get, Runtime.ok], Runtime.modeGuard .setStart] ++ tail

theorem instance_run (env : Locals) (heap : Heap) (p : Address) (rest : List Stmt)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none) :
    run 2 (.running (Runtime.instancePrefix ++ rest) env heap) =
      some (.running rest (CBody.bind env "m" (.pointer (some p))) heap) := by
  simp [Runtime.instancePrefix, Runtime.branch, Runtime.v,
    run, next, eval, CBody.bind, resolve, constants, CBody.cast, convert,
    boolean, Value.truth, hi, hn]

theorem branch_run (env : Locals) (heap : Heap) (condition : Expr) (choice : Bool)
    (yes no rest : List Stmt) (h : eval env heap condition = some (boolean choice)) :
    run 1 (.running (Runtime.branch condition yes no :: rest) env heap) =
      some (.running ((if choice then yes else no) ++ rest) env heap) := by
  cases choice <;> simp [Runtime.branch, run, next, h, boolean, Value.truth]

theorem empty_eval (env : Locals) (heap : Heap) (refs values : Nat)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) :
    eval env heap empty = some (boolean (refs == 0 && values == 0)) := by
  have hcast (n : Nat) : ((n : Int) == 0) = (n == 0) := by
    apply Bool.eq_iff_iff.mpr
    simp
  have hl : eval env heap (Runtime.eqv (Runtime.v "nValueReferences") (Runtime.n 0)) =
      some (boolean (refs == 0)) := by
    simp [Runtime.eqv, Runtime.v, Runtime.n, eval, resolve, hr, comparison, hcast]
  have hh : eval env heap (Runtime.eqv (Runtime.v "nValues") (Runtime.n 0)) =
      some (boolean (values == 0)) := by
    simp [Runtime.eqv, Runtime.v, Runtime.n, eval, resolve, hv, comparison, hcast]
  exact BoolProofs.eval_and hl hh

theorem nested_nonempty_run (env : Locals) (heap : Heap) (p : Address) (refs values : Nat)
    (tail : List Stmt) (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : refs ≠ 0 ∨ values ≠ 0) :
    run 3 (.running (nested tail) env heap) =
      some (.running (Runtime.modeGuard .setStart :: tail) (CBody.bind env "m" (.pointer (some p))) heap) := by
  have hcond : eval env heap empty = some (boolean false) := by
    rw [empty_eval env heap refs values hr hv]
    rcases he with he | he <;> simp [beq_eq_false_iff_ne.mpr he]
  have hb := branch_run env heap empty false (Runtime.require .get ++ [Runtime.ok]) []
    (Runtime.require .setStart ++ tail) hcond
  rw [show 3 = 1 + 2 from rfl, run_add]
  change (run 1 (.running (Runtime.branch empty (Runtime.require .get ++ [Runtime.ok]) ::
    (Runtime.require .setStart ++ tail)) env heap)).bind (run 2) = _
  rw [hb]
  simpa [Runtime.require, Runtime.modeGuard, List.append_assoc] using
    instance_run env heap p (Runtime.modeGuard .setStart :: tail) hi hn

theorem hoisted_nonempty_run (env : Locals) (heap : Heap) (p : Address) (refs values : Nat)
    (tail : List Stmt) (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : refs ≠ 0 ∨ values ≠ 0) :
    run 3 (.running (hoisted tail) env heap) =
      some (.running (Runtime.modeGuard .setStart :: tail) (CBody.bind env "m" (.pointer (some p))) heap) := by
  have hcond : eval (CBody.bind env "m" (.pointer (some p))) heap empty = some (boolean false) := by
    rw [empty_eval _ heap refs values (by simpa [CBody.bind] using hr) (by simpa [CBody.bind] using hv)]
    rcases he with he | he <;> simp [beq_eq_false_iff_ne.mpr he]
  rw [show 3 = 2 + 1 from rfl, run_add]
  unfold hoisted
  rw [List.append_assoc, instance_run env heap p _ hi hn]
  simpa using branch_run (CBody.bind env "m" (.pointer (some p))) heap empty false
    [Runtime.modeGuard .get, Runtime.ok] [] (Runtime.modeGuard .setStart :: tail) hcond


theorem return_ok (env : Locals) (heap : Heap) (p : Option Address) (rest : List Stmt)
    (hok : env "fmi3OK" = none) :
    run 1 (.running (Runtime.ok :: rest) (CBody.bind env "m" (.pointer p)) heap) =
      some (.returned ⟨.integer 0, heap⟩) := by
  simp [run, next, Runtime.ok, Runtime.ret, Runtime.v, eval, CBody.bind, resolve, hok, constants]

theorem nested_empty_run (env : Locals) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (tail : List Stmt) (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer 0)) (hv : env "nValues" = some (.integer 0))
    (hok : env "fmi3OK" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    run 5 (.running (nested tail) env heap) = some (.returned ⟨.integer 0, heap⟩) := by
  have hcond : eval env heap empty = some (boolean true) := empty_eval env heap 0 0 hr hv
  have hb := branch_run env heap empty true (Runtime.require .get ++ [Runtime.ok]) []
    (Runtime.require .setStart ++ tail) hcond
  have hp := LifecycleGuard.accept env heap p .get kind mode
    (Runtime.ok :: (Runtime.require .setStart ++ tail)) hi hn hk hm trivial
  have h4 : run 4 (.running (nested tail) env heap) =
      some (.running (Runtime.ok :: (Runtime.require .setStart ++ tail))
        (CBody.bind env "m" (.pointer (some p))) heap) := by
    rw [show 4 = 1 + 3 from rfl, run_add]
    change (run 1 (.running (Runtime.branch empty (Runtime.require .get ++ [Runtime.ok]) ::
      (Runtime.require .setStart ++ tail)) env heap)).bind (run 3) = _
    rw [hb]
    simpa [List.append_assoc] using hp
  rw [show 5 = 4 + 1 from rfl, run_add, h4]
  exact return_ok env heap (some p) _ hok

theorem hoisted_empty_run (env : Locals) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (tail : List Stmt) (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer 0)) (hv : env "nValues" = some (.integer 0))
    (hok : env "fmi3OK" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    run 5 (.running (hoisted tail) env heap) = some (.returned ⟨.integer 0, heap⟩) := by
  have hcond : eval (CBody.bind env "m" (.pointer (some p))) heap empty = some (boolean true) :=
    empty_eval _ heap 0 0 (by simpa [CBody.bind] using hr) (by simpa [CBody.bind] using hv)
  have hb := branch_run (CBody.bind env "m" (.pointer (some p))) heap empty true
    [Runtime.modeGuard .get, Runtime.ok] [] (Runtime.modeGuard .setStart :: tail) hcond
  have h3 : run 3 (.running (hoisted tail) env heap) =
      some (.running (Runtime.modeGuard .get :: Runtime.ok :: Runtime.modeGuard .setStart :: tail)
        (CBody.bind env "m" (.pointer (some p))) heap) := by
    rw [show 3 = 2 + 1 from rfl, run_add]
    unfold hoisted
    rw [List.append_assoc, instance_run env heap p _ hi hn]
    exact hb
  have hg := LifecycleGuard.eval_correct (CBody.bind env "m" (.pointer (some p))) heap p .get kind mode
    (by simp [CBody.bind, resolve]) hk hm
  have ha : allowed .get kind mode = true := (allowed_correct .get kind mode).mpr trivial
  rw [ha] at hg
  rw [show 5 = 3 + 2 from rfl, run_add, h3]
  simpa [run, next, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.negate, eval,
    hg, boolean, Value.truth] using return_ok env heap (some p) (Runtime.modeGuard .setStart :: tail) hok

theorem instance_null_run (env : Locals) (heap : Heap) (rest : List Stmt)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (he : env "fmi3Error" = none) :
    run 3 (.running (Runtime.instancePrefix ++ rest) env heap) =
      some (.returned ⟨.integer 3, heap⟩) := by
  simp [Runtime.instancePrefix, Runtime.branch, Runtime.v, Runtime.ret,
    run, next, eval, CBody.bind, resolve, constants, CBody.cast, convert,
    boolean, Value.truth, hi, hn, he]

theorem nested_null_run (env : Locals) (heap : Heap) (refs values : Nat) (tail : List Stmt)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : env "fmi3Error" = none) :
    run 4 (.running (nested tail) env heap) = some (.returned ⟨.integer 3, heap⟩) := by
  have hb := branch_run env heap empty (refs == 0 && values == 0) (Runtime.require .get ++ [Runtime.ok]) []
    (Runtime.require .setStart ++ tail) (empty_eval env heap refs values hr hv)
  rw [show 4 = 1 + 3 from rfl, run_add]
  change (run 1 (.running (Runtime.branch empty (Runtime.require .get ++ [Runtime.ok]) ::
    (Runtime.require .setStart ++ tail)) env heap)).bind (run 3) = _
  rw [hb]
  cases hc : refs == 0 && values == 0 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append,
      Option.bind_some, Runtime.require, List.append_assoc]
  · exact instance_null_run env heap _ hi hn he
  · exact instance_null_run env heap _ hi hn he

theorem hoisted_null_run (env : Locals) (heap : Heap) (tail : List Stmt)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (he : env "fmi3Error" = none) :
    run 3 (.running (hoisted tail) env heap) = some (.returned ⟨.integer 3, heap⟩) := by
  simpa [hoisted, List.append_assoc] using instance_null_run env heap
    ([Runtime.branch empty [Runtime.modeGuard .get, Runtime.ok], Runtime.modeGuard .setStart] ++ tail) hi hn he



noncomputable section
theorem nonnull_equivalent (program : CCalls.Program) (env : Locals) (heap : Heap)
    (p : Address) (kind : Kind) (mode : Mode) (refs values : Nat) (tail : List Stmt)
    (resultType : String) (stack : CCalls.Continuation) (behavior)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (hok : env "fmi3OK" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    (CCalls.machine program).Behaves (.body (.running (nested tail) env heap) resultType stack) behavior ↔
    (CCalls.machine program).Behaves (.body (.running (hoisted tail) env heap) resultType stack) behavior := by
  by_cases counts : refs = 0 ∧ values = 0
  · obtain ⟨rfl, rfl⟩ := counts
    have hb := CCalls.body_reaches program
      (run_reaches (nested_empty_run env heap p kind mode tail hi hn hr hv hok hk hm)) resultType stack
    have ha := CCalls.body_reaches program
      (run_reaches (hoisted_empty_run env heap p kind mode tail hi hn hr hv hok hk hm)) resultType stack
    exact (Transition.Machine.prefix_behaviors (CCalls.machine program) hb).trans
      (Transition.Machine.prefix_behaviors (CCalls.machine program) ha).symm
  · have hnz : refs ≠ 0 ∨ values ≠ 0 := by omega
    have hb := CCalls.body_reaches program
      (run_reaches (nested_nonempty_run env heap p refs values tail hi hn hr hv hnz)) resultType stack
    have ha := CCalls.body_reaches program
      (run_reaches (hoisted_nonempty_run env heap p refs values tail hi hn hr hv hnz)) resultType stack
    exact (Transition.Machine.prefix_behaviors (CCalls.machine program) hb).trans
      (Transition.Machine.prefix_behaviors (CCalls.machine program) ha).symm

theorem null_equivalent (program : CCalls.Program) (env : Locals) (heap : Heap)
    (refs values : Nat) (tail : List Stmt) (resultType : String) (stack : CCalls.Continuation) (behavior)
    (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : env "fmi3Error" = none) :
    (CCalls.machine program).Behaves (.body (.running (nested tail) env heap) resultType stack) behavior ↔
    (CCalls.machine program).Behaves (.body (.running (hoisted tail) env heap) resultType stack) behavior := by
  have hb := CCalls.body_reaches program
    (run_reaches (nested_null_run env heap refs values tail hi hn hr hv he)) resultType stack
  have ha := CCalls.body_reaches program
    (run_reaches (hoisted_null_run env heap tail hi hn he)) resultType stack
  exact (Transition.Machine.prefix_behaviors (CCalls.machine program) hb).trans
    (Transition.Machine.prefix_behaviors (CCalls.machine program) ha).symm
end
omit static in
/-- The actual setter is the hoisted form of the unchanged value operations. -/
theorem emitted : Runtime.setFloat64 = hoisted Runtime.setFloat64Values := rfl

omit static in
/-- The emitted setter satisfies the existing scope check. -/
theorem closed :
    Runtime.setFloat64.all CBodyEmbedding.closedBlocks = true := by
  simp [Runtime.setFloat64, Runtime.setFloat64Values, Runtime.instancePrefix, Runtime.countLoop,
    CBodyEmbedding.closedBlocks, CLoops.noDeclarations, Runtime.branch, Runtime.reject,
    Runtime.ret, Runtime.ok, Runtime.fail, Runtime.modeGuard]

/-- Nonempty calls reach their value operations or their emitted lifecycle
failure call, preserving the heap before any output access. -/
theorem entry_run (env : Locals) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (refs values : Nat) (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : refs ≠ 0 ∨ values ≠ 0)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    run 4 (.running Runtime.setFloat64 env heap) =
      some (.running ((if allowed .setStart kind mode then [] else
        [Runtime.fail "Call is not allowed in the current FMI state"]) ++ Runtime.setFloat64Values)
        (CBody.bind env "m" (.pointer (some p))) heap) := by
  have hp := hoisted_nonempty_run env heap p refs values Runtime.setFloat64Values hi hn hr hv he
  have hg := LifecycleGuard.eval_correct (CBody.bind env "m" (.pointer (some p))) heap p .setStart kind mode
    (by simp [CBody.bind, resolve]) hk hm
  rw [show 4 = 3 + 1 from rfl, run_add, emitted, hp]
  cases ha : allowed .setStart kind mode <;>
    simp [run, next, Runtime.reject, Runtime.branch, Runtime.negate, eval, hg, ha, boolean, Value.truth]

noncomputable section

/-- The same nonempty entry path in the typed target, retaining the caller's
continuation. This stops before value validation/writes or the failure helper. -/
theorem entry_reaches (program : CCalls.Program) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (refs values : Nat)
    (stack : CCalls.Typed.Continuation)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer refs))
    (hv : env "nValues" = some (.integer values)) (he : refs ≠ 0 ∨ values ≠ 0)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    ∃ types', Transition.Reaches (CCalls.Typed.machine program).step
      (.body (.running Runtime.setFloat64 env types heap) "fmi3Status" stack)
      (.body (.running ((if allowed .setStart kind mode then [] else
        [Runtime.fail "Call is not allowed in the current FMI state"]) ++ Runtime.setFloat64Values)
        (CBody.bind env "m" (.pointer (some p))) types' heap) "fmi3Status" stack) := by
  obtain ⟨types', execution, _⟩ := CBodyEmbedding.run_refines 4
    (.running Runtime.setFloat64 env heap) _ types closed
    (entry_run env heap p kind mode refs values hi hn hr hv he hk hm)
  exact ⟨types', CCalls.Typed.body_reaches program (CLoops.run_reaches execution) "fmi3Status" stack⟩

theorem empty_behaviors (program : CCalls.Program) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hi : env "instance" = some (.pointer (some p))) (hn : env "m" = none)
    (hr : env "nValueReferences" = some (.integer 0)) (hv : env "nValues" = some (.integer 0))
    (hok : env "fmi3OK" = none)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.body (.running Runtime.setFloat64 env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates ⟨.integer 0, heap⟩ :=
  CBodyEmbedding.typed_body_behaviors program
    (.running Runtime.setFloat64 env heap) types ⟨.integer 0, heap⟩ "fmi3Status" (.integer 0) 5
    closed (hoisted_empty_run env heap p kind mode _ hi hn hr hv hok hk hm)
    (by simp [CCalls.returnCast, CBody.cast, convert]) behavior

theorem null_behaviors (program : CCalls.Program) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (hi : env "instance" = some (.pointer none)) (hn : env "m" = none)
    (he : env "fmi3Error" = none) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.body (.running Runtime.setFloat64 env types heap) "fmi3Status" .done) behavior ↔
      behavior = .terminates ⟨.integer 3, heap⟩ :=
  CBodyEmbedding.typed_body_behaviors program
    (.running Runtime.setFloat64 env heap) types ⟨.integer 3, heap⟩ "fmi3Status" (.integer 3) 3
    closed (hoisted_null_run env heap _ hi hn he)
    (by simp [CCalls.returnCast, CBody.cast, convert]) behavior

end
end Rumoca.FMI3.SetterScope
