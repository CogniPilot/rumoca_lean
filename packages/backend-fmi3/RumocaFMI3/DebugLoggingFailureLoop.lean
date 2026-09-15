import RumocaFMI3.DebugLoggingRejections

noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops CStringMemory

/-- Finite-domain classification is independent of the C implementation. -/
theorem category_cases (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (expected : List UInt8) (n : Nat) :
    (∀ i < n, Accepted (selected i) (bytes i) expected) ∨
    ∃ bad, bad < n ∧ ¬ Accepted (selected bad) (bytes bad) expected ∧
      ∀ i < bad, Accepted (selected i) (bytes i) expected := by
  classical
  by_cases valid : ∀ i < n, Accepted (selected i) (bytes i) expected
  · exact Or.inl valid
  · have existsBad : ∃ i, i < n ∧ ¬ Accepted (selected i) (bytes i) expected := by simpa using valid
    refine Or.inr ⟨Nat.find existsBad, (Nat.find_spec existsBad).1, (Nat.find_spec existsBad).2, ?_⟩
    intro i before
    have smaller := Nat.find_min existsBad before
    have inside : i < n := lt_trans before (Nat.find_spec existsBad).1
    exact Classical.byContradiction (fun bad => smaller ⟨inside, bad⟩)

variable [interface : CInterface]

theorem validation_rejected_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (pointer : Option Address)
    (n bad : Nat) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (p expected : Address) (expectedBytes : List UInt8) (rest : List Stmt)
    (inside : bad < n) (bounded : n < 2^64)
    (counterType : types "k" = some .size)
    (count : env "nCategories" = some (.integer n))
    (array : env "categories" = some (.pointer pointer))
    (old : env "difference" = some (.integer 0))
    (differenceType : types "difference" = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (pointerType : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (bound : program.externals "strcmp" = some (CStringCalls.compareExternal integer))
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer n selected bytes)
    (prior : ∀ i < bad, Accepted (selected i) (bytes i) expectedBytes)
    (invalid : ¬ Accepted (selected bad) (bytes bad) expectedBytes)
    (failureName : env "fail" = none)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (outcomes : Transition.Events.Observation E CBody.Result → Prop)
    (failed : FailureContract program heap p "Unknown log category" outcomes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (validation :: rest) (counterEnv env "k" 0) types heap) "fmi3Status" .done) behavior ↔
    outcomes behavior := by
  apply (validation_prefix_equivalence program env types heap pointer n bad selected bytes expected
    expectedBytes rest "fmi3Status" .done (by omega) bounded counterType count array old differenceType
    unshadowed named pointerType integer bound literal expectedStored entries prior behavior).trans
  have entered := CLoops.loop_enter (counterEnv env "k" bad) types heap "k" (.id "nCategories")
    iteration rest bad n (by simp [counterEnv, CBody.bind])
    (by simp [CBody.eval, counterEnv, CBody.bind, resolve, count]) iteration_closed inside
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program entered "fmi3Status" .done) (.refl _)) behavior).trans
  obtain ⟨base, _, _, stored⟩ := entries bad inside
  exact iteration_invalid_behaviors program (counterEnv env "k" bad) types heap p expected (selected bad)
    (bytes bad) expectedBytes (.integer 0) (counterStep "k" :: validation :: rest)
    pointerType integer (by simp [counterEnv, CBody.bind, old]) differenceType
    (by simp [counterEnv, CBody.bind, unshadowed]) named bound
    (entry_eval env heap pointer n bad selected bytes entries inside array) literal stored expectedStored
    invalid (by simp [counterEnv, CBody.bind, failureName])
    (by simpa [counterEnv, CBody.bind, resolve] using instanceBound) outcomes failed behavior

end Rumoca.FMI3.DebugLogging
end
