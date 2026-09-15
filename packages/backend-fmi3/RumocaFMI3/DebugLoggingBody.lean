import RumocaFMI3.DebugLoggingExecution

/-! Complete behavior of the logging body after the shared instance guard.
Argument bindings and the actual string-library environment are kept separate
from original caller memory and the shared error-helper contract. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CTree CMemory CBody CLoops CStringMemory
open scoped Classical

structure Scope (env : Locals) (p : Address) (pointer : Option Address) (n : Nat) (enabled : Bool) : Prop where
  count : env "nCategories" = some (.integer n)
  array : env "categories" = some (.pointer pointer)
  handle : env "m" = some (.pointer (some p))
  flag : env "loggingOn" = some (boolean enabled)
  differenceFresh : env "difference" = none
  counterFresh : env "k" = none
  compareName : env "strcmp" = none
  failureName : env "fail" = none
  okName : env "fmi3OK" = none

variable [interface : CInterface]

structure Library (program : CCalls.Events.Program E) : Prop where
  pointer : interface.types "const char *" = some .pointer
  integer : interface.types "int" = some .int32
  size : interface.types "size_t" = some .size
  compareName : interface.constants "strcmp" = none
  compareBinding : program.externals "strcmp" = some (CStringCalls.compareExternal integer)
  ok : interface.constants "fmi3OK" = some (.integer 0)
  status : CCalls.returnCast "fmi3Status" (.integer 0) = some (.integer 0)

theorem prepare_code (program : CCalls.Events.Program E) (library : Library program)
    (env : Locals) (types : Types) (heap : Heap) (p : Address) (pointer : Option Address)
    (n : Nat) (enabled : Bool) (scope : Scope env p pointer n enabled)
    (readable : n = 0 ∨ pointer.isSome = true) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running code env types heap) "fmi3Status" .done)
      (.body (.running (validation :: finish) (working env 0) (workingTypes types) heap) "fmi3Status" .done) := by
  have first := missing_step env types heap pointer n
    (.declare "int" "difference" (.nat 0) :: .declare "size_t" "k" (.nat 0) :: validation :: finish)
    scope.count scope.array
  rw [if_pos readable] at first
  exact .next (CCalls.Events.body_step program first "fmi3Status" .done)
    (declarations_reaches program env types heap (validation :: finish) "fmi3Status" .done
      scope.differenceFresh scope.counterFresh library.integer library.size)

omit interface in
theorem Entries.readable (entries : Entries heap pointer n selected bytes) :
    n = 0 ∨ pointer.isSome = true := by
  by_cases zero : n = 0
  · exact Or.inl zero
  · obtain ⟨base, same, _, _⟩ := entries 0 (by omega)
    exact Or.inr (same ▸ rfl)

theorem code_success_behaviors (program : CCalls.Events.Program E) (library : Library program)
    (env : Locals) (types : Types) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (n : Nat) (enabled : Bool) (old : Option Value) (scope : Scope env p pointer n enabled)
    (bounded : n < 2^64) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer n selected bytes)
    (valid : ∀ i < n, Accepted (selected i) (bytes i) expectedBytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running code env types heap) "fmi3Status" .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩ := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (prepare_code program library env types heap p pointer n enabled scope entries.readable) behavior).trans
  apply (validation_valid_equivalence program (CBody.bind env "difference" (.integer 0))
    (workingTypes types) heap pointer n selected bytes expected expectedBytes finish "fmi3Status" .done
    bounded (by simp [workingTypes, bindType])
    (by simp [CBody.bind, scope.count]) (by simp [CBody.bind, scope.array])
    (by simp [CBody.bind]) (by simp [workingTypes, bindType])
    (by simp [CBody.bind, scope.compareName]) library.compareName library.pointer library.integer
    library.compareBinding literal expectedStored entries valid behavior).trans
  exact (CCalls.Events.internal_prefix program
    (finish_reaches program (working env n) (workingTypes types) heap p enabled old .done
      (by simp [working, counterEnv, CBody.bind, scope.handle])
      (by simp [working, counterEnv, CBody.bind, scope.flag])
      (by simp [working, counterEnv, resolve, CBody.bind, scope.okName, constants, library.ok])
      library.status storage)
    (CCalls.Events.return_forced program (.integer 0) (written heap p enabled))).behaviors behavior

theorem code_unknown_behaviors (program : CCalls.Events.Program E) (library : Library program)
    (env : Locals) (types : Types) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (n bad : Nat) (enabled : Bool) (scope : Scope env p pointer n enabled)
    (inside : bad < n) (bounded : n < 2^64)
    (selected : Nat → Option Address) (bytes : Nat → List UInt8) (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (entries : Entries heap pointer n selected bytes)
    (prior : ∀ i < bad, Accepted (selected i) (bytes i) expectedBytes)
    (invalid : ¬ Accepted (selected bad) (bytes bad) expectedBytes)
    (outcomes : Transition.Events.Observation E CBody.Result → Prop)
    (failed : FailureContract program heap p "Unknown log category" outcomes) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running code env types heap) "fmi3Status" .done) behavior ↔ outcomes behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (prepare_code program library env types heap p pointer n enabled scope entries.readable) behavior).trans
  exact validation_rejected_behaviors program (CBody.bind env "difference" (.integer 0))
    (workingTypes types) heap pointer n bad selected bytes p expected expectedBytes finish inside
    bounded (by simp [workingTypes, bindType])
    (by simp [CBody.bind, scope.count]) (by simp [CBody.bind, scope.array])
    (by simp [CBody.bind]) (by simp [workingTypes, bindType])
    (by simp [CBody.bind, scope.compareName]) library.compareName library.pointer library.integer
    library.compareBinding literal expectedStored entries prior invalid
    (by simp [CBody.bind, scope.failureName]) (by simp [resolve, CBody.bind, scope.handle]) outcomes failed behavior

theorem code_missing_behaviors (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (p : Address) (n : Nat)
    (enabled : Bool) (scope : Scope env p none n enabled) (positive : 0 < n)
    (outcomes : Transition.Events.Observation E CBody.Result → Prop)
    (failed : FailureContract program heap p "Missing log categories" outcomes) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running code env types heap) "fmi3Status" .done) behavior ↔ outcomes behavior := by
  have first := missing_step env types heap none n
    (.declare "int" "difference" (.nat 0) :: .declare "size_t" "k" (.nat 0) :: validation :: finish)
    scope.count scope.array
  rw [if_neg (by simp; omega)] at first
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program first "fmi3Status" .done) (.refl _)) behavior).trans
  exact failed.body env types _ scope.failureName (by simp [resolve, scope.handle]) behavior

/-- One statement covers every represented category request. A nonnull caller
array supplies readable cells and strings; no memory premise is imposed on a
missing array. The error outcomes are supplied by the proved shared helper,
and a successful write follows only after the whole selection is accepted. -/
theorem code_behaviors (program : CCalls.Events.Program E) (library : Library program)
    (env : Locals) (types : Types) (heap : Heap) (p expected : Address) (pointer : Option Address)
    (n : Nat) (enabled : Bool) (old : Option Value) (scope : Scope env p pointer n enabled)
    (bounded : n < 2^64) (selected : Nat → Option Address) (bytes : Nat → List UInt8)
    (expectedBytes : List UInt8)
    (literal : interface.literals "logStatus" = some expected)
    (expectedStored : Contents heap expected expectedBytes)
    (caller : pointer.isSome = true → Entries heap pointer n selected bytes)
    (storage : heap (p.member "logging") = some ⟨.boolean, true, old⟩)
    (missingOutcomes unknownOutcomes : Transition.Events.Observation E CBody.Result → Prop)
    (missingContract : FailureContract program heap p "Missing log categories" missingOutcomes)
    (unknownContract : FailureContract program heap p "Unknown log category" unknownOutcomes)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running code env types heap) "fmi3Status" .done) behavior ↔
    (if n = 0 ∨ pointer.isSome = true then
      if ∀ i < n, Accepted (selected i) (bytes i) expectedBytes then
        behavior = .terminates [] ⟨.integer 0, written heap p enabled⟩
      else unknownOutcomes behavior
     else missingOutcomes behavior) := by
  classical
  by_cases readable : n = 0 ∨ pointer.isSome = true
  · rw [if_pos readable]
    have entries : Entries heap pointer n selected bytes := by
      rcases readable with zero | somePointer
      · intro i inside
        omega
      · exact caller somePointer
    rcases category_cases selected bytes expectedBytes n with valid | ⟨bad, inside, invalid, prior⟩
    · rw [if_pos valid]
      exact code_success_behaviors program library env types heap p expected pointer n enabled old scope
        bounded selected bytes expectedBytes literal expectedStored entries valid storage behavior
    · have notAll : ¬ ∀ i < n, Accepted (selected i) (bytes i) expectedBytes :=
        fun all => invalid (all bad inside)
      rw [if_neg notAll]
      exact code_unknown_behaviors program library env types heap p expected pointer n bad enabled scope
        inside bounded selected bytes expectedBytes literal expectedStored entries prior invalid
        unknownOutcomes unknownContract behavior
  · rw [if_neg readable]
    have absent : pointer = none := by cases pointer <;> simp_all
    have positive : 0 < n := by omega
    subst pointer
    exact code_missing_behaviors program env types heap p n enabled scope positive
      missingOutcomes missingContract behavior

end Rumoca.FMI3.DebugLogging
end
