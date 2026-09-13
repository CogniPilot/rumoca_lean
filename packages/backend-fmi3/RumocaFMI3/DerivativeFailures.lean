import RumocaFMI3.DerivativeCalls

noncomputable section
namespace Rumoca.FMI3.DerivativeCalls
open CTree CMemory CBody

def FailureCondition (access : Bool) (kind : Kind) (mode : Mode) (buffer : Option Address) (count : UInt64) : Prop :=
  if access then Reference.Allowed .getDerivatives kind mode ∧ (count.toNat ≠ 1 ∨ buffer = none)
  else ¬ Reference.Allowed .getDerivatives kind mode

def failureMessage (access : Bool) : String :=
  if access then "Expected one continuous state" else ErrorCalls.rejectionMessage

theorem query_cases (kind : Kind) (mode : Mode) (handle buffer : Option Address) (count : UInt64) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((∃ address, buffer = some address ∧ count = 1 ∧ Reference.Allowed .getDerivatives kind mode) ∨
       ∃ access, FailureCondition access kind mode buffer count) := by
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases allowed : Reference.Allowed .getDerivatives kind mode
      · by_cases size : count.toNat = 1
        · have one : count = 1 := UInt64.toNat_inj.mp size
          cases buffer with
          | none => exact Or.inr ⟨true, allowed, Or.inr rfl⟩
          | some address => exact Or.inl ⟨address, rfl, one, allowed⟩
        · exact Or.inr ⟨true, allowed, Or.inl size⟩
      · exact Or.inr ⟨false, allowed⟩

theorem failure_unique (first : FailureCondition a kind mode buffer count)
    (second : FailureCondition b kind mode buffer count) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem null_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (behavior) :
    (CCalls.Events.machine program).Behaves (.calling signature.name (values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (Runtime.function model signature)
    ([Runtime.reject (Runtime.negate (Runtime.allowedExpression .getDerivatives)) ErrorCalls.rejectionMessage] ++ tail)
    (values none buffer count) (parameters none buffer count) heap defined (parameters_bound _ _ _)
    (by rfl) rfl (BodyEmbedding.body_closed model signature)
  all_goals simp [parameters, CBody.bind]

theorem invalid_run (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (invalid : count.toNat ≠ 1 ∨ buffer = none) :
    run 4 (.running (Runtime.body model signature) (parameters (some p) buffer count) heap) =
      some (.running (Runtime.fail "Expected one continuous state" :: action) (locals p buffer count) heap) := by
  have accepted := LifecycleGuard.accept (parameters (some p) buffer count) heap p .getDerivatives
    kind mode tail (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, accepted]
  exact ScalarAccess.invalid_run _ heap "derivatives" "nContinuousStates" buffer count action
    (by simp [parameters, CBody.bind, resolve]) (by simp [parameters, CBody.bind, resolve]) invalid

/-- Each independently classified error reaches the real failure helper before
any caller output access or numerical evaluation. -/
theorem failure_prefix (model : Solve.FMI3Model source) (access : Bool) (heap : Heap) (p : Address)
    (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (failure : FailureCondition access kind mode buffer count) :
    GuardedCalls.FailurePrefix (Runtime.function model signature) (values (some p) buffer count)
      heap p (failureMessage access) heap := by
  cases access with
  | false =>
      have rejected := LifecycleGuard.reject_prefix (parameters (some p) buffer count) heap p .getDerivatives
        kind mode tail (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm failure
      rw [← body_eq model] at rejected
      refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p) buffer count,
        locals p buffer count, tail, 3, parameters_bound _ _ _, rejected, ?_, ?_⟩
      · simp [locals, parameters, CBody.bind]
      · simp [locals, CBody.bind, resolve]
  | true =>
      refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p) buffer count,
        locals p buffer count, action, 4, parameters_bound _ _ _,
        invalid_run model heap p buffer count kind mode hk hm failure.1 failure.2, ?_, ?_⟩
      · simp [locals, parameters, CBody.bind]
      · simp [locals, CBody.bind, resolve]

end
end Rumoca.FMI3.DerivativeCalls
