import RumocaFMI3.DerivativeFailures

noncomputable section
namespace Rumoca.FMI3.EventIndicatorCalls
open CTree CMemory CBody

def signature : Signature :=
  ⟨"fmi3Status", "fmi3GetEventIndicators",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"fmi3Float64", "eventIndicators", true⟩,
     ⟨"size_t", "nEventIndicators", false⟩]⟩

def values (handle buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer handle, .pointer buffer, .integer count.toNat]

def parameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (fun _ => none) "nEventIndicators" (.integer count.toNat))
    "eventIndicators" (.pointer buffer)) "instance" (.pointer handle)

def locals (p : Address) (buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (parameters (some p) buffer count) "m" (.pointer (some p))

def tail : List Stmt :=
  [Runtime.reject (Runtime.nev (Runtime.v "nEventIndicators") (Runtime.n 0)) "There are no event indicators",
   Runtime.ok]

theorem body_eq (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .getDerivatives ++ tail := rfl

/-- The zero-length output has no element storage obligation. Rejected
counts and lifecycle states are classified before any potential output use. -/
def FailureCondition (access : Bool) (kind : Kind) (mode : Mode) (count : UInt64) : Prop :=
  if access then Reference.Allowed .getDerivatives kind mode ∧ count.toNat ≠ 0
  else ¬ Reference.Allowed .getDerivatives kind mode

def failureMessage (access : Bool) : String :=
  if access then "There are no event indicators" else ErrorCalls.rejectionMessage

theorem query_cases (kind : Kind) (mode : Mode) (handle : Option Address) (count : UInt64) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((count = 0 ∧ Reference.Allowed .getDerivatives kind mode) ∨
       ∃ access, FailureCondition access kind mode count) := by
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
    refine Or.inr ⟨p, rfl, ?_⟩
    by_cases allowed : Reference.Allowed .getDerivatives kind mode
    · by_cases size : count.toNat = 0
      · exact Or.inl ⟨UInt64.toNat_inj.mp size, allowed⟩
      · exact Or.inr ⟨true, allowed, size⟩
    · exact Or.inr ⟨false, allowed⟩

theorem failure_unique (first : FailureCondition a kind mode count)
    (second : FailureCondition b kind mode count) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters signature.parameters (values handle buffer count) = some (parameters handle buffer count) := by
  have converted : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ (by rfl) (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [signature, values, CCalls.parameters, CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, converted]
  rfl

theorem accepted_run (model : Solve.FMI3Model source) (heap : Heap) (p : Address)
    (buffer : Option Address) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode) :
    run 4 (.running (Runtime.body model signature) (parameters (some p) buffer 0) heap) =
      some (.running [Runtime.ok] (locals p buffer 0) heap) := by
  have guard := LifecycleGuard.accept (parameters (some p) buffer 0) heap p .getDerivatives .me mode tail
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, guard]
  simp [tail, locals, parameters, Runtime.reject, Runtime.branch, Runtime.nev, Runtime.v, Runtime.n,
    run, next, eval, resolve, CBody.bind, comparison, boolean, Value.truth]

theorem reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (buffer : Option Address) (mode : Mode)
    (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling signature.name (values (some p) buffer 0) heap stack)
      (.returning (.integer 0) heap stack) := by
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model signature)
    (values (some p) buffer 0) (parameters (some p) buffer 0) (locals p buffer 0)
    heap heap [Runtime.ok] stack 4 defined (parameters_bound _ _ _) (BodyEmbedding.body_closed model signature)
    (accepted_run model heap p buffer mode hk hm allowed)
  exact entered.trans (DerivativeCalls.finish program heap (locals p buffer 0) types stack
    (by simp [locals, parameters, CBody.bind]))

/-- Every actual successful call leaves the entire heap unchanged, with no
event or output access, including when the zero-length output pointer is null. -/
theorem behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (buffer : Option Address) (mode : Mode)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling signature.name (values (some p) buffer 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩ :=
  (CCalls.Events.internal_prefix program (reaches model program heap p buffer mode .done defined hk hm allowed)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

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
    (allowed : Reference.Allowed .getDerivatives kind mode) (invalid : count.toNat ≠ 0) :
    run 4 (.running (Runtime.body model signature) (parameters (some p) buffer count) heap) =
      some (.running [Runtime.fail "There are no event indicators", Runtime.ok] (locals p buffer count) heap) := by
  have accepted := LifecycleGuard.accept (parameters (some p) buffer count) heap p .getDerivatives kind mode tail
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, accepted]
  simp [tail, locals, parameters, Runtime.reject, Runtime.branch, Runtime.nev, Runtime.v, Runtime.n,
    run, next, eval, resolve, CBody.bind, comparison, boolean, Value.truth, invalid]

theorem failure_prefix (model : Solve.FMI3Model source) (access : Bool) (heap : Heap) (p : Address)
    (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (failure : FailureCondition access kind mode count) :
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
      locals p buffer count, [Runtime.ok], 4, parameters_bound _ _ _,
      invalid_run model heap p buffer count kind mode hk hm failure.1 failure.2, ?_, ?_⟩
    · simp [locals, parameters, CBody.bind]
    · simp [locals, CBody.bind, resolve]

end
end Rumoca.FMI3.EventIndicatorCalls
end
