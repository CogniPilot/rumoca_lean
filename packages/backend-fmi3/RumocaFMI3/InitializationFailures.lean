import RumocaFMI3.InitializationCalls
import RumocaFMI3.GuardedCalls

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory CBody

def Admitted (args : Raw) : Prop :=
  ∃ finite : Initialization.Arguments, args = Raw.ofFinite finite ∧ Arguments.Admissible finite

inductive Failure where | lifecycle | arguments
  deriving DecidableEq

def failureMessage : Failure → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .arguments => message

def FailureCondition (reason : Failure) (mode : Mode) (args : Raw) : Prop :=
  match reason with
  | .lifecycle => mode ≠ .instantiated
  | .arguments => mode = .instantiated ∧ ¬ Admitted args

theorem query_cases (handle : Option Address) (mode : Mode) (args : Raw) :
    handle = none ∨ ∃ p, handle = some p ∧
      ((mode = .instantiated ∧ Admitted args) ∨ ∃ reason, FailureCondition reason mode args) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      by_cases state : mode = .instantiated
      · by_cases admissible : Admitted args
        · exact Or.inl ⟨state, admissible⟩
        · exact Or.inr ⟨.arguments, state, admissible⟩
      · exact Or.inr ⟨.lifecycle, state⟩

theorem failure_unique (first : FailureCondition a mode args)
    (second : FailureCondition b mode args) : a = b := by
  cases a <;> cases b <;> simp_all [FailureCondition]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem null_behaviors (program : CCalls.Events.Program E) (heap : Heap) (args : Raw)
    (defined : program.internal.definitions signature.name = some (.tree function)) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling signature.name (arguments none args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program function
    (Runtime.modeGuard .enterInitialization :: Runtime.reject guard message :: tail)
    (arguments none args) (parameters none args) heap defined (parameters_bound _ _)
  · simp only [function, code, Runtime.require, List.append_assoc,
      List.cons_append, List.nil_append]
  · rfl
  · exact closed
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]

theorem lifecycle_prefix (heap : Heap) (p : Address) (args : Raw) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : mode ≠ .instantiated) :
    GuardedCalls.FailurePrefix function (arguments (some p) args) heap p ErrorCalls.rejectionMessage heap := by
  have reached := LifecycleGuard.reject_prefix (parameters (some p) args) heap p .enterInitialization kind mode
    (Runtime.reject guard message :: tail) (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind]) hk hm denied
  refine ⟨rfl, closed, parameters (some p) args, locals p args,
    Runtime.reject guard message :: tail, 3, parameters_bound _ _, ?_, ?_, ?_⟩
  · simpa only [function, code, List.append_assoc, List.singleton_append, locals] using reached
  · simp [locals, parameters, CBody.bind]
  · simp [locals, CBody.bind, resolve]

theorem arguments_prefix (heap : Heap) (p : Address) (args : Raw) (kind : Kind)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer 0)) (invalid : ¬ Admitted args) :
    GuardedCalls.FailurePrefix function (arguments (some p) args) heap p message heap := by
  have rejected : rejects args = true := by
    cases h : rejects args with
    | false => exact False.elim (invalid ((rejects_iff args).mp h))
    | true => rfl
  have reached := guard_run heap p args kind hk hm
  rw [rejected] at reached
  refine ⟨rfl, closed, parameters (some p) args, locals p args,
    tail, 4, parameters_bound _ _, ?_, ?_, ?_⟩
  · simpa only [function, ↓reduceIte, List.singleton_append] using reached
  · simp [locals, parameters, CBody.bind]
  · simp [locals, CBody.bind, resolve]

theorem failure_prefix (heap : Heap) (p : Address) (args : Raw) (kind : Kind) (mode : Mode) (reason : Failure)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (condition : FailureCondition reason mode args) :
    GuardedCalls.FailurePrefix function (arguments (some p) args) heap p (failureMessage reason) heap := by
  cases reason with
  | lifecycle => exact lifecycle_prefix heap p args kind mode hk hm condition
  | arguments =>
      obtain ⟨rfl, invalid⟩ := condition
      exact arguments_prefix heap p args kind hk hm invalid

end
end Rumoca.FMI3.InitializationCalls
