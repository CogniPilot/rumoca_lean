import RumocaFMI3.GuardedNoop
import RumocaFMI3.EventIndicatorEnvironment

/-! The emitted discrete-evaluation call for the event-free Solve product.
The reference guard is separate from the no-op's whole-heap effect. -/
noncomputable section
namespace Rumoca.FMI3.DiscreteEvaluation
open CTree CMemory CBody CLiteral StaticFactory CLiteral.Interface CCalls.Events

def signature : Signature :=
  ⟨"fmi3Status", "fmi3EvaluateDiscreteStates", [⟨"fmi3Instance", "instance", false⟩]⟩

def arguments (handle : Option Address) : List Value := [.pointer handle]

def parameters (handle : Option Address) : Locals :=
  CBody.bind (fun _ => none) "instance" (.pointer handle)

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .evaluateDiscrete ++ [Runtime.ok] := rfl

theorem parameters_bound (literals : CLiteralAddresses) (handle : Option Address) :
    @CCalls.parameters (cInterface literals) signature.parameters (arguments handle) =
      some (parameters handle) := rfl

/-- This classification covers every represented handle, interface and mode;
it does not claim that an invalid native pointer is safe to dereference. -/
theorem query_cases (handle : Option Address) (kind : Kind) (mode : Mode) :
    handle = none ∨ ∃ p, handle = some p ∧
      (Reference.Allowed .evaluateDiscrete kind mode ∨
        ¬ Reference.Allowed .evaluateDiscrete kind mode) := by
  classical
  cases handle with
  | none => exact Or.inl rfl
  | some p => exact Or.inr ⟨p, rfl, Classical.em _⟩

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

structure QuietContract [CInterface] (program : Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .evaluateDiscrete kind mode →
    ∀ behavior, (machine program).Behaves
      (.calling signature.name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ heap behavior, (machine program).Behaves
    (.calling signature.name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

/-- Parameter types, literal addresses and the exact emitted body determine
the interface transfer. Other target bindings need not agree. -/
theorem quiet_agreed {E : Type} (target : CInterface)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (types : (cInterface literals).types = target.types)
    (bytes : (cInterface literals).literals = target.literals)
    (agrees : CodeAgrees (cInterface literals) target (Runtime.body model signature)) :
    letI : CInterface := target
    ∀ (program : Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program := by
  letI : CInterface := target
  intro program defined
  constructor
  · intro heap p kind mode hk hm allowed behavior
    have executed := GuardedCalls.unchanged_body (static := ⟨literals⟩) .evaluateDiscrete
      (parameters (some p)) heap p kind mode
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind]) hk hm allowed
    rw [← body model] at executed
    exact body_call_interface_behaviors (cInterface literals)
      (target)
      types bytes
      program (Runtime.function model signature) _ _ heap _ (.integer 0) 4 defined
      (parameters_bound literals (some p)) (BodyEmbedding.body_closed model signature)
      agrees executed rfl behavior
  · intro heap behavior
    let rest := Runtime.modeGuard .evaluateDiscrete :: [Runtime.ok]
    have executed := GuardedCalls.null_body (static := ⟨literals⟩) (parameters none) heap rest
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind])
    have shaped : (Runtime.function model signature).body = Runtime.instancePrefix ++ rest := by
      simp [Runtime.function, body, Runtime.require, rest, List.append_assoc]
    rw [← shaped] at executed
    exact body_call_interface_behaviors (cInterface literals)
      (target)
      types bytes
      program (Runtime.function model signature) _ _ heap _ (.integer 3) 3 defined
      (parameters_bound literals none) (BodyEmbedding.body_closed model signature)
      agrees executed rfl behavior

theorem body_agrees_static (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    CodeAgrees (cInterface literals) (executionInterface objects literals)
      (Runtime.body model signature) := by
  rw [body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, executionInterface, CInterface.constants, objectConstants]

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program :=
  quiet_agreed (RuntimeEnvironment.interface header objects literals) literals model
    (RuntimeEnvironment.types_agree header objects literals) rfl
    (body_agrees header objects literals model)

theorem quiet_static_correct {E : Type} (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : Program E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      QuietContract program :=
  quiet_agreed (executionInterface objects literals) literals model
    (StaticInitialization.interface_types objects literals) rfl
    (body_agrees_static objects literals model)

theorem failure_prefix (model : Solve.FMI3Model source) (literals : CLiteralAddresses)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (denied : ¬ Reference.Allowed .evaluateDiscrete kind mode) :
    @GuardedCalls.FailurePrefix (cInterface literals) (Runtime.function model signature)
      (arguments (some p)) heap p ErrorCalls.rejectionMessage heap := by
  letI : CInterface := cInterface literals
  have reached := LifecycleGuard.reject_prefix (static := ⟨literals⟩) (parameters (some p)) heap p
    .evaluateDiscrete kind mode [Runtime.ok]
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm denied
  refine ⟨rfl, BodyEmbedding.body_closed model signature, parameters (some p),
    CBody.bind (parameters (some p)) "m" (.pointer (some p)),
    [Runtime.ok], 3, parameters_bound literals _, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, CBody.resolve]

end Rumoca.FMI3.DiscreteEvaluation
end
