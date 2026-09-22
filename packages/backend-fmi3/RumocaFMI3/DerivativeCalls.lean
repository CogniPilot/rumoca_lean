import RumocaFMI3.ModelRhs
import RumocaFMI3.StateEntry

noncomputable section
namespace Rumoca.FMI3.DerivativeCalls
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def signature : Signature :=
  ⟨"fmi3Status", "fmi3GetContinuousStateDerivatives",
    [⟨"fmi3Instance", "instance", false⟩, ⟨"fmi3Float64", "derivatives", true⟩,
     ⟨"size_t", "nContinuousStates", false⟩]⟩

def values (handle buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer handle, .pointer buffer, .integer count.toNat]

def parameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (CBody.bind (CBody.bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "derivatives" (.pointer buffer)) "instance" (.pointer handle)

def locals (p : Address) (buffer : Option Address) (count : UInt64) : Locals :=
  CBody.bind (parameters (some p) buffer count) "m" (.pointer (some p))

def target : Expr := .index (Runtime.v "derivatives") (Runtime.n 0)

def action : List Stmt :=
  [.assign target (Runtime.call "model_rhs" [.address (Runtime.field "model")]), Runtime.ok]

def tail : List Stmt := Runtime.scalarAccessCheck "derivatives" "nContinuousStates" ++ action

theorem parameters_bound (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters signature.parameters (values handle buffer count) = some (parameters handle buffer count) := by
  have converted : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ (by rfl) (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [signature, values, CCalls.parameters, CCalls.parameterType, Bool.false_eq_true, ↓reduceIte, converted]
  rfl

omit static in
theorem body_eq (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .getDerivatives ++ tail := rfl

theorem accepted_run (model : Solve.FMI3Model source) (heap : Heap) (p buffer : Address) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode) :
    run 4 (.running (Runtime.body model signature) (parameters (some p) (some buffer) 1) heap) =
      some (.running action (locals p (some buffer) 1) heap) := by
  have guard := LifecycleGuard.accept (parameters (some p) (some buffer) 1) heap p
    .getDerivatives .me mode tail (by simp [parameters, CBody.bind])
    (by simp [parameters, CBody.bind]) hk hm allowed
  rw [body_eq, show 4 = 3 + 1 from rfl, run_add, guard]
  simpa only [Option.bind_some, tail, locals] using ScalarAccess.valid_run
    (locals p (some buffer) 1) heap "derivatives" "nContinuousStates" buffer action
    (by simp [locals, parameters, CBody.bind, resolve]) (by simp [locals, parameters, CBody.bind, resolve])

def continuation (env : Locals) (types : CLoops.Types) (stack : CCalls.Typed.Continuation) :
    CCalls.Typed.Continuation := .caller (.assign target) [Runtime.ok] env types "fmi3Status" stack

theorem enter_rhs (program : CCalls.Events.Program E) (heap : Heap) (p buffer : Address)
    (types : CLoops.Types) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running action (locals p (some buffer) 1) types heap) "fmi3Status" stack) =
      some (.calling "model_rhs" [.pointer (some (p.member "model"))] heap
        (continuation (locals p (some buffer) 1) types stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    action, target, Runtime.call, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith,
    CCalls.Events.enterCallWith, CCalls.Events.resolveWith, CCalls.Indirect.operand, CCalls.Indirect.resolveWith, CBody.legacyExpressions,
    CCalls.argumentsWith, CBody.legacyExpressions, locals, parameters, CBody.bind, CBody.resolve, CBody.constants,
    Value.address, continuation]

theorem return_rhs (program : CCalls.Events.Program E) (heap : Heap) (p buffer : Address)
    (types : CLoops.Types) (stack : CCalls.Typed.Continuation) (value : Binary64.Value) (old : Option Value)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    CCalls.Events.internalNext program
      (.returning (.finite value) heap (continuation (locals p (some buffer) 1) types stack)) =
      some (.body (.running [Runtime.ok] (locals p (some buffer) 1) types
        (StateProofs.written heap buffer (Binary64.toBits value).val)) "fmi3Status" stack) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith, CBody.legacyExpressions, continuation,
    target, Runtime.v, Runtime.n, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, locals, parameters, CBody.bind,
    CBody.resolve, CBody.constants, Value.address, Value.finite,
    store_float64 heap buffer old _ storage, StateProofs.written]

theorem finish (program : CCalls.Events.Program E) (heap : Heap) (env : Locals)
    (types : CLoops.Types) (stack : CCalls.Typed.Continuation) (ok : env "fmi3OK" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running [Runtime.ok] env types heap) "fmi3Status" stack)
      (.returning (.integer 0) heap stack) := by
  refine .next (t := .body (.returned ⟨.integer 0, heap⟩) "fmi3Status" stack) ?_ (.next ?_ (.refl _))
  · simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
      Runtime.ok, Runtime.ret, Runtime.v, CBody.eval, CBody.evalWith, CBody.resolve, CBody.constants, ok]
  · rfl

theorem reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling signature.name (values (some p) (some buffer) 1) heap stack)
      (.returning (.integer 0) (StateProofs.written heap buffer
        (Binary64.toBits (ModelExchange.derivative model.solve state)).val) stack) := by
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model signature)
    (values (some p) (some buffer) 1) (parameters (some p) (some buffer) 1) (locals p (some buffer) 1)
    heap heap action stack 4 defined (parameters_bound _ _ _) (BodyEmbedding.body_closed model signature)
    (accepted_run model heap p buffer mode hk hm allowed)
  refine entered.trans (.next (enter_rhs program heap p buffer types stack) ?_)
  refine (ModelRhs.reaches model program heap (some (p.member "model"))
    (continuation (locals p (some buffer) 1) types stack) helper numerical same).trans
    (.next (return_rhs program heap p buffer types stack model.solve.realRhs old storage) ?_)
  exact finish program _ (locals p (some buffer) 1) types stack (by simp [locals, parameters, CBody.bind])

theorem behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (storage : heap buffer = some ⟨.float64, true, old⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) (some buffer) 1) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, StateProofs.written heap buffer
        (Binary64.toBits (ModelExchange.derivative model.solve state)).val⟩ :=
  (CCalls.Events.internal_prefix program (reaches model program heap p buffer mode state old .done
    defined helper numerical same hk hm allowed storage)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

end Rumoca.FMI3.DerivativeCalls
