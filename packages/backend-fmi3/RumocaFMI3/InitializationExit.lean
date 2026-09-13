import RumocaFMI3.InitializationBodies
import RumocaFMI3.GuardedCalls
import RumocaC.BodyEvents

noncomputable section
namespace Rumoca.FMI3.InitializationExit
open CTree CMemory CBody

def signature : Signature := ⟨"fmi3Status", "fmi3ExitInitializationMode", [⟨"fmi3Instance", "instance", false⟩]⟩
def arguments (handle : Option Address) : List Value := [.pointer handle]
def parameters (handle : Option Address) : Locals := CBody.bind (fun _ => none) "instance" (.pointer handle)
def tail : List Stmt := [Runtime.branch (Runtime.eqv (Runtime.field "kind") (Runtime.n 0))
  [Runtime.setMode .event] [Runtime.setMode .step], Runtime.ok]

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = Runtime.require .exitInitialization ++ tail := by
  simp [Runtime.body, signature, tail]

theorem closed (model : Solve.FMI3Model source) :
    (Runtime.body model signature).all CBodyEmbedding.closedBlocks = true := by
  rw [body]
  simp [tail, Runtime.require, Runtime.instancePrefix, Runtime.reject, Runtime.branch,
    Runtime.fail, Runtime.ret, Runtime.setMode, Runtime.put, Runtime.ok,
    CBodyEmbedding.closedBlocks, CLoops.noDeclarations]

theorem finite_parameters (p : Address) : parameters (some p) = HistoryBodies.parameters p := by
  funext name
  simp [parameters, HistoryBodies.parameters, CBody.bind]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle : Option Address) :
    CCalls.parameters signature.parameters (arguments handle) = some (parameters handle) := by
  simp [CCalls.parameters, CCalls.parameterType, signature, arguments, parameters, CBody.cast, convert]

theorem call_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (kind : Kind)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationBodies.exitHeap heap p kind⟩ := by
  have kindLoaded : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)) := by
    cases kind <;> exact hk
  have executed := InitializationBodies.exit_run model signature rfl heap p kind kindLoaded hm
  rw [← finite_parameters] at executed
  exact CCalls.Events.body_call_behaviors program (Runtime.function model signature) _ _ heap _ (.integer 0) 6
    defined (parameters_bound _) (closed model) executed rfl behavior

theorem null_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions signature.name = some (.tree (Runtime.function model signature))) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling signature.name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (Runtime.function model signature)
    (Runtime.modeGuard .exitInitialization :: tail) (arguments none) (parameters none) heap defined (parameters_bound _)
  · change Runtime.body model signature = _
    rw [body]
    simp only [Runtime.require, List.append_assoc, List.cons_append, List.nil_append]
  · rfl
  · exact closed model
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]
  · simp [parameters, CBody.bind]

theorem failure_prefix (model : Solve.FMI3Model source) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (denied : mode ≠ .initialization) :
    GuardedCalls.FailurePrefix (Runtime.function model signature) (arguments (some p)) heap p
      ErrorCalls.rejectionMessage heap := by
  have reached := LifecycleGuard.reject_prefix (parameters (some p)) heap p .exitInitialization kind mode tail
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm denied
  refine ⟨rfl, closed model, parameters (some p), CBody.bind (parameters (some p)) "m" (.pointer (some p)),
    tail, 3, parameters_bound _, ?_, ?_, ?_⟩
  · simpa only [Runtime.function, body] using reached
  · simp [parameters, CBody.bind]
  · simp [CBody.bind, resolve]

end
end Rumoca.FMI3.InitializationExit
