import RumocaFMI3.StaticErrorCalls
import RumocaFMI3.RuntimeEnvironment
import RumocaC.CallSignature

/-! Shared execution of the existing unsupported-capability body. This module
does not classify legal FMI calls: each member still needs metadata and
standards correspondence. Typed arguments determine fresh locals; no returned
status or successful public execution is an input premise. -/
noncomputable section
namespace Rumoca.FMI3.CapabilityRejection
open CTree CMemory CBody CLiteral.Interface StaticFactory CCalls.Events

def message : String := "FMI capability is not supported"
def code : List Stmt := Runtime.instancePrefix ++ [Runtime.fail message]
def instanceParameter : Parameter := ⟨"fmi3Instance", "instance", false⟩

structure Profile (sig : Signature) (tail : List Parameter) : Prop where
  result : sig.result = "fmi3Status"
  parameters : sig.parameters = instanceParameter :: tail
  unique : (sig.parameters.map Parameter.name).Nodup
  fresh : ∀ name ∈ ["m", "fail", "fmi3Error"], name ∉ tail.map Parameter.name

def locals (tail : List Parameter) (handle : Option Address) (outputs : List Value) : Locals :=
  CCalls.Signature.locals (instanceParameter :: tail) (.pointer handle :: outputs)

/-- The existing header-readiness contract supplies an argument witness for
every profiled signature; the raw call domain is not empty by construction. -/
theorem arguments_exist [CInterface] (profile : Profile sig tail)
    (ready : CCalls.Signature.Ready sig) :
    ∃ values, CCalls.Signature.Arguments tail values values := by
  obtain ⟨_, known, _⟩ := ready
  rw [profile.parameters, List.all_cons, Bool.and_eq_true] at known
  exact CCalls.Signature.arguments_exist known.2

theorem locals_instance : locals tail handle outputs "instance" = some (.pointer handle) := by
  simp [locals, CCalls.Signature.locals_cons, instanceParameter, CBody.bind]

theorem locals_fresh (profile : Profile sig tail) (length : tail.length = outputs.length)
    (name : String) (member : name ∈ ["m", "fail", "fmi3Error"]) :
    locals tail handle outputs name = none := by
  apply CCalls.Signature.locals_missing (by simpa using length)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simpa [instanceParameter] using profile.fresh _ (by simp)

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (profile : Profile sig tail)
    (arguments : CCalls.Signature.Arguments tail inputs outputs) (handle : Option Address) :
    CCalls.parameters sig.parameters (.pointer handle :: inputs) =
      some (locals tail handle outputs) := by
  rw [profile.parameters]
  apply CCalls.Signature.parameters_bound
    (CCalls.Signature.Arguments.cons (type := .pointer) (by rfl) (by rfl) arguments)
  simpa only [profile.parameters] using profile.unique

theorem nonnull_body (env : Locals) (heap : Heap) (p : Address)
    (instanceValue : env "instance" = some (.pointer (some p))) (fresh : env "m" = none) :
    run 2 (.running code env heap) =
      some (.running [Runtime.fail message] (CBody.bind env "m" (.pointer (some p))) heap) := by
  simp [code, Runtime.instancePrefix, Runtime.branch, Runtime.ret, Runtime.v,
    run, next, CBody.nextWith, CBody.legacyExpressions, eval, CBody.evalWith,
    CBody.bind, CBody.resolve, constants, CBody.cast, convert,
    Value.truth, boolean, instanceValue, fresh]

theorem failure_prefix (model : Solve.FMI3Model source) (profile : Profile sig tail)
    (routed : Runtime.body model sig = code)
    (arguments : CCalls.Signature.Arguments tail inputs outputs) (heap : Heap) (p : Address) :
    GuardedCalls.FailurePrefix (Runtime.function model sig) (.pointer (some p) :: inputs)
      heap p message heap := by
  refine ⟨profile.result, BodyEmbedding.body_closed model sig,
    locals tail (some p) outputs, CBody.bind (locals tail (some p) outputs) "m" (.pointer (some p)),
    [], 2, parameters_bound profile arguments (some p), ?_, ?_, ?_⟩
  · change run 2 (.running (Runtime.body model sig) _ heap) = _
    rw [routed]
    exact nonnull_body _ heap p locals_instance
      (locals_fresh profile arguments.length "m" (by simp))
  · simp [CBody.bind, locals_fresh profile arguments.length "fail" (by simp)]
  · simp [CBody.bind, CBody.resolve]

theorem null_body (profile : Profile sig tail)
    (arguments : CCalls.Signature.Arguments tail inputs outputs) (heap : Heap) :
    run 3 (.running code (locals tail none outputs) heap) =
      some (.returned ⟨.integer 3, heap⟩) :=
  GuardedCalls.null_body _ heap [Runtime.fail message] locals_instance
    (locals_fresh profile arguments.length "m" (by simp))
    (locals_fresh profile arguments.length "fmi3Error" (by simp))

end

theorem code_agrees (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals) code := by
  simp [code, CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.instancePrefix,
    Runtime.fail, Runtime.branch, Runtime.ret, Runtime.v, Runtime.call, Expr.nullPointer,
    RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants, objectConstants]

theorem null_call {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (profile : Profile sig tail)
    (routed : Runtime.body model sig = code)
    (arguments : @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap),
      program.internal.definitions sig.name = some (.tree (Runtime.function model sig)) →
      ∀ observed, (machine program).Behaves (.calling sig.name (.pointer none :: inputs) heap .done) observed ↔
        observed = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined observed
  apply body_call_interface_behaviors (cInterface literals) _
    (RuntimeEnvironment.types_agree header objects literals) rfl program (Runtime.function model sig)
    (.pointer none :: inputs) (locals tail none outputs) heap ⟨.integer 3, heap⟩ (.integer 3) 3 defined
    (parameters_bound (static := ⟨literals⟩) profile arguments none) (BodyEmbedding.body_closed model sig)
  · simpa only [Runtime.function, routed] using code_agrees header objects literals
  · simpa only [Runtime.function, routed] using null_body (static := ⟨literals⟩) profile arguments heap
  · change @CCalls.returnCast (cInterface literals) sig.result (.integer 3) = some (.integer 3)
    rw [profile.result]
    rfl

theorem suppressed_call {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (profile : Profile sig tail)
    (routed : Runtime.body model sig = code)
    (arguments : @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap) (p text : Address) (old : Option Value)
      (logger : Option Address) (logging : Bool),
      program.internal.definitions sig.name = some (.tree (Runtime.function model sig)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals message = some text →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) →
      ∀ observed, (machine program).Behaves
        (.calling sig.name (.pointer (some p) :: inputs) heap .done) observed ↔
        observed = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p text old logger logging defined helper bound mode loggerValue loggingValue suppressed observed
  exact StaticErrors.failure_suppressed_behaviors ((ErrorContext.static objects literals).withRounding header)
    program (Runtime.function model sig) (.pointer (some p) :: inputs) heap heap p text message old logger logging
    (by simpa only [Runtime.function, routed] using code_agrees header objects literals)
    (failure_prefix (static := ⟨literals⟩) model profile routed arguments heap p)
    defined helper bound mode loggerValue loggingValue suppressed observed

/-- Every external callback execution is retained, as is the modeled blocked
alternative when none returns. No selected result is an assumption. -/
theorem logged_call {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (profile : Profile sig tail)
    (routed : Runtime.body model sig = code)
    (arguments : @CCalls.Signature.Arguments (cInterface literals) tail inputs outputs) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap) (p text category logger : Address)
      (old : Option Value) (environment : Option Address) (name : String) (foreign : External E),
      program.internal.definitions sig.name = some (.tree (Runtime.function model sig)) →
      program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
      literals message = some text → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      heap (p.member "mode") = some ⟨.int32, true, old⟩ →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) →
      ∀ observed, (machine program).Behaves
        (.calling sig.name (.pointer (some p) :: inputs) heap .done) observed ↔
        (∃ events value after, foreign.execute (Logging.arguments environment category text)
          (LifecycleBodies.writeMode heap p .terminated) events value after ∧
          observed = .terminates events ⟨.integer 3, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments environment category text)
          (LifecycleBodies.writeMode heap p .terminated) events value after) ∧ observed = .wrong []) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p text category logger old environment name foreign defined helper bound categoryBound
    address external prototype mode loggerValue loggingValue environmentValue observed
  exact StaticErrors.failure_all_behaviors ((ErrorContext.static objects literals).withRounding header)
    program (Runtime.function model sig) (.pointer (some p) :: inputs) heap heap p text category logger message name
    environment old foreign
    (by simpa only [Runtime.function, routed] using code_agrees header objects literals)
    (failure_prefix (static := ⟨literals⟩) model profile routed arguments heap p)
    defined helper bound address external prototype categoryBound mode loggerValue loggingValue environmentValue observed

end Rumoca.FMI3.CapabilityRejection
end
