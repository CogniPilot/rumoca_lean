import RumocaFMI3.ScheduledCreationContract
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3InstantiateScheduledExecution` contract, as a package-checked
product.

The scalar body `Runtime.body model signature` for
`fmi3InstantiateScheduledExecution` is the fixed rejection `FactoryRejection.code
message`: it optionally logs `"Scheduled Execution is unsupported"` and returns
`NULL` without reserving any instance. It reads no source name and touches no
tensor region, so it is identical for every prepared model, tensor or scalar
(`independent`). The Co-Simulation and tensor profiles equally decline Scheduled
Execution, so the scalar rejection behaviors transfer verbatim: a quiet call (no
logger, or logging disabled) returns `NULL` leaving the whole heap unchanged, and
a logging call emits the diagnostic through the supplied logger callback. The
logger, environment and logging-flag premises are call arguments the creation
request carries, exactly as in the scalar proof.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar factory, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorScheduledCreation
open CTree CMemory CBody CCalls.Events StaticFactory CLiteral.Interface
open Rumoca.FMI3.ScheduledCreation (signature message Raw signature_printable quiet_call logged_call)

/-- The `fmi3InstantiateScheduledExecution` body does not depend on the prepared
model: the tensor and scalar factories share the identical emitted function. -/
theorem independent (m m' : Solve.FMI3Model source) :
    Runtime.function m signature = Runtime.function m' signature := rfl

section
variable [interface : CInterface]
open CTree.Printer

/-- The tensor `fmi3InstantiateScheduledExecution` function contract, in the shape
the other tensor behavioral contracts use, over the runtime execution interface.
The quiet and logged behaviors are the scalar `ScheduledCreation` rejection
behaviors; their logger, environment and logging-flag premises are the creation
request's own call arguments. -/
structure Contract (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  quiet : ∀ {E} (program : Program E) (heap : Heap) (args : Raw),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    (args.logger.isSome && args.logging) = false →
    ∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
      observed = .terminates [] ⟨.pointer none, heap⟩
  logged : ∀ {E} (program : Program E) (heap : Heap) (logger category text' : Address)
    (name : String) (foreign : External E) (args : Raw),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    args.logger = some logger → args.logging = true →
    literals "logStatus" = some category → literals message = some text' →
    program.addresses logger = some name → program.externals name = some foreign →
    foreign.signature = Logging.signature name →
    ∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
      (∃ events value after, foreign.execute (Logging.arguments args.environment category text')
        heap events value after ∧ observed = .terminates events ⟨.pointer none, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text')
        heap events value after) ∧ observed = .wrong [])

theorem contract (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    Contract literals model (Runtime.function model signature).render :=
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  { independent := fun _ => rfl
    printed := rfl
    closed := BodyEmbedding.body_closed model signature
    denotes := RuntimePrinter.function_tokenization model signature signature_printable
    quiet := fun program heap args defined cond observed =>
      quiet_call header objects literals model args program heap defined cond observed
    logged := fun program heap logger category text' name foreign args defined loggerBound logging
        categoryBound textBound address external prototype observed =>
      logged_call header objects literals model args program heap logger category text' name foreign
        defined loggerBound logging categoryBound textBound address external prototype observed }

end
end Rumoca.FMI3.TensorScheduledCreation
