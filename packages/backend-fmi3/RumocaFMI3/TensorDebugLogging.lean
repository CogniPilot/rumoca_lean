import RumocaFMI3.DebugLoggingRuntime
import RumocaFMI3.DebugLoggingContract
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3SetDebugLogging` contract over the tensor instance record, as a
package-checked product.

The scalar body `Runtime.body model signature` for `fmi3SetDebugLogging` is the
fixed statement list `Runtime.require .logging ++ DebugLogging.code`; it reads no
source name and touches no tensor region, and is already emitted as the
model-free constant `DebugLogging.function` (`Runtime.function model signature =
DebugLogging.function`), so it is identical for every prepared model, tensor or
scalar (`independent`). A legal request updates only the instance's logging flag
and returns `fmi3OK`; an illegal request is rejected quietly or through the logger
callback; a null handle returns `fmi3Error`. The handle/lifecycle, logger,
environment and logging-flag premises are reads of the instance record metadata
cells the tensor record also carries, so the scalar runtime execution transfers
verbatim to a tensor instance record heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorDebugLogging
open CTree CMemory CBody CStringMemory StaticFactory CLiteral.Interface
open Rumoca.FMI3.DebugLogging (signature function function_eq failureMessage
  SuppressedContract LoggedContract runtime_null_correct runtime_suppressed_correct runtime_logged_correct)

/-- The `fmi3SetDebugLogging` body does not depend on the prepared model: the
tensor and scalar instances share the identical model-free emitted function. -/
theorem independent (m m' : Solve.FMI3Model source) :
    Runtime.function m signature = Runtime.function m' signature := rfl

open CTree.Printer CTree.Syntax in
/-- The public signature prints under the shared runtime typedefs, so the emitted
function denotes itself. -/
theorem denotation (model : Solve.FMI3Model source) :
    FunctionTokenization RuntimePrinter.typedefs (Runtime.function model signature).render
      (Runtime.function model signature) := by
  apply RuntimePrinter.function_tokenization
  refine ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, by decide +kernel⟩
  all_goals first
    | exact TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel))
    | exact TypeSpelling.const
        (show TypeSpelling RuntimePrinter.typedefs "fmi3String" from
          TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)))

section
variable [interface : CInterface]
open CTree.Printer

/-- The tensor `fmi3SetDebugLogging` function contract, in the shape the other
tensor behavioral contracts use, over the runtime execution interface. The null,
suppressed-rejection and logged-rejection behaviors are the scalar `DebugLogging`
runtime behaviors; their handle/lifecycle, logger, environment and logging-flag
premises are reads of the tensor instance record's own metadata cells. -/
structure Contract (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  null : ∀ {E} (program : CCalls.Events.Program E),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    ∀ (heap : Heap) (enabled : Bool) (count : UInt64) (pointer : Option Address) behavior,
      (CCalls.Events.machine program).Behaves
        (.calling signature.name (DebugLogging.arguments none enabled count pointer) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  suppressed : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (category : Address)
    (messages : Bool → Address) (integer : interface.types "int" = some CType.int32),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    program.externals "strcmp" = some (CStringCalls.compareExternal integer) →
    literals "logStatus" = some category →
    (∀ unknown, literals (failureMessage unknown) = some (messages unknown)) →
    Contents heap category (content "logStatus") → SuppressedContract program heap
  logged : ∀ (program : CCalls.Events.Program Invocation) (heap : Heap) (category : Address)
    (messages : Bool → Address) (integer : interface.types "int" = some CType.int32),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) →
    program.externals "strcmp" = some (CStringCalls.compareExternal integer) →
    literals "logStatus" = some category →
    (∀ unknown, literals (failureMessage unknown) = some (messages unknown)) →
    Contents heap category (content "logStatus") → LoggedContract program heap category messages

theorem contract (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    Contract literals model (Runtime.function model signature).render :=
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  { independent := fun _ => rfl
    printed := rfl
    closed := BodyEmbedding.body_closed model signature
    denotes := denotation model
    null := fun program defined heap enabled count pointer behavior =>
      runtime_null_correct header objects literals program (function_eq model ▸ defined)
        heap enabled count pointer behavior
    suppressed := fun program heap category messages _ defined helper compare literal bound contents =>
      runtime_suppressed_correct header objects literals program heap category messages
        (function_eq model ▸ defined) helper compare literal bound contents
    logged := fun program heap category messages _ defined helper compare literal bound contents =>
      runtime_logged_correct header objects literals program heap category messages
        (function_eq model ▸ defined) helper compare literal bound contents }

end
end Rumoca.FMI3.TensorDebugLogging
