import RumocaFMI3.CompletedContract
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3CompletedIntegratorStep` contract over the tensor instance record,
as a package-checked product.

The scalar body `Runtime.body model signature` for `fmi3CompletedIntegratorStep`
is a fixed statement list: the handle/lifecycle guard, an output-pointer check,
the constant writes of the two result flags, and the completed-time bookkeeping,
followed by `fmi3OK`. It reads no source name and touches no tensor region, so it
is identical for every prepared model, tensor or scalar (`independent`). A valid
call writes the fixed flags and time history and returns `fmi3OK`; a null handle
returns `fmi3Error`. The handle/lifecycle premises are reads of the instance
record metadata cells (`kind`, `mode`) the tensor record also carries, so the
scalar execution transfers verbatim to a tensor instance record heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorCompletedStep
open CTree CMemory CBody StaticFactory CLiteral.Interface
open Rumoca.FMI3.CompletedCalls (signature arguments call_behaviors null_behaviors)

/-- The `fmi3CompletedIntegratorStep` body does not depend on the prepared model:
the tensor and scalar instances share the identical emitted function. -/
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
  · exact ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  all_goals exact ⟨TypeSpelling.pointer (text := "fmi3Boolean")
    (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩

section
variable [interface : CInterface]
open CTree.Printer

/-- The tensor `fmi3CompletedIntegratorStep` function contract, in the shape the
other tensor behavioral contracts use, over the static-storage execution
interface. The successful and null behaviors are the scalar `CompletedCalls`
behaviors, whose handle/lifecycle premises are reads of the tensor instance
record's own metadata cells. -/
structure Contract (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p event terminate : Address)
    (flag : Bool) (clock : Time.Clock),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 3) →
    HistoryProofs.Stored heap p clock →
    HistoryBodies.BoolWritable heap event → HistoryBodies.BoolWritable heap terminate →
    event.block ≠ p.block → terminate.block ≠ p.block →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (some event) (some terminate) flag) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, HistoryBodies.completedHeap heap p event terminate clock⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (event terminate : Option Address) (flag : Bool),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none event terminate flag) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    Contract model (Runtime.function model signature).render :=
  letI : CInterface := executionInterface objects literals
  { independent := fun _ => rfl
    printed := rfl
    closed := BodyEmbedding.body_closed model signature
    denotes := denotation model
    successful := fun program heap p event terminate flag clock defined hk hm stored he ht hne hnt =>
      call_behaviors objects literals model program heap p event terminate flag clock defined hk hm
        stored he ht hne hnt
    null := fun program heap event terminate flag defined =>
      null_behaviors objects literals model program heap event terminate flag defined }

end
end Rumoca.FMI3.TensorCompletedStep
