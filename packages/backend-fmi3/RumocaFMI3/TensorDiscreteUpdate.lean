import RumocaFMI3.DiscreteContract
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3UpdateDiscreteStates` contract over the tensor instance record, as
a package-checked product.

The scalar body `Runtime.body model signature` for `fmi3UpdateDiscreteStates` is a
fixed statement list: the handle/lifecycle guard, an output-pointer check, and the
constant writes of the six discrete-update result fields, followed by `fmi3OK`. It
reads no source name and touches no tensor region, so it is identical for every
prepared model, tensor or scalar (`independent`). A valid call writes the fixed
`0`/false results into the caller's output pointers and returns `fmi3OK`; a null
handle returns `fmi3Error`. The handle/lifecycle premises are reads of the
instance record metadata cells (`kind`, `mode`) the tensor record also carries,
and the writes land in the caller's own output storage, so the scalar execution
transfers verbatim to a tensor instance record heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorDiscreteUpdate
open CTree CMemory CBody StaticFactory CLiteral.Interface
open Rumoca.FMI3.DiscreteCalls (signature arguments outputs call_behaviors null_behaviors)

/-- The `fmi3UpdateDiscreteStates` body does not depend on the prepared model: the
tensor and scalar instances share the identical emitted function. -/
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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  all_goals first
    | exact ⟨TypeSpelling.pointer (text := "fmi3Boolean")
        (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩
    | exact ⟨TypeSpelling.pointer (text := "fmi3Float64")
        (.named (.typedefName (by decide +kernel) (by decide +kernel))), by decide +kernel⟩

section
variable [interface : CInterface]
open CTree.Printer

/-- The tensor `fmi3UpdateDiscreteStates` function contract, in the shape the
other tensor behavioral contracts use, over the static-storage execution
interface. The successful and null behaviors are the scalar `DiscreteCalls`
behaviors: the handle/lifecycle premises are reads of the tensor instance record's
own metadata cells and the writes land in the caller's output storage. -/
structure Contract (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (addresses : String → Address),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer 2) →
    (∀ entry ∈ outputs addresses, COutputAssignments.Writable heap entry) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (fun name => some (addresses name))) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, COutputAssignments.after heap (outputs addresses)⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (addresses : String → Option Address),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none addresses) heap .done) behavior ↔
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
    successful := fun program heap p addresses defined hk hm writable =>
      call_behaviors objects literals model program heap p addresses defined hk hm writable
    null := fun program heap addresses defined =>
      null_behaviors objects literals model program heap addresses defined }

end
end Rumoca.FMI3.TensorDiscreteUpdate
