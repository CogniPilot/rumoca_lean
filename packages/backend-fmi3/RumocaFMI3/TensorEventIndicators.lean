import RumocaFMI3.EventIndicatorFunction
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3GetEventIndicators` contract over the tensor instance record, as
a package-checked product.

The scalar body `Runtime.body model signature` for `fmi3GetEventIndicators` reads
no source name and touches no tensor region: it is the fixed statement list
`Runtime.require .getDerivatives ++ [reject (nev nEventIndicators 0) ..., ok]`,
so it is identical for every prepared model, tensor or scalar
(`independent`). The event-free unit product exposes no event indicators, so a
valid empty query returns `fmi3OK` leaving the whole heap unchanged, and a null
handle returns `fmi3Error`. The successful and null-handle premises are reads of
the instance record metadata cells (`kind`, `mode`) that the tensor instance
record also carries, so the scalar execution transfers verbatim to a tensor
instance record heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorEventIndicators
open CTree CMemory CBody
open Rumoca.FMI3.EventIndicatorCalls (signature values behaviors null_behaviors)

/-- The `fmi3GetEventIndicators` body does not depend on the prepared model: the
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
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree.Printer

/-- The tensor `fmi3GetEventIndicators` function contract. It bundles model
independence, the emitted text, closedness and C denotation, the sole successful
empty-query behavior and the null-handle rejection, in the shape the other tensor
behavioral contracts use. The successful and null behaviors are the scalar
`EventIndicatorCalls` behaviors, whose handle/lifecycle premises are reads of the
tensor instance record's own metadata cells. -/
structure Contract (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (buffer : Option Address) (mode : Mode),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    load heap (p.member "kind") = some (.integer 0) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives .me mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values (some p) buffer 0) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (model : Solve.FMI3Model source) :
    Contract model (Runtime.function model signature).render where
  independent _ := rfl
  printed := rfl
  closed := BodyEmbedding.body_closed model signature
  denotes := denotation model
  successful program heap p buffer mode defined hk hm allowed :=
    behaviors model program heap p buffer mode defined hk hm allowed
  null program heap buffer count defined :=
    null_behaviors model program heap buffer count defined

end
end Rumoca.FMI3.TensorEventIndicators
