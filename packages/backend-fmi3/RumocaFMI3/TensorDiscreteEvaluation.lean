import RumocaFMI3.DiscreteEvaluationCalls
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3EvaluateDiscreteStates` contract over the tensor instance record,
as a package-checked product.

The scalar body `Runtime.body model signature` for `fmi3EvaluateDiscreteStates`
is the fixed statement list `Runtime.require .evaluateDiscrete ++ [ok]`; it reads
no source name and touches no tensor region, so it is identical for every
prepared model, tensor or scalar (`independent`). The event-free unit product has
no discrete update work, so a valid call returns `fmi3OK` leaving the whole heap
unchanged and a null handle returns `fmi3Error`. The handle/lifecycle premises are
reads of the instance record metadata cells (`kind`, `mode`) the tensor record
also carries, so the scalar quiet execution transfers verbatim to a tensor
instance record heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorDiscreteEvaluation
open CTree CMemory CBody StaticFactory CLiteral.Interface
open Rumoca.FMI3.DiscreteEvaluation (signature arguments quiet_static_correct)

/-- The `fmi3EvaluateDiscreteStates` body does not depend on the prepared model:
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
  subst param
  exact ⟨TypeSpelling.named (.typedefName (by decide +kernel) (by decide +kernel)),
    by decide +kernel⟩

section
variable [interface : CInterface]
open CTree.Printer

/-- The tensor `fmi3EvaluateDiscreteStates` function contract, in the shape the
other tensor behavioral contracts use, over the static-storage execution
interface. The successful and null behaviors are the scalar `DiscreteEvaluation`
quiet behaviors, whose handle/lifecycle premises are reads of the tensor instance
record's own metadata cells. -/
structure Contract (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed .evaluateDiscrete kind mode →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap),
    program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments none) heap .done) behavior ↔
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
    successful := fun program heap p kind mode defined hk hm allowed =>
      (quiet_static_correct objects literals model program defined).successful heap p kind mode hk hm allowed
    null := fun program heap defined =>
      (quiet_static_correct objects literals model program defined).null heap }

end
end Rumoca.FMI3.TensorDiscreteEvaluation
