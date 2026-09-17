import RumocaFMI3.Version
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3GetVersion` contract, as a package-checked product.

The scalar body `Runtime.body model signature` for `fmi3GetVersion` is the fixed
statement `[ret (.str "3.0")]`; it reads no source name, no instance handle and no
tensor region, so it is identical for every prepared model, tensor or scalar
(`independent`). The call returns a pointer to the collected `"3.0"` literal,
leaving the heap unchanged, independently of any instance record. Reusing the
scalar `Version.call_behaviors` therefore delivers the tensor `fmi3GetVersion`
behavior verbatim.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorVersion
open CTree CMemory
open Rumoca.FMI3.Version (signature call_behaviors function_tokenization)

/-- The `fmi3GetVersion` body does not depend on the prepared model: the tensor
and scalar instances share the identical emitted function. -/
theorem independent (m m' : Solve.FMI3Model source) :
    Runtime.function m signature = Runtime.function m' signature := rfl

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree.Printer

/-- The tensor `fmi3GetVersion` function contract, in the shape the other tensor
behavioral contracts use. `fmi3GetVersion` carries no instance handle, so it has
no null-handle case; its sole behavior returns a pointer to the `"3.0"` literal
with the heap unchanged. -/
structure Contract (model : Solve.FMI3Model source) (text : String) : Prop where
  independent : ∀ (m' : Solve.FMI3Model source), Runtime.function m' signature = Runtime.function model signature
  printed : text = (Runtime.function model signature).render
  closed : (Runtime.function model signature).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionTokenization RuntimePrinter.typedefs text (Runtime.function model signature)
  successful : ∀ (program : CCalls.Program) (heap : Heap) (base : Address),
    program.definitions signature.name = some (.tree (Runtime.function model signature)) →
    static.addresses "3.0" = some base →
    ∀ behavior, (CCalls.Typed.machine program).Behaves
      (.calling signature.name [] heap .done) behavior ↔
      behavior = .terminates ⟨.pointer (some base), heap⟩

theorem contract (model : Solve.FMI3Model source) :
    Contract model (Runtime.function model signature).render where
  independent _ := rfl
  printed := rfl
  closed := BodyEmbedding.body_closed model signature
  denotes := function_tokenization model
  successful program heap base defined bound :=
    call_behaviors model program heap base defined bound

end
end Rumoca.FMI3.TensorVersion
