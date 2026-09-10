import RumocaC.TensorProgramCalls
import RumocaC.TensorProgramContract

/-! Complete-file contracts include the outer function's parameter binding
and ordinary call execution, retaining the previous body and printer contract. -/
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

def CallCorrect (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions),
    @Library interface definitions → definitions f.name = some f.tree →
    ∀ (args : Arguments.Values), Arguments.Valid f.parameters args →
    ∀ (locations : Locations) (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap),
    LayoutBound (Arguments.locals f.parameters args) locations layout → Represents locations layout heap values →
    Ready (Arguments.locals f.parameters args) locations p plan layout heap → Finite.Executes p values result →
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound (Arguments.locals f.parameters args) locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
        behavior = .terminates finalHeap

def CallArtifactContract (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  ArtifactContract source f p plan layout ∧ CallCorrect f p plan layout

theorem call_artifact_correct (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (printed : source = f.tree.render) (valid : f.valid = true) (matched : Syntax.Matches f p plan layout) :
    CallArtifactContract source f p plan layout := by
  refine ⟨artifact_correct source f p plan layout printed valid matched, ?_⟩
  intro interface definitions library found args arguments locations values result heap bound represented ready executed
  exact program_call_refines f valid p plan layout matched definitions library found args arguments
    locations values result heap bound represented ready executed

end Rumoca.CTensor.Lowering
