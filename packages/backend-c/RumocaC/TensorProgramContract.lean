import RumocaC.TensorProgramProofs
import RumocaC.TensorProgramPrinter

/-! Bind a complete printed tensor-call body to ordered finite Solve execution.
Storage is supplied at entry. Allocation, native linkage and the wrapper's
external call ABI are not assumptions disguised as compiler theorems. -/
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

def BodyCorrect (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  ∀ [interface : CInterface] (locals : CBody.Locals) (types : CLoops.Types) (locations : Locations)
    (definitions : CLoops.Calls.Definitions),
    @Setup interface locals definitions →
    ∀ (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap),
    LayoutBound locals locations layout → Represents locations layout heap values →
    Ready locals locations p plan layout heap → Finite.Executes p values result →
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound locals locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.body (.running f.tree.body locals types heap) .done) behavior ↔
        behavior = .terminates finalHeap

def ArtifactContract (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  Syntax.Denotes source f ∧ Syntax.Matches f p plan layout ∧ BodyCorrect f p plan layout

def BodyCorrectFor (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  ∀ [interface : CInterface] (locals : CBody.Locals) (types : CLoops.Types) (locations : Locations)
    (definitions : CLoops.Calls.Definitions),
    SetupFor (interface := interface) p locals definitions →
    ∀ (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap),
    LayoutBound locals locations layout → Represents locations layout heap values →
    Ready locals locations p plan layout heap → Finite.Executes p values result →
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound locals locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.body (.running f.tree.body locals types heap) .done) behavior ↔
        behavior = .terminates finalHeap

def ArtifactContractFor (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  Syntax.Denotes source f ∧ Syntax.Matches f p plan layout ∧ BodyCorrectFor f p plan layout

theorem body_correct_for (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (matched : Syntax.Matches f p plan layout) : BodyCorrectFor f p plan layout := by
  intro interface locals types locations definitions setup values result heap bound represented ready executed
  change f.tree.body = (emit p plan layout).code ++ [.ret none] at matched
  rw [matched]
  exact emit_refines_for locals types locations definitions p setup plan layout values
    result heap bound represented ready executed

theorem artifact_correct_for (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (printed : source = f.tree.render) (valid : f.valid = true)
    (matched : Syntax.Matches f p plan layout) : ArtifactContractFor source f p plan layout := by
  exact ⟨printed ▸ Syntax.render_denotes f valid, matched, body_correct_for f p plan layout matched⟩

theorem BodyCorrectFor.to_full (h : BodyCorrectFor f p plan layout) : BodyCorrect f p plan layout := by
  intro interface locals types locations definitions setup
  exact h locals types locations definitions (setup.restrict p)

theorem ArtifactContractFor.to_full (h : ArtifactContractFor source f p plan layout) :
    ArtifactContract source f p plan layout :=
  ⟨h.1, h.2.1, BodyCorrectFor.to_full h.2.2⟩

theorem body_correct (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (matched : Syntax.Matches f p plan layout) : BodyCorrect f p plan layout :=
  BodyCorrectFor.to_full (body_correct_for f p plan layout matched)

theorem artifact_correct (source : String) (f : Syntax.Function)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (printed : source = f.tree.render) (valid : f.valid = true)
    (matched : Syntax.Matches f p plan layout) : ArtifactContract source f p plan layout :=
  ArtifactContractFor.to_full (artifact_correct_for source f p plan layout printed valid matched)

end Rumoca.CTensor.Lowering
