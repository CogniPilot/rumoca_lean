import RumocaC.TensorDiagonalProgramCalls
import RumocaC.TensorProgramPrinter

namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

def DiagonalCallCorrect (f : Syntax.Function) (p : DiagonalProgram Γ shape)
    (plan : Plan p.coefficients) (layout : Layout Γ) (output : Buffer p.shape) : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions),
    @Library interface definitions → definitions Diagonal.function.signature.name = some Diagonal.function →
    definitions f.name = some f.tree → ∀ args, Arguments.Valid f.parameters args →
    ∀ (locations : Locations) (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap),
    LayoutBound (Arguments.locals f.parameters args) locations layout → Represents locations layout heap values →
    Ready (Arguments.locals f.parameters args) locations p.coefficients plan layout heap →
    Reserved locations output p.coefficients plan layout → Bound (Arguments.locals f.parameters args) locations output →
    Writable heap (locations output) p.shape.volume → p.shape.volume < 2 ^ 64 →
    Finite.Executes p.coefficients values coefficients →
    ∃ finalHeap, Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      (∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
        behavior = .terminates finalHeap

def DiagonalArtifactContract (source : String) (f : Syntax.Function) (p : DiagonalProgram Γ shape)
    (plan : Plan p.coefficients) (layout : Layout Γ) (output : Buffer p.shape) : Prop :=
  Syntax.Denotes source f ∧ DiagonalScope f ∧ DiagonalMatches f p plan layout output ∧
    DiagonalCallCorrect f p plan layout output

theorem diagonal_artifact_correct (source : String) (f : Syntax.Function) (p : DiagonalProgram Γ shape)
    (plan : Plan p.coefficients) (layout : Layout Γ) (output : Buffer p.shape)
    (printed : source = f.tree.render) (valid : f.valid = true) (scope : DiagonalScope f)
    (matched : DiagonalMatches f p plan layout output) : DiagonalArtifactContract source f p plan layout output := by
  refine ⟨printed ▸ Syntax.render_denotes f valid, scope, matched, ?_⟩
  intro interface definitions library diagonalDefined found args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed
  exact diagonal_call_refines f valid scope p plan layout output matched definitions library diagonalDefined found
    args arguments locations values coefficients heap bound represented ready reserved outputBound writable bounded executed

end Rumoca.CTensor.Lowering
