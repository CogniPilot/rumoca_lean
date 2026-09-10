import RumocaC.TypedCallProofs
import RumocaC.TensorProgramCallContract
import RumocaC.TensorDiagonalProgramContract

/-! Prepared Solve programs retain their exact result and memory frame under
typed calls, including arbitrary caller continuations and standalone behavior.
These contracts derive from complete finite executions of the actual trees;
they do not supply storage, header bindings or FMI lifecycle policy. -/

namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

/-- The same prepared-program contract in the typed, value-returning call
machine. Definition-table/header and storage premises remain explicit. -/
def TypedCallCorrect (f : Syntax.Function) (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions) (target : CCalls.Program),
    CCalls.Typed.Extends definitions target → @Library interface definitions → definitions f.name = some f.tree →
    ∀ (args : Arguments.Values), Arguments.Valid f.parameters args →
    ∀ (locations : Locations) (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap),
    LayoutBound (Arguments.locals f.parameters args) locations layout → Represents locations layout heap values →
    Ready (Arguments.locals f.parameters args) locations p plan layout heap → Finite.Executes p values result →
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound (Arguments.locals f.parameters args) locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      CCalls.Typed.CallResult target f.name (Arguments.values f.parameters args) heap finalHeap

theorem typed_call_correct (h : CallCorrect f p plan layout) : TypedCallCorrect f p plan layout := by
  intro interface definitions target linked library found args arguments locations values result heap
    bound represented ready executed
  obtain ⟨finalHeap, reads, resultBound, frame, behavior⟩ := h definitions library found args arguments
    locations values result heap bound represented ready executed
  exact ⟨finalHeap, reads, resultBound, frame,
    CCalls.Typed.loop_call_result target definitions linked ((behavior _).mpr rfl)⟩

def TypedDiagonalCallCorrect (f : Syntax.Function) (p : DiagonalProgram Γ shape)
    (plan : Plan p.coefficients) (layout : Layout Γ) (output : Buffer p.shape) : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions) (target : CCalls.Program),
    CCalls.Typed.Extends definitions target → @Library interface definitions →
    definitions Diagonal.function.signature.name = some Diagonal.function →
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
      CCalls.Typed.CallResult target f.name (Arguments.values f.parameters args) heap finalHeap

theorem typed_diagonal_call_correct (h : DiagonalCallCorrect f p plan layout output) :
    TypedDiagonalCallCorrect f p plan layout output := by
  intro interface definitions target linked library diagonalDefined found args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed
  obtain ⟨finalHeap, reads, coefficientReads, frame, behavior⟩ := h definitions library diagonalDefined found
    args arguments locations values coefficients heap bound represented ready reserved outputBound writable bounded executed
  exact ⟨finalHeap, reads, coefficientReads, frame,
    CCalls.Typed.loop_call_result target definitions linked ((behavior _).mpr rfl)⟩

end Rumoca.CTensor.Lowering
