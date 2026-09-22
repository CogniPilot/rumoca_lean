import RumocaC.TensorSquareTable
import RumocaC.TensorIVPContract

/-! Complete numerical calls on the actual printed definition table. The
library/lookup premises are discharged, not carried into the closed products.
Target header meanings, entry storage and finite arithmetic remain explicit.
The FMI runtime dictionary repair is required to instantiate those headers. -/
noncomputable section
namespace Rumoca.TensorKernel
open CTree CMemory CMemory.TensorView CTensor CTensor.Lowering Solve.Tensor

def ClosedProgramCall (p : Program Γ shape) (entry : ProgramEntry p) : Prop :=
  ∀ [interface : CInterface], CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
  ∀ (args : Arguments.Values), Arguments.Valid entry.function.parameters args →
  ∀ (locations : Locations) (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap),
  LayoutBound (Arguments.locals entry.function.parameters args) locations (Named.Layout.erase entry.layout) →
  Represents locations (Named.Layout.erase entry.layout) heap values →
  Ready (Arguments.locals entry.function.parameters args) locations p (Named.Plan.erase p entry.plan)
    (Named.Layout.erase entry.layout) heap → Finite.Executes p values result →
  ∃ finalHeap,
    Reads finalHeap (locations (emit p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)).result) result ∧
    Bound (Arguments.locals entry.function.parameters args) locations
      (emit p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)).result ∧
    (∀ q, Outside locations p (Named.Plan.erase p entry.plan) q → finalHeap q = heap q) ∧
    (Writable heap (locations (emit p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)).result)
        shape.volume →
      Writable finalHeap (locations (emit p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)).result)
        shape.volume) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling entry.function.name (Arguments.values entry.function.parameters args) heap .done) behavior ↔
      behavior = .terminates finalHeap

theorem close_program (p : Program Γ shape) (entry : ProgramEntry p)
    (valid : entry.function.valid = true)
    (found : definitions entry.function.name = some entry.function.tree)
    (libraries : ∀ [interface : CInterface], CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
      LibraryFor p definitions) : ClosedProgramCall p entry := by
  intro interface binaryHeader fillHeader args arguments locations values result heap bound represented ready executed
  exact (entry.correct_for valid).1.2 definitions (libraries binaryHeader fillHeader) found args arguments
    locations values result heap bound represented ready executed

theorem initial_closed (shape : Tensor.Shape) :
    ClosedProgramCall (ProgramFixture.IVPEntry.kernel shape).initialProgram
      (ProgramFixture.IVPEntry.plan shape).initial :=
  close_program _ _ (ProgramFixture.IVPEntry.plan_valid shape).1 (initial_defined shape)
    (fun _ _ => initial_library shape ‹_› ‹_›)

theorem derivative_closed (shape : Tensor.Shape) :
    ClosedProgramCall (ProgramFixture.IVPEntry.kernel shape).derivative
      (ProgramFixture.IVPEntry.plan shape).derivative :=
  close_program _ _ (ProgramFixture.IVPEntry.plan_valid shape).2.1 (derivative_defined shape)
    (fun _ _ => derivative_library shape ‹_› ‹_›)

def ClosedDiagonalCall (p : DiagonalProgram Γ shape) (entry : Lowering.DiagonalEntry p) : Prop :=
  ∀ [interface : CInterface], CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
  ∀ (args : Arguments.Values), Arguments.Valid entry.function.parameters args →
  ∀ (locations : Locations) (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap),
  LayoutBound (Arguments.locals entry.function.parameters args) locations (Named.Layout.erase entry.layout) →
  Represents locations (Named.Layout.erase entry.layout) heap values →
  Ready (Arguments.locals entry.function.parameters args) locations p.coefficients
    (Named.Plan.erase p.coefficients entry.plan) (Named.Layout.erase entry.layout) heap →
  Reserved locations entry.output.erase p.coefficients (Named.Plan.erase p.coefficients entry.plan)
    (Named.Layout.erase entry.layout) →
  Bound (Arguments.locals entry.function.parameters args) locations entry.output.erase →
  Writable heap (locations entry.output.erase) p.shape.volume → p.shape.volume < 2 ^ 64 →
  Finite.Executes p.coefficients values coefficients →
  ∃ finalHeap,
    Reads finalHeap (locations entry.output.erase) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
    Reads finalHeap (locations (emit p.coefficients (Named.Plan.erase p.coefficients entry.plan)
      (Named.Layout.erase entry.layout)).result) coefficients ∧
    (∀ q, DiagonalOutside locations p (Named.Plan.erase p.coefficients entry.plan) entry.output.erase q →
      finalHeap q = heap q) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling entry.function.name (Arguments.values entry.function.parameters args) heap .done) behavior ↔
      behavior = .terminates finalHeap

theorem diagonal_closed (shape : Tensor.Shape) :
    ClosedDiagonalCall (ArrayProfile.squareJacobianProgram shape) (ProgramFixture.IVPEntry.plan shape).diagonal := by
  intro interface binaryHeader fillHeader args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed
  exact (Lowering.DiagonalEntry.correct_for (ProgramFixture.IVPEntry.plan shape).diagonal
      (ProgramFixture.IVPEntry.plan_valid shape).2.2.1).1.2.2.2
    definitions (coefficient_library shape binaryHeader fillHeader) diagonal_defined
    (coefficient_diagonal_defined shape) args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed

/-- Every instantaneous Solve entry executes on the exact numerical table;
there is no unused-operation, entry-lookup or alternate-table premise. -/
structure ClosedIVPCalls (shape : Tensor.Shape) : Prop where
  initial : ClosedProgramCall (ProgramFixture.IVPEntry.kernel shape).initialProgram
    (ProgramFixture.IVPEntry.plan shape).initial
  derivative : ClosedProgramCall (ProgramFixture.IVPEntry.kernel shape).derivative
    (ProgramFixture.IVPEntry.plan shape).derivative
  diagonal : ClosedDiagonalCall (ArrayProfile.squareJacobianProgram shape)
    (ProgramFixture.IVPEntry.plan shape).diagonal

theorem ivp_closed (shape : Tensor.Shape) : ClosedIVPCalls shape :=
  ⟨initial_closed shape, derivative_closed shape, diagonal_closed shape⟩

end Rumoca.TensorKernel
