import RumocaC.TensorSquareIVPEntry
import RumocaC.TreeTable
import RumocaC.TensorProgramCalls

/-! The prepared square numerical product's exact ordered C function trees.
Only helper operations used by its indexed programs are required. This owner
consumes the core IVP and supplies no source resolution or solver policy.
The compiler separately binds these trees to independently read artifact bytes. -/
namespace Rumoca.TensorKernel
open CTree CTensor CTensor.Lowering CCalls.TreeTable

def functions : List Function :=
  [Fill.function, CTensor.function .add, CTensor.function .mul, Diagonal.function,
   (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).initial.function.tree,
   (ProgramFixture.IVPEntry.plan ArrayProfile.stateShape).derivative.function.tree,
   ProgramFixture.DiagonalEntry.profile.tree, SquareDiagonal.function]

theorem functions_unique : (functions.map (fun f => f.signature.name)).Nodup := by
  decide +kernel

def definitions : CLoops.Calls.Definitions := treeDefinitions functions

theorem defined_member (fn : Function) (member : fn ∈ functions) :
    definitions fn.signature.name = some fn :=
  lookup_member functions fn functions_unique member

theorem fill_defined : definitions Fill.function.signature.name = some Fill.function :=
  defined_member _ (by simp [functions])

theorem binary_defined (op : Tensor.BinaryOp) (used : op = .add ∨ op = .mul) :
    definitions (CTensor.function op).signature.name = some (CTensor.function op) := by
  rcases used with rfl | rfl
  all_goals exact defined_member _ (by simp [functions])

theorem diagonal_defined : definitions Diagonal.function.signature.name = some Diagonal.function :=
  defined_member _ (by simp [functions])

theorem initial_defined (shape : Tensor.Shape) :
    definitions (ProgramFixture.IVPEntry.plan shape).initial.function.name =
      some (ProgramFixture.IVPEntry.plan shape).initial.function.tree :=
  defined_member _ (by simp [functions]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) )

theorem derivative_defined (shape : Tensor.Shape) :
    definitions (ProgramFixture.IVPEntry.plan shape).derivative.function.name =
      some (ProgramFixture.IVPEntry.plan shape).derivative.function.tree :=
  defined_member _ (by simp [functions]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) )

theorem coefficient_diagonal_defined (shape : Tensor.Shape) :
    definitions (Lowering.DiagonalEntry.function (ProgramFixture.IVPEntry.plan shape).diagonal).name =
      some (Lowering.DiagonalEntry.function (ProgramFixture.IVPEntry.plan shape).diagonal).tree := by
  rw [ProgramFixture.IVPEntry.jacobian_function]
  exact defined_member ProgramFixture.DiagonalEntry.profile.tree (by simp [functions])

theorem square_diagonal_defined :
    definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function :=
  defined_member _ (by simp [functions])

theorem initial_required (shape : Tensor.Shape) :
    requiredOps (ProgramFixture.IVPEntry.kernel shape).initialProgram = [] := rfl

theorem derivative_required (shape : Tensor.Shape) :
    requiredOps (ProgramFixture.IVPEntry.kernel shape).derivative = [.mul] := rfl

theorem coefficient_required (shape : Tensor.Shape) :
    requiredOps (ArrayProfile.squareJacobianProgram shape).coefficients = [.mul, .mul, .mul, .add] := rfl

variable [interface : CInterface]

theorem initial_library (shape : Tensor.Shape)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor (ProgramFixture.IVPEntry.kernel shape).initialProgram definitions := by
  refine ⟨binaryHeader, fillHeader, ?_, fill_defined⟩
  intro op used
  simp [initial_required] at used

theorem derivative_library (shape : Tensor.Shape)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor (ProgramFixture.IVPEntry.kernel shape).derivative definitions := by
  refine ⟨binaryHeader, fillHeader, ?_, fill_defined⟩
  intro op used
  have eq : op = .mul := by simpa [derivative_required] using used
  exact binary_defined op (Or.inr eq)

theorem coefficient_library (shape : Tensor.Shape)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface) :
    LibraryFor (ArrayProfile.squareJacobianProgram shape).coefficients definitions := by
  refine ⟨binaryHeader, fillHeader, ?_, fill_defined⟩
  intro op used
  have allowed : op = .mul ∨ op = .add := by simpa [coefficient_required] using used
  exact binary_defined op allowed.symm

end Rumoca.TensorKernel
