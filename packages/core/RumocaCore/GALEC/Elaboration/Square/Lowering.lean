import RumocaCore.GALEC.Elaboration.Surface
import RumocaCore.GALEC.SquareBodies

/-! Exact generic lowering of the surface square/clear/scatter loops.
Trailing skips are retained exactly as produced by the actual list lowerer;
the independent typing derivation certifies that result, not a body matcher. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration.Surface
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

def pointwiseSource (inputName rhsName : String) : AST.Statement :=
  unitLoop "k" (dimension inputName 1)
    [.assign (stateReference rhsName [iterator "k"])
      (.binary (.literal "*") (.reference (stateReference inputName [iterator "k"]))
        (.reference (stateReference inputName [iterator "k"])))]

def clearSource (jacobianName : String) : AST.Statement :=
  unitLoop "r" (dimension jacobianName 1)
    [unitLoop "c" (dimension jacobianName 2)
      [.assign (stateReference jacobianName [iterator "r", iterator "c"]) (.literal (.literal "0.0"))]]

def scatterSource (inputName jacobianName : String) : AST.Statement :=
  unitLoop "k" (dimension inputName 1)
    [.assign (stateReference jacobianName [iterator "k", iterator "k"])
      (.binary (.literal "+") (.reference (stateReference inputName [iterator "k"]))
        (.reference (stateReference inputName [iterator "k"])))]

def squareSource (inputName rhsName jacobianName : String) : List AST.Statement :=
  [pointwiseSource inputName rhsName, clearSource jacobianName, scatterSource inputName jacobianName]

def loweredPointwise (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩) :
    Statement inputs outputs bounds :=
  .bounded extent (.seq (.assign rhs vectorSubscripts (squaredInput.toTerm source vectorSubscripts)) .skip)

def loweredClear (jacobian : Ref outputs (matrixShape extent extent)) : Statement inputs outputs bounds :=
  .bounded extent (.seq
    (.bounded extent (.seq (.assign jacobian MatrixBodies.matrixSubscripts (.literal .zero)) .skip)) .skip)

def loweredScatter (source : Ref inputs ⟨[extent]⟩) (jacobian : Ref outputs (matrixShape extent extent)) :
    Statement inputs outputs bounds :=
  .bounded extent (.seq (.assign jacobian diagonalSubscripts (doubledInput.toTerm source vectorSubscripts)) .skip)

def loweredSquare (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) : Statement inputs outputs bounds :=
  .seq (loweredPointwise source rhs) (.seq (loweredClear jacobian) (.seq (loweredScatter source jacobian) .skip))

theorem pointwise_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (rhsBound : BindingTable.Resolves table [rhsName] ⟨_, .writable rhs⟩)
    (known : HasShape [inputName] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling) (fresh : Loops.Binder.Fresh names "k") :
    Bodies.StatementElaborates table HasShape ceiling names
      (pointwiseSource inputName rhsName) (loweredPointwise source rhs) := by
  have oneBound : 1 ≤ ceiling := by omega
  refine .loop (dimension_header names fresh known rfl positive within oneBound) (.cons (.assign ?_) .nil)
  refine AssignmentLowering.Elaborates.assign (target := ⟨_, rhs, vectorSubscripts⟩)
    (.writable (reference_typed table _ rhsBound (vector_indices "k" names))) ?_
  have inputTyped := ExpressionLowering.Elaborates.reference
    (read := ⟨_, .readOnly source, vectorSubscripts⟩)
    (reference_typed table _ inputBound (vector_indices "k" names))
  exact .binary .mul inputTyped inputTyped

theorem scatter_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : Ref inputs ⟨[extent]⟩) (jacobian : Ref outputs (matrixShape extent extent))
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (known : HasShape [inputName] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling) (fresh : Loops.Binder.Fresh names "k") :
    Bodies.StatementElaborates table HasShape ceiling names
      (scatterSource inputName jacobianName) (loweredScatter source jacobian) := by
  have oneBound : 1 ≤ ceiling := by omega
  refine .loop (dimension_header names fresh known rfl positive within oneBound) (.cons (.assign ?_) .nil)
  refine AssignmentLowering.Elaborates.assign (target := ⟨_, jacobian, diagonalSubscripts⟩)
    (.writable (reference_typed table _ jacobianBound (diagonal_indices "k" names))) ?_
  have inputTyped := ExpressionLowering.Elaborates.reference
    (read := ⟨_, .readOnly source, vectorSubscripts⟩)
    (reference_typed table _ inputBound (vector_indices "k" names))
  exact .binary .add inputTyped inputTyped

theorem clear_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (jacobian : Ref outputs (matrixShape extent extent))
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (known : HasShape [jacobianName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (rowFresh : Loops.Binder.Fresh names "r") (colFresh : Loops.Binder.Fresh names "c") :
    Bodies.StatementElaborates table HasShape ceiling names
      (clearSource jacobianName) (loweredClear jacobian) := by
  have oneBound : 1 ≤ ceiling := by omega
  refine .loop (dimension_header names rowFresh known rfl positive within oneBound) (.cons ?_ .nil)
  refine .loop (dimension_header _ (.cons (by decide) colFresh) known rfl positive within axisBound)
    (.cons (.assign ?_) .nil)
  refine AssignmentLowering.Elaborates.assign (target := ⟨_, jacobian, MatrixBodies.matrixSubscripts⟩)
    (.writable (reference_typed table _ jacobianBound (matrix_indices "r" "c" (by decide) names))) .zero

theorem square_typed (table : BindingTable inputs outputs)
    (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (rhsBound : BindingTable.Resolves table [rhsName] ⟨_, .writable rhs⟩)
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (inputKnown : HasShape [inputName] ⟨[extent]⟩)
    (jacobianKnown : HasShape [jacobianName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Bodies.BodyElaborates table HasShape ceiling .nil (squareSource inputName rhsName jacobianName)
      (loweredSquare source rhs jacobian) :=
  .cons (pointwise_typed table .nil source rhs inputBound rhsBound inputKnown positive within .nil)
    (.cons (clear_typed table .nil jacobian jacobianBound jacobianKnown positive within axisBound .nil .nil)
      (.cons (scatter_typed table .nil source jacobian inputBound jacobianBound inputKnown positive within .nil) .nil))

end Rumoca.GALEC.Elaboration.Square
