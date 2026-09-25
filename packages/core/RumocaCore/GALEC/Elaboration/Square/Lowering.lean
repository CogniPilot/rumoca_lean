import RumocaCore.GALEC.Elaboration.Surface
import RumocaCore.GALEC.SquareBodies

/-! Exact generic lowering of the surface square/clear/scatter loops and of the
checked DoStep body that guards them with finiteness checks and `OVERFLOW`.
Trailing skips are retained exactly as produced by the actual list lowerer;
the independent typing derivation certifies that result, not a body matcher. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration.Surface
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

/-- The product `self.u[k] * self.u[k]` of the input at the loop index. -/
def productSource (inputName : String) : AST.Expr :=
  .binary (.literal "*") (.reference (stateReference inputName [iterator "k"]))
    (.reference (stateReference inputName [iterator "k"]))

/-- The sum `self.u[k] + self.u[k]` of the input at the loop index. -/
def sumSource (inputName : String) : AST.Expr :=
  .binary (.literal "+") (.reference (stateReference inputName [iterator "k"]))
    (.reference (stateReference inputName [iterator "k"]))

def pointwiseSource (inputName rhsName : String) : AST.Statement :=
  unitLoop "k" (dimension inputName 1)
    [.assign (stateReference rhsName [iterator "k"]) (productSource inputName)]

def clearSource (jacobianName : String) : AST.Statement :=
  unitLoop "r" (dimension jacobianName 1)
    [unitLoop "c" (dimension jacobianName 2)
      [.assign (stateReference jacobianName [iterator "r", iterator "c"]) (.literal (.number "0.0"))]]

def scatterSource (inputName jacobianName : String) : AST.Statement :=
  unitLoop "k" (dimension inputName 1)
    [.assign (stateReference jacobianName [iterator "k", iterator "k"]) (sumSource inputName)]

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

/-- The canonical spelling of the predefined `OVERFLOW` signal. -/
def overflowName : AST.Name := .ident Signal.overflow.name

/-- The set that `OVERFLOW` names. -/
def overflowSet : SignalSet := .ofList [.overflow]

/-- `if isFinite(e) then else signal OVERFLOW; end if;` -/
def guardSource (argument : AST.Expr) : AST.Statement :=
  .ifThen [(.expr (.call (.ident Names.finiteTest) [argument]), [])] (some [.signal [overflowName]])

/-- The read-only preflight: every product and every sum of the input is
checked, in one loop and before any write. -/
def preflightSource (inputName : String) : AST.Statement :=
  unitLoop "k" (dimension inputName 1)
    [guardSource (productSource inputName), guardSource (sumSource inputName)]

/-- The checked DoStep body: the preflight; then, when a check failed, the
check `signal in OVERFLOW` unsets the signal and its body sets it again, so it
reaches the method exit; otherwise the square body runs. -/
def checkedSource (inputName rhsName jacobianName : String) : List AST.Statement :=
  [preflightSource inputName,
   .ifThen [(.signalCheck none false [overflowName] none, [.signal [overflowName]])]
     (some (squareSource inputName rhsName jacobianName))]

def loweredGuard (term : ScalarTerm inputs outputs bounds) : Statement inputs outputs bounds :=
  .branch (.finite term) .skip (.seq (.signal overflowSet) .skip)

def loweredPreflight (source : Ref inputs ⟨[extent]⟩) : Statement inputs outputs bounds :=
  .bounded extent (.seq (loweredGuard (squaredInput.toTerm source vectorSubscripts))
    (.seq (loweredGuard (doubledInput.toTerm source vectorSubscripts)) .skip))

def loweredChecked (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent)) : Statement inputs outputs bounds :=
  .seq (loweredPreflight source)
    (.seq (.branch (.signalIn overflowSet) (.seq (.signal overflowSet) .skip)
      (loweredSquare source rhs jacobian)) .skip)

theorem product_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : Ref inputs ⟨[extent]⟩)
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩) :
    ExpressionLowering.Elaborates table (.cons (bound := extent) "k" names) (productSource inputName)
      (squaredInput.toTerm source vectorSubscripts) := by
  have inputTyped := ExpressionLowering.Elaborates.reference
    (read := ⟨_, .readOnly source, vectorSubscripts⟩)
    (reference_typed table _ inputBound (vector_indices "k" names))
  exact .binary .mul inputTyped inputTyped

theorem sum_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : Ref inputs ⟨[extent]⟩)
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩) :
    ExpressionLowering.Elaborates table (.cons (bound := extent) "k" names) (sumSource inputName)
      (doubledInput.toTerm source vectorSubscripts) := by
  have inputTyped := ExpressionLowering.Elaborates.reference
    (read := ⟨_, .readOnly source, vectorSubscripts⟩)
    (reference_typed table _ inputBound (vector_indices "k" names))
  exact .binary .add inputTyped inputTyped

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
  exact AssignmentLowering.Elaborates.assign (target := ⟨_, rhs, vectorSubscripts⟩)
    (.writable (reference_typed table _ rhsBound (vector_indices "k" names)))
    (product_typed table names source inputBound)

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
  exact AssignmentLowering.Elaborates.assign (target := ⟨_, jacobian, diagonalSubscripts⟩)
    (.writable (reference_typed table _ jacobianBound (diagonal_indices "k" names)))
    (sum_typed table names source inputBound)

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

theorem overflow_denotes : SignalNames.Denotes [overflowName] overflowSet := ⟨[.overflow], rfl, rfl⟩

theorem guard_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (typed : ExpressionLowering.Elaborates table names argument term) :
    Bodies.StatementElaborates table HasShape ceiling names (guardSource argument) (loweredGuard term) :=
  .branch (.cons (.finite typed) .nil (.otherwise (.cons (.signal overflow_denotes) .nil)))

theorem preflight_typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : Ref inputs ⟨[extent]⟩)
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (known : HasShape [inputName] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling) (fresh : Loops.Binder.Fresh names "k") :
    Bodies.StatementElaborates table HasShape ceiling names
      (preflightSource inputName) (loweredPreflight source) := by
  have oneBound : 1 ≤ ceiling := by omega
  exact .loop (dimension_header names fresh known rfl positive within oneBound)
    (.cons (guard_typed table _ (product_typed table names source inputBound))
      (.cons (guard_typed table _ (sum_typed table names source inputBound)) .nil))

theorem checked_typed (table : BindingTable inputs outputs)
    (source : Ref inputs ⟨[extent]⟩) (rhs : Ref outputs ⟨[extent]⟩)
    (jacobian : Ref outputs (matrixShape extent extent))
    (inputBound : BindingTable.Resolves table [inputName] ⟨_, .readOnly source⟩)
    (rhsBound : BindingTable.Resolves table [rhsName] ⟨_, .writable rhs⟩)
    (jacobianBound : BindingTable.Resolves table [jacobianName] ⟨_, .writable jacobian⟩)
    (inputKnown : HasShape [inputName] ⟨[extent]⟩)
    (jacobianKnown : HasShape [jacobianName] (matrixShape extent extent))
    (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Bodies.BodyElaborates table HasShape ceiling .nil (checkedSource inputName rhsName jacobianName)
      (loweredChecked source rhs jacobian) :=
  .cons (preflight_typed table .nil source inputBound inputKnown positive within .nil)
    (.cons (.branch (.cons (.signalIn overflow_denotes) (.cons (.signal overflow_denotes) .nil)
      (.otherwise (square_typed table source rhs jacobian inputBound rhsBound jacobianBound
        inputKnown jacobianKnown positive within axisBound)))) .nil)

end Rumoca.GALEC.Elaboration.Square
