import RumocaCore.GALEC.Elaboration.Square.Execution
import RumocaCore.GALEC.Elaboration.Layout.Execution
import RumocaCore.GALEC.Elaboration.Layout.NoAlias

/-! A concrete, non-enumerating declaration/table instance for the existing
square repair. Roles below are an explicit logical execution configuration,
NOT a proof that the normative method-permission policy accepts it. The AST
declarations still need actual scanner/parser and emitted-text provenance. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

def squareDeclarations (extent : Nat) : List AST.Declaration :=
  [⟨.public, .input, .variable, .literal "Real", [.literal (toString extent)], .ident "u"⟩,
   ⟨.public, .output, .variable, .literal "Real", [.literal (toString extent)], .ident "x"⟩,
   ⟨.public, .output, .variable, .literal "Real", [.literal (toString extent), .literal (toString extent)], .ident "J"⟩,
   ⟨.protected, .local, .constant, .literal "Real", [], .ident "samplePeriod"⟩]

def squareFields (extent : Nat) : List Layout.Field :=
  [⟨⟨"u", .public, .input, .variable, ⟨[extent]⟩⟩, .readOnly⟩,
   ⟨⟨"x", .public, .output, .variable, ⟨[extent]⟩⟩, .writable⟩,
   ⟨⟨"J", .public, .output, .variable, matrixShape extent extent⟩, .writable⟩,
   ⟨⟨"samplePeriod", .protected, .local, .constant, ⟨[]⟩⟩, .readOnly⟩]

theorem square_declared (positive : 0 < extent) (within : extent ≤ ceiling) :
    Declarations.Real.DeclaresAll ceiling (squareDeclarations extent)
      ((squareFields extent).map Layout.Field.declaration) := by
  have axis : Declarations.Extents.AxisDenotes ceiling (.literal (toString extent)) extent :=
    .literal (_root_.Parser.DecimalNat.render_denotes extent) positive within
  exact .cons (.real (.cons axis .nil))
    (.cons (.real (.cons axis .nil))
      (.cons (.real (.cons axis (.cons axis .nil)))
        (.cons (.real .nil) .nil (by simp)) (by simp)) (by simp)) (by simp)

def squareInput (extent : Nat) : Ref (Layout.inputShapes (squareFields extent)) ⟨[extent]⟩ := .here
def squareRhs (extent : Nat) : Ref (Layout.outputShapes (squareFields extent)) ⟨[extent]⟩ := .here
def squareJacobian (extent : Nat) : Ref (Layout.outputShapes (squareFields extent)) (matrixShape extent extent) :=
  .there .here

theorem input_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (squareFields extent)) ["u"] ⟨_, .readOnly (squareInput extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

theorem rhs_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (squareFields extent)) ["x"] ⟨_, .writable (squareRhs extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

theorem jacobian_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (squareFields extent)) ["J"] ⟨_, .writable (squareJacobian extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

theorem input_known (positive : 0 < extent) (within : extent ≤ ceiling) :
    Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent) ["u"] ⟨[extent]⟩ :=
  (Layout.bindingShape_iff_source _ (square_declared positive within) _ _).mp rfl

theorem jacobian_known (positive : 0 < extent) (within : extent ≤ ceiling) :
    Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent) ["J"] (matrixShape extent extent) :=
  (Layout.bindingShape_iff_source _ (square_declared positive within) _ _).mp rfl

/-- No caller-supplied binding or shape oracle: all are built from these
ordered, independently validated declarations. The extent is not enumerated. -/
theorem layout_body_lowered (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling) :
    Layout.body (squareFields extent) ceiling (squareSource "u" "x" "J") =
      some (loweredSquare (squareInput extent) (squareRhs extent) (squareJacobian extent)) :=
  square_lowered _ _ _ (Layout.bindingShape_iff_source _ (square_declared positive within))
    _ _ _ (input_bound extent) (rhs_bound extent) (jacobian_bound extent)
    (input_known positive within) (jacobian_known positive within) positive within axisBound

theorem layout_source_executes (positive : 0 < extent) (within : extent ≤ ceiling) (axisBound : 2 ≤ ceiling)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (squareFields extent))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (squareFields extent))) :
    Bodies.Source.statements (Layout.bindings (squareFields extent))
      (Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent)) ceiling step zero one
      @input .nil @env (squareSource "u" "x" "J") @before @after ↔
    (SquareBodies.body (squareInput extent) (squareRhs extent) (squareJacobian extent)).Executes
      step zero one @input @env @before @after :=
  square_source_executes _ _ _ (Layout.bindingShape_iff_source _ (square_declared positive within))
    _ _ _ (input_bound extent) (rhs_bound extent) (jacobian_bound extent)
    (input_known positive within) (jacobian_known positive within) positive within axisBound
    step zero one @input @env @before @after

end Rumoca.GALEC.Elaboration.Square
