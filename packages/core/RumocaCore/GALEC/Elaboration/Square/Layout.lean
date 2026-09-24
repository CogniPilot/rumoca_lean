import RumocaCore.GALEC.Elaboration.Square.Execution
import RumocaCore.GALEC.Elaboration.Layout.Execution
import RumocaCore.GALEC.Elaboration.Layout.NoAlias
import RumocaCore.GALEC.Elaboration.Initialization.Body
import RumocaCore.GALEC.Elaboration.Capabilities.Initialization

/-! A concrete, non-enumerating declaration/table instance for the existing
square repair. Roles below are an explicit logical execution configuration,
NOT a proof that the normative method-permission policy accepts it. The AST
declarations still need actual scanner/parser and emitted-text provenance. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor Rumoca.Solve.Tensor Coefficients VectorBodies

def squarePublic (extent : Nat) : List AST.Declaration :=
  [⟨.input, .literal "Real", [Surface.natural extent], .ident "u"⟩,
   ⟨.output, .literal "Real", [Surface.natural extent], .ident "x"⟩,
   ⟨.output, .literal "Real", [Surface.natural extent, Surface.natural extent], .ident "J"⟩]

def squareProtected : List AST.Declaration :=
  [⟨.constant, .literal "Real", [], .ident "samplePeriod"⟩]

/-- The declarations of a block with sections `squarePublic` and `squareProtected`. -/
def squareDeclarations (extent : Nat) : List (AST.Visibility × AST.Declaration) :=
  (squarePublic extent).map (.public, ·) ++ squareProtected.map (.protected, ·)

def squareFields (extent : Nat) : List Layout.Field :=
  [⟨⟨"u", .public, .input, ⟨[extent]⟩⟩, .readOnly⟩,
   ⟨⟨"x", .public, .output, ⟨[extent]⟩⟩, .writable⟩,
   ⟨⟨"J", .public, .output, matrixShape extent extent⟩, .writable⟩,
   ⟨⟨"samplePeriod", .protected, .constant, ⟨[]⟩⟩, .readOnly⟩]

theorem square_declared (positive : 0 < extent) (within : extent ≤ ceiling) :
    Declarations.Real.DeclaresAll ceiling (squareDeclarations extent)
      ((squareFields extent).map Layout.Field.declaration) := by
  have axis := Declarations.Extents.natural_denotes positive within
  exact .cons (.real (by decide) (.cons axis .nil))
    (.cons (.real (by decide) (.cons axis .nil))
      (.cons (.real (by decide) (.cons axis (.cons axis .nil)))
        (.cons (.real (by decide) .nil) .nil (by simp)) (by simp)) (by simp)) (by simp)

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

theorem rhs_known (positive : 0 < extent) (within : extent ≤ ceiling) :
    Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent) ["x"] ⟨[extent]⟩ :=
  (Layout.bindingShape_iff_source _ (square_declared positive within) _ _).mp rfl

/-! The same four declarations in the Startup role layout that whole-block
preparation uses: the input stays read-only while the state, Jacobian and
scalar constant are writable. The extent is a parameter and never enumerated. -/

def startupFields (extent : Nat) : List Layout.Field :=
  Capabilities.Initialization.fields ((squareFields extent).map Layout.Field.declaration)

def startupRhs (extent : Nat) : Ref (Layout.outputShapes (startupFields extent)) ⟨[extent]⟩ := .here
def startupJacobian (extent : Nat) :
    Ref (Layout.outputShapes (startupFields extent)) (matrixShape extent extent) := .there .here
def startupPeriod (extent : Nat) : Ref (Layout.outputShapes (startupFields extent)) scalar :=
  .there (.there .here)

theorem startup_rhs_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (startupFields extent)) ["x"]
      ⟨_, .writable (startupRhs extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

theorem startup_jacobian_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (startupFields extent)) ["J"]
      ⟨_, .writable (startupJacobian extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

theorem startup_period_bound (extent : Nat) :
    BindingTable.Resolves (Layout.bindings (startupFields extent)) ["samplePeriod"]
      ⟨_, .writable (startupPeriod extent)⟩ :=
  (BindingTable.lookup_iff _ _ _).mp rfl

/-- Generic lowering, with no caller-supplied shape oracle or target bindings. -/
theorem startup_lowered (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) :
    Layout.body (startupFields extent) ceiling (Initialization.Body.source "x" "J" "samplePeriod") =
      some (Initialization.Body.lowered (startupRhs extent) (startupJacobian extent)
        (startupPeriod extent)) :=
  Initialization.Body.lower _ _ _
    (Layout.bindingShape_iff_source (startupFields extent) (by
      rw [startupFields, Capabilities.Initialization.fields_declarations]
      exact square_declared positive within))
    _ _ _ (startup_rhs_bound extent) (startup_jacobian_bound extent) (startup_period_bound extent)
    (rhs_known positive within) (jacobian_known positive within) positive within axisBound

theorem startup_source_executes (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α (Layout.inputShapes (startupFields extent))) (env : IteratorEnv [])
    (before after : Env α (Layout.outputShapes (startupFields extent))) :
    Bodies.Source.statements (Layout.bindings (startupFields extent))
      (Declarations.ShapeLookup.HasShape ceiling (squareDeclarations extent)) ceiling step zero one
      @input .nil @env (Initialization.Body.source "x" "J" "samplePeriod") @before @after ↔
      InitializationBodies.Initializes (startupRhs extent) (startupJacobian extent)
        (startupPeriod extent) zero one @before @after :=
  Initialization.Body.source_executes _ _ _
    (Layout.bindingShape_iff_source (startupFields extent) (by
      rw [startupFields, Capabilities.Initialization.fields_declarations]
      exact square_declared positive within))
    _ _ _ (startup_rhs_bound extent) (startup_jacobian_bound extent) (startup_period_bound extent)
    (rhs_known positive within) (jacobian_known positive within) positive within axisBound
    step zero one @input @env @before @after

end Rumoca.GALEC.Elaboration.Square
