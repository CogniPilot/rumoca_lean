import RumocaCore.GALEC.Elaboration.Square.Layout
import RumocaCore.GALEC.Elaboration.Scalar.Preparation

/-! The tensor square block as a source tree, and its preparation by the generic
whole-block preparer, for every positive state extent within the ceiling. Loops
keep rank and extents through `size` queries; no tensor cell is enumerated. -/
namespace Rumoca.GALEC.Elaboration.Square
open Elaboration Rumoca.Tensor

/-- Startup clears the state output `x` and the Jacobian output `J`, then sets
the sample period. -/
def startupMethod : AST.Method :=
  ⟨.ident "Startup", [], Initialization.Body.source Names.state "J" Names.clock, .ident "Startup"⟩

/-- DoStep exposes `OVERFLOW`. It first checks that every product `u[k] * u[k]`
and every sum `u[k] + u[k]` is finite, writing nothing; if a check fails it
signals `OVERFLOW` and writes nothing, and otherwise it assigns the pointwise
product to `x`, clears `J` and scatters the diagonal coefficients `u[k] + u[k]`. -/
def stepMethod : AST.Method :=
  ⟨.ident "DoStep", [overflowName], checkedSource "u" Names.state "J", .ident "DoStep"⟩

/-- The tensor square block for a state extent: input `u`, outputs `x` and `J`,
the protected sample period, and the Startup, Recalibrate and DoStep methods. -/
def source (extent : Nat) : AST.Block :=
  ⟨.ident Names.squareBlock, squarePublic extent, squareProtected,
    [startupMethod, Scalar.recalibrateMethod, stepMethod], .ident Names.squareBlock⟩

def startupResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨startupFields extent, Initialization.Body.lowered
    (startupRhs extent) (startupJacobian extent) (startupPeriod extent)⟩

def recalibrateResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨squareFields extent, .skip⟩

def stepResult (extent : Nat) : Methods.Preparation.Result :=
  ⟨squareFields extent, loweredChecked (squareInput extent) (squareRhs extent) (squareJacobian extent)⟩

/-- The square method results under a header interface. -/
def preparedResult (extent : Nat) (interface : Block.Headers.Interface) : Block.Result :=
  ⟨interface, startupResult extent, recalibrateResult extent, stepResult extent⟩

/-- The three selected methods of the square block. -/
def interface : Block.Headers.Interface :=
  ⟨Names.squareBlock, startupMethod, Scalar.recalibrateMethod, stepMethod⟩

/-- Startup and Recalibrate expose no signal. -/
theorem startup_exposes : Reach.Exposes startupMethod SignalSet.empty :=
  (Reach.exposed_iff _ _).mp (by decide +kernel)

theorem recalibrate_exposes : Reach.Exposes Scalar.recalibrateMethod SignalSet.empty :=
  Reach.exposes_empty _ rfl .nil

/-- DoStep exposes exactly `OVERFLOW`, the out-reachable set of its body (§1.3). -/
theorem step_exposes : Reach.Exposes stepMethod overflowSet :=
  (Reach.exposed_iff _ _).mp (by decide +kernel)

/-- The square block prepares to the square method results for every positive
extent within the ceiling; the extent is never enumerated. -/
theorem prepared (positive : 0 < extent) (within : extent ≤ ceiling)
    (axisBound : 2 ≤ ceiling) :
    Block.Prepares ceiling (source extent) (preparedResult extent interface) := by
  have declared := square_declared positive within
  refine ⟨(Block.Headers.read_iff _ _).mp rfl, ?_, ?_, ?_⟩
  · exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) startup_exposes declared
      ((Layout.body_iff _ (Methods.Preparation.declared_fields _ declared) _ _).mp
        (startup_lowered positive within axisBound))
  · show Methods.Preparation.Prepares _ Capabilities.DoStep.role ceiling (source extent)
      ⟨Capabilities.Generic.fields Capabilities.DoStep.role
        ((squareFields extent).map Layout.Field.declaration), .skip⟩
    exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) recalibrate_exposes declared .nil
  · show Methods.Preparation.Prepares _ Capabilities.DoStep.role ceiling (source extent)
      ⟨Capabilities.Generic.fields Capabilities.DoStep.role
        ((squareFields extent).map Layout.Field.declaration),
        loweredChecked (squareInput extent) (squareRhs extent) (squareJacobian extent)⟩
    exact .body ((Methods.Headers.select_iff _ _ _).mp rfl) step_exposes declared
      ((Layout.body_iff _ (Methods.Preparation.declared_fields Capabilities.DoStep.role
        declared) _ _).mp (layout_body_lowered positive within axisBound))

end Rumoca.GALEC.Elaboration.Square
