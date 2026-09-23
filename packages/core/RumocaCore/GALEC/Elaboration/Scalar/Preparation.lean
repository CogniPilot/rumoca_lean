import RumocaCore.GALEC.Elaboration.Methods.Preparation
import RumocaCore.GALEC.Elaboration.Capabilities.Initialization
import RumocaCore.GALEC.Elaboration.Capabilities.DoStep.Policy
import RumocaCore.GALEC.Elaboration.Surface
import GALECParser.ProfileProjection

/-! Universal compatibility of the original scalar AST with generic named
method preparation. The embedding is proof data, not a runtime body matcher.
No new parser, source admission, lifecycle or actual-artifact claim. -/
namespace Rumoca.GALEC.Elaboration.Scalar
open Elaboration Elaboration.Surface Rumoca.Tensor Rumoca.Solve.Tensor

def declarations (b : Syntax.Block) : List Declarations.Real.Descriptor :=
  [⟨b.state, .public, .output, .variable, scalar⟩,
   ⟨b.clock, .protected, .local, .constant, scalar⟩]

def startupFields (b : Syntax.Block) : List Layout.Field :=
  Capabilities.Generic.fields Capabilities.Initialization.role (declarations b)

def stepFields (b : Syntax.Block) : List Layout.Field :=
  Capabilities.Generic.fields Capabilities.DoStep.role (declarations b)

def startupState (b : Syntax.Block) : Ref (Layout.outputShapes (startupFields b)) scalar := .here
def startupClock (b : Syntax.Block) : Ref (Layout.outputShapes (startupFields b)) scalar := .there .here
def stepState (b : Syntax.Block) : Ref (Layout.outputShapes (stepFields b)) scalar := .here

def startupResult (b : Syntax.Block) : Methods.Preparation.Result :=
  ⟨startupFields b, .seq (.assign (startupState b) .nil (.literal .zero))
    (.seq (.assign (startupClock b) .nil (.literal .one)) .skip)⟩

def recalibrateResult (b : Syntax.Block) : Methods.Preparation.Result :=
  ⟨stepFields b, .skip⟩

def stepResult (b : Syntax.Block) : Methods.Preparation.Result :=
  ⟨stepFields b, .seq (.assign (stepState b) .nil
    (.binary .add (.output (stepState b) .nil) (.literal .one))) .skip⟩

theorem declared (b : Syntax.Block) (different : b.state ≠ b.clock) (ceiling : Nat) :
    Declarations.Real.DeclaresAll ceiling (ProfileProjection.ofScalar b).declarations
      (declarations b) :=
  .cons (.real .nil) (.cons (.real .nil) .nil (by simp)) (by simpa [declarations] using different)

theorem startup_state_bound (b : Syntax.Block) :
    BindingTable.Resolves (Layout.bindings (startupFields b)) [b.state]
      ⟨scalar, .writable (startupState b)⟩ := .here

theorem startup_clock_bound (b : Syntax.Block) (different : b.state ≠ b.clock) :
    BindingTable.Resolves (Layout.bindings (startupFields b)) [b.clock]
      ⟨scalar, .writable (startupClock b)⟩ :=
  .there (by simpa using Ne.symm different) .here

theorem step_state_bound (b : Syntax.Block) :
    BindingTable.Resolves (Layout.bindings (stepFields b)) [b.state]
      ⟨scalar, .writable (stepState b)⟩ := .here

theorem startup_selected (b : Syntax.Block) :
    Methods.Headers.Selects (.literal "Startup") (ProfileProjection.ofScalar b).methods
      (ProfileProjection.startup b.initialState b.initialClock) :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem recalibrate_selected (b : Syntax.Block) :
    Methods.Headers.Selects (.literal "Recalibrate") (ProfileProjection.ofScalar b).methods
      ProfileProjection.recalibrate :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem step_selected (b : Syntax.Block) :
    Methods.Headers.Selects (.literal "DoStep") (ProfileProjection.ofScalar b).methods
      (ProfileProjection.scalarStep b.stepTarget b.stepRead) :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem startup_typed (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Bodies.BodyElaborates (Layout.bindings (startupFields b))
      (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
      ceiling .nil (ProfileProjection.startup b.initialState b.initialClock).body
      (startupResult b).2 := by
  rcases resolved with ⟨_, different, initState, initClock, _, _⟩
  rw [initState, initClock]
  exact .cons (.assign (.assign
    (.writable (reference_typed _ .nil (startup_state_bound b) .nil)) .zero))
    (.cons (.assign (.assign
      (.writable (reference_typed _ .nil (startup_clock_bound b different) .nil)) .one)) .nil)

theorem step_typed (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Bodies.BodyElaborates (Layout.bindings (stepFields b))
      (Declarations.ShapeLookup.HasShape ceiling (ProfileProjection.ofScalar b).declarations)
      ceiling .nil (ProfileProjection.scalarStep b.stepTarget b.stepRead).body (stepResult b).2 := by
  rcases resolved with ⟨_, _, _, _, target, read⟩
  rw [target, read]
  exact .cons (.assign (.assign
    (.writable (reference_typed _ .nil (step_state_bound b) .nil))
    (.parens (.binary .add
      (.reference (reference_typed _ .nil (step_state_bound b) .nil)) .one)))) .nil

theorem startup_prepared (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.Prepares (.literal "Startup") Capabilities.Initialization.role ceiling
      (ProfileProjection.ofScalar b) (startupResult b) :=
  .body (startup_selected b) (declared b resolved.2.1 ceiling) (startup_typed b resolved ceiling)

theorem recalibrate_prepared (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.Prepares (.literal "Recalibrate") Capabilities.DoStep.role ceiling
      (ProfileProjection.ofScalar b) (recalibrateResult b) :=
  .body (recalibrate_selected b) (declared b resolved.2.1 ceiling) .nil

theorem step_prepared (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.Prepares (.literal "DoStep") Capabilities.DoStep.role ceiling
      (ProfileProjection.ofScalar b) (stepResult b) :=
  .body (step_selected b) (declared b resolved.2.1 ceiling) (step_typed b resolved ceiling)

theorem startup_lowered (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.literal "Startup") Capabilities.Initialization.role ceiling
      (ProfileProjection.ofScalar b) = some (startupResult b) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (startup_prepared b resolved ceiling)

theorem recalibrate_lowered (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.literal "Recalibrate") Capabilities.DoStep.role ceiling
      (ProfileProjection.ofScalar b) = some (recalibrateResult b) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (recalibrate_prepared b resolved ceiling)

theorem step_lowered (b : Syntax.Block) (resolved : Syntax.Resolved b) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.literal "DoStep") Capabilities.DoStep.role ceiling
      (ProfileProjection.ofScalar b) = some (stepResult b) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (step_prepared b resolved ceiling)

end Rumoca.GALEC.Elaboration.Scalar
