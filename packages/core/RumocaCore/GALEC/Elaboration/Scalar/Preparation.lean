import RumocaCore.GALEC.Elaboration.Block.Preparation
import RumocaCore.GALEC.Elaboration.Surface

/-! The scalar unit block as a source tree, and its preparation by the generic
whole-block preparer. `source` is a specification tree for the scalar layout,
not a runtime body matcher; the parse of the emitted scalar text is shown equal
to it where that text is certified. The state and clock names
are arbitrary distinct names. No lifecycle or actual-artifact claim. -/
namespace Rumoca.GALEC.Elaboration.Scalar
open Elaboration Elaboration.Surface Rumoca.Tensor Rumoca.Solve.Tensor

def startupMethod (state clock : String) : AST.Method :=
  ⟨.ident "Startup",
    [.assign (stateReference state []) (.literal (.number "0.0")),
     .assign (stateReference clock []) (.literal (.number "1.0"))], .ident "Startup"⟩

def recalibrateMethod : AST.Method :=
  ⟨.ident "Recalibrate", [], .ident "Recalibrate"⟩

def stepMethod (state : String) : AST.Method :=
  ⟨.ident "DoStep",
    [.assign (stateReference state []) (.parens
      (.binary (.literal "+") (.reference (stateReference state [])) (.literal (.number "1.0"))))],
    .ident "DoStep"⟩

def stateDeclaration (state : String) : AST.Declaration :=
  ⟨.output, .literal "Real", [], .ident state⟩

def clockDeclaration (clock : String) : AST.Declaration :=
  ⟨.constant, .literal "Real", [], .ident clock⟩

def sourceDeclarations (state clock : String) : List (AST.Visibility × AST.Declaration) :=
  [(.public, stateDeclaration state), (.protected, clockDeclaration clock)]

def source (name state clock : String) : AST.Block :=
  ⟨.ident name, [stateDeclaration state], [clockDeclaration clock],
    [startupMethod state clock, recalibrateMethod, stepMethod state], .ident name⟩

def declarations (state clock : String) : List Declarations.Real.Descriptor :=
  [⟨state, .public, .output, scalar⟩, ⟨clock, .protected, .constant, scalar⟩]

def startupFields (state clock : String) : List Layout.Field :=
  Capabilities.Generic.fields Capabilities.Initialization.role (declarations state clock)

def stepFields (state clock : String) : List Layout.Field :=
  Capabilities.Generic.fields Capabilities.DoStep.role (declarations state clock)

def startupState (state clock : String) :
    Ref (Layout.outputShapes (startupFields state clock)) scalar := .here
def startupClock (state clock : String) :
    Ref (Layout.outputShapes (startupFields state clock)) scalar := .there .here
def stepState (state clock : String) :
    Ref (Layout.outputShapes (stepFields state clock)) scalar := .here

def startupResult (state clock : String) : Methods.Preparation.Result :=
  ⟨startupFields state clock,
    .seq (.assign (startupState state clock) .nil (.literal .zero))
      (.seq (.assign (startupClock state clock) .nil (.literal .one)) .skip)⟩

def recalibrateResult (state clock : String) : Methods.Preparation.Result :=
  ⟨stepFields state clock, .skip⟩

def stepResult (state clock : String) : Methods.Preparation.Result :=
  ⟨stepFields state clock, .seq (.assign (stepState state clock) .nil
    (.binary .add (.output (stepState state clock) .nil) (.literal .one))) .skip⟩

theorem declared (different : state ≠ clock) (ceiling : Nat) :
    Declarations.Real.DeclaresAll ceiling (sourceDeclarations state clock)
      (declarations state clock) :=
  .cons (.real (by decide) .nil) (.cons (.real (by decide) .nil) .nil (by simp))
    (by simpa [declarations] using different)

theorem startup_state_bound (state clock : String) :
    BindingTable.Resolves (Layout.bindings (startupFields state clock)) [state]
      ⟨scalar, .writable (startupState state clock)⟩ := .here

theorem startup_clock_bound (different : state ≠ clock) :
    BindingTable.Resolves (Layout.bindings (startupFields state clock)) [clock]
      ⟨scalar, .writable (startupClock state clock)⟩ :=
  .there (by simpa using Ne.symm different) .here

theorem step_state_bound (state clock : String) :
    BindingTable.Resolves (Layout.bindings (stepFields state clock)) [state]
      ⟨scalar, .writable (stepState state clock)⟩ := .here

theorem startup_selected (name state clock : String) :
    Methods.Headers.Selects (.ident "Startup") (source name state clock).methods
      (startupMethod state clock) :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem recalibrate_selected (name state clock : String) :
    Methods.Headers.Selects (.ident "Recalibrate") (source name state clock).methods
      recalibrateMethod :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem step_selected (name state clock : String) :
    Methods.Headers.Selects (.ident "DoStep") (source name state clock).methods
      (stepMethod state) :=
  (Methods.Headers.select_iff _ _ _).mp rfl

theorem startup_typed (different : state ≠ clock) (ceiling : Nat) :
    Bodies.BodyElaborates (Layout.bindings (startupFields state clock))
      (Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      ceiling .nil (startupMethod state clock).body (startupResult state clock).2 :=
  .cons (.assign (.assign
    (.writable (reference_typed _ .nil (startup_state_bound state clock) .nil)) .zero))
    (.cons (.assign (.assign
      (.writable (reference_typed _ .nil (startup_clock_bound different) .nil)) .one)) .nil)

theorem step_typed (state clock : String) (ceiling : Nat) :
    Bodies.BodyElaborates (Layout.bindings (stepFields state clock))
      (Declarations.ShapeLookup.HasShape ceiling (sourceDeclarations state clock))
      ceiling .nil (stepMethod state).body (stepResult state clock).2 :=
  .cons (.assign (.assign
    (.writable (reference_typed _ .nil (step_state_bound state clock) .nil))
    (.parens (.binary .add
      (.reference (reference_typed _ .nil (step_state_bound state clock) .nil)) .one)))) .nil

theorem startup_prepared (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.Prepares (.ident "Startup") Capabilities.Initialization.role ceiling
      (source name state clock) (startupResult state clock) :=
  .body (startup_selected name state clock) (declared different ceiling)
    (startup_typed different ceiling)

theorem recalibrate_prepared (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.Prepares (.ident "Recalibrate") Capabilities.DoStep.role ceiling
      (source name state clock) (recalibrateResult state clock) :=
  .body (recalibrate_selected name state clock) (declared different ceiling) .nil

theorem step_prepared (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.Prepares (.ident "DoStep") Capabilities.DoStep.role ceiling
      (source name state clock) (stepResult state clock) :=
  .body (step_selected name state clock) (declared different ceiling)
    (step_typed state clock ceiling)

theorem startup_lowered (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.ident "Startup") Capabilities.Initialization.role ceiling
      (source name state clock) = some (startupResult state clock) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (startup_prepared name different ceiling)

theorem recalibrate_lowered (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.ident "Recalibrate") Capabilities.DoStep.role ceiling
      (source name state clock) = some (recalibrateResult state clock) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (recalibrate_prepared name different ceiling)

theorem step_lowered (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Methods.Preparation.fromBlock (.ident "DoStep") Capabilities.DoStep.role ceiling
      (source name state clock) = some (stepResult state clock) :=
  (Methods.Preparation.fromBlock_iff _ _ _ _ _).mpr (step_prepared name different ceiling)

def interface (name state clock : String) : Block.Headers.Interface :=
  ⟨name, startupMethod state clock, recalibrateMethod, stepMethod state⟩

def result (name state clock : String) : Block.Result :=
  ⟨interface name state clock, startupResult state clock, recalibrateResult state clock,
    stepResult state clock⟩

theorem headers (name state clock : String) :
    Block.Headers.Valid (source name state clock) (interface name state clock) :=
  ⟨.matched, startup_selected name state clock, recalibrate_selected name state clock,
    step_selected name state clock, by
      intro method member
      simp only [source, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)⟩

/-- The whole scalar block prepares, through the generic block preparer, to
exactly the three scalar method results. -/
theorem prepared (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Block.Prepares ceiling (source name state clock) (result name state clock) :=
  ⟨headers name state clock, startup_prepared name different ceiling,
    recalibrate_prepared name different ceiling, step_prepared name different ceiling⟩

theorem fromBlock_source (name : String) (different : state ≠ clock) (ceiling : Nat) :
    Block.fromBlock ceiling (source name state clock) = some (result name state clock) :=
  (Block.fromBlock_iff _ _ _).mpr (prepared name different ceiling)

end Rumoca.GALEC.Elaboration.Scalar
