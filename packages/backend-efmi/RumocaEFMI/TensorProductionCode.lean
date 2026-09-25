import RumocaEFMI.TensorAlgorithmCode
import RumocaC.TensorFillCode
import RumocaC.TensorCode
import RumocaC.TensorDiagonalCode
import RumocaC.TensorSquareDiagonal
import RumocaC.TensorSquareIVPEntry
import RumocaC.TensorProductPreflightCode
import RumocaC.TensorSumPreflightCode

/-! Production Code rendering for the fixed-extent tensor square profile.

The Production Code translation unit reuses the certified tensor kernel entries
the way the FMI 3 side does: the numerical code is the certified kernel text
(`rumoca_initialize`, `rumoca_rhs`, `rumoca_square_jacobian_diag` and the shared
helpers), included in the translation unit rather than re-emitted, and the eFMI
Production Code method functions (`Startup`, `Recalibrate`, `DoStep`) call those
prepared entries against the array members of the instance record. The method
functions follow the scalar Production Code interface conventions generalized to
array variables: each method returns a fixed 32-bit status, clears its own error
word on entry, and addresses the logical variables through the `Model *self`
formal parameter.

This file resolves no names, solves no equations and selects no numerical
policy. The prepared `Solve.PointwiseIVP` square kernel is the source of truth:
the derivative method computes the prepared derivative `u * u` (pointwise), and the Jacobian
output computes the dense diagonal Jacobian `diag(2*u)`; a backend cannot invent
a different problem. Tensor rank and extents stay symbolic in every semantic
theorem; the concrete extents appear only in the pinned artifact text. -/
namespace Rumoca.EFMI.TensorProduction
open Rumoca.Tensor Rumoca.Solve Rumoca.CTree
open Rumoca.CTensor.ProgramFixture

/-! ### The eFMI Production Code C interface for array variables

The instance record `Model` declares each logical variable as a fixed-extent C
array member alongside the 32-bit error word. The manifest describes the same
members with their dimensions. -/

/-- The error word member, as in the scalar Production Code profile. -/
def statusName : String := "errorSignalStatus"

/-- A logical array variable of the tensor square profile: its C member name and
its fixed dimensions (row-major element count is the product of the extents). -/
structure ArrayVar where
  name : String
  dims : List Nat
  deriving Repr, DecidableEq

def ArrayVar.volume (v : ArrayVar) : Nat := v.dims.foldl (· * ·) 1

/-- Input `u`, output square `x` and dense Jacobian `J`, matching the pinned
tensor Algorithm Code `input Real u[2]; output Real x[2]; output Real J[2, 2];`. -/
def inputVar : ArrayVar := ⟨"u", [2]⟩
def squareVar : ArrayVar := ⟨GALEC.Names.state, [2]⟩
def jacobianVar : ArrayVar := ⟨"J", [2, 2]⟩

def modelVars : List ArrayVar := [inputVar, squareVar, jacobianVar]

/-- The element count of each variable of the profile. -/
theorem inputVar_volume : inputVar.volume = 2 := rfl
theorem squareVar_volume : squareVar.volume = 2 := rfl
theorem jacobianVar_volume : jacobianVar.volume = 4 := rfl

/-! ### The certified kernel translation-unit text

The numerical code is the join of the certified kernel renders in dependency
order, with `<math.h>`, `<stddef.h>` and `<stdint.h>` prepended, exactly the emission
the tensor C artifact checks certify. Nothing here re-derives the numerical
bodies; each fragment is a certified render. -/

/-- The headers of the translation unit: `isfinite` needs `<math.h>`. -/
def includes : String := "#include <math.h>\n#include <stddef.h>\n#include <stdint.h>\n"

/-- The shared tensor helpers, the prepared square IVP entries and the two
read-only preflights, in emission order. `rumoca_initialize` writes the zero
state, `rumoca_rhs` writes the elementwise product `u * u`,
`rumoca_square_jacobian_diag` writes the dense diagonal Jacobian `diag(2*u)`
with no coefficient buffer, and `rumoca_tensor_mul_finite` and
`rumoca_tensor_add_finite` report whether every product and every sum is finite. -/
def kernelPieces : List String :=
  [includes,
   Rumoca.CTensor.Fill.function.render,
   (Rumoca.CTensor.function .add).render,
   (Rumoca.CTensor.function .mul).render,
   Rumoca.CTensor.Diagonal.function.render,
   IVPEntry.sources.initial,
   IVPEntry.sources.derivative,
   IVPEntry.jacobianDiagSource,
   Rumoca.CTensor.ProductPreflight.function.render,
   Rumoca.CTensor.SumPreflight.function.render]

/-- The certified kernel translation-unit text. -/
def kernelText : String := String.join kernelPieces

/-! ### The eFMI Production Code interface header

The instance record and the error/real aliases the manifest also declares. The
storage profile is finite binary64; its correspondence to C object layout is an
explicitly reviewed boundary, not a theorem about a host ABI. -/

def realAlias : String := "EfmiReal"
def statusAlias : String := "EfmiStatus"

def memberDecl (v : ArrayVar) : String :=
  "  " ++ realAlias ++ " " ++ v.name ++ "[" ++ toString v.volume ++ "];\n"

/-- The Production Code interface header: the real and status type aliases and
the `Model` record with one array member per logical variable and the error
word. -/
def header : String :=
  "typedef double " ++ realAlias ++ ";\n" ++
  "typedef int32_t " ++ statusAlias ++ ";\n" ++
  "typedef struct {\n" ++
  String.join (modelVars.map memberDecl) ++
  "  " ++ realAlias ++ " " ++ GALEC.Names.clock ++ ";\n" ++
  "  " ++ statusAlias ++ " " ++ statusName ++ ";\n" ++
  "} Model;\n\n"

/-! ### The Production Code method functions

Each method function returns the fixed status word after clearing it on entry,
mirroring the scalar Production Code profile. The bodies call the certified
kernel entries against the array members. -/

def selfField (name : String) : Expr := .field (.id "self") name true

/-- Wrap a method body in the eFMI status-returning method-function convention. -/
def method (name : String) (body : List Stmt) : Function :=
  ⟨⟨statusAlias, name, [⟨"Model *", "self", false⟩]⟩,
    .assign (selfField statusName) (.nat 0) :: (body ++ [.ret (some (selfField statusName))]), false⟩

def startupName : String := GALEC.Names.function GALEC.Names.squareBlock .startup
def recalibrateName : String := GALEC.Names.function GALEC.Names.squareBlock .recalibrate
def doStepName : String := GALEC.Names.function GALEC.Names.squareBlock .doStep

/-- Arguments of the initializer call for the state output `x`. -/
def squareInitializerArgs : List Expr := [selfField squareVar.name, .nat squareVar.volume]

/-- Arguments of the initializer call for the Jacobian output `J`. -/
def jacobianInitializerArgs : List Expr := [selfField jacobianVar.name, .nat jacobianVar.volume]

/-- The two initializer calls of the Startup body: `x`, then `J`. -/
def initializationPrefix : List Stmt :=
  [.eval (.call (.id "rumoca_initialize") squareInitializerArgs),
   .eval (.call (.id "rumoca_initialize") jacobianInitializerArgs)]

/-- Startup initializes the state output `x` and the Jacobian output `J` to
positive zero through the prepared initializer entry, each with its own volume,
then sets the sample period. -/
def startupFunction : Function :=
  method startupName
    (initializationPrefix ++ [.assign (selfField GALEC.Names.clock) (.cast "double" (.nat 1))])

/-- Recalibrate has no periodic clock work in the tensor square profile. -/
def recalibrateFunction : Function := method recalibrateName []

/-- The arguments of both preflight calls: the input `u`, twice, and its volume. -/
def preflightArgs : List Expr := [selfField inputVar.name, selfField inputVar.name, .nat inputVar.volume]

/-- The status of the overflow outcome: the §1.6 encoding of the signal set
`{OVERFLOW}` that the DoStep method of the Algorithm Code exposes. -/
def overflowStatus : Nat := GALEC.SignalSet.encode GALEC.Elaboration.Square.overflowSet

/-- The failure test: a product or a sum of the input is not finite. -/
def unchecked : Expr :=
  .bin .or (.bin .eq (.id "squares") (.nat 0)) (.bin .eq (.id "sums") (.nat 0))

/-- The numerical kernel calls of DoStep: the prepared derivative into the
square output `x` and the dense diagonal Jacobian into `J`. The derivative
entry's unused state register is pointed at the readable input `u`; the square
right-hand side ignores it, so the written value is exactly `u * u` (pointwise). -/
def kernelCalls : List Stmt :=
  [.eval (.call (.id "rumoca_rhs")
    [selfField inputVar.name, selfField inputVar.name, selfField squareVar.name,
      .nat inputVar.volume]),
   .eval (.call (.id "rumoca_square_jacobian_diag")
    [selfField inputVar.name, selfField jacobianVar.name,
      .nat inputVar.volume, .nat jacobianVar.volume])]

/-- DoStep first checks, with the read-only preflights and before any write,
that every product `u[k] * u[k]` and every sum `u[k] + u[k]` is finite. If a
check fails it stores the `OVERFLOW` status and writes nothing else; otherwise
it runs the kernel calls. -/
def doStepFunction : Function :=
  method doStepName
    [.declare "int32_t" "squares"
      (.call (.id Rumoca.CTensor.ProductPreflight.function.signature.name) preflightArgs),
     .declare "int32_t" "sums"
      (.call (.id Rumoca.CTensor.SumPreflight.function.signature.name) preflightArgs),
     .branch unchecked [.assign (selfField statusName) (.nat overflowStatus)] kernelCalls]

def functions : List Function := [startupFunction, recalibrateFunction, doStepFunction]

/-- The complete Production Code translation unit: the certified kernel text, the
interface header and the three method functions. -/
def render : String :=
  kernelText ++ header ++ String.join (functions.map Function.render)

end Rumoca.EFMI.TensorProduction
