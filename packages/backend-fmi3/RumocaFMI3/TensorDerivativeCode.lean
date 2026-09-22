import RumocaFMI3.TensorFloat64Access
import RumocaCore.Tensor.Matrix
import RumocaFMI3.TensorDerivativePreflight

/-! Tensor derivative getter code shared by admission, continuation and public
entry proofs. Shape and prepared-entry ownership are unchanged. -/
namespace Rumoca.FMI3.TensorContinuousStates
open CTree CMemory CBody CLoops TensorInstance
open TensorFloat64 (getLoopSuffix getCopyBody)

def derivParameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  bind (bind (bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "derivatives" (.pointer buffer)) "instance" (.pointer handle)

def derivGuardEnv (p buffer : Address) (count : UInt64) : Locals :=
  bind (derivParameters (some p) (some buffer) count) "m" (.pointer (some p))

def derivCountReject (volume : Nat) : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
    Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"

def derivEntryArgs : List Expr :=
  [Runtime.region stateName, Runtime.region inputName, Runtime.region derivativeName,
    Runtime.v "nContinuousStates"]

def jacobianEntryArgs (shape : Tensor.Shape) : List Expr :=
  [Runtime.region inputName, Runtime.region outputName, Runtime.v "nContinuousStates",
    Runtime.n (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume]

def derivCopyTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "src" (Runtime.region derivativeName) ::
  .declare "fmi3Float64 *" "values" (Runtime.v "derivatives") ::
  .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix

def jacobianCall (shape : Tensor.Shape) : Stmt :=
  .eval (Runtime.call "rumoca_square_jacobian_diag" (jacobianEntryArgs shape))

def derivTail (shape : Tensor.Shape) : Bool → List Stmt
  | false => derivCopyTail shape
  | true => jacobianCall shape :: derivCopyTail shape

/-- After inline preflight, the existing size-typed counter is reset and reused
for the copy. No shadowing declaration or mutation of ABI parameters is needed. -/
def derivCheckedCopyTail (shape : Tensor.Shape) : List Stmt :=
  [.declare "fmi3Float64 *" "src" (Runtime.region derivativeName),
   .declare "fmi3Float64 *" "values" (Runtime.v "derivatives"),
   .declare "size_t" "expected" (Runtime.n shape.volume),
   .assign (.id "k") (.nat 0), CLoops.loop "k" (Runtime.v "expected") getCopyBody, Runtime.ok]

def derivCheckedTail (shape : Tensor.Shape) : Bool → List Stmt
  | false => derivCheckedCopyTail shape
  | true => jacobianCall shape :: derivCheckedCopyTail shape

def derivCheckedBody (shape : Tensor.Shape) (hasOutput : Bool) : List Stmt :=
  Runtime.require .getDerivatives ++
    (derivCountReject shape.volume :: (TensorDerivativePreflight.body ++
      (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCheckedTail shape hasOutput)))

def derivCheckedFunction (shape : Tensor.Shape) (hasOutput : Bool) : CTree.Function :=
  ⟨DerivativeCalls.signature, derivCheckedBody shape hasOutput, false⟩

def derivBody (shape : Tensor.Shape) (hasOutput : Bool) : List Stmt := derivCheckedBody shape hasOutput

def derivFunction (shape : Tensor.Shape) (hasOutput : Bool) : CTree.Function :=
  derivCheckedFunction shape hasOutput

end Rumoca.FMI3.TensorContinuousStates
