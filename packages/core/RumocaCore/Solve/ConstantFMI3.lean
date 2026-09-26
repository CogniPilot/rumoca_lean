import RumocaCore.Constant.Semantics
import RumocaCore.Solve.Interface

/-! Prepared FMI 3 deployment data for one constant-rate (G01) problem: a model
name, the owned constant-rate initial value problem over `N` states and the
resolved declared interface of the source. The interface carries one scalar
declaration per source state, so the exported variables are the source
variables; how the states are laid out in an instance record is decided by the
backend's C record stage, not here. No input and no dense output exist. -/
namespace Rumoca.Solve
open Rumoca.Tensor Rumoca.ConstantProfile

structure ConstantFMI3Model (n : Nat) where
  name : String
  ivp : ConstantIVP n
  interface : Interface

/-- The constant-rate profile never exposes a dense (Jacobian) output. -/
def ConstantFMI3Model.hasOutput (_ : ConstantFMI3Model n) : Bool := false

end Rumoca.Solve
