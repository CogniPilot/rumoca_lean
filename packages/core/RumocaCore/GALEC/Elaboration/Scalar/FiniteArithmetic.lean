import RumocaCore.Solve.Tensor.Finite
import RumocaCore.GALEC.Binary64

/-! Only the original scalar DoStep operation is total on finite binary64.
This is not a total-arithmetic assumption for other additions or operations. -/
namespace Rumoca.GALEC.Elaboration.Scalar
open Rumoca.Tensor Rumoca.Solve.Tensor

theorem finite_add_one (value result : Binary64.Value) :
    Finite.Result .add value Binary64.one result ↔
      result = GALEC.roundedAdd value Binary64.one := by
  have domain : Finite.Domain .add value Binary64.one := by
    simpa only [Finite.Domain, Binary64.units_one, Binary64.overflowUnits] using
      Binary64.advance_no_overflow value
  rw [Finite.result_iff]
  simp only [domain, true_and, BinaryOp.scalar, Finite.ops, GALEC.roundedAdd]

end Rumoca.GALEC.Elaboration.Scalar
