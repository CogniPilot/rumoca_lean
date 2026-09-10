import RumocaCore.GALEC.Semantics
import RumocaCore.Real.Binary64

/-! The numerical proof interpretation is separate from generic algorithm
instructions and their executable lowering. Runtime code generation does not
import the noncomputable IEEE specification or mathlib's arithmetic tactics. -/
namespace Rumoca.GALEC

noncomputable def roundedAdd (x y : Binary64.Value) : Binary64.Value :=
  Binary64.roundedAdd x y

end Rumoca.GALEC
