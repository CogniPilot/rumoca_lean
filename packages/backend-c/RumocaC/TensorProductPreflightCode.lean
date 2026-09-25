import RumocaC.TensorFinitePreflightCode

/-! Read-only preflight of the shared tensor multiplication operation. Both
inputs may alias; no output or scratch buffer is used. -/
namespace Rumoca.CTensor.ProductPreflight
open CTree

def value : Expr := FinitePreflight.coordinate .mul

def function : Function := FinitePreflight.operation "rumoca_tensor_mul_finite" .mul

end Rumoca.CTensor.ProductPreflight
