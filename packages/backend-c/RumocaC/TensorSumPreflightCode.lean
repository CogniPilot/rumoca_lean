import RumocaC.TensorFinitePreflightCode

/-! Read-only preflight of the shared tensor addition operation. Both inputs
may alias; no output or scratch buffer is used. -/
namespace Rumoca.CTensor.SumPreflight
open CTree

def value : Expr := FinitePreflight.coordinate .add

def function : Function := FinitePreflight.operation "rumoca_tensor_add_finite" .add

end Rumoca.CTensor.SumPreflight
