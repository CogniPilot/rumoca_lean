import RumocaC.TensorFinitePreflightCode

/-! Read-only preflight of the shared tensor multiplication operation. Both
inputs may alias; no output or scratch buffer is used. -/
namespace Rumoca.CTensor.ProductPreflight
open CTree

def value : Expr := .bin .mul (indexed "left") (indexed "right")

def function : Function where
  signature := ⟨"int32_t", "rumoca_tensor_mul_finite",
    [⟨"const double *", "left", false⟩, ⟨"const double *", "right", false⟩,
      ⟨"size_t", "count", false⟩]⟩
  body := FinitePreflight.body value
  static := false

end Rumoca.CTensor.ProductPreflight
