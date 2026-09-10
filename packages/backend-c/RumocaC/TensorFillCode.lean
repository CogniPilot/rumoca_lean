import RumocaC.TensorCode

/-! Runtime fill for an already shaped Solve register. Literal selection
belongs to its Solve instruction; the helper accepts the resulting value. -/
namespace Rumoca.CTensor.Fill
open CTree

def function : Function where
  signature := ⟨"void", "rumoca_tensor_fill",
    [⟨"double", "value", false⟩, ⟨"double *", "out", false⟩, ⟨"size_t", "count", false⟩]⟩
  body := CLoops.counted "k" (.id "count") [.assign (indexed "out") (.id "value")] ++ [.ret none]
  static := false

def invoke (value output count : Expr) : Stmt :=
  .eval (.call (.id function.signature.name) [value, output, count])

end Rumoca.CTensor.Fill
