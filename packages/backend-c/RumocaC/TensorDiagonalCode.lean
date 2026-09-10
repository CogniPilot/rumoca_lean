import RumocaC.TensorFillCode
import RumocaC.Algorithm
import RumocaC.TensorProgramSyntax

/-! Materialize an already prepared diagonal observation at its dense output.
Solve supplies coefficients and shape; the backend emits one reusable helper,
without differentiating expressions or enumerating matrix coordinates. -/
namespace Rumoca.CTensor.Diagonal
open CTree

def signatureParameters : List Lowering.Syntax.Parameter :=
  [⟨.input, "coeff"⟩, ⟨.output, "out"⟩, ⟨.count, "count"⟩, ⟨.count, "cells"⟩]

def operation : List Stmt :=
  [.assign (.index (.id "out") (.id "offset")) (indexed "coeff"),
   .assign (.id "offset") (.bin .add (.id "offset") (.id "stride"))]

def tail : List Stmt :=
  [.declare "size_t" "offset" (.nat 0),
   .declare "size_t" "stride" (.bin .add (.id "count") (.nat 1))] ++
  CLoops.counted "k" (.id "count") operation ++ [.ret none]

def function : Function where
  signature := ⟨"void", "rumoca_tensor_diagonal", signatureParameters.map Lowering.Syntax.Parameter.tree⟩
  body := Fill.invoke (CAlgorithm.literal .zero) (.id "out") (.id "cells") :: tail
  static := false

def invoke (coeff output count cells : Expr) : Stmt :=
  .eval (.call (.id function.signature.name) [coeff, output, count, cells])

end Rumoca.CTensor.Diagonal
