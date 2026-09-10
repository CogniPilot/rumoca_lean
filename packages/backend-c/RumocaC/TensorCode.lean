import RumocaC.LoopCode
import RumocaCore.Tensor.Operators

/-! Pointwise C helpers consumed by prepared tensor programs. One loop serves
every extent. Operands, output storage and count are explicit parameters; the
backend makes no source-language, shape-inference or differentiation choices. -/
namespace Rumoca.CTensor
open CTree

def binaryOp : Tensor.BinaryOp → CTree.BinOp
  | .add => .add
  | .mul => .mul

def indexed (name : String) : Expr := .index (.id name) (.id "k")

def operation (op : Tensor.BinaryOp) : List Stmt :=
  [.assign (indexed "out") (.bin (binaryOp op) (indexed "left") (indexed "right"))]

def body (op : Tensor.BinaryOp) : List Stmt :=
  CLoops.counted "k" (.id "count") (operation op) ++ [.ret none]

def function (op : Tensor.BinaryOp) : Function where
  signature := ⟨"void", match op with | .add => "rumoca_tensor_add" | .mul => "rumoca_tensor_mul",
    [⟨"const double *", "left", false⟩, ⟨"const double *", "right", false⟩,
      ⟨"double *", "out", false⟩, ⟨"size_t", "count", false⟩]⟩
  body := body op
  static := false

/-- A prepared tensor instruction supplies buffer expressions and its count. -/
def invoke (op : Tensor.BinaryOp) (left right output count : Expr) : Stmt :=
  .eval (.call (.id (function op).signature.name) [left, right, output, count])

end Rumoca.CTensor
