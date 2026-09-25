import RumocaC.TensorFiniteScanCode

/-! Shared read-only counted expression classifier. This code module has no
proof or interface dependency. The calling backend supplies the expression,
or the tensor operation whose coordinates the classifier checks. -/
namespace Rumoca.CTensor.FinitePreflight
open CTree

def iteration (value : Expr) : List Stmt :=
  [.assign (.id "sample") value] ++ FiniteScan.iterationFor (.id "sample")

def segmentWith (flagType : String) (value : Expr) : List Stmt :=
  [.declare "double" "sample" (.decimal false 0 0), .declare flagType "valid" (.nat 1)] ++
    CLoops.counted "k" (.id "count") (iteration value)

def segment (value : Expr) : List Stmt := segmentWith "int32_t" value

def body (value : Expr) : List Stmt := segment value ++ [.ret (some (.id "valid"))]

/-- The coordinate `left[k] op right[k]` of a shared binary tensor operation. -/
def coordinate (op : BinOp) : Expr := .bin op (indexed "left") (indexed "right")

/-- The read-only preflight of a shared binary tensor operation: it returns
whether every coordinate `left[k] op right[k]` is finite. Both inputs may
alias; no output or scratch buffer is used. -/
def operation (name : String) (op : BinOp) : Function where
  signature := ⟨"int32_t", name,
    [⟨"const double *", "left", false⟩, ⟨"const double *", "right", false⟩,
      ⟨"size_t", "count", false⟩]⟩
  body := body (coordinate op)
  static := false

end Rumoca.CTensor.FinitePreflight
