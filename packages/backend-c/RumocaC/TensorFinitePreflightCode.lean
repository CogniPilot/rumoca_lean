import RumocaC.TensorFiniteScanCode

/-! Shared read-only counted expression classifier. This code module has no
proof or interface dependency. The calling backend supplies the expression. -/
namespace Rumoca.CTensor.FinitePreflight
open CTree

def iteration (value : Expr) : List Stmt :=
  [.assign (.id "sample") value] ++ FiniteScan.iterationFor (.id "sample")

def body (value : Expr) : List Stmt :=
  [.declare "double" "sample" (.decimal false 0 0), .declare "int32_t" "valid" (.nat 1)] ++
    CLoops.counted "k" (.id "count") (iteration value) ++
    [.ret (some (.id "valid"))]

end Rumoca.CTensor.FinitePreflight
