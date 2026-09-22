import RumocaC.TensorCode

/-! A shared, read-only whole-tensor finiteness scanner. Shape selection and
interface error policy remain outside this helper. One runtime loop serves all
extents; there is one return and no allocation or tensor scalarization. -/
namespace Rumoca.CTensor.FiniteScan
open CTree

def iteration : List Stmt :=
  [.branch (.not (.call (.id "isfinite") [indexed "values"]))
    [.assign (.id "valid") (.nat 0)] []]

def function : Function where
  signature := ⟨"int32_t", "rumoca_tensor_all_finite",
    [⟨"const double *", "values", false⟩, ⟨"size_t", "count", false⟩]⟩
  body := [.declare "int32_t" "valid" (.nat 1)] ++
    CLoops.counted "k" (.id "count") iteration ++ [.ret (some (.id "valid"))]
  static := false

end Rumoca.CTensor.FiniteScan
