import RumocaC.TensorFiniteScanCode

/-! Executable C construction for a fixed-rate scalar Euler preflight.
Only code data is constructed here; finite-prefix witnesses and numerical
execution proofs belong to the separate semantic modules. -/
namespace Rumoca.CEulerPreflight
open CTree

def guard : Expr := .bin .ne (.id "valid") (.nat 0)
def copySample : Stmt := .branch guard [.assign (.id "sample") (.id "candidate")] []
def active : List Stmt :=
  [.assign (.id "candidate") (.bin .add (.id "sample") (.id "rate"))] ++
    CTensor.FiniteScan.iterationFor (.id "candidate") ++ [copySample]
def iteration : List Stmt := [.branch guard active []]
def segment : List Stmt :=
  [.declare "double" "sample" (.id "initial"),
   .declare "double" "candidate" (.id "initial"),
   .declare "int32_t" "valid" (.nat 1)] ++
    CLoops.counted "n" (.id "count") iteration
def function : Function where
  signature := ⟨"int32_t", "rumoca_euler_finite",
    [⟨"double", "initial", false⟩, ⟨"double", "rate", false⟩,
      ⟨"size_t", "count", false⟩]⟩
  body := segment ++ [.ret (some (.id "valid"))]
  static := false

end Rumoca.CEulerPreflight
