import RumocaCore.GALEC.Method

/-! Canonical names shared by the Algorithm Code blocks, the Production Code
instance members and functions, and the eFMI manifests. Each name is defined
here once; every emitted spelling is derived from it. -/
namespace Rumoca.GALEC.Names

/-- The scalar unit block. -/
@[simp] abbrev unitBlock : String := "UnitIntegrator"
/-- The tensor square block. -/
@[simp] abbrev squareBlock : String := "TensorSquare"
/-- The state output. -/
@[simp] abbrev state : String := "x"
/-- The protected sample-period constant. -/
@[simp] abbrev clock : String := "samplePeriod"
/-- The builtin finiteness test admitted as a branch condition. -/
@[simp] abbrev finiteTest : String := "isFinite"

/-- The Algorithm Code name of a lifecycle method. -/
@[simp] abbrev method : Method → String
  | .startup => "Startup"
  | .recalibrate => "Recalibrate"
  | .doStep => "DoStep"

/-- The Production Code function of a block's lifecycle method. -/
@[simp] abbrev function (block : String) (m : Method) : String := block ++ "_" ++ method m

end Rumoca.GALEC.Names
