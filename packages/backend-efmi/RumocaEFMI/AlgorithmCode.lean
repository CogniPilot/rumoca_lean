import RumocaCore.Solve.Algorithm
import RumocaCore.GALEC.Elaboration.Scalar.Preparation
import GALECParser.Print

/-! Algorithm Code emission for the scalar unit profile. The block is the core
scalar builder's tree with the canonical names; the text is `Print.block` of
that tree. This file resolves no names, solves no equations and selects no
numerical policy; the prepared `Solve.Algorithm.Model` is the source of truth. -/
namespace Rumoca.EFMI

/-- The scalar unit block: output `x`, the protected sample period and the
Startup, Recalibrate and DoStep methods. -/
def scalarBlock : GALEC.AST.Block :=
  GALEC.Elaboration.Scalar.source "UnitIntegrator" "x" "samplePeriod"

/-- The scalar Algorithm Code text of a prepared unit model. -/
def renderAlgorithm (_model : Solve.Algorithm.Model source) : String :=
  GALEC.Print.block scalarBlock

end Rumoca.EFMI
