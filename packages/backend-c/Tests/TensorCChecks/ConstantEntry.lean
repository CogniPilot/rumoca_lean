import RumocaC.ConstantKernelProgram

/-! Development fixture for the G01 constant-rate numerical C. The rates mirror
`examples/ConstantRates.mo` (`der(x) = 2.5`, `der(y) = -1`); the source-to-IVP
binding for the actual model text is proved in the compiler package. Here the
rate literals enter directly as their exact base-ten content, as the tensor IVP
fixture supplies its program directly. -/
namespace Rumoca.CConstant.Fixture
open Rumoca.ConstantProfile

/-- The declaration-order rate literals: `2.5 = 25 * 10^-1`, `-1 = -1 * 10^0`. -/
def rates : List Decimal := [⟨1, 25, -1⟩, ⟨-1, 1, 0⟩]

/-- The rendered numerical C, the bytes the emitter writes and the checker reads:
the preamble and the three kernel entries rendered through the shared printer. -/
def source : String := programText rates

theorem source_eq : programText rates = source := rfl

/-- Normalize the fixed structured printer over the fixture rates to a string
literal before the kernel byte-equality check, as the tensor fixtures do for
their rendered helpers. -/
macro "constant_expand_fixture" : tactic => `(tactic|
  simp [rates, programText, preamble, rhsFunction, stepFunction, sampleFunction,
    rhsStmts, stepStmts, rateLit, CLoops.counted, CLoops.loop, CLoops.counterStep,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render, CTree.Expr.decimalMagnitude])

end Rumoca.CConstant.Fixture
