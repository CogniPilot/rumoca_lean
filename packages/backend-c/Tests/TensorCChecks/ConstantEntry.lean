import RumocaC.ConstantKernelProgram
import RumocaC.TreeLexical

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

/-! ### The rendered kernel functions tokenize and denote

An independent token grammar for each fixture entry is checked against the
shared C scanner, mirroring the tensor helper printer certificates. A negative
constant tokenizes as the `-` punctuator applied to the unsigned magnitude
(C has no negative literal tokens), and the exponent sign closes the number so
`25e-1` tokenizes as `25e`, `-`, `1`. -/
open _root_.Parser

/-- The token grammar of `rumoca_constant_rhs`. -/
def rhsTokens : List Token :=
  (["void", "rumoca_constant_rhs", "(", "double", "*", "der", ")", "{",
    "der", "[", "0", "]", "=", "25e", "-", "1", ";",
    "der", "[", "1", "]", "=", "(", "-", "1e0", ")", ";", "return", ";", "}"] : List String).map Token.literal

/-- The token grammar of `rumoca_constant_step`. -/
def stepTokens : List Token :=
  (["void", "rumoca_constant_step", "(", "double", "*", "x", ")", "{",
    "x", "[", "0", "]", "=", "(", "x", "[", "0", "]", "+", "25e", "-", "1", ")", ";",
    "x", "[", "1", "]", "=", "(", "x", "[", "1", "]", "+", "(", "-", "1e0", ")", ")", ";",
    "return", ";", "}"] : List String).map Token.literal

/-- The token grammar of `rumoca_constant_sample`. -/
def sampleTokens : List Token :=
  (["void", "rumoca_constant_sample", "(", "double", "*", "x", ",", "size_t", "n", ")", "{",
    "size_t", "i", "=", "0", ";", "while", "(", "(", "i", "<", "n", ")", ")", "{",
    "x", "[", "0", "]", "=", "(", "x", "[", "0", "]", "+", "25e", "-", "1", ")", ";",
    "x", "[", "1", "]", "=", "(", "x", "[", "1", "]", "+", "(", "-", "1e0", ")", ")", ";",
    "i", "=", "(", "i", "+", "1", ")", ";", "}", "return", ";", "}"] : List String).map Token.literal

/-- The rendered source denotes the given token grammar under the shared C
scanner. -/
def Denotes (source : String) (tokens : List Token) : Prop :=
  Scanner.Lexes CTree.Syntax.config source.toList tokens

private theorem denotes_of_lex {source : String} {tokens : List Token}
    (h : (Scanner.lex CTree.Syntax.config source).toOption = some tokens) : Denotes source tokens := by
  apply (Scanner.lex_correct _ _ _).mp
  cases hl : Scanner.lex CTree.Syntax.config source with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

theorem rhs_denotes : Denotes (rhsFunction rates).render rhsTokens :=
  denotes_of_lex (by constant_expand_fixture; decide +kernel)

theorem step_denotes : Denotes (stepFunction rates).render stepTokens :=
  denotes_of_lex (by constant_expand_fixture; decide +kernel)

theorem sample_denotes : Denotes (sampleFunction rates).render sampleTokens :=
  denotes_of_lex (by constant_expand_fixture; decide +kernel)

end Rumoca.CConstant.Fixture
