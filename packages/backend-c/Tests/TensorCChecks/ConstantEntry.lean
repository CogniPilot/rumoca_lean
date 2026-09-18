import RumocaC.ConstantKernelCode

/-! Development fixture for the G01 constant-rate numerical C. The rates mirror
`examples/ConstantRates.mo` (`der(x) = 2.5`, `der(y) = -1`); the source-to-IVP
binding for the actual model text is proved in the compiler package. Here the
rate literals enter directly as their exact base-ten content, as the tensor IVP
fixture supplies its program directly. -/
namespace Rumoca.CConstant.Fixture
open Rumoca.ConstantProfile

/-- The declaration-order rate literals: `2.5 = 25 * 10^-1`, `-1 = -1 * 10^0`. -/
def rates : List Decimal := [⟨1, 25, -1⟩, ⟨-1, 1, 0⟩]

/-- The prepared two-state IVP for the fixture rates. -/
def ivp : ConstantIVP rates.length := ConstantIVP.ofList rates

/-- The rendered numerical C, the bytes the emitter writes and the checker reads. -/
def source : String := renderRates rates

theorem render_eq : ivp.render = source := render_ofList rates

end Rumoca.CConstant.Fixture
