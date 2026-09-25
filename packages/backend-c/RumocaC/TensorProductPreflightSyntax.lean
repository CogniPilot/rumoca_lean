import RumocaC.TensorProductPreflightCode
import RumocaC.TensorOperationPreflightSyntax

/-! Independent token specification of the multiplication preflight. -/
namespace Rumoca.CTensor.ProductPreflight.Syntax
open _root_.Parser

def tokens : List Token := FinitePreflight.Syntax.tokens "rumoca_tensor_mul_finite" "*"

def Denotes (source : String) : Prop :=
  Scanner.Lexes FiniteScan.Syntax.config source.toList tokens

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes : Denotes ProductPreflight.function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex FiniteScan.Syntax.config ProductPreflight.function.render).toOption =
      some tokens := by
    simp only [ProductPreflight.function, tokens]
    tensor_expand_operation_preflight_printer
    decide +kernel
  cases hl : Scanner.lex FiniteScan.Syntax.config ProductPreflight.function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

end Rumoca.CTensor.ProductPreflight.Syntax
