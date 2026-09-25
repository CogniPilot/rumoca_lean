import RumocaC.TensorProductPreflightCode
import RumocaC.TensorOperationPreflightSyntax

/-! The printed multiplication preflight lexes to the operation preflight tokens. -/
namespace Rumoca.CTensor.ProductPreflight.Syntax
open _root_.Parser

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes :
    FinitePreflight.Syntax.Denotes "rumoca_tensor_mul_finite" "*" ProductPreflight.function.render :=
  FinitePreflight.Syntax.denotes_of_lex (by
    simp only [ProductPreflight.function, FinitePreflight.Syntax.tokens]
    tensor_expand_operation_preflight_printer
    decide +kernel)

end Rumoca.CTensor.ProductPreflight.Syntax
