import RumocaC.TensorSumPreflightCode
import RumocaC.TensorOperationPreflightSyntax

/-! The printed addition preflight lexes to the operation preflight tokens. -/
namespace Rumoca.CTensor.SumPreflight.Syntax
open _root_.Parser

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes :
    FinitePreflight.Syntax.Denotes "rumoca_tensor_add_finite" "+" SumPreflight.function.render :=
  FinitePreflight.Syntax.denotes_of_lex (by
    simp only [SumPreflight.function, FinitePreflight.Syntax.tokens]
    tensor_expand_operation_preflight_printer
    decide +kernel)

end Rumoca.CTensor.SumPreflight.Syntax
