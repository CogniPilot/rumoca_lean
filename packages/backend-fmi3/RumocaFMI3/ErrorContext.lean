import RumocaFMI3.StaticInitialization
import RumocaFMI3.GuardedCalls
import RumocaC.Fenv

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory CLiteral.Interface

/-- The local bindings needed by failure execution. No successful execution,
whole-program agreement or native callback behavior is a field. -/
structure ErrorContext (literals : CLiteralAddresses) where
  target : CInterface
  types : (cInterface literals).types = target.types
  bytes : literals = target.literals
  helper : CodeAgrees (cInterface literals) target Runtime.helpers[0].body
  error : target.constants "fmi3Error" = some (.integer 3)
  ordinary : target.constants "fail" = none

namespace ErrorContext

def static (objects : Objects) (literals : CLiteralAddresses) : ErrorContext literals where
  target := executionInterface objects literals
  types := StaticInitialization.interface_types objects literals
  bytes := rfl
  helper := by
    simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.helpers,
      Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
      Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both,
      executionInterface, objectConstants]
  error := rfl
  ordinary := rfl

/-- Extending the rounding header preserves every binding used by the error
helper; other public functions may use the added macro. -/
def withRounding (context : ErrorContext literals) (header : CFenv.Header) : ErrorContext literals where
  target := header.interface context.target
  types := context.types
  bytes := context.bytes
  helper := by
    simpa [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.helpers,
      Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
      Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both,
      CFenv.Header.interface] using context.helper
  error := context.error
  ordinary := context.ordinary

theorem instance_binding (context : ErrorContext literals) :
    context.target.constants "m" = none := by
  have used := context.helper
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, Runtime.helpers,
    Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
    Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both] at used
  aesop

theorem error_cast (context : ErrorContext literals) :
    @CCalls.returnCast context.target "fmi3Status" (.integer 3) = some (.integer 3) := by
  rw [← returnCast_agreement (cInterface literals) context.target context.types]
  rfl

theorem logging_arguments (context : ErrorContext literals) (name : String)
    (environment : Option Address) (category message : Address) :
    @CCalls.Events.convertedArguments context.target (Logging.signature name).parameters
      (Logging.arguments environment category message) =
      some (Logging.arguments environment category message) := by
  simp [CCalls.Events.convertedArguments, Logging.signature, Logging.arguments,
    CCalls.parameters, CBody.bind, CBody.cast, ← context.types, CCalls.parameterType, convert]

end ErrorContext
end Rumoca.FMI3
end
