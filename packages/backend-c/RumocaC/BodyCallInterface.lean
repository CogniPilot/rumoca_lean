import RumocaC.LiteralInterfaceBody
import RumocaC.BodyEvents

/-! Transfer closed-body call proofs across checked interface bindings. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLiteral.Interface

/-- Reuse a closed-body proof in a target interface that agrees on this
function's syntax. Other functions in the target table may use new bindings;
no agreement or successful execution of those functions is required. -/
theorem body_call_interface_behaviors (before after : CInterface)
    (sameTypes : before.types = after.types) (sameLiterals : before.literals = after.literals)
    (program : @Program after E) (fn : Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (n : Nat)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (bound : @parameters before fn.signature.parameters args = some env)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (agrees : CodeAgrees before after fn.body)
    (executed : @CBody.run before n (.running fn.body env heap) = some (.returned result))
    (cast : @returnCast before fn.signature.result result.value = some returned) (behavior) :
    (@machine E after program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates [] ⟨returned, result.heap⟩ := by
  letI : CInterface := after
  apply body_call_behaviors program fn args env heap result returned n defined
    ((parameters_agreement before after sameTypes _ _).symm.trans bound) closed
    ((body_run_agreement before after sameTypes sameLiterals n
      (.running fn.body env heap) agrees).symm.trans executed)
    ((returnCast_agreement before after sameTypes _ _).symm.trans cast) behavior

end Rumoca.CCalls.Events
end
