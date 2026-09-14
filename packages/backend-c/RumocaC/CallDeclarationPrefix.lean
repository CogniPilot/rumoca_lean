import RumocaC.NamedDeclarations
import RumocaC.CallEventPrefix

/-! Compose ordinary external calls in fresh declarations with their
typed continuation, preserving every later eventful behavior. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CMemory CTree
variable [interface : CInterface]

/-- A determinate external call in a fresh declaration reaches its ordinary
continuation. Future callbacks remain unrestricted by this finite prefix. -/
theorem external_declaration_path (program : Program E)
    (env : CBody.Locals) (types : CLoops.Types) (heap after : Heap)
    (declaredType destination callee : String) (args : List Expr) (values converted : List Value)
    (rest : List Stmt) (resultType : String) (stack : Typed.Continuation)
    (fn : External E) (events : List E) (value result : Value) (type : CType)
    (fresh : env destination = none) (unshadowed : env callee = none)
    (named : interface.constants callee = none) (ordinary : callee ≠ "isfinite")
    (evaluated : arguments env heap args = some values)
    (found : program.externals callee = some fn)
    (parameters : convertedArguments fn.signature.parameters values = some converted)
    (executed : fn.execute converted heap events value after)
    (unique : ∀ trace output changed, fn.execute converted heap trace output changed →
      trace = events ∧ output = value ∧ changed = after)
    (typed : interface.types declaredType = some type)
    (cast : convert type value = some result) :
    Transition.Events.Prefix (machine program)
      (.body (.running (.declare declaredType destination (.call (.id callee) args) :: rest)
        env types heap) resultType stack)
      events
      (.body (.running rest (CBody.bind env destination result)
        (CLoops.bindType types destination type) after) resultType stack) := by
  have entered := internal_path program (.next
    (named_declare_entry program env types heap declaredType destination callee args values
      rest resultType stack fresh unshadowed named ordinary evaluated) (.refl _))
  have called := external_path program found parameters executed unique
    (.caller (.declare declaredType destination) rest env types resultType stack)
  have returned := internal_path program (.next
    (declare_result program env types after declaredType destination rest resultType stack
      value result type fresh typed cast) (.refl _))
  simpa only [List.nil_append, List.append_nil] using (entered.trans called).trans returned


end Rumoca.CCalls.Events
end
