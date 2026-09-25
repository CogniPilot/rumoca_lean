import RumocaC.ContextCalls
import RumocaEFMI.TensorArrayMembers
import RumocaEFMI.TensorNumericalLinkage

/-! Actual eFMI tensor call arguments and status-clear/RHS dispatch in the
shared context-aware machine: the method prefix, the preflight dispatches and the
kernel dispatch. This is not helper completion. -/
noncomputable section
namespace Rumoca.EFMI.TensorContextCalls
open CTree CMemory CDeclaredMembers CContextMachine
open TensorProduction CTensor
variable [interface : CInterface]

def expressions (objects : Objects) : Expressions := declared TensorArrayMembers.declarations objects

def rhsArgs : List Expr :=
  [selfField inputVar.name, selfField inputVar.name, selfField squareVar.name, .nat inputVar.volume]

def jacobianArgs : List Expr :=
  [selfField inputVar.name, selfField jacobianVar.name, .nat inputVar.volume, .nat jacobianVar.volume]

def afterRhs : List Stmt :=
  [.eval (.call (.id "rumoca_square_jacobian_diag") jacobianArgs), .ret (some (selfField statusName))]

/-- DoStep after both preflight declarations: the failure test and the return. -/
def afterPreflights : List Stmt :=
  [.branch unchecked [.assign (selfField statusName) (.nat overflowStatus)] kernelCalls,
    .ret (some (selfField statusName))]

omit interface in
theorem doStep_body : doStepFunction.body =
    .assign (selfField statusName) (.nat 0) ::
      .declare "int32_t" "squares"
        (.call (.id CTensor.ProductPreflight.function.signature.name) preflightArgs) ::
      .declare "int32_t" "sums"
        (.call (.id CTensor.SumPreflight.function.signature.name) preflightArgs) ::
      afterPreflights := rfl

omit interface in
theorem kernel_body : kernelCalls ++ [.ret (some (selfField statusName))] =
    .eval (.call (.id "rumoca_rhs") rhsArgs) :: afterRhs := rfl

theorem rhs_arguments (rep : Represents TensorArrayMembers.declarations objects
    TensorArrayMembers.record heap base)
    (bound : env "self" = some (.pointer (some base))) :
    arguments (expressions objects) env heap rhsArgs =
      some [.pointer (some (base.member inputVar.name)), .pointer (some (base.member inputVar.name)),
        .pointer (some (base.member squareVar.name)), .integer inputVar.volume] := by
  have input := (TensorArrayMembers.array_argument rep inputVar (by simp [modelVars]) bound).1
  have output := (TensorArrayMembers.array_argument rep squareVar (by simp [modelVars]) bound).1
  simp only [rhsArgs, arguments, CCalls.argumentsWith, expressions, declared, CBody.declaredExpressions, input, output,
    CBody.evalWith, bind, Option.bind_some, pure]

theorem jacobian_arguments (rep : Represents TensorArrayMembers.declarations objects
    TensorArrayMembers.record heap base)
    (bound : env "self" = some (.pointer (some base))) :
    arguments (expressions objects) env heap jacobianArgs =
      some [.pointer (some (base.member inputVar.name)), .pointer (some (base.member jacobianVar.name)),
        .integer inputVar.volume, .integer jacobianVar.volume] := by
  have input := (TensorArrayMembers.array_argument rep inputVar (by simp [modelVars]) bound).1
  have output := (TensorArrayMembers.array_argument rep jacobianVar (by simp [modelVars]) bound).1
  simp only [jacobianArgs, arguments, CCalls.argumentsWith, expressions, declared, CBody.declaredExpressions, input, output,
    CBody.evalWith, bind, Option.bind_some, pure]

theorem preflight_arguments (rep : Represents TensorArrayMembers.declarations objects
    TensorArrayMembers.record heap base)
    (bound : env "self" = some (.pointer (some base))) :
    arguments (expressions objects) env heap preflightArgs =
      some (FinitePreflight.argumentValues (some (base.member inputVar.name))
        (some (base.member inputVar.name)) inputVar.volume) := by
  have input := (TensorArrayMembers.array_argument rep inputVar (by simp [modelVars]) bound).1
  simp only [preflightArgs, arguments, CCalls.argumentsWith, expressions, declared,
    CBody.declaredExpressions, input, CBody.evalWith, bind, Option.bind_some, pure,
    FinitePreflight.argumentValues]

/-- Status clearing changes no declaration context. Its actual store may be
proved from caller storage; array allocation/type representation survives it. -/
theorem method_clear (name : String) (body : List Stmt) (objects : Objects)
    (env : CBody.Locals) (types : CLoops.Types) (heap after : Heap) (base : Address)
    (bound : env "self" = some (.pointer (some base)))
    (stored : store heap (base.member statusName) (.integer 0) = some after) :
    loopNext (expressions objects) (.running (method name body).body env types heap) =
      some (.running (body ++ [.ret (some (selfField statusName))]) env types after) := by
  simp only [method, loopNext, CLoops.nextWith, CLoops.evalWith, expressions, declared,
    CBody.declaredExpressions, CBody.evalWith,
    selfField, CBody.lvalueWith, CBody.resolve, bound, Option.orElse_some,
    Value.address, if_true, Nat.cast_zero, stored, bind, Option.bind_some, pure]

/-- The kernel calls dispatch the RHS with pointers derived from actual array
declarations. No fabricated array-pointer cells. -/
theorem kernel_rhs_dispatch (p : CCalls.Program) (objects : Objects)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (base : Address)
    (rep : Represents TensorArrayMembers.declarations objects TensorArrayMembers.record heap base)
    (bound : env "self" = some (.pointer (some base)))
    (unshadowed : env "rumoca_rhs" = none)
    (stack : CCalls.Typed.Continuation) :
    next (expressions objects) p
      (.body (.running (kernelCalls ++ [.ret (some (selfField statusName))]) env types heap)
        statusAlias stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (base.member inputVar.name)), .pointer (some (base.member inputVar.name)),
          .pointer (some (base.member squareVar.name)), .integer inputVar.volume]
        heap (.caller .discard afterRhs env types statusAlias stack)) := by
  rw [kernel_body]
  exact declared_invoke_step TensorArrayMembers.declarations objects p "rumoca_rhs"
    rhsArgs _ afterRhs env types heap statusAlias stack (by decide +kernel) unshadowed
    (rhs_arguments rep bound)

end Rumoca.EFMI.TensorContextCalls
