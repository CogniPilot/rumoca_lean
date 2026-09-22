import RumocaEFMI.TensorDoStep

/-! Actual one-pointer eFMI method entry and complete ordinary DoStep call. -/
noncomputable section
namespace Rumoca.EFMI.ContextMethod
open CTree CMemory CMemory.TensorView CDeclaredMembers
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

def locals (base : Address) : CBody.Locals := CBody.bind (fun _ => none) "self" (.pointer (some base))
def types : CLoops.Types := CLoops.bindType (fun _ => none) "self" .pointer

theorem entry (unusedKernel : CSyntax.Program) (objects : Objects) (name : String)
    (code : List Stmt) (member : method name code ∈ TensorProduction.functions)
    (heap : Heap) (base : Address) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) (program unusedKernel) (.calling name [.pointer (some base)] heap stack) =
      some (.body (.running (method name code).body (locals base) types heap) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  have found := method_defined unusedKernel (method name code) member
  change (program unusedKernel).definitions name = some (.tree (method name code)) at found
  simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, found]
  rfl

theorem doStep (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (input rhs coefficients : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite coefficients[i])) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, ContextDoStep.Outcome objects heap finalHeap base input rhs coefficients ∧
      (∀ stack, Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
        (.calling doStepName [.pointer (some base)] heap stack)
        (.returning (.integer 0) finalHeap stack)) ∧
      ∀ behavior, (machine (expressions objects) (program unusedKernel)).Behaves
        (.calling doStepName [.pointer (some base)] heap .done) behavior ↔
        behavior = .terminates ⟨.integer 0, finalHeap⟩ := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨finalHeap, outcome, ran⟩ := ContextDoStep.body unusedKernel objects heap base input rhs coefficients
    storage executed adds (locals base) types rfl rfl rfl .done
  have entered := entry unusedKernel objects doStepName
    [.eval (.call (.id "rumoca_rhs") rhsArgs),
      .eval (.call (.id "rumoca_square_jacobian_diag") jacobianArgs)]
    (by simp [TensorProduction.functions, doStepFunction, rhsArgs, jacobianArgs]) heap base .done
  have complete : Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
      (.calling doStepName [.pointer (some base)] heap .done) (.halted ⟨.integer 0, finalHeap⟩) :=
    .next entered (ran.trans (.next rfl (.refl _)))
  exact ⟨finalHeap, outcome,
    fun stack => append_reaches (expressions objects) (program unusedKernel) complete stack,
    fun _ => (machine (expressions objects) (program unusedKernel)).behavior_iff complete rfl⟩

end Rumoca.EFMI.ContextMethod
