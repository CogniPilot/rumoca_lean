import RumocaEFMI.TensorDoStep
import RumocaCore.Array.ADFiniteSquare

/-! Actual one-pointer eFMI method entry and complete ordinary DoStep call. -/
noncomputable section
namespace Rumoca.EFMI.ContextMethod
open CTree CMemory CMemory.TensorView CDeclaredMembers
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

def locals (base : Address) : CBody.Locals := CBody.bind (fun _ => none) "self" (.pointer (some base))
def types : CLoops.Types := CLoops.bindType (fun _ => none) "self" .pointer

/-- Exact ordinary method return, including every saved continuation and all
canonical top-level behaviors, for a supplied function table. -/
def Completes (p : CCalls.Program) (objects : Objects) (name : String)
    (heap after : Heap) (base : Address) : Prop :=
  letI : CInterface := NumericalInterface.interface
  (∀ stack, Transition.Reaches (machine (expressions objects) p).step
    (.calling name [.pointer (some base)] heap stack)
    (.returning (.integer 0) after stack)) ∧
  ∀ behavior, (machine (expressions objects) p).Behaves
    (.calling name [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, after⟩

theorem entry_in (p : CCalls.Program) (objects : Objects) (name : String) (code : List Stmt)
    (found : p.definitions name = some (.tree (method name code)))
    (heap : Heap) (base : Address) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) p (.calling name [.pointer (some base)] heap stack) =
      some (.body (.running (method name code).body (locals base)
        types heap) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, found]
  rfl

theorem complete_in (p : CCalls.Program) (objects : Objects) (name : String) (code : List Stmt)
    (found : p.definitions name = some (.tree (method name code)))
    (heap after : Heap) (base : Address)
    (ran : letI : CInterface := NumericalInterface.interface
      Transition.Reaches (machine (expressions objects) p).step
        (.body (.running (method name code).body (locals base)
          types heap) statusAlias .done)
        (.returning (.integer 0) after .done)) :
    Completes p objects name heap after base := by
  letI : CInterface := NumericalInterface.interface
  have entered := entry_in p objects name code found heap base .done
  have finished : Transition.Reaches (machine (expressions objects) p).step
      (.calling name [.pointer (some base)] heap .done) (.halted ⟨.integer 0, after⟩) :=
    .next entered (ran.trans (.next rfl (.refl _)))
  exact ⟨fun stack => append_reaches (expressions objects) p finished stack,
    fun _ => (machine (expressions objects) p).behavior_iff finished rfl⟩

theorem entry (unusedKernel : CSyntax.Program) (objects : Objects) (name : String)
    (code : List Stmt) (member : method name code ∈ TensorProduction.functions)
    (heap : Heap) (base : Address) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) (program unusedKernel) (.calling name [.pointer (some base)] heap stack) =
      some (.body (.running (method name code).body (locals base) types heap) statusAlias stack) :=
  entry_in (program unusedKernel) objects name code
    (method_defined unusedKernel (method name code) member) heap base stack


theorem doStep_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (found : p.definitions doStepName = some (.tree doStepFunction))
    (objects : Objects) (heap : Heap) (base : Address) (input rhs coefficients : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite coefficients[i])) :
    ∃ after, ContextDoStep.Outcome objects heap after base input rhs coefficients ∧
      Completes p objects doStepName heap after base := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨after, outcome, ran⟩ := ContextDoStep.body_in p linked objects heap base input rhs coefficients
    storage executed adds (locals base) types rfl rfl rfl .done
  exact ⟨after, outcome, complete_in p objects doStepName
    [.eval (.call (.id "rumoca_rhs") rhsArgs),
      .eval (.call (.id "rumoca_square_jacobian_diag") jacobianArgs)]
    found heap after base ran⟩

def coefficients (input : Values inputShape) : Values inputShape :=
  (ArrayProfile.squareJacobianProgram inputShape).coefficients.eval Finite.ops
    Binary64.positiveZero Binary64.one (ArrayProfile.environment input input)

/-- Finite primal execution derives the actual AD coefficient arithmetic;
no independent addition domain is required. -/
theorem doStep_from_rhs_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (found : p.definitions doStepName = some (.tree doStepFunction))
    (objects : Objects) (heap : Heap) (base : Address) (input rhs : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs) :
    ∃ after, ContextDoStep.Outcome objects heap after base input rhs (coefficients input) ∧
      Completes p objects doStepName heap after base :=
  doStep_in p linked found objects heap base input rhs (coefficients input) storage executed
    (ArrayProfile.ADExact.coefficient_adds_from_finite_rhs input input rhs executed)

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
        behavior = .terminates ⟨.integer 0, finalHeap⟩ :=
  doStep_in (program unusedKernel) (numerical_in_actual unusedKernel)
    (method_defined unusedKernel doStepFunction (by simp [TensorProduction.functions]))
    objects heap base input rhs coefficients storage executed adds

end Rumoca.EFMI.ContextMethod
