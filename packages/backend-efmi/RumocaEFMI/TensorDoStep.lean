import RumocaEFMI.TensorPublicJacobian

/-! Whole actual DoStep body, including status clear, both nested numerical
calls and status return. Conditional finite arithmetic on the shared canonical machine. -/
noncomputable section
namespace Rumoca.EFMI.ContextDoStep
open CTree CMemory CMemory.TensorView CDeclaredMembers CDeclaredMembers.MemberStorage
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

structure Outcome (objects : Objects) (before after : Heap) (base : Address)
    (input rhs coefficients : Values inputShape) : Prop where
  storage : Storage objects after base input
  square : Reads after (base.member squareVar.name) rhs
  jacobian : Reads after (base.member jacobianVar.name)
    ((ArrayProfile.squareJacobianProgram inputShape).eval Finite.ops Binary64.positiveZero Binary64.one
      (ArrayProfile.environment input input))
  derivative : Finite.Executes (ArrayProfile.squareJacobianProgram inputShape).coefficients
    (ArrayProfile.environment input input) coefficients
  mathematical : SquareJacobianObservation.Observes after (base.member jacobianVar.name) input input
  status : load after (base.member statusName) = some (.integer 0)
  clock : after (base.member clockName) = before (base.member clockName)
  frame : ∀ q, q ≠ base.member statusName →
    (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
    (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
    after q = before q

theorem status_expression (objects : Objects) (heap : Heap) (base : Address)
    (input : Values inputShape) (storage : Storage objects heap base input)
    (env : CBody.Locals) (bound : env "self" = some (.pointer (some base)))
    (status : load heap (base.member statusName) = some (.integer 0)) :
    letI : CInterface := NumericalInterface.interface
    (expressions objects).value env heap (selfField statusName) = some (.integer 0) := by
  letI : CInterface := NumericalInterface.interface
  change CDeclaredMembers.eval TensorArrayMembers.declarations objects env heap _ = _
  rw [TensorArrayMembers.status_scalar storage.represents bound,
    TensorNumericalLinkage.selfField_eval env heap base statusName bound, status]

theorem body (unusedKernel : CSyntax.Program) (objects : Objects) (heap : Heap)
    (base : Address) (input rhs coefficients : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite coefficients[i]))
    (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base)))
    (rhsUnshadowed : env "rumoca_rhs" = none)
    (jacUnshadowed : env "rumoca_square_jacobian_diag" = none)
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    ∃ finalHeap, Outcome objects heap finalHeap base input rhs coefficients ∧
      Transition.Reaches (machine (expressions objects) (program unusedKernel)).step
        (.body (.running doStepFunction.body env types heap) statusAlias stack)
        (.returning (.integer 0) finalHeap stack) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨rhsHeap, rhsStorage, rhsReads, rhsFrame, rhsRan⟩ :=
    PublicRHS.helper unusedKernel objects (cleared heap base) base input rhs storage.after_clear executed
  obtain ⟨jacStorage, ad, jacRan, jacReads, observes, jacFrame⟩ :=
    PublicJacobian.helper unusedKernel objects rhsHeap base input rhs coefficients rhsStorage executed adds
  let finalHeap := Diagonal.resultHeap rhsHeap (base.member jacobianVar.name) coefficients
  have finalSquare : Reads finalHeap (base.member squareVar.name) rhs :=
    reads_framed rhsReads (PublicRHS.member_preserved jacFrame (by decide +kernel))
  have rhsStatus : rhsHeap (base.member statusName) = (cleared heap base) (base.member statusName) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved rhsFrame
      (show statusName ≠ squareVar.name by decide +kernel) 0
  have jacStatus : finalHeap (base.member statusName) = rhsHeap (base.member statusName) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved jacFrame
      (show statusName ≠ jacobianVar.name by decide +kernel) 0
  have finalStatus : load finalHeap (base.member statusName) = some (.integer 0) := by
    simpa only [load, jacStatus, rhsStatus] using (cleared_status_reads (heap := heap) (base := base))
  have rhsClock : rhsHeap (base.member clockName) = (cleared heap base) (base.member clockName) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved rhsFrame
      (show clockName ≠ squareVar.name by decide +kernel) 0
  have jacClock : finalHeap (base.member clockName) = rhsHeap (base.member clockName) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved jacFrame
      (show clockName ≠ jacobianVar.name by decide +kernel) 0
  have outcome : Outcome objects heap finalHeap base input rhs coefficients :=
    ⟨jacStorage, finalSquare, jacReads, ad, observes, finalStatus,
      jacClock.trans (rhsClock.trans storage.clock_after_clear.1),
      fun q status outsideX outsideJ =>
        (jacFrame q outsideJ).trans ((rhsFrame q outsideX).trans (cleared_other status))⟩
  have dispatched := doStep_rhs_dispatch (program unusedKernel) objects env types heap
    (cleared heap base) base storage.represents bound rhsUnshadowed storage.clear_store stack
  have rhsDone := (rhsRan.1 (.caller .discard afterRhs env types statusAlias stack)).trans
    (Transition.Reaches.next (show next (expressions objects) (program unusedKernel)
      (.returning .void rhsHeap (.caller .discard afterRhs env types statusAlias stack)) =
      some (.body (.running afterRhs env types rhsHeap) statusAlias stack) from rfl) (.refl _))
  have jacDone := invoke_reaches (expressions objects) (program unusedKernel) jacRan jacobianArgs
    [.ret (some (selfField statusName))] env types statusAlias stack (by decide +kernel)
    jacUnshadowed (by rfl) (jacobian_arguments rhsStorage.represents bound)
  have evaluated := status_expression objects finalHeap base input jacStorage env bound finalStatus
  have typed : typedEval (expressions objects) env types finalHeap (selfField statusName) =
      some (.integer 0) := evaluated
  have returnStep : next (expressions objects) (program unusedKernel)
      (.body (.running [.ret (some (selfField statusName))] env types finalHeap) statusAlias stack) =
      some (.body (.returned ⟨.integer 0, finalHeap⟩) statusAlias stack) := by
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, CLoops.nextWith, typed, bind, Option.bind_some, pure]
  have castStep : next (expressions objects) (program unusedKernel)
      (.body (.returned ⟨.integer 0, finalHeap⟩) statusAlias stack) =
      some (.returning (.integer 0) finalHeap stack) := by rfl
  exact ⟨finalHeap, outcome, dispatched.trans (rhsDone.trans
    (jacDone.trans (.next returnStep (.next castStep (.refl _)))))⟩

end Rumoca.EFMI.ContextDoStep
