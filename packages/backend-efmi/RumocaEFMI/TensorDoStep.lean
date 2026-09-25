import RumocaEFMI.TensorPublicJacobian
import RumocaC.TensorProductPreflightContract
import RumocaC.TensorSumPreflightContract

/-! Whole actual DoStep body on the shared canonical machine, for every
represented finite input: status clear, both read-only preflight calls, the
failure test, and either the `OVERFLOW` status store or both nested numerical
calls, then the status return. Exactly two outcomes exist. No finite-square to
finite-sum fact is used: the sum preflight supplies the coefficient domain. -/
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
  clock : after (base.member GALEC.Names.clock) = before (base.member GALEC.Names.clock)
  frame : ∀ q, q ≠ base.member statusName →
    (∀ i < squareShape.volume, q ≠ (base.member squareVar.name).index i) →
    (∀ i < jacobianShape.volume, q ≠ (base.member jacobianVar.name).index i) →
    after q = before q

/-- The overflow outcome: the status holds the encoding of `{OVERFLOW}`, every
other cell is unchanged, and the storage stays represented. -/
structure OverflowOutcome (objects : Objects) (before after : Heap) (base : Address)
    (input : Values inputShape) : Prop where
  storage : Storage objects after base input
  status : load after (base.member statusName) = some (.integer overflowStatus)
  frame : ∀ q, q ≠ base.member statusName → after q = before q

/-- Result of the product preflight on the input. -/
def products (input : Values inputShape) : Bool :=
  Numerical.allFiniteBits (MultiplicationTotal.result input input)

/-- Result of the sum preflight on the input. -/
def sums (input : Values inputShape) : Bool :=
  Numerical.allFiniteBits (SumPreflight.result input input)

/-- The AD coefficients of the prepared Jacobian at the input. -/
def coefficients (input : Values inputShape) : Values inputShape :=
  (ArrayProfile.squareJacobianProgram inputShape).coefficients.eval Finite.ops
    Binary64.positiveZero Binary64.one (ArrayProfile.environment input input)

/-- The sum preflight alone supplies the coefficient arithmetic. -/
theorem sum_adds (input : Values inputShape) (finite : sums input = true) :
    ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite (coefficients input)[i]) := by
  intro i
  have domain := (SumPreflight.result_allFinite input input).mp finite i
  refine ⟨(Binary64.sum_above_negative_overflow _ _).mpr domain.1,
    (Binary64.sum_below_overflow _ _).mpr domain.2, ?_⟩
  rw [coefficients, ArrayProfile.ADExact.coefficients_eval_get]
  exact Binary64.roundedAdd_spec _ _

theorem status_expression (objects : Objects) (heap : Heap) (base : Address)
    (input : Values inputShape) (storage : Storage objects heap base input)
    (env : CBody.Locals) (bound : env "self" = some (.pointer (some base))) (value : Int)
    (status : load heap (base.member statusName) = some (.integer value)) :
    letI : CInterface := NumericalInterface.interface
    (expressions objects).value env heap (selfField statusName) = some (.integer value) := by
  letI : CInterface := NumericalInterface.interface
  change CDeclaredMembers.eval TensorArrayMembers.declarations objects env heap _ = _
  rw [TensorArrayMembers.status_scalar storage.represents bound,
    TensorNumericalLinkage.selfField_eval env heap base statusName bound, status]

theorem boolean_int32 (flag : Bool) : convert .int32 (CBody.boolean flag) = some (CBody.boolean flag) := by
  cases flag <;> rfl

/-- The kernel calls after a passing check, from the cleared store. -/
theorem kernel_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p) (objects : Objects)
    (heap : Heap) (base : Address) (input rhs coefficients : Values inputShape)
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
      Transition.Reaches (machine (expressions objects) p).step
        (.body (.running (kernelCalls ++ [.ret (some (selfField statusName))]) env types
          (cleared heap base)) statusAlias stack)
        (.returning (.integer 0) finalHeap stack) := by
  letI : CInterface := NumericalInterface.interface
  obtain ⟨rhsHeap, rhsStorage, rhsReads, rhsFrame, rhsRan⟩ :=
    PublicRHS.helper_in p linked objects (cleared heap base) base input rhs storage.after_clear executed
  obtain ⟨jacStorage, ad, jacRan, jacReads, observes, jacFrame⟩ :=
    PublicJacobian.helper_in p linked objects rhsHeap base input rhs coefficients rhsStorage executed adds
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
  have rhsClock : rhsHeap (base.member GALEC.Names.clock) = (cleared heap base) (base.member GALEC.Names.clock) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved rhsFrame
      (show GALEC.Names.clock ≠ squareVar.name by decide +kernel) 0
  have jacClock : finalHeap (base.member GALEC.Names.clock) = rhsHeap (base.member GALEC.Names.clock) := by
    simpa only [Address.index_zero] using PublicRHS.member_preserved jacFrame
      (show GALEC.Names.clock ≠ jacobianVar.name by decide +kernel) 0
  have outcome : Outcome objects heap finalHeap base input rhs coefficients :=
    ⟨jacStorage, finalSquare, jacReads, ad, observes, finalStatus,
      jacClock.trans (rhsClock.trans storage.clock_after_clear.1),
      fun q status outsideX outsideJ =>
        (jacFrame q outsideJ).trans ((rhsFrame q outsideX).trans (cleared_other status))⟩
  have dispatched := kernel_rhs_dispatch p objects env types (cleared heap base) base
    storage.after_clear.represents bound rhsUnshadowed stack
  have rhsDone := (rhsRan.1 (.caller .discard afterRhs env types statusAlias stack)).trans
    (Transition.Reaches.next (show next (expressions objects) p
      (.returning .void rhsHeap (.caller .discard afterRhs env types statusAlias stack)) =
      some (.body (.running afterRhs env types rhsHeap) statusAlias stack) from rfl) (.refl _))
  have jacDone := invoke_reaches (expressions objects) p jacRan jacobianArgs
    [.ret (some (selfField statusName))] env types statusAlias stack (by decide +kernel)
    jacUnshadowed (by rfl) (jacobian_arguments rhsStorage.represents bound)
  have evaluated := status_expression objects finalHeap base input jacStorage env bound 0 finalStatus
  have typed : typedEval (expressions objects) env types finalHeap (selfField statusName) =
      some (.integer 0) := evaluated
  have returnStep : next (expressions objects) p
      (.body (.running [.ret (some (selfField statusName))] env types finalHeap) statusAlias stack) =
      some (.body (.returned ⟨.integer 0, finalHeap⟩) statusAlias stack) := by
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, CLoops.nextWith, typed, bind, Option.bind_some, pure]
  have castStep : next (expressions objects) p
      (.body (.returned ⟨.integer 0, finalHeap⟩) statusAlias stack) =
      some (.returning (.integer 0) finalHeap stack) := by rfl
  exact ⟨finalHeap, outcome, .next dispatched (rhsDone.trans
    (jacDone.trans (.next returnStep (.next castStep (.refl _)))))⟩

/-- Locals after both preflight declarations. -/
def checkedLocals (env : CBody.Locals) (input : Values inputShape) : CBody.Locals :=
  CBody.bind (CBody.bind env "squares" (CBody.boolean (products input))) "sums"
    (CBody.boolean (sums input))

def checkedTypes (types : CLoops.Types) : CLoops.Types :=
  CLoops.bindType (CLoops.bindType types "squares" .int32) "sums" .int32

/-- Fresh locals and unshadowed callees of the DoStep body. -/
structure Unshadowed (env : CBody.Locals) : Prop where
  squares : env "squares" = none
  sums : env "sums" = none
  product : env ProductPreflight.function.signature.name = none
  sum : env SumPreflight.function.signature.name = none
  rhs : env "rumoca_rhs" = none
  jacobian : env "rumoca_square_jacobian_diag" = none

/-- Status clear and both read-only preflights: the store is only cleared,
and the locals hold both classifications. -/
theorem preflights_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (objects : Objects) (heap : Heap) (base : Address) (input : Values inputShape)
    (storage : Storage objects heap base input) (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base))) (fresh : Unshadowed env)
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    Transition.Reaches (machine (expressions objects) p).step
      (.body (.running doStepFunction.body env types heap) statusAlias stack)
      (.body (.running afterPreflights (checkedLocals env input) (checkedTypes types)
        (cleared heap base)) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  have clearedStorage := storage.after_clear
  have clearing := method_clear doStepName
    [.declare "int32_t" "squares" (.call (.id ProductPreflight.function.signature.name) preflightArgs),
     .declare "int32_t" "sums" (.call (.id SumPreflight.function.signature.name) preflightArgs),
     .branch unchecked [.assign (selfField statusName) (.nat overflowStatus)] kernelCalls]
    objects env types heap (cleared heap base) base bound storage.clear_store
  have first : next (expressions objects) p
      (.body (.running doStepFunction.body env types heap) statusAlias stack) =
      some (.body (.running (.declare "int32_t" "squares"
          (.call (.id ProductPreflight.function.signature.name) preflightArgs) ::
        .declare "int32_t" "sums" (.call (.id SumPreflight.function.signature.name) preflightArgs) ::
        afterPreflights) env types (cleared heap base)) statusAlias stack) := by
    have direct : CLoops.nextWith (expressions objects) (.running doStepFunction.body env types heap) =
        some (.running (.declare "int32_t" "squares"
            (.call (.id ProductPreflight.function.signature.name) preflightArgs) ::
          .declare "int32_t" "sums" (.call (.id SumPreflight.function.signature.name) preflightArgs) ::
          afterPreflights) env types (cleared heap base)) := clearing
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, direct]
  have readable : FiniteScan.Readable (cleared heap base) (some (base.member inputVar.name))
      (EncodedTensor.finiteBits input) := by
    intro i
    refine ⟨base.member inputVar.name, rfl, ?_⟩
    simpa only [Fin.getElem_fin, EncodedTensor.finiteBits_get] using clearedStorage.input_reads i
  let afterSquares : List Stmt :=
    .declare "int32_t" "sums" (.call (.id SumPreflight.function.signature.name) preflightArgs) ::
      afterPreflights
  have callSquares := declared_declare_step TensorArrayMembers.declarations objects p
    ProductPreflight.function.signature.name preflightArgs _ "int32_t" "squares" .int32
    afterSquares env types (cleared heap base) statusAlias stack (by decide +kernel) fresh.product rfl
    (preflight_arguments clearedStorage.represents bound)
  have ranSquares := ProductPreflight.call_reaches TensorArrayMembers.declarations objects p input input
    (cleared heap base) (some (base.member inputVar.name)) (some (base.member inputVar.name))
    (.caller (.declare "int32_t" "squares") afterSquares env types statusAlias stack)
    (linked _ _ product_preflight_defined) NumericalInterface.preflight_header readable readable
    (by decide +kernel)
  have resumeSquares := resume_declare (expressions objects) p
    (CBody.boolean (products input)) (CBody.boolean (products input)) (cleared heap base)
    "int32_t" "squares" .int32 afterSquares env types statusAlias stack fresh.squares rfl
    (boolean_int32 _)
  let env1 := CBody.bind env "squares" (CBody.boolean (products input))
  let types1 := CLoops.bindType types "squares" .int32
  have bound1 : env1 "self" = some (.pointer (some base)) := by simp [env1, CBody.bind, bound]
  have callSums := declared_declare_step TensorArrayMembers.declarations objects p
    SumPreflight.function.signature.name preflightArgs _ "int32_t" "sums" .int32
    afterPreflights env1 types1 (cleared heap base) statusAlias stack (by decide +kernel)
    (by simpa [env1, CBody.bind, SumPreflight.function, FinitePreflight.operation] using fresh.sum) rfl
    (preflight_arguments clearedStorage.represents bound1)
  have ranSums := SumPreflight.call_reaches TensorArrayMembers.declarations objects p input input
    (cleared heap base) (some (base.member inputVar.name)) (some (base.member inputVar.name))
    (.caller (.declare "int32_t" "sums") afterPreflights env1 types1 statusAlias stack)
    (linked _ _ sum_preflight_defined) NumericalInterface.preflight_header readable readable
    (by decide +kernel)
  have resumeSums := resume_declare (expressions objects) p
    (CBody.boolean (sums input)) (CBody.boolean (sums input)) (cleared heap base)
    "int32_t" "sums" .int32 afterPreflights env1 types1 statusAlias stack
    (by simp [env1, CBody.bind, fresh.sums]) rfl (boolean_int32 _)
  exact .next first (.next callSquares (ranSquares.trans (.next resumeSquares
    (.next callSums (ranSums.trans (.next resumeSums (.refl _)))))))

/-- The failure test selects the status store exactly when a check failed. -/
theorem branch_step (p : CCalls.Program) (objects : Objects) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (input : Values inputShape) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) p
      (.body (.running afterPreflights (checkedLocals env input) types heap) statusAlias stack) =
      some (.body (.running
        ((if products input && sums input then kernelCalls
          else [.assign (selfField statusName) (.nat overflowStatus)]) ++
          [.ret (some (selfField statusName))]) (checkedLocals env input) types heap) statusAlias stack) := by
  letI : CInterface := NumericalInterface.interface
  cases hp : products input <;> cases hs : sums input <;>
    simp [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, CLoops.nextWith,
      afterPreflights, unchecked, kernelCalls, CLoops.noDeclarations, CLoops.evalWith,
      expressions, declared, CBody.declaredExpressions, CBody.evalWith, CBody.resolve,
      checkedLocals, CBody.bind, hp, hs, CBody.comparison, CBody.boolean, Value.truth]

/-- The overflow branch stores the status and returns it; nothing else changes. -/
theorem overflow_in (p : CCalls.Program) (objects : Objects) (heap : Heap) (base : Address)
    (input : Values inputShape) (storage : Storage objects heap base input)
    (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base))) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    Transition.Reaches (machine (expressions objects) p).step
      (.body (.running ([.assign (selfField statusName) (.nat overflowStatus)] ++
        [.ret (some (selfField statusName))]) env types (cleared heap base)) statusAlias stack)
      (.returning (.integer overflowStatus) (raised (cleared heap base) base) stack) := by
  letI : CInterface := NumericalInterface.interface
  have clearedStorage := storage.after_clear
  have stored := raise_of_status clearedStorage.status
  have assignStep : next (expressions objects) p
      (.body (.running ([.assign (selfField statusName) (.nat overflowStatus)] ++
        [.ret (some (selfField statusName))]) env types (cleared heap base)) statusAlias stack) =
      some (.body (.running [.ret (some (selfField statusName))] env types
        (raised (cleared heap base) base)) statusAlias stack) := by
    simp only [List.cons_append, List.nil_append, next, CCalls.Typed.nextIn,
      CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, expressions, declared,
      CBody.declaredExpressions, CBody.evalWith, selfField, CBody.lvalueWith, CBody.resolve, bound,
      Option.orElse_some, Value.address, stored, bind, Option.bind_some, pure, ↓reduceIte,
      Option.bind_some]
  have evaluated := status_expression objects (raised (cleared heap base) base) base input
    clearedStorage.after_raise env bound overflowStatus raised_status_reads
  have typed : typedEval (expressions objects) env types (raised (cleared heap base) base)
      (selfField statusName) = some (.integer overflowStatus) := evaluated
  have returnStep : next (expressions objects) p
      (.body (.running [.ret (some (selfField statusName))] env types
        (raised (cleared heap base) base)) statusAlias stack) =
      some (.body (.returned ⟨.integer overflowStatus, raised (cleared heap base) base⟩)
        statusAlias stack) := by
    simp only [next, CCalls.Typed.nextIn, CCalls.Typed.nextWithExpressions, CLoops.nextWith,
      typed, bind, Option.bind_some, pure]
  have castStep : next (expressions objects) p
      (.body (.returned ⟨.integer overflowStatus, raised (cleared heap base) base⟩) statusAlias stack) =
      some (.returning (.integer overflowStatus) (raised (cleared heap base) base) stack) := by rfl
  exact .next assignStep (.next returnStep (.next castStep (.refl _)))

theorem overflow_outcome (storage : Storage objects heap base input) :
    OverflowOutcome objects heap (raised (cleared heap base) base) base input :=
  ⟨storage.after_clear.after_raise, raised_status_reads,
    fun _ different => (raised_other different).trans (cleared_other different)⟩

/-- Exactly two outcomes of the whole body, for every represented finite
input: every product and sum finite, status zero and the square/AD outputs;
otherwise the `OVERFLOW` status with every other cell unchanged. -/
theorem body_outcomes_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (objects : Objects) (heap : Heap) (base : Address) (input : Values inputShape)
    (storage : Storage objects heap base input) (env : CBody.Locals) (types : CLoops.Types)
    (bound : env "self" = some (.pointer (some base))) (fresh : Unshadowed env)
    (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    (products input = true ∧ sums input = true ∧
      ∃ rhs finalHeap, Finite.Executes (ArrayProfile.squareProgram inputShape)
        (ArrayProfile.environment input input) rhs ∧
        Outcome objects heap finalHeap base input rhs (coefficients input) ∧
        Transition.Reaches (machine (expressions objects) p).step
          (.body (.running doStepFunction.body env types heap) statusAlias stack)
          (.returning (.integer 0) finalHeap stack)) ∨
    ((products input = false ∨ sums input = false) ∧
      OverflowOutcome objects heap (raised (cleared heap base) base) base input ∧
      Transition.Reaches (machine (expressions objects) p).step
        (.body (.running doStepFunction.body env types heap) statusAlias stack)
        (.returning (.integer overflowStatus) (raised (cleared heap base) base) stack)) := by
  letI : CInterface := NumericalInterface.interface
  have pre := preflights_in p linked objects heap base input storage env types bound fresh stack
  have branched := branch_step p objects env (checkedTypes types) (cleared heap base) input stack
  have bound2 : checkedLocals env input "self" = some (.pointer (some base)) := by
    simp [checkedLocals, CBody.bind, bound]
  cases hp : products input <;> cases hs : sums input
  all_goals simp only [hp, hs, Bool.and_false, Bool.and_true, Bool.false_eq_true, if_false,
    if_true] at branched
  · exact Or.inr ⟨Or.inl rfl, overflow_outcome storage,
      pre.trans (.next branched (overflow_in p objects heap base input storage _ _ bound2 stack))⟩
  · exact Or.inr ⟨Or.inl rfl, overflow_outcome storage,
      pre.trans (.next branched (overflow_in p objects heap base input storage _ _ bound2 stack))⟩
  · exact Or.inr ⟨Or.inr rfl, overflow_outcome storage,
      pre.trans (.next branched (overflow_in p objects heap base input storage _ _ bound2 stack))⟩
  · obtain ⟨rhs, executed⟩ := (ProductPreflight.square_finite_execution input input).mp hp
    obtain ⟨finalHeap, outcome, ran⟩ := kernel_in p linked objects heap base input rhs
      (coefficients input) storage executed (sum_adds input hs) (checkedLocals env input)
      (checkedTypes types) bound2 (by simp [checkedLocals, CBody.bind, fresh.rhs])
      (by simp [checkedLocals, CBody.bind, fresh.jacobian]) stack
    exact Or.inl ⟨rfl, rfl, rhs, finalHeap, executed, outcome, pre.trans (.next branched ran)⟩

end Rumoca.EFMI.ContextDoStep
