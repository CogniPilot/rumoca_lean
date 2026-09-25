import RumocaEFMI.TensorDoStep

/-! Actual one-pointer eFMI method entry and the complete DoStep call with its
two outcomes. -/
noncomputable section
namespace Rumoca.EFMI.ContextMethod
open CTree CMemory CMemory.TensorView CDeclaredMembers
open CTensor Solve.Tensor TensorProduction TensorPublicStorage TensorNumericalLinkage
open CContextMachine TensorContextCalls

def locals (base : Address) : CBody.Locals := CBody.bind (fun _ => none) "self" (.pointer (some base))
def types : CLoops.Types := CLoops.bindType (fun _ => none) "self" .pointer

/-- Exact method return with the given status, including every saved
continuation and all canonical top-level behaviors, for a supplied function table. -/
def Returns (p : CCalls.Program) (objects : Objects) (name : String)
    (heap after : Heap) (base : Address) (status : Int) : Prop :=
  letI : CInterface := NumericalInterface.interface
  (∀ stack, Transition.Reaches (machine (expressions objects) p).step
    (.calling name [.pointer (some base)] heap stack)
    (.returning (.integer status) after stack)) ∧
  ∀ behavior, (machine (expressions objects) p).Behaves
    (.calling name [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates ⟨.integer status, after⟩

/-- An ordinary return: the status encodes the empty signal set. -/
def Completes (p : CCalls.Program) (objects : Objects) (name : String)
    (heap after : Heap) (base : Address) : Prop :=
  Returns p objects name heap after base 0

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

theorem returns_in (p : CCalls.Program) (objects : Objects) (name : String) (code : List Stmt)
    (found : p.definitions name = some (.tree (method name code)))
    (heap after : Heap) (base : Address) (status : Int)
    (ran : letI : CInterface := NumericalInterface.interface
      Transition.Reaches (machine (expressions objects) p).step
        (.body (.running (method name code).body (locals base)
          types heap) statusAlias .done)
        (.returning (.integer status) after .done)) :
    Returns p objects name heap after base status := by
  letI : CInterface := NumericalInterface.interface
  have entered := entry_in p objects name code found heap base .done
  have finished : Transition.Reaches (machine (expressions objects) p).step
      (.calling name [.pointer (some base)] heap .done) (.halted ⟨.integer status, after⟩) :=
    .next entered (ran.trans (.next rfl (.refl _)))
  exact ⟨fun stack => append_reaches (expressions objects) p finished stack,
    fun _ => (machine (expressions objects) p).behavior_iff finished rfl⟩

theorem complete_in (p : CCalls.Program) (objects : Objects) (name : String) (code : List Stmt)
    (found : p.definitions name = some (.tree (method name code)))
    (heap after : Heap) (base : Address)
    (ran : letI : CInterface := NumericalInterface.interface
      Transition.Reaches (machine (expressions objects) p).step
        (.body (.running (method name code).body (locals base)
          types heap) statusAlias .done)
        (.returning (.integer 0) after .done)) :
    Completes p objects name heap after base :=
  returns_in p objects name code found heap after base 0 ran

theorem entry (unusedKernel : CSyntax.Program) (objects : Objects) (name : String)
    (code : List Stmt) (member : method name code ∈ TensorProduction.functions)
    (heap : Heap) (base : Address) (stack : CCalls.Typed.Continuation) :
    letI : CInterface := NumericalInterface.interface
    next (expressions objects) (program unusedKernel) (.calling name [.pointer (some base)] heap stack) =
      some (.body (.running (method name code).body (locals base) types heap) statusAlias stack) :=
  entry_in (program unusedKernel) objects name code
    (method_defined unusedKernel (method name code) member) heap base stack

theorem fresh (base : Address) : ContextDoStep.Unshadowed (locals base) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [locals, CBody.bind, ProductPreflight.function, SumPreflight.function,
      FinitePreflight.operation]

/-- The two outcomes of the public DoStep call, for every represented finite
input: every product and sum finite, an ordinary return and the square/AD
outputs; otherwise the `OVERFLOW` status with every other cell unchanged. -/
theorem doStep_outcomes_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (found : p.definitions doStepName = some (.tree doStepFunction))
    (objects : Objects) (heap : Heap) (base : Address) (input : Values inputShape)
    (storage : Storage objects heap base input) :
    (ContextDoStep.products input = true ∧ ContextDoStep.sums input = true ∧
      ∃ rhs after, Finite.Executes (ArrayProfile.squareProgram inputShape)
        (ArrayProfile.environment input input) rhs ∧
        ContextDoStep.Outcome objects heap after base input rhs (ContextDoStep.coefficients input) ∧
        Completes p objects doStepName heap after base) ∨
    ((ContextDoStep.products input = false ∨ ContextDoStep.sums input = false) ∧
      ContextDoStep.OverflowOutcome objects heap (raised (cleared heap base) base) base input ∧
      Returns p objects doStepName heap (raised (cleared heap base) base) base overflowStatus) := by
  letI : CInterface := NumericalInterface.interface
  rcases ContextDoStep.body_outcomes_in p linked objects heap base input storage (locals base) types
      rfl (fresh base) .done with
    ⟨products, sums, rhs, after, executed, outcome, ran⟩ | ⟨failed, outcome, ran⟩
  · exact Or.inl ⟨products, sums, rhs, after, executed, outcome,
      returns_in p objects doStepName _ found heap after base 0 ran⟩
  · exact Or.inr ⟨failed, outcome,
      returns_in p objects doStepName _ found heap _ base overflowStatus ran⟩

/-- Coefficients with finite sums are the prepared AD coefficients. -/
theorem coefficients_unique (input coefficients : Values inputShape)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite coefficients[i])) :
    coefficients = ContextDoStep.coefficients input := by
  have sums : ContextDoStep.sums input = true := by
    apply (SumPreflight.result_allFinite input input).mpr
    intro i
    exact ⟨(Binary64.sum_above_negative_overflow _ _).mp (adds i).1,
      (Binary64.sum_below_overflow _ _).mp (adds i).2.1⟩
  apply Tensor.Value.ext
  intro i hi
  have same := Binary64.adds_unique (adds ⟨i, hi⟩) (ContextDoStep.sum_adds input sums ⟨i, hi⟩)
  exact Float64.Number.finite.inj same

/-- Finite primal execution and finite coefficient sums give the ordinary return. -/
theorem doStep_in (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (found : p.definitions doStepName = some (.tree doStepFunction))
    (objects : Objects) (heap : Heap) (base : Address) (input rhs coefficients : Values inputShape)
    (storage : Storage objects heap base input)
    (executed : Finite.Executes (ArrayProfile.squareProgram inputShape)
      (ArrayProfile.environment input input) rhs)
    (adds : ∀ i : Fin inputShape.volume, Binary64.Adds input[i] input[i] (.finite coefficients[i])) :
    ∃ after, ContextDoStep.Outcome objects heap after base input rhs coefficients ∧
      Completes p objects doStepName heap after base := by
  rw [coefficients_unique input coefficients adds]
  rcases doStep_outcomes_in p linked found objects heap base input storage with
    ⟨_, _, other, after, otherRan, outcome, completed⟩ | ⟨failed, _, _⟩
  · have same := Finite.execution_unique otherRan executed
    subst same
    exact ⟨after, outcome, completed⟩
  · exfalso
    rcases failed with products | sums
    · have finite := (ProductPreflight.square_finite_execution input input).mpr ⟨rhs, executed⟩
      simp [ContextDoStep.products, finite] at products
    · have finite : ContextDoStep.sums input = true := by
        apply (SumPreflight.result_allFinite input input).mpr
        intro i
        exact ⟨(Binary64.sum_above_negative_overflow _ _).mp (adds i).1,
          (Binary64.sum_below_overflow _ _).mp (adds i).2.1⟩
      rw [finite] at sums
      cases sums

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
