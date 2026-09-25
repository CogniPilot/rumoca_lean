import RumocaCore.GALEC.Elaboration.Expressions
import RumocaCore.GALEC.Elaboration.Signals.Names
import RumocaCore.GALEC.Names

/-! Branch conditions from the actual AST. The only admitted Boolean condition
is the builtin `isFinite(e)` with one admitted Real argument (Boolean by the
restricted interpretation of the TODO-labelled condition typing); every other
callee, including `jacobian`, and every other expression is rejected. The only
admitted error-signal check is `signal in S1, ..., Sn` with predefined names;
a signal closure, a negation, an unrestricted check and a fallback condition
are rejected. The §1.4 test-set rule is checked by the reachability analysis. -/
namespace Rumoca.GALEC.Elaboration.ConditionLowering
open _root_.Parser
open Rumoca.Tensor Rumoca.Solve.Tensor

def lower (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Condition → Option (Condition inputs outputs bounds)
  | .expr (.call callee [argument]) =>
      if callee = .ident Names.finiteTest then
        (ExpressionLowering.lower table names argument).map .finite
      else none
  | .signalCheck none false (first :: rest) none =>
      (SignalNames.read (first :: rest)).map .signalIn
  | _ => none

inductive Elaborates (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Condition → Condition inputs outputs bounds → Prop where
  | finite : ExpressionLowering.Elaborates table names argument term →
      Elaborates table names (.expr (.call (.ident Names.finiteTest) [argument])) (.finite term)
  | signalIn : SignalNames.Denotes (first :: rest) tested →
      Elaborates table names (.signalCheck none false (first :: rest) none) (.signalIn tested)

theorem lower_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Condition) (condition : Condition inputs outputs bounds) :
    lower table names source = some condition ↔ Elaborates table names source condition := by
  constructor
  · intro found
    unfold lower at found
    split at found
    · rename_i callee argument
      split at found
      · rename_i named
        subst named
        obtain ⟨term, lowered, rfl⟩ := Option.map_eq_some_iff.mp found
        exact .finite ((ExpressionLowering.lower_iff _ _ _ _).mp lowered)
      · contradiction
    · obtain ⟨tested, read, rfl⟩ := Option.map_eq_some_iff.mp found
      exact .signalIn ((SignalNames.read_iff _ _).mp read)
    · contradiction
  · intro typed
    cases typed with
    | finite argument =>
      simp [lower, (ExpressionLowering.lower_iff _ _ _ _).mpr argument]
    | signalIn denoted =>
      simp [lower, (SignalNames.read_iff _ _).mpr denoted]

/-- Independent source meaning of a satisfied admitted condition, with the
state its branch body starts from: `isFinite(e)` holds when `e` has a result
the classification calls finite; a check holds when a tested signal is set,
and its tested signals are unset before the body (§1.4). -/
def Enters (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (state : Signaled α outputs) :
    AST.Condition → Signaled α outputs → Prop
  | .expr (.call callee [argument]), entry =>
      callee = .ident Names.finiteTest ∧
      (∃ result, ExpressionLowering.Evaluates table names step zero one @input @state.1 @env
        argument result ∧ finite result) ∧ entry = state
  | .signalCheck none false tested none, entry =>
      ∃ set, SignalNames.Denotes tested set ∧ SignalSet.Meets set state.2 ∧
        entry = ⟨state.1, state.2.diff set⟩
  | _, _ => False

/-- Independent source meaning of an unsatisfied admitted condition. -/
def Fails (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (state : Signaled α outputs) :
    AST.Condition → Prop
  | .expr (.call callee [argument]) =>
      callee = .ident Names.finiteTest ∧
      ¬ ∃ result, ExpressionLowering.Evaluates table names step zero one @input @state.1 @env
        argument result ∧ finite result
  | .signalCheck none false tested none =>
      ∃ set, SignalNames.Denotes tested set ∧ ¬ SignalSet.Meets set state.2
  | _ => False

variable {inputs outputs : List Shape} {bounds : List Nat}
  {table : BindingTable inputs outputs} {names : IteratorNames bounds}
  {source : AST.Condition} {condition : Condition inputs outputs bounds}

theorem enters_correct (typed : Elaborates table names source condition)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (state entry : Signaled α outputs) :
    Enters table names step finite zero one @input @env state source entry ↔
      condition.Holds step finite zero one @input state @env ∧ entry = condition.enter state := by
  cases typed with
  | finite argument =>
    simp only [Enters, Condition.Holds, Condition.enter, true_and,
      ExpressionLowering.lowering_correct argument]
  | signalIn denoted =>
    simp only [Enters, Condition.Holds, Condition.enter]
    constructor
    · rintro ⟨set, again, meets, rfl⟩
      cases SignalNames.denotes_unique denoted again
      exact ⟨meets, rfl⟩
    · rintro ⟨meets, rfl⟩
      exact ⟨_, denoted, meets, rfl⟩

theorem fails_correct (typed : Elaborates table names source condition)
    (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (env : IteratorEnv bounds) (state : Signaled α outputs) :
    Fails table names step finite zero one @input @env state source ↔
      ¬ condition.Holds step finite zero one @input state @env := by
  cases typed with
  | finite argument =>
    simp only [Fails, Condition.Holds, true_and, ExpressionLowering.lowering_correct argument]
  | signalIn denoted =>
    simp only [Fails, Condition.Holds]
    constructor
    · rintro ⟨set, again, missed⟩
      cases SignalNames.denotes_unique denoted again
      exact missed
    · intro missed
      exact ⟨_, denoted, missed⟩

theorem closure_rejected (closure : AST.Name) (negated : Bool) (tested : List AST.Name)
    (fallback : Option AST.Expr) :
    lower (bounds := bounds) table names (.signalCheck (some closure) negated tested fallback) = none :=
  rfl

theorem negation_rejected (closure : Option AST.Name) (tested : List AST.Name)
    (fallback : Option AST.Expr) :
    lower (bounds := bounds) table names (.signalCheck closure true tested fallback) = none := by
  cases closure <;> rfl

theorem unrestricted_rejected (closure : Option AST.Name) (negated : Bool)
    (fallback : Option AST.Expr) :
    lower (bounds := bounds) table names (.signalCheck closure negated [] fallback) = none := by
  cases closure <;> cases negated <;> cases fallback <;> rfl

theorem fallback_rejected (closure : Option AST.Name) (negated : Bool) (tested : List AST.Name)
    (fallback : AST.Expr) :
    lower (bounds := bounds) table names (.signalCheck closure negated tested (some fallback)) =
      none := by
  cases closure <;> cases negated <;> cases tested <;> rfl

/-- Every Boolean condition other than a one-argument `isFinite` call is rejected. -/
theorem callee_rejected (callee : AST.Name) (other : callee ≠ .ident Names.finiteTest)
    (arguments : List AST.Expr) :
    lower (bounds := bounds) table names (.expr (.call callee arguments)) = none := by
  cases arguments with
  | nil => rfl
  | cons argument rest =>
    cases rest with
    | nil => simp only [lower, if_neg other]
    | cons _ _ => rfl

theorem expression_rejected (value : AST.Expr) (notCall : ∀ callee arguments, value ≠ .call callee arguments) :
    lower (bounds := bounds) table names (.expr value) = none := by
  cases value with
  | call callee arguments => exact absurd rfl (notCall callee arguments)
  | _ => rfl

/-- `isFinite` of an argument outside the admitted Real expressions is rejected. -/
theorem argument_rejected (argument : AST.Expr)
    (outside : ExpressionLowering.lower table names argument = none) :
    lower (bounds := bounds) table names
      (.expr (.call (.ident Names.finiteTest) [argument])) = none := by
  simp [lower, outside]

end Rumoca.GALEC.Elaboration.ConditionLowering
