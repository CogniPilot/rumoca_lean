import RumocaCore.GALEC.Elaboration.Reads

/-! The current Real-expression slice: zero/one, shaped state reads, ordered
addition/multiplication and parentheses. No reassociation, function recognition
or automatic differentiation occurs here. Arithmetic may be partial or
nondeterministic in both source and target execution relations. -/
namespace Rumoca.GALEC.Elaboration.ExpressionLowering
open _root_.Parser
open Rumoca.Tensor Rumoca.Solve.Tensor

inductive Operator : Token → BinaryOp → Prop where
  | add : Operator (.literal "+") .add
  | mul : Operator (.literal "*") .mul

def operator : Token → Option BinaryOp
  | .literal "+" => some .add
  | .literal "*" => some .mul
  | _ => none

theorem operator_iff (token : Token) (op : BinaryOp) :
    operator token = some op ↔ Operator token op := by
  constructor
  · intro found
    unfold operator at found
    split at found
    · cases Option.some.inj found; exact .add
    · cases Option.some.inj found; exact .mul
    · contradiction
  · intro meaning
    cases meaning <;> rfl

def lower (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Expr → Option (ScalarTerm inputs outputs bounds)
  | .reference ref => (ReadLowering.lower table names ref).map Read.term
  | .literal (.literal "0.0") => some (.literal .zero)
  | .literal (.literal "1.0") => some (.literal .one)
  | .binary token left right =>
      (operator token).bind fun op => (lower table names left).bind fun l =>
        (lower table names right).map (ScalarTerm.binary op l)
  | .parens body => lower table names body
  | _ => none

inductive Elaborates (table : BindingTable inputs outputs) (names : IteratorNames bounds) :
    AST.Expr → ScalarTerm inputs outputs bounds → Prop where
  | reference {ref : AST.Reference} {read : Read inputs outputs bounds} :
      ReadLowering.Elaborates table names ref read →
      Elaborates table names (.reference ref) read.term
  | zero : Elaborates table names (.literal (.literal "0.0")) (.literal .zero)
  | one : Elaborates table names (.literal (.literal "1.0")) (.literal .one)
  | binary : Operator token op → Elaborates table names left l → Elaborates table names right r →
      Elaborates table names (.binary token left right) (.binary op l r)
  | parens : Elaborates table names body term → Elaborates table names (.parens body) term

theorem lower_sound (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Expr) (term : ScalarTerm inputs outputs bounds)
    (found : lower table names source = some term) : Elaborates table names source term := by
  unfold lower at found
  split at found
  · rename_i ref
    obtain ⟨read, lowered, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact .reference ((ReadLowering.lower_iff table names ref read).mp lowered)
  · cases Option.some.inj found; exact .zero
  · cases Option.some.inj found; exact .one
  · rename_i token left right
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
    obtain ⟨op, meaning, l, leftLowered, r, rightLowered, same⟩ := found
    cases same
    exact .binary ((operator_iff token op).mp meaning)
      (lower_sound table names left l leftLowered) (lower_sound table names right r rightLowered)
  · rename_i body
    exact .parens (lower_sound table names body term found)
  · contradiction
termination_by sizeOf source

theorem lower_complete (typed : Elaborates table names source term) :
    lower table names source = some term := by
  induction typed with
  | reference typed =>
    simp only [lower, (ReadLowering.lower_iff _ _ _ _).mpr typed, Option.map_some]
  | zero => rfl
  | one => rfl
  | binary meaning left right ihl ihr =>
    simp only [lower, (operator_iff _ _).mpr meaning, Option.bind_some, ihl, ihr, Option.map_some]
  | parens inner ih => exact ih

theorem lower_iff (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (source : AST.Expr) (term : ScalarTerm inputs outputs bounds) :
    lower table names source = some term ↔ Elaborates table names source term :=
  ⟨lower_sound table names source term, lower_complete⟩

/-- Independent ordered source-expression execution. `step` is the same
explicit arithmetic relation later used for target execution, not an evaluator. -/
inductive Evaluates (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) : AST.Expr → α → Prop where
  | reference : ReadLowering.Evaluates table names input state env ref value →
      Evaluates table names step zero one input state env (.reference ref) value
  | zero : Evaluates table names step zero one input state env (.literal (.literal "0.0")) zero
  | one : Evaluates table names step zero one input state env (.literal (.literal "1.0")) one
  | binary : Operator token op →
      Evaluates table names step zero one input state env left a →
      Evaluates table names step zero one input state env right b → step op a b value →
      Evaluates table names step zero one input state env (.binary token left right) value
  | parens : Evaluates table names step zero one input state env body value →
      Evaluates table names step zero one input state env (.parens body) value

variable {inputs outputs : List Shape} {bounds : List Nat}
  {table : BindingTable inputs outputs} {names : IteratorNames bounds}
  {source : AST.Expr} {term : ScalarTerm inputs outputs bounds}

theorem lowering_correct (typed : Elaborates table names source term)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) (value : α) :
    Evaluates table names step zero one input state env source value ↔
      term.Evaluates step zero one input state env value := by
  induction typed generalizing value with
  | reference typed =>
    constructor
    · intro evaluated
      cases evaluated with
      | reference read =>
        exact (ReadLowering.source_to_term ((ReadLowering.lower_iff _ _ _ _).mpr typed)
          step zero one input state env value).mp read
    · intro evaluated
      exact .reference ((ReadLowering.source_to_term ((ReadLowering.lower_iff _ _ _ _).mpr typed)
        step zero one input state env value).mpr evaluated)
  | zero =>
    constructor
    · intro evaluated
      generalize spelling : AST.Expr.literal (.literal "0.0") = other at evaluated
      cases evaluated <;> simp_all
      exact .literal .zero
    · intro evaluated; cases evaluated; exact .zero
  | one =>
    constructor
    · intro evaluated
      generalize spelling : AST.Expr.literal (.literal "1.0") = other at evaluated
      cases evaluated <;> simp_all
      exact .literal .one
    · intro evaluated; cases evaluated; exact .one
  | @binary token op left l right r meaning leftTyped rightTyped ihl ihr =>
    constructor
    · intro evaluated
      cases evaluated with
      | binary otherMeaning leftValue rightValue arithmetic =>
        have same := Option.some.inj
          (((operator_iff _ _).mpr otherMeaning).symm.trans
            ((operator_iff _ _).mpr meaning))
        cases same
        exact .binary ((ihl _).mp leftValue) ((ihr _).mp rightValue) arithmetic
    · intro evaluated
      cases evaluated with
      | binary leftValue rightValue arithmetic =>
        exact .binary meaning ((ihl _).mpr leftValue) ((ihr _).mpr rightValue) arithmetic
  | parens inner ih =>
    constructor
    · intro evaluated; cases evaluated with
      | parens value => exact (ih _).mp value
    · intro evaluated; exact .parens ((ih _).mpr evaluated)

theorem source_to_term (lowered : lower table names source = some term)
    (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) (state : Env α outputs) (env : IteratorEnv bounds) (value : α) :
    Evaluates table names step zero one input state env source value ↔
      term.Evaluates step zero one input state env value :=
  lowering_correct ((lower_iff table names source term).mp lowered) step zero one input state env value

end Rumoca.GALEC.Elaboration.ExpressionLowering
