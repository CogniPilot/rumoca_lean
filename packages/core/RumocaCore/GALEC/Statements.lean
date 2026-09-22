import RumocaCore.GALEC.IndexSyntax
import RumocaCore.Solve.Tensor.Environment
import RumocaCore.GALEC.TensorWrites

/-! Reusable resolved statement syntax, not a production GALEC parser.
Inputs and iterator bindings are immutable. Only the separate output context
is writable. Bounds are prepared natural extents, not arbitrary body callbacks.
Surface range elaboration and target Integer bounds remain separate. -/
namespace Rumoca.GALEC
open Rumoca.Tensor Rumoca.Solve.Tensor Rumoca.GALEC

inductive ScalarTerm (inputs outputs : List Shape) (bounds : List Nat) where
  | literal (value : Literal)
  | input (ref : Ref inputs shape) (indices : Subscripts bounds shape.dimensions)
  | output (ref : Ref outputs shape) (indices : Subscripts bounds shape.dimensions)
  | binary (op : BinaryOp) (left right : ScalarTerm inputs outputs bounds)

def ScalarTerm.eval (ops : ScalarOps α) (zero one : α) (input : Env α inputs)
    (state : Env α outputs) (iterators : IteratorEnv bounds) :
    ScalarTerm inputs outputs bounds → α
  | .literal value => value.eval zero one
  | .input ref indices => (input ref)[Coordinate.index (indices.eval iterators)]
  | .output ref indices => (state ref)[Coordinate.index (indices.eval iterators)]
  | .binary op left right => op.scalar ops
      (left.eval ops zero one input state iterators) (right.eval ops zero one input state iterators)

/-- Independent scalar expression relation. Partial arithmetic is permitted;
total evaluator correspondence below requires an explicit arithmetic law. -/
inductive ScalarTerm.Evaluates (step : BinaryOp → α → α → α → Prop)
    (zero one : α) (input : Env α inputs) (state : Env α outputs)
    (iterators : IteratorEnv bounds) : ScalarTerm inputs outputs bounds → α → Prop where
  | literal (value : Literal) : Evaluates step zero one input state iterators
      (.literal value) (value.eval zero one)
  | input (ref : Ref inputs shape) (indices : Subscripts bounds shape.dimensions) :
      Evaluates step zero one input state iterators (.input ref indices)
        ((input ref)[Coordinate.index (indices.eval iterators)])
  | output (ref : Ref outputs shape) (indices : Subscripts bounds shape.dimensions) :
      Evaluates step zero one input state iterators (.output ref indices)
        ((state ref)[Coordinate.index (indices.eval iterators)])
  | binary {op left right a b result} :
      Evaluates step zero one input state iterators left a →
      Evaluates step zero one input state iterators right b → step op a b result →
      Evaluates step zero one input state iterators (.binary op left right) result

theorem ScalarTerm.eval_correct (term : ScalarTerm inputs outputs bounds)
    (ops : ScalarOps α) (step : BinaryOp → α → α → α → Prop)
    (arithmetic : ∀ op a b result, step op a b result ↔ result = op.scalar ops a b)
    (zero one : α) (input : Env α inputs) (state : Env α outputs)
    (iterators : IteratorEnv bounds) (result : α) :
    Evaluates step zero one input state iterators term result ↔
      result = term.eval ops zero one input state iterators := by
  induction term generalizing result with
  | literal value =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .literal value
  | input ref indices =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .input ref indices
  | output ref indices =>
    constructor
    · intro h; cases h; rfl
    · rintro rfl; exact .output ref indices
  | binary op left right ihl ihr =>
    constructor
    · intro h
      cases h with
      | binary hl hr he =>
        obtain rfl := (ihl _).mp hl
        obtain rfl := (ihr _).mp hr
        exact (arithmetic _ _ _ _).mp he
    · rintro rfl
      exact .binary ((ihl _).mpr rfl) ((ihr _).mpr rfl)
        ((arithmetic _ _ _ _).mpr rfl)

inductive Statement (inputs outputs : List Shape) : List Nat → Type where
  | skip : Statement inputs outputs bounds
  | assign (ref : Ref outputs shape) (indices : Subscripts bounds shape.dimensions)
      (value : ScalarTerm inputs outputs bounds) : Statement inputs outputs bounds
  | seq (first second : Statement inputs outputs bounds) : Statement inputs outputs bounds
  | bounded (bound : Nat) (body : Statement inputs outputs (bound :: bounds)) :
      Statement inputs outputs bounds

def Statement.execute (ops : ScalarOps α) (zero one : α) (input : Env α inputs) :
    Statement inputs outputs bounds → IteratorEnv bounds → Env α outputs → Env α outputs
  | .skip, _, state => state
  | .assign ref indices value, iterators, state =>
      Env.update state ref (TensorWrites.write (state ref) (Coordinate.index (indices.eval iterators))
        (value.eval ops zero one input state iterators))
  | .seq first second, iterators, state =>
      second.execute ops zero one input iterators (first.execute ops zero one input iterators state)
  | .bounded _ body, iterators, state =>
      Iteration.run (σ := Env α outputs)
        (fun i current => body.execute ops zero one input (iterators.push i) current) state

/-- The relation uses scalar execution, independently specified cell writes
and environment frames. It never refers to `Statement.execute`. -/
def Statement.Executes (step : BinaryOp → α → α → α → Prop) (zero one : α)
    (input : Env α inputs) : Statement inputs outputs bounds →
    IteratorEnv bounds → Env α outputs → Env α outputs → Prop
  | .skip, _, before, after => @after = @before
  | .assign ref indices value, iterators, before, after =>
      ∃ result tensor,
        value.Evaluates step zero one input before iterators result ∧
        TensorWrites.Writes (before ref) (Coordinate.index (indices.eval iterators)) result tensor ∧
        Env.Updates before ref tensor after
  | .seq first second, iterators, before, after =>
      ∃ middle, first.Executes step zero one input iterators before middle ∧
        second.Executes step zero one input iterators middle after
  | .bounded bound body, iterators, before, after =>
      Iteration.Executes (σ := Env α outputs) (fun i current next =>
        body.Executes step zero one input (iterators.push i) current next) bound before after

theorem Statement.execute_correct (stmt : Statement inputs outputs bounds)
    (ops : ScalarOps α) (step : BinaryOp → α → α → α → Prop)
    (arithmetic : ∀ op a b result, step op a b result ↔ result = op.scalar ops a b)
    (zero one : α) (input : Env α inputs) (iterators : IteratorEnv bounds)
    (before after : Env α outputs) :
    stmt.Executes step zero one input iterators before after ↔
      @after = (fun {_s} r => stmt.execute ops zero one input iterators before r) := by
  induction stmt generalizing before after with
  | skip => rfl
  | assign ref indices value =>
    simp only [Executes, ScalarTerm.eval_correct _ ops step arithmetic,
      TensorWrites.write_correct, Env.update_correct, execute]
    constructor
    · rintro ⟨result, tensor, rfl, rfl, written⟩; exact written
    · intro written; exact ⟨_, _, rfl, rfl, written⟩
  | seq first second ihf ihs =>
    simp only [Executes, ihf, ihs, execute]
    constructor
    · rintro ⟨middle, rfl, written⟩; exact written
    · intro written; exact ⟨_, rfl, written⟩
  | bounded bound body ih =>
    exact Iteration.run_correct (σ := Env α outputs) _ _
      (fun i current next => ih (iterators.push i) current next) before after

end Rumoca.GALEC
