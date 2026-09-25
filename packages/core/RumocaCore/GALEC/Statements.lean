import RumocaCore.GALEC.IndexSyntax
import RumocaCore.Solve.Tensor.Environment
import RumocaCore.GALEC.TensorWrites
import RumocaCore.GALEC.Signals

/-! Reusable resolved statement syntax, not a production GALEC parser.
Inputs and iterator bindings are immutable. Only the separate output context
is writable. Bounds are prepared natural extents, not arbitrary body callbacks.
Surface range elaboration and target Integer bounds remain separate. Branch
conditions test the finiteness of a term (`isFinite`) or the set error signals;
error-signal statements set signals (eFMI 1.0.0 Beta 1 §3.2.5 §1). -/
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
/-- A branch condition: finiteness of a Real term (the builtin `isFinite`) or
an error-signal check that is satisfied when a tested signal is set. -/
inductive Condition (inputs outputs : List Shape) (bounds : List Nat) where
  | finite (term : ScalarTerm inputs outputs bounds)
  | signalIn (tested : SignalSet)

inductive Statement (inputs outputs : List Shape) : List Nat → Type where
  | skip : Statement inputs outputs bounds
  | assign (ref : Ref outputs shape) (indices : Subscripts bounds shape.dimensions)
      (value : ScalarTerm inputs outputs bounds) : Statement inputs outputs bounds
  | seq (first second : Statement inputs outputs bounds) : Statement inputs outputs bounds
  | bounded (bound : Nat) (body : Statement inputs outputs (bound :: bounds)) :
      Statement inputs outputs bounds
  | branch (condition : Condition inputs outputs bounds)
      (yes no : Statement inputs outputs bounds) : Statement inputs outputs bounds
  | signal (raised : SignalSet) : Statement inputs outputs bounds

/-- Statements without control over error signals: no branch and no
error-signal statement. Their data relation below is their whole meaning. -/
def Statement.SignalFree : Statement inputs outputs bounds → Prop
  | .skip | .assign .. => True
  | .seq first second => first.SignalFree ∧ second.SignalFree
  | .bounded _ body => body.SignalFree
  | .branch .. | .signal _ => False

/-- The data relation of signal-free statements. It uses scalar execution,
independently specified cell writes and environment frames, and never refers
to an executable function. Branches and error-signal statements have their
meaning only in `Statement.Runs`, which carries the signal state. -/
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
  | .branch .., _, _, _ | .signal _, _, _, _ => False

/-- The writable store together with the set of currently set error signals. -/
abbrev Signaled (α : Type) (outputs : List Shape) := Env α outputs × SignalSet

/-- A finiteness condition holds when the term has a result that the supplied
classification calls finite; a check holds when a tested signal is set
(eFMI §3.2.5 §1.4). The classification is `fun _ => True` for partial finite
arithmetic, where a missing result is the non-finite outcome. -/
def Condition.Holds (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) (state : Signaled α outputs) (iterators : IteratorEnv bounds) :
    Condition inputs outputs bounds → Prop
  | .finite term => ∃ result, term.Evaluates step zero one input state.1 iterators result ∧ finite result
  | .signalIn tested => SignalSet.Meets tested state.2

/-- A satisfied check unsets its tested signals immediately before its body
(§1.4); a finiteness condition leaves the state unchanged. -/
def Condition.enter : Condition inputs outputs bounds → Signaled α outputs → Signaled α outputs
  | .finite _, state => state
  | .signalIn tested, state => ⟨state.1, state.2.diff tested⟩

/-- Execution with error signals. Data statements keep the signal set; a
branch runs its first body when its condition holds and its second otherwise;
an error-signal statement adds its signals (§1.2). -/
def Statement.Runs (step : BinaryOp → α → α → α → Prop) (finite : α → Prop) (zero one : α)
    (input : Env α inputs) : Statement inputs outputs bounds →
    IteratorEnv bounds → Signaled α outputs → Signaled α outputs → Prop
  | .skip, _, before, after => after = before
  | .assign ref indices value, iterators, before, after =>
      (Statement.assign ref indices value).Executes step zero one input iterators before.1 after.1 ∧
        after.2 = before.2
  | .seq first second, iterators, before, after =>
      ∃ middle, first.Runs step finite zero one input iterators before middle ∧
        second.Runs step finite zero one input iterators middle after
  | .bounded bound body, iterators, before, after =>
      Iteration.Executes (σ := Signaled α outputs) (fun i current next =>
        body.Runs step finite zero one input (iterators.push i) current next) bound before after
  | .branch condition yes no, iterators, before, after =>
      (condition.Holds step finite zero one input before iterators ∧
        yes.Runs step finite zero one input iterators (condition.enter before) after) ∨
      (¬ condition.Holds step finite zero one input before iterators ∧
        no.Runs step finite zero one input iterators before after)
  | .signal raised, _, before, after => after = ⟨before.1, before.2.union raised⟩

/-- Iterating a signal-free relation over signaled states is iterating it over
stores with the signal set fixed. -/
theorem Iteration.executes_signalFree {bound : Nat}
    (data : Fin bound → Env α outputs → Env α outputs → Prop)
    (signaled : Fin bound → Signaled α outputs → Signaled α outputs → Prop)
    (bridge : ∀ i before after, signaled i before after ↔ data i before.1 after.1 ∧ after.2 = before.2)
    (count : Nat) (before after : Signaled α outputs) :
    Iteration.Executes signaled count before after ↔
      Iteration.Executes data count before.1 after.1 ∧ after.2 = before.2 := by
  constructor
  · intro executed
    induction executed with
    | zero state => exact ⟨.zero _, rfl⟩
    | next within _ body ih =>
      obtain ⟨earlier, same⟩ := ih
      obtain ⟨step, kept⟩ := (bridge _ _ _).mp body
      exact ⟨.next within earlier step, kept.trans same⟩
  · rintro ⟨executed, kept⟩
    have lifted : ∀ (raised : SignalSet) (count : Nat) (first last : Env α outputs),
        Iteration.Executes data count @first @last →
        Iteration.Executes signaled count ⟨@first, raised⟩ ⟨@last, raised⟩ := by
      intro raised count first last executed
      induction executed with
      | zero state => exact .zero _
      | next within _ body ih => exact .next within ih ((bridge _ _ _).mpr ⟨body, rfl⟩)
    have equal : after = ⟨after.1, before.2⟩ := Prod.ext rfl kept
    rw [equal]
    exact lifted before.2 count before.1 after.1 executed

/-- Every existing data theorem applies to signal-free statements unchanged:
their execution with signals is their data execution with the signal set kept. -/
theorem Statement.signalFree_executes (stmt : Statement inputs outputs bounds)
    (free : stmt.SignalFree) (step : BinaryOp → α → α → α → Prop) (finite : α → Prop)
    (zero one : α) (input : Env α inputs) (iterators : IteratorEnv bounds)
    (before after : Signaled α outputs) :
    stmt.Runs step finite zero one input iterators before after ↔
      stmt.Executes step zero one input iterators before.1 after.1 ∧ after.2 = before.2 := by
  induction stmt generalizing before after with
  | skip =>
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨same, kept⟩; exact Prod.ext same kept
  | assign ref indices value => exact Iff.rfl
  | seq first second ihf ihs =>
    obtain ⟨freeFirst, freeSecond⟩ := free
    constructor
    · rintro ⟨middle, firstRun, secondRun⟩
      obtain ⟨firstData, firstKept⟩ := (ihf freeFirst _ _ _).mp firstRun
      obtain ⟨secondData, secondKept⟩ := (ihs freeSecond _ _ _).mp secondRun
      exact ⟨⟨_, firstData, secondData⟩, secondKept.trans firstKept⟩
    · rintro ⟨⟨middle, firstData, secondData⟩, kept⟩
      exact ⟨(middle, before.2), (ihf freeFirst _ _ _).mpr ⟨firstData, rfl⟩,
        (ihs freeSecond _ _ _).mpr ⟨secondData, kept⟩⟩
  | bounded bound body ih =>
    exact Iteration.executes_signalFree _ _
      (fun i current next => ih free (iterators.push i) current next) bound before after
  | branch => exact free.elim
  | signal => exact free.elim

def Condition.test (ops : ScalarOps α) (finite : α → Bool) (zero one : α) (input : Env α inputs)
    (state : Signaled α outputs) (iterators : IteratorEnv bounds) :
    Condition inputs outputs bounds → Bool
  | .finite term => finite (term.eval ops zero one input state.1 iterators)
  | .signalIn tested => SignalSet.meets tested state.2

/-- Total execution with signals for total arithmetic and a decided finiteness
classification. -/
def Statement.execute (ops : ScalarOps α) (finite : α → Bool) (zero one : α)
    (input : Env α inputs) : Statement inputs outputs bounds → IteratorEnv bounds →
    Signaled α outputs → Signaled α outputs
  | .skip, _, state => state
  | .assign ref indices value, iterators, state =>
      (Env.update state.1 ref (TensorWrites.write (state.1 ref)
        (Coordinate.index (indices.eval iterators))
        (value.eval ops zero one input state.1 iterators)), state.2)
  | .seq first second, iterators, state =>
      second.execute ops finite zero one input iterators
        (first.execute ops finite zero one input iterators state)
  | .bounded _ body, iterators, state =>
      Iteration.run (σ := Signaled α outputs)
        (fun i current => body.execute ops finite zero one input (iterators.push i) current) state
  | .branch condition yes no, iterators, state =>
      if condition.test ops finite zero one input state iterators then
        yes.execute ops finite zero one input iterators (condition.enter state)
      else no.execute ops finite zero one input iterators state
  | .signal raised, _, state => ⟨state.1, state.2.union raised⟩

theorem Condition.test_correct (condition : Condition inputs outputs bounds)
    (ops : ScalarOps α) (step : BinaryOp → α → α → α → Prop)
    (arithmetic : ∀ op a b result, step op a b result ↔ result = op.scalar ops a b)
    (finite : α → Bool) (zero one : α) (input : Env α inputs) (state : Signaled α outputs)
    (iterators : IteratorEnv bounds) :
    condition.Holds step (fun value => finite value = true) zero one input state iterators ↔
      condition.test ops finite zero one input state iterators = true := by
  cases condition with
  | finite term =>
    simp only [Holds, test, ScalarTerm.eval_correct _ ops step arithmetic, exists_eq_left]
  | signalIn tested => exact (SignalSet.meets_iff _ _).symm

theorem Statement.execute_correct (stmt : Statement inputs outputs bounds)
    (ops : ScalarOps α) (step : BinaryOp → α → α → α → Prop)
    (arithmetic : ∀ op a b result, step op a b result ↔ result = op.scalar ops a b)
    (finite : α → Bool) (zero one : α) (input : Env α inputs) (iterators : IteratorEnv bounds)
    (before after : Signaled α outputs) :
    stmt.Runs step (fun value => finite value = true) zero one input iterators before after ↔
      after = stmt.execute ops finite zero one input iterators before := by
  induction stmt generalizing before after with
  | skip => rfl
  | assign ref indices value =>
    simp only [Runs, Executes, ScalarTerm.eval_correct _ ops step arithmetic,
      TensorWrites.write_correct, Env.update_correct, execute]
    constructor
    · rintro ⟨⟨result, tensor, rfl, rfl, written⟩, kept⟩
      exact Prod.ext written kept
    · rintro rfl
      exact ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩
  | seq first second ihf ihs =>
    simp only [Runs, ihf, ihs, execute]
    constructor
    · rintro ⟨middle, rfl, written⟩; exact written
    · intro written; exact ⟨_, rfl, written⟩
  | bounded bound body ih =>
    exact Iteration.run_correct (σ := Signaled α outputs) _ _
      (fun i current next => ih (iterators.push i) current next) before after
  | branch condition yes no ihy ihn =>
    simp only [Runs, execute, Condition.test_correct condition ops step arithmetic]
    by_cases satisfied : condition.test ops finite zero one input before iterators = true
    · rw [if_pos satisfied]
      simp only [satisfied, not_true_eq_false, false_and, or_false, true_and]
      exact ihy _ _ _
    · rw [if_neg satisfied]
      simp only [satisfied, Bool.false_eq_true, false_and, false_or, not_false_eq_true, true_and]
      exact ihn _ _ _
  | signal raised => rfl

end Rumoca.GALEC
