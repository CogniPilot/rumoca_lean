import RumocaC.LiteralPointers
import RumocaCore.Transition.Simulation

/-! Lower string expressions to references to named static character arrays.
The name map may be partial; unregistered literals are retained. Complete
emission separately requires coverage and valid global declarations. -/
namespace Rumoca.CLiteral.Lowering
open CTree CMemory

abbrev Symbols := String → Option String

def expression (symbols : Symbols) : Expr → Expr
  | .str text => match symbols text with
      | some name => .id name
      | none => .str text
  | .bin op a b => .bin op (expression symbols a) (expression symbols b)
  | .not a => .not (expression symbols a)
  | .deref a => .deref (expression symbols a)
  | .address a => .address (expression symbols a)
  | .field a name pointer => .field (expression symbols a) name pointer
  | .index a i => .index (expression symbols a) (expression symbols i)
  | .call fn args => .call (expression symbols fn) (args.map (expression symbols))
  | .cast type value => .cast type (expression symbols value)
  | .id name => .id name
  | .nat n => .nat n
  | .sizeof type => .sizeof type

def statement (symbols : Symbols) : Stmt → Stmt
  | .declare type name value => .declare type name (expression symbols value)
  | .assign target value => .assign (expression symbols target) (expression symbols value)
  | .eval value => .eval (expression symbols value)
  | .ret value => .ret (value.map (expression symbols))
  | .branch condition yes no => .branch (expression symbols condition)
      (yes.map (statement symbols)) (no.map (statement symbols))
  | .whileLoop condition body => .whileLoop (expression symbols condition) (body.map (statement symbols))

def function (symbols : Symbols) (fn : Function) : Function :=
  { fn with body := fn.body.map (statement symbols) }

/-- Literal pooling cannot change whether a cast operand is the integer
literal zero. In particular a named string object cannot become a null pointer
constant merely by having a particular address or runtime payload. -/
@[simp] theorem expression_zeroLiteral (symbols : Symbols) (expr : Expr) :
    CBody.zeroLiteral (expression symbols expr) = CBody.zeroLiteral expr := by
  cases expr <;> simp only [expression]
  all_goals try rfl
  rename_i text
  cases symbols text <;> rfl

variable [interface : CInterface]

/-- A generated reference resolves to the same pointer as its source literal.
This includes name capture: a conflicting local cannot be ignored. -/
def Bound (symbols : Symbols) (env : CBody.Locals) : Prop :=
  ∀ text name, symbols text = some name →
    CBody.resolve env name = (interface.literals text).map (fun p => .pointer (some p))

/-- A data symbol must not acquire the syntactically recognized intrinsic's
meaning when an unsupported expression is used in a call position. -/
def NoIntrinsic (symbols : Symbols) : Prop :=
  ∀ text name, symbols text = some name → name ≠ "isfinite"

omit interface in
theorem intrinsic_iff (safe : NoIntrinsic symbols) (e : Expr) :
    expression symbols e = .id "isfinite" ↔ e = .id "isfinite" := by
  cases e <;> simp only [expression, reduceCtorEq]
  rename_i text
  cases found : symbols text with
  | none => simp
  | some name => simp [safe text name found]

private theorem call_nil (env : CBody.Locals) (heap : Heap) (fn : Expr) :
    CBody.eval env heap (.call fn []) = none := by
  cases fn <;> simp [CBody.eval]

private theorem call_many (env : CBody.Locals) (heap : Heap) (fn a b : Expr)
    (rest : List Expr) : CBody.eval env heap (.call fn (a :: b :: rest)) = none := by
  cases fn <;> simp [CBody.eval]

private theorem call_other (env : CBody.Locals) (heap : Heap) (fn a : Expr)
    (other : fn ≠ .id "isfinite") : CBody.eval env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [CBody.eval]

/-- Replacing a literal by a correctly bound data symbol preserves both its
value and its supported lvalue contexts, including failed evaluations. -/
theorem expression_correct (bound : Bound symbols env) (safe : NoIntrinsic symbols)
    (heap : Heap) (e : Expr) :
    CBody.eval env heap (expression symbols e) = CBody.eval env heap e ∧
    CBody.lvalue env heap (expression symbols e) = CBody.lvalue env heap e := by
  induction e using Expr.rec (motive_2 := fun args => ∀ a ∈ args,
      CBody.eval env heap (expression symbols a) = CBody.eval env heap a ∧
      CBody.lvalue env heap (expression symbols a) = CBody.lvalue env heap a) with
  | id name => simp [expression]
  | nat n => simp [expression]
  | str text =>
      cases found : symbols text with
      | none => simp [expression, found]
      | some name => simp [expression, found, CBody.eval, CBody.lvalue, bound text name found]
  | bin op a b ha hb =>
      cases op <;> simp [expression, CBody.eval, CBody.lvalue, ha.1, hb.1]
  | not a ha => simp [expression, CBody.eval, CBody.lvalue, ha.1]
  | deref a ha => simp [expression, CBody.eval, CBody.lvalue, ha.1]
  | address a ha => simp [expression, CBody.eval, CBody.lvalue, ha.2]
  | field a name pointer ha => simp [expression, CBody.eval, CBody.lvalue, ha.1, ha.2]
  | index a i ha hi => simp [expression, CBody.eval, CBody.lvalue, ha.1, ha.2, hi.1]
  | cast type a ha =>
      have casts (value : Value) :
          CBody.expressionCast type (expression symbols a) value = CBody.expressionCast type a value := by
        unfold CBody.expressionCast
        rw [expression_zeroLiteral]
      simp only [expression, CBody.eval, CBody.lvalue, ha.1, casts, and_self]
  | sizeof type => simp [expression]
  | call fn args hfn hargs =>
      refine ⟨?_, by simp [expression, CBody.lvalue]⟩
      simp only [expression]
      cases args with
      | nil => simp only [List.map_nil, call_nil]
      | cons a rest =>
          cases rest with
          | nil =>
              have ha := (hargs a (by simp)).1
              simp only [List.map_cons, List.map_nil]
              by_cases intrinsic : fn = .id "isfinite"
              · subst fn
                simp [expression, CBody.eval, ha]
              · rw [call_other env heap _ _ (fun eq => intrinsic ((intrinsic_iff safe fn).mp eq)),
                  call_other env heap _ _ intrinsic]
          | cons b rest => simp only [List.map_cons, call_many]
  | nil => simp_all
  | cons a rest ha hrest =>
      rename_i value member
      rcases List.mem_cons.mp member with rfl | tail
      · exact ha
      · exact hrest value tail

theorem arguments_correct (bound : Bound symbols env) (safe : NoIntrinsic symbols)
    (heap : Heap) (args : List Expr) :
    CCalls.arguments env heap (args.map (expression symbols)) =
      CCalls.arguments env heap args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp [CCalls.arguments, (expression_correct bound safe heap a).1, ih]

/-- The source body may not declare a local over a generated data name. -/
def FreshName (symbols : Symbols) (name : String) : Prop :=
  ∀ text, symbols text ≠ some name

def FreshDeclarations (symbols : Symbols) : Stmt → Prop
  | .declare _ name _ => FreshName symbols name
  | .branch _ yes no =>
      (∀ s ∈ yes, FreshDeclarations symbols s) ∧ (∀ s ∈ no, FreshDeclarations symbols s)
  | .whileLoop _ body => ∀ s ∈ body, FreshDeclarations symbols s
  | _ => True
termination_by s => sizeOf s
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_›
    simp only [Stmt.branch.sizeOf_spec, Stmt.whileLoop.sizeOf_spec]
    omega

theorem Bound.bind (bound : Bound symbols env) (fresh : FreshName symbols localName)
    (value : Value) : Bound symbols (CBody.bind env localName value) := by
  intro text name named
  have different : name ≠ localName := by
    intro eq
    exact fresh text (eq ▸ named)
  simpa only [CBody.resolve, CBody.bind, if_neg different] using bound text name named

def bodyState (symbols : Symbols) : CBody.State → CBody.State
  | .running code env heap => .running (code.map (statement symbols)) env heap
  | .returned result => .returned result

def bodySafe (symbols : Symbols) : CBody.State → Prop
  | .running code env _ => Bound symbols env ∧ ∀ s ∈ code, FreshDeclarations symbols s
  | .returned _ => True

omit interface in
private theorem map_choice {α β : Type} (f : α → β) (c : Bool) (yes no : List α) :
    (if c then yes else no).map f = if c then yes.map f else no.map f := by
  cases c <;> rfl

/-- Each body step, including rejection, commutes with literal lowering. -/
theorem body_next (safe : NoIntrinsic symbols) (s : CBody.State)
    (bound : bodySafe symbols s) :
    CBody.next (bodyState symbols s) = (CBody.next s).map (bodyState symbols) := by
  cases s with
  | returned result => rfl
  | running code env heap =>
      have ev := fun e => (expression_correct bound.1 safe heap e).1
      have lv := fun e => (expression_correct bound.1 safe heap e).2
      cases code with
      | nil => rfl
      | cons stmt rest =>
          cases stmt <;>
            simp [bodyState, statement, CBody.next, ev, lv, Option.map_bind]
          all_goals try simp only [map_choice, List.map_append, List.map_cons, statement]
          case declare type name value =>
            cases (env name).isSome <;> simp [bodyState]
          case ret value =>
            cases value <;> simp [bodyState, ev, Option.map_bind]

theorem body_safe_next (bound : bodySafe symbols s) (step : CBody.next s = some t) :
    bodySafe symbols t := by
  unfold CBody.next at step
  split at step
  all_goals
    aesop (add safe apply Bound.bind)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        bodySafe, FreshDeclarations])

/-- The same number of steps yields the same values, locals and heap; only
remaining string syntax changes. Failure is preserved as well. -/
theorem body_run (safe : NoIntrinsic symbols) (bound : bodySafe symbols s) (n : Nat) :
    CBody.run n (bodyState symbols s) = (CBody.run n s).map (bodyState symbols) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [CBody.run, body_next safe s bound]
      cases step : CBody.next s with
      | none => simp [CBody.run, step]
      | some t => simpa [CBody.run, step] using ih (body_safe_next bound step)

/-- Reuse a proved source-body result after lowering without assuming a result
for the target. Determinism excludes any other terminating, stuck or divergent
behavior of the lowered body. -/
theorem body_terminates (safe : NoIntrinsic symbols) (bound : bodySafe symbols s)
    (run : CBody.run n s = some (.returned result)) (behavior) :
    CBody.machine.Behaves (bodyState symbols s) behavior ↔ behavior = .terminates result := by
  apply CBody.behaviors_of_run (n := n)
  simpa only [run, Option.map_some, bodyState] using body_run safe bound n

/-- A complete step correspondence for the memory-body fragment. The fresh
declaration invariant is preserved by execution, not assumed anew at each step. -/
def bodyBisimulation (safe : NoIntrinsic symbols) :
    Transition.FunctionalBisimulation CBody.machine CBody.machine where
  map := bodyState symbols
  Valid := bodySafe symbols
  step := by
    intro s t valid next
    refine ⟨body_safe_next valid next, ?_⟩
    change CBody.next s = some t at next
    change CBody.next (bodyState symbols s) = some (bodyState symbols t)
    simpa only [next, Option.map_some] using body_next safe s valid
  reflect := by
    intro s t valid next
    have lowered : (CBody.next s).map (bodyState symbols) = some t :=
      (body_next safe s valid).symm.trans next
    cases original : CBody.next s with
    | none => simp [original] at lowered
    | some u =>
        exact ⟨u, original, (Option.some.inj (by simpa only [original, Option.map_some] using lowered)).symm⟩
  final := by intro s valid; cases s <;> rfl

/-- Literal lowering preserves and reflects all body observations: ordinary
termination with its exact heap, stuck execution, and divergence. -/
theorem body_behaviors (safe : NoIntrinsic symbols) (bound : bodySafe symbols s)
    (behavior : Transition.Observation CBody.Result) :
    CBody.machine.Behaves (bodyState symbols s) behavior ↔ CBody.machine.Behaves s behavior :=
  (bodyBisimulation safe).behaviors bound behavior

end Rumoca.CLiteral.Lowering
