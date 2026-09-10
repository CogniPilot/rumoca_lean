import RumocaC.LiteralLowering

/-! Literal lowering for the typed loop fragment. Named static objects live
outside the local namespace, so counter and assignment rules cannot mistake
a lowered string reference for a numeric local. -/
noncomputable section
namespace Rumoca.CLiteral.Lowering
open CTree CMemory
variable [interface : CInterface]

def FreshLocals (symbols : Symbols) (env : CBody.Locals) : Prop :=
  ∀ text name, symbols text = some name → env name = none

omit interface in
theorem FreshLocals.bind (fresh : FreshLocals symbols env)
    (nameFresh : FreshName symbols localName) (value : Value) :
    FreshLocals symbols (CBody.bind env localName value) := by
  intro text name named
  have different : name ≠ localName := by
    intro eq
    exact nameFresh text (eq ▸ named)
  simp only [CBody.bind, if_neg different, fresh text name named]

omit interface in
private theorem add_pointer_left (p : Option Address) (value : Value) :
    CArithmetic.floatAdd (.pointer p) value = none := rfl

omit interface in
private theorem add_pointer_right (p : Option Address) (value : Value) :
    CArithmetic.floatAdd value (.pointer p) = none := by
  unfold CArithmetic.floatAdd
  cases CCalls.finiteValue value <;> rfl

private theorem literal_add_left (env : CBody.Locals) (heap : Heap) (text : String) (other : Expr) :
    ((CBody.eval env heap (.str text)).bind fun a =>
      (CBody.eval env heap other).bind (CArithmetic.floatAdd a)) = none := by
  simp only [CBody.eval]
  cases interface.literals text <;> cases CBody.eval env heap other <;>
    simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, add_pointer_left]

private theorem literal_add_right (env : CBody.Locals) (heap : Heap) (other : Expr) (text : String) :
    ((CBody.eval env heap other).bind fun a =>
      (CBody.eval env heap (.str text)).bind (CArithmetic.floatAdd a)) = none := by
  simp only [CBody.eval]
  cases interface.literals text <;> cases CBody.eval env heap other <;>
    simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some, add_pointer_right]

private theorem named_add_left (types : CLoops.Types) (heap : Heap) (name text : String)
    (fresh : env name = none)
    (value : CBody.eval env heap (.id name) = CBody.eval env heap (.str text)) (other : Expr) :
    CLoops.eval env types heap (.bin .add (.id name) other) = none := by
  cases other with
  | nat n =>
      by_cases unit : n = 1
      · subst n; simp [CLoops.eval, fresh]
      · simp [CLoops.eval, unit, value, literal_add_left]
  | _ => simp [CLoops.eval, fresh, value, literal_add_left]

private theorem named_add_right (types : CLoops.Types) (heap : Heap) (name text : String)
    (fresh : env name = none)
    (value : CBody.eval env heap (.id name) = CBody.eval env heap (.str text)) (other : Expr) :
    CLoops.eval env types heap (.bin .add other (.id name)) = none := by
  cases other <;> simp [CLoops.eval, fresh, value, literal_add_right]

private theorem string_add_left (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (text : String) (other : Expr) :
    CLoops.eval env types heap (.bin .add (.str text) other) = none := by
  simpa only [CLoops.eval] using literal_add_left env heap text other

private theorem string_add_right (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (other : Expr) (text : String) :
    CLoops.eval env types heap (.bin .add other (.str text)) = none := by
  simpa only [CLoops.eval] using literal_add_right env heap other text

private theorem add_correct (bound : Bound symbols env) (fresh : FreshLocals symbols env)
    (safe : NoIntrinsic symbols) (types : CLoops.Types) (heap : Heap) (a b : Expr) :
    CLoops.eval env types heap (.bin .add (expression symbols a) (expression symbols b)) =
      CLoops.eval env types heap (.bin .add a b) := by
  have ha := (expression_correct bound safe heap a).1
  have hb := (expression_correct bound safe heap b).1
  cases a with
  | str text =>
      simp only [expression] at ha ⊢
      cases found : symbols text with
      | none => simp only [string_add_left]
      | some name =>
          simp only [found] at ha ⊢
          rw [named_add_left types heap name text (fresh text name found) ha, string_add_left]
  | _ =>
      cases b with
      | str text =>
          simp only [expression] at hb ⊢
          cases found : symbols text with
          | none => simp only [string_add_right]
          | some name =>
              simp only [found] at hb ⊢
              rw [named_add_right types heap name text (fresh text name found) hb, string_add_right]
      | _ => simp only [expression] at ha hb ⊢ <;> simp [CLoops.eval, ha, hb]

/-- Numeric local rules and finite arithmetic retain the same outcomes after
string references are lowered. Generated data names are fresh in local scope. -/
theorem loop_expression_correct (bound : Bound symbols env) (fresh : FreshLocals symbols env)
    (safe : NoIntrinsic symbols) (types : CLoops.Types) (heap : Heap) (e : Expr) :
    CLoops.eval env types heap (expression symbols e) = CLoops.eval env types heap e := by
  have ev := fun a => (expression_correct bound safe heap a).1
  have he := ev e
  cases e with
  | bin op a b =>
      cases op <;> try simpa only [expression, CLoops.eval] using he
      · simpa only [expression] using add_correct bound fresh safe types heap a b
      · simp only [expression, CLoops.eval, ev]
  | str text =>
      cases found : symbols text with
      | none => simp [expression, found]
      | some name => simp [expression, found, CLoops.eval, CBody.eval, bound text name found]
  | id _ | nat _ | sizeof _ => simp [expression, CLoops.eval]
  | _ => simpa only [expression, CLoops.eval] using he

/-- Local writes, as well as declarations, must avoid the static data names. -/
def FreshWrites (symbols : Symbols) : Stmt → Prop
  | .declare _ name _ => FreshName symbols name
  | .assign (.id name) _ => FreshName symbols name
  | .branch _ yes no =>
      (∀ s ∈ yes, FreshWrites symbols s) ∧ (∀ s ∈ no, FreshWrites symbols s)
  | .whileLoop _ body => ∀ s ∈ body, FreshWrites symbols s
  | _ => True
termination_by s => sizeOf s
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_›
    simp only [Stmt.branch.sizeOf_spec, Stmt.whileLoop.sizeOf_spec]
    omega

omit interface in
theorem noDeclarations_lowered (symbols : Symbols) (s : Stmt) :
    CLoops.noDeclarations (statement symbols s) = CLoops.noDeclarations s := by
  induction s using Stmt.rec (motive_2 := fun code =>
      (code.map (statement symbols)).all CLoops.noDeclarations = code.all CLoops.noDeclarations) with
  | declare | assign | eval | ret => simp [statement, CLoops.noDeclarations]
  | branch condition yes no hy hn => simp [statement, CLoops.noDeclarations, hy, hn]
  | whileLoop condition body hb => simp [statement, CLoops.noDeclarations, hb]
  | nil => rfl
  | cons stmt rest hs hr => simp [hs, hr]

def loopState (symbols : Symbols) : CLoops.State → CLoops.State
  | .running code env types heap => .running (code.map (statement symbols)) env types heap
  | .returned result => .returned result

def loopSafe (symbols : Symbols) : CLoops.State → Prop
  | .running code env _ _ =>
      Bound symbols env ∧ FreshLocals symbols env ∧ ∀ s ∈ code, FreshWrites symbols s
  | .returned _ => True

theorem loop_safe_next (valid : loopSafe symbols s) (step : CLoops.next s = some t) :
    loopSafe symbols t := by
  unfold CLoops.next at step
  split at step
  all_goals
    aesop (add safe apply [Bound.bind, FreshLocals.bind])
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        loopSafe, FreshWrites])

theorem loop_next (safe : NoIntrinsic symbols) (s : CLoops.State) (valid : loopSafe symbols s) :
    CLoops.next (loopState symbols s) = (CLoops.next s).map (loopState symbols) := by
  cases s with
  | returned result => rfl
  | running code env types heap =>
      have ev := fun e => loop_expression_correct valid.1 valid.2.1 safe types heap e
      have lv := fun e => (expression_correct valid.1 safe heap e).2
      cases code with
      | nil => rfl
      | cons stmt rest =>
          cases stmt with
          | assign target value =>
              have targetEq := lv target
              cases target with
              | str text =>
                  cases found : symbols text with
                  | none => simp [loopState, statement, expression, found, CLoops.next, ev, CBody.lvalue]
                  | some name =>
                      simp [loopState, statement, expression, found, CLoops.next, ev,
                        valid.2.1 text name found, CBody.lvalue]
              | _ =>
                  simp only [expression] at targetEq ⊢
                  simp [loopState, statement, expression, CLoops.next, ev, targetEq, Option.map_bind]
          | declare type name value =>
              cases defined : (env name).isSome <;>
                simp [loopState, statement, CLoops.next, ev, Option.map_bind, defined]
          | ret value =>
              cases value <;> simp [loopState, statement, CLoops.next, ev, Option.map_bind]
          | eval value => simp [loopState, statement, CLoops.next, ev, Option.map_bind]
          | branch condition yes no =>
              simp [loopState, statement, CLoops.next, ev, List.all_map,
                noDeclarations_lowered]
              split <;> simp_all [Option.map_bind, loopState, apply_ite (List.map (statement symbols))]
          | whileLoop condition body =>
              simp [loopState, statement, CLoops.next, ev, List.all_map,
                noDeclarations_lowered]
              split <;> simp_all [Option.map_bind, loopState, statement, apply_ite (List.map (statement symbols))]

def loopBisimulation (safe : NoIntrinsic symbols) :
    Transition.FunctionalBisimulation CLoops.machine CLoops.machine where
  map := loopState symbols
  Valid := loopSafe symbols
  step := by
    intro s t valid next
    refine ⟨loop_safe_next valid next, ?_⟩
    change CLoops.next s = some t at next
    change CLoops.next (loopState symbols s) = some (loopState symbols t)
    simpa only [next, Option.map_some] using loop_next safe s valid
  reflect := by
    intro s t valid next
    have lowered : (CLoops.next s).map (loopState symbols) = some t :=
      (loop_next safe s valid).symm.trans next
    cases original : CLoops.next s with
    | none => simp [original] at lowered
    | some u =>
        exact ⟨u, original, (Option.some.inj (by simpa only [original, Option.map_some] using lowered)).symm⟩
  final := by intro s valid; cases s <;> rfl

/-- The loop fragment preserves every outcome with its exact returned heap;
neither successful execution nor termination is a premise. -/
theorem loop_behaviors (safe : NoIntrinsic symbols) (valid : loopSafe symbols s)
    (behavior : Transition.Observation CBody.Result) :
    CLoops.machine.Behaves (loopState symbols s) behavior ↔ CLoops.machine.Behaves s behavior :=
  (loopBisimulation safe).behaviors valid behavior

end Rumoca.CLiteral.Lowering
