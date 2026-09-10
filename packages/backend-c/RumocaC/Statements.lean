import RumocaC.Lowering
import RumocaCore.Transition

/-! Independently interpreted C statements for the frozen emitted profile.
Expressions are pure; local bindings are explicit, and a missing binding is
stuck. The unsigned counter has exactly 64 bits and subtraction wraps in the
general semantics. Compiled executions prove that wrap is never reached. -/
noncomputable section
namespace Rumoca.CStatements
open Binary64 Transition
set_option maxRecDepth 10000

abbrev Counter := Fin (2 ^ 64)

def decrement (n : Counter) : Counter :=
  ⟨(n.val + 2 ^ 64 - 1) % 2 ^ 64, Nat.mod_lt _ (by decide)⟩

theorem decrement_positive (n : Counter) (h : 0 < n.val) :
    (decrement n).val = n.val - 1 := by
  have hn := n.isLt
  simp only [decrement]
  omega

def eval (localX : Option Value) : C.Expr → Option Value
  | .one => some one
  | .arg => localX
  | .add a b => do
    let av ← eval localX a
    let bv ← eval localX b
    if CExecution.finiteRoundDomain (units av + units bv)
      then some (roundedAdd av bv) else none

theorem eval_bound (x : Value) (e : C.Expr) : eval (some x) e = CExecution.eval x e := by
  induction e with
  | one => rfl
  | arg => rfl
  | add a b ha hb => simp only [eval, CExecution.eval, ha, hb]

def Scoped (hasX : Bool) : C.Expr → Prop
  | .one => True
  | .arg => hasX = true
  | .add a b => Scoped hasX a ∧ Scoped hasX b

inductive Stmt where
  | assign (e : C.Expr)
  | decrement
  | seq (a b : Stmt)
  | whileNonzero (body : Stmt)
  | ret (e : C.Expr)
  deriving DecidableEq

abbrev Function := CExecution.Function

/-- Concrete syntax's fixed declarations introduce exactly these function
bodies. Scoping is checked separately from recognizing C tokens. -/
def body (p : CSyntax.Program) : Function → Stmt
  | .rhs => .ret p.rhs
  | .step => .ret p.step
  | .sample => .seq (.whileNonzero (.seq (.assign p.sample) .decrement)) (.ret .arg)

/-- Concrete statement syntax, independent of the function grammar's prefix tables. -/
def stmtTokens : Stmt → List String
  | .assign e => ["x", "="] ++ CSyntax.exprTokens e ++ [";"]
  | .decrement => ["n", "=", "n", "-", "UINT64_C", "(", "1", ")", ";"]
  | .seq a b => stmtTokens a ++ stmtTokens b
  | .whileNonzero b => ["while", "(", "n", "!=", "0", ")", "{"] ++ stmtTokens b ++ ["}"]
  | .ret e => ["return"] ++ CSyntax.exprTokens e ++ [";"]

def programTokens (p : CSyntax.Program) (linkage : C.Linkage := .external) : List String :=
  CSyntax.linkageTokens linkage ++ ["double", "rumoca_rhs", "(", "void", ")", "{"] ++ stmtTokens (body p .rhs) ++ ["}"] ++
  CSyntax.linkageTokens linkage ++ ["double", "rumoca_step", "(", "double", "x", ")", "{"] ++ stmtTokens (body p .step) ++ ["}"] ++
  CSyntax.linkageTokens linkage ++ ["double", "rumoca_sample", "(", "double", "x", ",", "uint64_t", "n", ")", "{"] ++
    stmtTokens (body p .sample) ++ ["}"]

theorem body_tokens (p : CSyntax.Program) (linkage : C.Linkage := .external) :
    p.tokens linkage = programTokens p linkage := by
  simp [CSyntax.Program.tokens, CSyntax.rhsPrefix, CSyntax.stepPrefix,
    CSyntax.samplePrefix, CSyntax.sampleSuffix, programTokens, body, stmtTokens,
    CSyntax.exprTokens, List.append_assoc]

theorem denotes_statements (h : CSyntax.Denotes text p linkage) :
    ∃ chars, text.toList = C.preamble.toList ++ chars ∧ CSyntax.Lexes chars (programTokens p linkage) := by
  obtain ⟨chars, ht, hl⟩ := h
  exact ⟨chars, ht, body_tokens p linkage ▸ hl⟩

def WellScoped (p : CSyntax.Program) : Prop :=
  Scoped false p.rhs ∧ Scoped true p.step ∧ Scoped true p.sample

theorem lower_scoped (m : Solve.Model source) : WellScoped (CExecution.program m) := by
  simp [WellScoped, CExecution.program, CSyntax.fromTarget, C.lower_is_unit,
    C.unitModule, C.Module.step, Scoped]

structure Locals where
  x : Option Value
  n : Option Counter

/-- Function entry establishes parameter scope, not arbitrary ambient values. -/
def parameters (f : Function) (x : Value) (n : Counter) : Locals :=
  match f with
  | .rhs => ⟨none, none⟩
  | .step => ⟨some x, none⟩
  | .sample => ⟨some x, some n⟩

inductive State where
  | entry (f : Function) (x : Value) (n : Counter)
  | running (code : List Stmt) (locals : Locals)
  | returned (x : Value)

/-- A continuation is the remaining statement list. Return discards it.
There are distinct transitions for each assignment and for decrement. -/
def next (p : CSyntax.Program) : State → Option State
  | .entry f x n => some (.running [body p f] (parameters f x n))
  | .returned _ => none
  | .running [] _ => none
  | .running (.seq a b :: k) locals => some (.running (a :: b :: k) locals)
  | .running (.ret e :: _) locals => do
    let y ← eval locals.x e
    return .returned y
  | .running (.assign e :: k) locals => do
    let _ ← locals.x
    let y ← eval locals.x e
    return .running k { locals with x := some y }
  | .running (.decrement :: k) locals => do
    let n ← locals.n
    return .running k { locals with n := some (decrement n) }
  | .running (.whileNonzero b :: k) locals => do
    let n ← locals.n
    if n.val = 0 then return .running k locals
    else return .running (b :: .whileNonzero b :: k) locals

def Step (p : CSyntax.Program) (s t : State) : Prop := next p s = some t

def final : State → Option Value
  | .returned x => some x
  | _ => none

def machine (p : CSyntax.Program) : Machine State Value where
  step := Step p
  final := final
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by
    intro s r h t ht
    cases s <;> simp_all [final, Step, next]

abbrev Reaches (p : CSyntax.Program) := Transition.Reaches (Step p)

private def loopBody (p : CSyntax.Program) : Stmt := .seq (.assign p.sample) .decrement
private def loopCode (p : CSyntax.Program) : List Stmt := [.whileNonzero (loopBody p), .ret .arg]
private def locals (x : Value) (n : Counter) : Locals := ⟨some x, some n⟩

theorem sample_eval (m : Solve.Model source) (x : Value) :
    eval (some x) (CExecution.program m).sample = some (m.advance x) := by
  rw [eval_bound]
  exact C.lower_binary64_correct m x

/-- The statement machine executes the actual loop by induction on the bounded
counter. Each loop iteration consists of four separate control/data steps. -/
private theorem loop_reaches (m : Solve.Model source) (x : Value) (n : Counter) :
    Reaches (CExecution.program m)
      (.running (loopCode (CExecution.program m)) (locals x n))
      (.returned (m.run x n.val)) := by
  generalize hk : n.val = k
  induction k using Nat.strong_induction_on generalizing x n with
  | h k ih =>
    by_cases hz : n.val = 0
    · have hr : m.run x k = x := by rw [← hk, hz]; rfl
      rw [hr]
      refine .next (t := .running [.ret .arg] (locals x n)) ?_ (.next (by rfl) (.refl _))
      simp only [Step, next, loopCode, locals, bind, Option.bind_some, hz, if_true, pure]
    · have hd := decrement_positive n (by omega)
      have smaller : (decrement n).val < k := by omega
      have hr : m.run x k = m.run (m.advance x) (decrement n).val := by
        have he : k = (decrement n).val + 1 := by omega
        exact (congrArg (m.run x) he).trans (Solve.Model.run.eq_2 m x _)
      rw [hr]
      refine .next (t := .running
        (loopBody (CExecution.program m) :: loopCode (CExecution.program m)) (locals x n)) ?_ ?_
      · simp only [Step, next, loopCode, locals, bind, Option.bind_some, hz, if_false,
          pure]
      refine .next (t := .running
        (.assign (CExecution.program m).sample :: .decrement :: loopCode (CExecution.program m))
        (locals x n)) (by rfl) ?_
      refine .next (t := .running (.decrement :: loopCode (CExecution.program m))
        (locals (m.advance x) n)) ?_ ?_
      · simp only [Step, next, locals, bind, Option.bind_some, sample_eval, pure]
      exact .next (by rfl) (ih _ smaller (m.advance x) (decrement n) rfl)

/-- Scope, statement execution and binary64 register semantics meet here. -/
theorem lower_correct (m : Solve.Model source) (x : Value) (n : Counter) :
    Reaches (CExecution.program m) (.entry .sample x n) (.returned (m.run x n.val)) :=
  .next (by rfl) (.next (by rfl) (loop_reaches m x n))

def result (m : Solve.Model source) (f : Function) (x : Value) (n : Counter) : Value :=
  match f with
  | .rhs => m.realRhs
  | .step => m.advance x
  | .sample => m.run x n.val

theorem call_reaches (m : Solve.Model source) (f : Function) (x : Value) (n : Counter) :
    Reaches (CExecution.program m) (.entry f x n) (.returned (result m f x n)) := by
  cases f with
  | sample => exact lower_correct m x n
  | rhs =>
    rw [result, m.realRhs_eq_one]
    refine .next (by rfl) (.next ?_ (.refl _))
    simp [Step, next, body, parameters, CExecution.program, CSyntax.fromTarget,
      C.lower_is_unit, C.unitModule, eval]
  | step =>
    refine .next (by rfl) (.next ?_ (.refl _))
    simp only [Step, next, body, parameters, eval_bound, result, CExecution.program,
      CSyntax.fromTarget, C.lower_binary64_correct, bind, Option.bind_some, pure]

/-- Every target behavior is exactly the selected Solve call result. This
excludes both divergence and undefined/stuck executions, for every ABI input. -/
theorem behaviors_correct (m : Solve.Model source) (f : Function) (x : Value) (n : Counter) :
    (machine (CExecution.program m)).Behaves (.entry f x n) b ↔
      b = .terminates (result m f x n) :=
  (machine _).behavior_iff (call_reaches m f x n) rfl

theorem all_terminate (m : Solve.Model source) (f : Function) (x : Value) (n : Counter) :
    Acc (fun t s => Step (CExecution.program m) s t) (.entry f x n) :=
  (call_reaches m f x n).accessible (machine _).deterministic (by intro t h; cases h)

theorem all_complete (m : Solve.Model source) (f : Function) (x : Value) (n : Counter)
    (h : Reaches (CExecution.program m) (.entry f x n) s) :
    Reaches (CExecution.program m) s (.returned (result m f x n)) :=
  (call_reaches m f x n).completes (machine _).deterministic (by intro t h; cases h) h

/-- C syntax alone can recognize an unbound identifier. Execution cannot
read it: the void RHS has no x parameter. -/
theorem unbound_rhs_stuck (x : Value) (n : Counter) :
    next (⟨.arg, .arg, .arg⟩ : CSyntax.Program)
      (.running [.ret .arg] (parameters .rhs x n)) = none := rfl

end Rumoca.CStatements
