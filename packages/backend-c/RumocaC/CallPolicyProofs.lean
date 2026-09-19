import RumocaC.CallPolicy
import RumocaC.CallTargets
import RumocaC.Loops
import RumocaC.TypedCalls

/-! Sound call collection, loop preservation and direct-call graph ranking for the shared authored C machine. -/
namespace Rumoca.CCallPolicy
open CTree CMemory CCalls

theorem expression_calls_complete (permitted : Expr → Prop) (expr : Expr) :
    (∀ callee ∈ expressionCalls expr, permitted callee) ↔ ExpressionAdmits permitted expr := by
  induction expr using Expr.rec (motive_2 := fun args =>
      (∀ callee ∈ args.flatMap expressionCalls, permitted callee) ↔
        ∀ arg ∈ args, ExpressionAdmits permitted arg) with
  | id | nat | decimal | str | sizeof => simp [expressionCalls, ExpressionAdmits]
  | bin _ _ _ ha hb | index _ _ ha hb =>
      simp only [expressionCalls, ExpressionAdmits, List.forall_mem_append, ha, hb]
  | not _ ha | deref _ ha | address _ ha | field _ _ _ ha | cast _ _ ha =>
      simpa only [expressionCalls, ExpressionAdmits] using ha
  | call _ _ hf ha => simp only [expressionCalls, ExpressionAdmits, List.forall_mem_cons, List.forall_mem_append, hf, ha]
  | nil => simp
  | cons _ _ he ha => simp only [List.flatMap_cons, List.forall_mem_append, List.forall_mem_cons, he, ha]

theorem statement_calls_complete (permitted : Expr → Prop) (stmt : Stmt) :
    (∀ callee ∈ statementCalls stmt, permitted callee) ↔ StatementAdmits permitted stmt := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      (∀ callee ∈ code.flatMap statementCalls, permitted callee) ↔
        ∀ stmt ∈ code, StatementAdmits permitted stmt) with
  | declare | eval => simp only [statementCalls, StatementAdmits, expression_calls_complete]
  | assign => simp only [statementCalls, StatementAdmits, List.forall_mem_append, expression_calls_complete]
  | ret value => cases value <;> simp [statementCalls, StatementAdmits, expression_calls_complete]
  | branch _ _ _ hy hn =>
      simp only [statementCalls, StatementAdmits, List.forall_mem_append, expression_calls_complete, hy, hn, and_assoc]
  | whileLoop _ _ hb => simp only [statementCalls, StatementAdmits, List.forall_mem_append, expression_calls_complete, hb]
  | nil => simp
  | cons _ _ hs hc => simp only [List.flatMap_cons, List.forall_mem_append, List.forall_mem_cons, hs, hc]

theorem checkExpression_correct (check : Expr → Bool) (expr : Expr) :
    checkExpression check expr = true ↔ ExpressionAdmits (fun e => check e = true) expr := by
  induction expr using Expr.rec (motive_2 := fun args =>
      args.all (checkExpression check) = true ↔
        ∀ arg ∈ args, ExpressionAdmits (fun e => check e = true) arg) with
  | id | nat | decimal | str | sizeof => simp [checkExpression, ExpressionAdmits]
  | bin _ _ _ ha hb | index _ _ ha hb =>
      simp only [checkExpression, ExpressionAdmits, Bool.and_eq_true, ha, hb]
  | not _ ha | deref _ ha | address _ ha | field _ _ _ ha | cast _ _ ha =>
      simpa only [checkExpression, ExpressionAdmits] using ha
  | call _ _ hf ha =>
      simp only [checkExpression, ExpressionAdmits, Bool.and_eq_true,
        List.all_subtype, List.unattach_attach, hf, ha, and_assoc]
  | nil => simp
  | cons _ _ he ha =>
      simp only [List.all_cons, Bool.and_eq_true, List.forall_mem_cons, he, ha]

theorem checkStatement_correct (check : Expr → Bool) (stmt : Stmt) :
    checkStatement check stmt = true ↔ StatementAdmits (fun e => check e = true) stmt := by
  induction stmt using Stmt.rec (motive_2 := fun code =>
      code.all (checkStatement check) = true ↔
        ∀ stmt ∈ code, StatementAdmits (fun e => check e = true) stmt) with
  | declare | eval => simp only [checkStatement, StatementAdmits, checkExpression_correct]
  | assign => simp only [checkStatement, StatementAdmits, Bool.and_eq_true, checkExpression_correct]
  | ret value => cases value <;> simp [checkStatement, StatementAdmits, checkExpression_correct]
  | branch _ _ _ hy hn =>
      simp only [checkStatement, StatementAdmits, Bool.and_eq_true, List.all_subtype,
        List.unattach_attach, checkExpression_correct, hy, hn, and_assoc]
  | whileLoop _ _ hb =>
      simp only [checkStatement, StatementAdmits, Bool.and_eq_true, List.all_subtype,
        List.unattach_attach, checkExpression_correct, hb]
  | nil => simp
  | cons _ _ hs hc =>
      simp only [List.all_cons, Bool.and_eq_true, List.forall_mem_cons, hs, hc]

/-- Kernel-checkable acceptance of a complete function body; there is no
special-casing of examples, function names, branches or loop trip counts. -/
theorem checkFunction_correct (check : Expr → Bool) (fn : Function) :
    checkFunction check fn = true ↔ ∀ stmt ∈ fn.body, StatementAdmits (fun e => check e = true) stmt := by
  simp only [checkFunction, List.all_eq_true, checkStatement_correct]

/-- The direct walk has exactly the same accepted and rejected functions as
checking the complete inventory, for every predicate and C tree. -/
theorem checkFunction_inventory (check : Expr → Bool) (fn : Function) :
    checkFunction check fn = (fn.body.flatMap statementCalls).all check := by
  apply Bool.eq_iff_iff.mpr
  rw [checkFunction_correct]
  simp only [List.all_eq_true, List.mem_flatMap]
  constructor
  · intro accepted callee occurs
    obtain ⟨stmt, member, occurs⟩ := occurs
    exact (statement_calls_complete _ stmt).mpr (accepted stmt member) callee occurs
  · intro accepted stmt member
    apply (statement_calls_complete _ stmt).mp
    intro callee occurs
    exact accepted callee ⟨stmt, member, occurs⟩

theorem operand_callee (stmt : Stmt) (operand : Indirect.Operand)
    (found : Indirect.operand stmt = some operand) : operand.callee ∈ statementCalls stmt := by
  cases stmt with
  | declare _ _ value | assign _ value | eval value =>
      cases value <;> simp_all [Indirect.operand, statementCalls, expressionCalls]
      subst operand
      simp
  | ret value =>
      cases value with
      | none => simp [Indirect.operand] at found
      | some value =>
          cases value <;> simp_all [Indirect.operand, statementCalls, expressionCalls]
          subst operand
          simp
  | branch | whileLoop => simp [Indirect.operand] at found

theorem checked_operand (checked : checkFunction check fn = true)
    (member : stmt ∈ fn.body) (found : Indirect.operand stmt = some operand) :
    check operand.callee = true := by
  have allowed := (checkFunction_correct check fn).mp checked stmt member
  exact (statement_calls_complete _ stmt).mpr allowed operand.callee (operand_callee stmt operand found)

private theorem valueTarget_not_named (value : Value) (name : String) :
    Indirect.valueTarget value ≠ some (.named name) := by
  cases value <;> simp [Indirect.valueTarget]
  split <;> simp_all

/-- Named resolution can only originate at the corresponding identifier.
Function-pointer calls remain an explicit separately checked boundary. -/
theorem named_origin [CInterface] (env : CBody.Locals) (heap : Heap) (callee : Expr)
    (found : Indirect.resolve env heap callee = some (.named name)) : callee = .id name := by
  cases callee with
  | id actual =>
      cases resolved : CBody.resolve env actual with
      | none => simpa [Indirect.resolve, resolved] using found
      | some value => exact False.elim (valueTarget_not_named value name (by simpa [Indirect.resolve, resolved] using found))
  | field object field pointer | index object field =>
      simp only [Indirect.resolve, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
      obtain ⟨value, _, called⟩ := found
      exact False.elim (valueTarget_not_named value name called)
  | _ => simp [Indirect.resolve] at found

theorem checked_named_target [CInterface] (checked : checkFunction check fn = true)
    (member : stmt ∈ fn.body) (extracted : Indirect.operand stmt = some operand)
    (resolved : Indirect.resolve env heap operand.callee = some (.named name)) :
    check (.id name) = true := by
  have permitted := checked_operand checked member extracted
  rwa [named_origin env heap operand.callee resolved] at permitted

/-- Every pending statement retains its call policy as branches and loops
are stepped. Pure expression evaluation cannot introduce statement syntax. -/
def LoopReady (permitted : Expr → Prop) : CLoops.State → Prop
  | .running code _ _ _ => ∀ stmt ∈ code, StatementAdmits permitted stmt
  | .returned _ => True

theorem loop_ready_next [CInterface] (ready : LoopReady permitted s)
    (step : CLoops.next s = some t) : LoopReady permitted t := by
  unfold CLoops.next at step
  split at step
  all_goals aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    LoopReady, StatementAdmits])

theorem loop_ready_reaches [CInterface] (ready : LoopReady permitted s)
    (path : Transition.Reaches CLoops.machine.step s t) : LoopReady permitted t := by
  induction path with
  | refl => exact ready
  | next first rest ih => exact ih (loop_ready_next ready first)

theorem rank_callee_correct (rank : String → Option Nat) (caller : Nat) (expr : Expr) :
    rankCallee rank caller expr = true ↔
      ∀ name, expr = .id name → ∀ callee, rank name = some callee → callee < caller := by
  cases expr <;> simp [rankCallee]
  split <;> simp_all

theorem check_rank_correct (rank : String → Option Nat) (fn : Function) :
    checkRank rank fn = true ↔ ∃ caller, rank fn.signature.name = some caller ∧
      ∀ name, .id name ∈ fn.body.flatMap statementCalls →
        ∀ callee, rank name = some callee → callee < caller := by
  unfold checkRank
  cases found : rank fn.signature.name with
  | none => simp
  | some caller =>
      simp only [Option.some.injEq, exists_eq_left', checkFunction_inventory, List.all_eq_true,
        rank_callee_correct]
      constructor
      · intro checked name member callee target
        exact checked (.id name) member name rfl callee target
      · intro checked expr member name same callee target
        subst expr
        exact checked name member callee target

theorem check_ranks_correct (rank : String → Option Nat) (functions : List Function) :
    checkRanks rank functions = true ↔ Ranked rank functions := by
  simp only [checkRanks, List.all_eq_true, check_rank_correct, Ranked]

/-- Numerical definitions use the existing call-free statement machine.
Their internal loops do not create calls back into the adapter scheduler. -/
def definitionCalls : Definition → List Expr
  | .tree fn => fn.body.flatMap statementCalls
  | .kernel _ => []

/-- Numerical execution cannot issue a call back into the shared scheduler.
This justifies numerical definitions being leaves in the direct-call graph. -/
theorem kernel_no_call [CInterface]
    (enter : CLoops.State → String → Typed.Continuation → Option Typed.State)
    (program : Program) (state : CStatements.State) (heap : Heap) (stack : Typed.Continuation)
    (name : String) (args : List Value) (after : Heap) (later : Typed.Continuation) :
    Typed.nextWith enter program (.kernel state heap stack) ≠
      some (.calling name args after later) := by
  cases state <;> simp [Typed.nextWith, Option.bind_eq_bind, Option.bind_eq_some_iff]

def ProgramRanked (rank : String → Option Nat) (program : Program) : Prop :=
  ∀ name definition, program.definitions name = some definition →
    ∃ caller, rank name = some caller ∧
      ∀ callee, .id callee ∈ definitionCalls definition →
        ∀ target, rank callee = some target → target < caller

/-- Include numerical definitions as leaves of the same authored program,
rather than silently treating calls to the numerical kernel as externals. -/
def ProgramEdge (program : Program) (caller callee : String) : Prop :=
  ∃ definition, program.definitions caller = some definition ∧
    .id callee ∈ definitionCalls definition ∧
    ∃ target, program.definitions callee = some target

theorem program_edge_decreases (ranked : ProgramRanked rank program)
    (edge : ProgramEdge program caller callee) :
    (rank callee).getD 0 < (rank caller).getD 0 := by
  obtain ⟨definition, found, calls, target, foundTarget⟩ := edge
  obtain ⟨a, ha, lowers⟩ := ranked caller definition found
  obtain ⟨b, hb, _⟩ := ranked callee target foundTarget
  simpa only [ha, hb, Option.getD_some] using lowers callee calls b hb

private theorem decreasing_path {Node : Type} {edge : Node → Node → Prop}
    {rank : Node → Nat} {a b : Node} (decreases : ∀ {a b}, edge a b → rank b < rank a)
    (path : Transition.Reaches edge a b) : rank b ≤ rank a := by
  induction path with
  | refl => exact Nat.le_refl _
  | next first rest ih => exact Nat.le_trans ih (Nat.le_of_lt (decreases first))

theorem program_no_cycle (ranked : ProgramRanked rank program)
    (first : ProgramEdge program caller callee) :
    ¬ Transition.Reaches (ProgramEdge program) callee caller := by
  intro path
  have lower := program_edge_decreases ranked first
  have upper := decreasing_path (fun edge => program_edge_decreases ranked edge) path
  exact Nat.not_lt_of_ge upper lower

/-- The initial body carries its full syntactic inventory. The existing loop
preservation theorem transports this invariant through nested control flow. -/
theorem function_inventory_ready (fn : Function) (env : CBody.Locals)
    (types : CLoops.Types) (heap : Heap) :
    LoopReady (fun e => e ∈ fn.body.flatMap statementCalls)
      (.running fn.body env types heap) := by
  intro stmt member
  apply (statement_calls_complete _ _).mp
  intro callee occurs
  exact List.mem_flatMap.mpr ⟨stmt, member, occurs⟩

/-- A named call resolved by the actual shared C resolver lies in the same
prepared program's graph. Indirect calls are deliberately not converted to
named calls merely because their source designator is an identifier. -/
theorem resolved_named_edge [CInterface] (program : Program) (fn : Function)
    (defined : program.definitions caller = some (.tree fn))
    (ready : LoopReady (fun e => e ∈ fn.body.flatMap statementCalls)
      (.running (stmt :: rest) env types heap))
    (extracted : Indirect.operand stmt = some operand)
    (resolved : Indirect.resolve env heap operand.callee = some (.named callee))
    (target : program.definitions callee = some definition) :
    ProgramEdge program caller callee := by
  have policy := ready stmt (List.mem_cons_self)
  have occurs := (statement_calls_complete _ _).mpr policy operand.callee
    (operand_callee stmt operand extracted)
  rw [named_origin env heap operand.callee resolved] at occurs
  exact ⟨.tree fn, defined, occurs, definition, target⟩

end Rumoca.CCallPolicy
