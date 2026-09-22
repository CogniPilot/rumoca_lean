import RumocaC.LiteralInterface

/-! Changing a global dictionary must preserve the original program, including
failed and nonterminating calls. The agreement predicate names only syntax
lookups; no successful execution is assumed. -/
namespace Rumoca.CLiteral.Interface
open CTree CMemory

def ExprAgrees (before after : CInterface) (e : Expr) : Prop :=
  ∀ name ∈ names e, before.constants name = after.constants name

def StmtAgrees (before after : CInterface) : Stmt → Prop
  | .declare _ _ value | .eval value | .ret (some value) => ExprAgrees before after value
  | .assign target value => ExprAgrees before after target ∧ ExprAgrees before after value
  | .ret none => True
  | .branch condition yes no => ExprAgrees before after condition ∧
      (∀ s ∈ yes, StmtAgrees before after s) ∧ ∀ s ∈ no, StmtAgrees before after s
  | .whileLoop condition body => ExprAgrees before after condition ∧
      ∀ s ∈ body, StmtAgrees before after s
termination_by s => sizeOf s
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_›
    simp only [Stmt.branch.sizeOf_spec, Stmt.whileLoop.sizeOf_spec]
    omega

def CodeAgrees (before after : CInterface) (code : List Stmt) : Prop :=
  ∀ s ∈ code, StmtAgrees before after s

def LoopAgrees (before after : CInterface) : CLoops.State → Prop
  | .running code _ _ _ => CodeAgrees before after code
  | .returned _ => True

theorem loop_agrees_next (valid : LoopAgrees before after s)
    (step : @CLoops.next before s = some t) : LoopAgrees before after t := by
  unfold CLoops.next CLoops.nextWith at step
  split at step
  all_goals aesop (add simp [LoopAgrees, CodeAgrees, StmtAgrees,
    Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff])

theorem loop_next_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (s : CLoops.State) (valid : LoopAgrees before after s) :
    @CLoops.next before s = @CLoops.next after s := by
  cases s with
  | returned result => rfl
  | running code env locals heap =>
      cases code with
      | nil => rfl
      | cons stmt rest =>
          have head := valid stmt (by simp)
          cases stmt with
          | declare type name value =>
              simp only [StmtAgrees] at head
              have ev := loop_expression_agreement before after types literals env locals heap value head
              simp [CLoops.next, CLoops.nextWith, types, ev]
          | assign target value =>
              simp only [StmtAgrees] at head
              have ev := loop_expression_agreement before after types literals env locals heap value head.2
              have lv := (expression_agreement before after types literals env heap target head.1).2
              change (@CBody.legacyExpressions before).address env heap target =
                (@CBody.legacyExpressions after).address env heap target at lv
              cases target <;> simp [CLoops.next, CLoops.nextWith, ev, lv]
          | eval value =>
              simp only [StmtAgrees] at head
              have ev := loop_expression_agreement before after types literals env locals heap value head
              simp [CLoops.next, CLoops.nextWith, ev]
          | ret value =>
              cases value with
              | none => rfl
              | some value =>
                  simp only [StmtAgrees] at head
                  have ev := loop_expression_agreement before after types literals env locals heap value head
                  simp [CLoops.next, CLoops.nextWith, ev]
          | branch condition yes no =>
              simp only [StmtAgrees] at head
              have ev := loop_expression_agreement before after types literals env locals heap condition head.1
              simp [CLoops.next, CLoops.nextWith, ev]
          | whileLoop condition body =>
              simp only [StmtAgrees] at head
              have ev := loop_expression_agreement before after types literals env locals heap condition head.1
              simp [CLoops.next, CLoops.nextWith, ev]

theorem arguments_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (env : CBody.Locals) (heap : Heap) (args : List Expr)
    (agree : ∀ arg ∈ args, ExprAgrees before after arg) :
    @CCalls.arguments before env heap args = @CCalls.arguments after env heap args := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp only [CCalls.arguments, CBody.legacyExpressions] at ih
      have same := (expression_agreement before after types literals env heap a (agree a (by simp))).1
      simp [CCalls.arguments, CCalls.argumentsWith, CBody.legacyExpressions, same, ih (fun e member => agree e (List.mem_cons_of_mem _ member))]

theorem cast_agreement (before after : CInterface) (types : before.types = after.types)
    (type : String) (value : Value) :
    @CBody.cast before type value = @CBody.cast after type value := by
  simp [CBody.cast, types]

theorem returnCast_agreement (before after : CInterface) (types : before.types = after.types)
    (type : String) (value : Value) :
    @CCalls.returnCast before type value = @CCalls.returnCast after type value := by
  simp [CCalls.returnCast, cast_agreement before after types]

theorem parameters_agreement (before after : CInterface) (types : before.types = after.types)
    (params : List Parameter) (args : List Value) :
    @CCalls.parameters before params args = @CCalls.parameters after params args := by
  induction params generalizing args with
  | nil => cases args <;> rfl
  | cons param rest ih =>
      cases args <;> simp [CCalls.parameters, ih, cast_agreement before after types]

theorem parameterTypes_agreement (before after : CInterface) (types : before.types = after.types)
    (params : List Parameter) :
    @CLoops.Calls.parameterTypes before params = @CLoops.Calls.parameterTypes after params := by
  induction params with
  | nil => rfl
  | cons param rest ih => simp [CLoops.Calls.parameterTypes, ih, types]

def DestinationAgrees (before after : CInterface) : CCalls.Destination → Prop
  | .assign target => ExprAgrees before after target
  | _ => True

theorem ExprAgrees.arguments (agree : ExprAgrees before after (.call fn args)) :
    ∀ arg ∈ args, ExprAgrees before after arg := by
  intro arg member name used
  apply agree name
  simp only [names, List.mem_append]
  exact Or.inr (List.mem_flatMap.mpr ⟨arg, member, used⟩)

theorem operand_agreement (agree : StmtAgrees before after stmt)
    (operand : CCalls.callOperand stmt = some (dest, name, args)) :
    DestinationAgrees before after dest ∧ ∀ arg ∈ args, ExprAgrees before after arg := by
  unfold CCalls.callOperand at operand
  split at operand
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at operand
  all_goals rcases operand with ⟨rfl, rfl, rfl⟩
  all_goals simp only [StmtAgrees] at agree
  · exact ⟨agree.1, agree.2.arguments⟩
  all_goals exact ⟨trivial, agree.arguments⟩

theorem enterCall_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (s : CLoops.State) (valid : LoopAgrees before after s) (resultType : String)
    (stack : CCalls.Typed.Continuation) :
    @CCalls.Typed.enterCall before s resultType stack = @CCalls.Typed.enterCall after s resultType stack := by
  cases s with
  | returned result => rfl
  | running code env locals heap =>
      cases code with
      | nil => rfl
      | cons stmt rest =>
          cases operand : CCalls.callOperand stmt with
          | none => simp [CCalls.Typed.enterCall, CCalls.Typed.enterCallWith, operand]
          | some request =>
              obtain ⟨dest, name, args⟩ := request
              have same := arguments_agreement before after types literals env heap args
                (operand_agreement (valid stmt (by simp)) operand).2
              simp [CCalls.Typed.enterCall, CCalls.Typed.enterCallWith, operand, same]

inductive StackAgrees (before after : CInterface) : CCalls.Typed.Continuation → Prop
  | done : StackAgrees before after .done
  | caller : DestinationAgrees before after dest → CodeAgrees before after rest →
      StackAgrees before after outer →
      StackAgrees before after (.caller dest rest env locals resultType outer)

def StateAgrees (before after : CInterface) : CCalls.Typed.State → Prop
  | .body state _ stack => LoopAgrees before after state ∧ StackAgrees before after stack
  | .calling _ _ _ stack | .kernel _ _ stack | .returning _ _ stack => StackAgrees before after stack
  | .halted _ => True

def ProgramAgrees (before after : CInterface) (program : CCalls.Program) : Prop :=
  ∀ name fn, program.definitions name = some (.tree fn) → CodeAgrees before after fn.body

theorem resume_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (value : Value) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (valid : StackAgrees before after stack) :
    @CCalls.Typed.resume before value heap stack = @CCalls.Typed.resume after value heap stack := by
  cases stack with
  | done => rfl
  | caller dest rest env locals resultType outer =>
      cases valid with
      | caller destinationAgrees codeAgrees outerAgrees =>
          cases dest with
          | discard => rfl
          | ret => simp [CCalls.Typed.resume, CCalls.Typed.resumeWith, returnCast_agreement before after types]
          | declare type name => simp [CCalls.Typed.resume, CCalls.Typed.resumeWith, types]
          | assign target =>
              have same := (expression_agreement before after types literals env heap target destinationAgrees).2
              change (@CBody.legacyExpressions before).address env heap target =
                (@CBody.legacyExpressions after).address env heap target at same
              cases target <;> simp [CCalls.Typed.resume, CCalls.Typed.resumeWith, same]

theorem enterCall_agrees_next (valid : LoopAgrees before after s)
    (stackAgrees : StackAgrees before after stack)
    (step : @CCalls.Typed.enterCall before s resultType stack = some t) : StateAgrees before after t := by
  cases s with
  | returned => simp [CCalls.Typed.enterCall, CCalls.Typed.enterCallWith] at step
  | running code env locals heap =>
      cases code with
      | nil =>
          simp only [CCalls.Typed.enterCall, CCalls.Typed.enterCallWith] at step
          split at step
          · cases Option.some.inj step; exact stackAgrees
          · contradiction
      | cons stmt rest =>
          simp only [CCalls.Typed.enterCall, CCalls.Typed.enterCallWith, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff] at step
          obtain ⟨⟨dest, name, args⟩, operand, step⟩ := step
          split at step
          · contradiction
          · simp only [Option.bind_eq_some_iff, Option.some.injEq] at step
            obtain ⟨values, arguments, result⟩ := step
            cases result
            exact StackAgrees.caller (operand_agreement (valid stmt (by simp)) operand).1
              (fun s member => valid s (List.mem_cons_of_mem _ member)) stackAgrees

theorem resume_agrees_next (valid : StackAgrees before after stack)
    (step : @CCalls.Typed.resume before value heap stack = some t) : StateAgrees before after t := by
  cases valid with
  | done => cases Option.some.inj step; trivial
  | caller destAgrees codeAgrees outerAgrees =>
      rename_i dest rest outer env locals resultType
      cases dest with
      | discard => cases Option.some.inj step; exact ⟨codeAgrees, outerAgrees⟩
      | ret =>
          simp only [CCalls.Typed.resume, CCalls.Typed.resumeWith, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at step
          obtain ⟨converted, convertedEq, rfl⟩ := step
          exact outerAgrees
      | declare type name =>
          simp only [CCalls.Typed.resume, CCalls.Typed.resumeWith] at step
          split at step
          · contradiction
          · simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
              Option.some.injEq] at step
            obtain ⟨declared, declaredEq, converted, convertedEq, rfl⟩ := step
            exact ⟨codeAgrees, outerAgrees⟩
      | assign target =>
          cases target with
          | id name =>
              simp only [CCalls.Typed.resume, CCalls.Typed.resumeWith, Option.bind_eq_bind, Option.pure_def,
                Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨old, oldEq, declared, declaredEq, converted, convertedEq, rfl⟩ := step
              exact ⟨codeAgrees, outerAgrees⟩
          | _ =>
              simp only [CCalls.Typed.resume, CCalls.Typed.resumeWith, Option.bind_eq_bind, Option.pure_def,
                Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨address, addressEq, newHeap, stored, rfl⟩ := step
              exact ⟨codeAgrees, outerAgrees⟩

theorem nextWith_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (program : CCalls.Program)
    (enterBefore enterAfter : CLoops.State → String → CCalls.Typed.Continuation → Option CCalls.Typed.State)
    (entry : ∀ state, LoopAgrees before after state → ∀ resultType stack,
      enterBefore state resultType stack = enterAfter state resultType stack)
    (s : CCalls.Typed.State) (valid : StateAgrees before after s) :
    @CCalls.Typed.nextWith before enterBefore program s = @CCalls.Typed.nextWith after enterAfter program s := by
  cases s with
  | halted result => rfl
  | returning value heap stack => exact resume_agreement before after types literals value heap stack valid
  | calling name args heap stack =>
      cases defined : program.definitions name with
      | none => simp [defined, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions]
      | some fn =>
          cases fn <;> simp [defined, parameters_agreement before after types,
            parameterTypes_agreement before after types, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions]
  | kernel state heap stack => cases state <;> rfl
  | body state resultType stack =>
      cases state with
      | returned result => simp [returnCast_agreement before after types, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions]
      | running code env locals heap =>
          have same := loop_next_agreement before after types literals (.running code env locals heap) valid.1
          have calls := entry (.running code env locals heap)
            valid.1 resultType stack
          simp only [same, calls, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions]

theorem nextWith_agrees (checked : ProgramAgrees before after program)
    (enterBefore : CLoops.State → String → CCalls.Typed.Continuation → Option CCalls.Typed.State)
    (entry : ∀ {state resultType stack target}, LoopAgrees before after state →
      StackAgrees before after stack → enterBefore state resultType stack = some target →
        StateAgrees before after target)
    (valid : StateAgrees before after s) (step : @CCalls.Typed.nextWith before enterBefore program s = some t) :
    StateAgrees before after t := by
  cases s with
  | halted result => simp [CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
  | returning value heap stack => exact resume_agrees_next valid step
  | calling name args heap stack =>
      cases defined : program.definitions name with
      | none => simp [defined, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
      | some fn =>
          cases fn with
          | kernel fn =>
              simp only [defined, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
              obtain ⟨state, entered, rfl⟩ := step
              exact valid
          | tree fn =>
              simp only [defined, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
              obtain ⟨env, parameters, locals, parameterTypes, rfl⟩ := step
              exact ⟨checked name fn defined, valid⟩
  | kernel state heap stack =>
      cases state <;>
        simp only [Option.bind_eq_bind, Option.pure_def,
          Option.bind_eq_some_iff, Option.some.injEq, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
      all_goals aesop (add simp StateAgrees)
  | body state resultType stack =>
      cases state with
      | returned result =>
          simp only [Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] at step
          obtain ⟨converted, conversion, rfl⟩ := step
          exact valid.2
      | running code env locals heap =>
          cases next : @CLoops.next before (.running code env locals heap) with
          | none =>
              exact entry valid.1 valid.2
                (by simpa only [next, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] using step)
          | some state =>
              have result : CCalls.Typed.State.body state resultType stack = t :=
                Option.some.inj (by simpa only [next, CCalls.Typed.nextWith, CCalls.Typed.nextWithExpressions] using step)
              cases result
              exact ⟨loop_agrees_next valid.1 next, valid.2⟩

theorem next_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (program : CCalls.Program) (s : CCalls.Typed.State) (valid : StateAgrees before after s) :
    @CCalls.Typed.next before program s = @CCalls.Typed.next after program s :=
  nextWith_agreement before after types literals program
    (@CCalls.Typed.enterCall before) (@CCalls.Typed.enterCall after)
    (enterCall_agreement before after types literals) s valid

theorem next_agrees (checked : ProgramAgrees before after program)
    (valid : StateAgrees before after s) (step : @CCalls.Typed.next before program s = some t) :
    StateAgrees before after t :=
  nextWith_agrees checked (@CCalls.Typed.enterCall before) enterCall_agrees_next valid step

def callBisimulation (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (program : CCalls.Program) (checked : ProgramAgrees before after program) :
    Transition.FunctionalBisimulation (@CCalls.Typed.machine before program)
      (@CCalls.Typed.machine after program) where
  map := id
  Valid := StateAgrees before after
  step := by
    intro s t valid step
    refine ⟨next_agrees checked valid step, ?_⟩
    change @CCalls.Typed.next after program s = some t
    exact (next_agreement before after types literals program s valid).symm.trans step
  reflect := by
    intro s t valid step
    refine ⟨t, ?_, rfl⟩
    change @CCalls.Typed.next before program s = some t
    exact (next_agreement before after types literals program s valid).trans step
  final := by intro s valid; cases s <;> rfl

/-- Every observation is preserved in both directions after an interface
change that preserves the original program's referenced names. -/
theorem call_behaviors (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (program : CCalls.Program) (checked : ProgramAgrees before after program)
    (valid : StateAgrees before after s) (behavior : Transition.Observation CBody.Result) :
    (@CCalls.Typed.machine after program).Behaves s behavior ↔
      (@CCalls.Typed.machine before program).Behaves s behavior :=
  (callBisimulation before after types literals program checked).behaviors valid behavior

theorem invocation_behaviors (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (program : CCalls.Program) (checked : ProgramAgrees before after program)
    (name : String) (args : List Value) (heap : Heap) (behavior : Transition.Observation CBody.Result) :
    (@CCalls.Typed.machine after program).Behaves (.calling name args heap .done) behavior ↔
      (@CCalls.Typed.machine before program).Behaves (.calling name args heap .done) behavior :=
  call_behaviors before after types literals program checked (s := .calling name args heap .done)
    StackAgrees.done behavior

end Rumoca.CLiteral.Interface
