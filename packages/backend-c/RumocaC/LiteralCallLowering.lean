import RumocaC.LiteralLoopLowering

/-! Ordinary call entry and return for literal lowering. A literal array is
data, so a string expression in direct callee position is outside this typed
fragment. This condition is structural; no callee result is assumed. -/
noncomputable section
namespace Rumoca.CLiteral.Lowering
open CTree CMemory
variable [interface : CInterface]

def destination (symbols : Symbols) : CCalls.Destination → CCalls.Destination
  | .assign target => .assign (expression symbols target)
  | .declare type name => .declare type name
  | .discard => .discard
  | .ret => .ret

def CallHeadSafe : Stmt → Prop
  | .assign _ (.call (.str _) _) | .declare _ _ (.call (.str _) _)
  | .eval (.call (.str _) _) | .ret (some (.call (.str _) _)) => False
  | _ => True

omit interface in
theorem callOperand_lowered (symbols : Symbols) (stmt : Stmt) (safe : CallHeadSafe stmt) :
    CCalls.callOperand (statement symbols stmt) =
      (CCalls.callOperand stmt).map (fun (dest, name, args) =>
        (destination symbols dest, name, args.map (expression symbols))) := by
  cases stmt with
  | branch | whileLoop => simp [statement, CCalls.callOperand]
  | ret value =>
      cases value with
      | none => simp [statement, CCalls.callOperand]
      | some value =>
          cases value with
          | str text =>
              cases found : symbols text <;> simp [statement, expression, found, CCalls.callOperand]
          | call fn args =>
              cases fn <;> simp_all [statement, expression, CCalls.callOperand, destination, CallHeadSafe]
          | _ => simp [statement, expression, CCalls.callOperand, destination]
  | assign target value | declare type name value | eval value =>
      cases value with
      | str text =>
          cases found : symbols text <;> simp [statement, expression, found, CCalls.callOperand]
      | call fn args =>
          cases fn <;> simp_all [statement, expression, CCalls.callOperand, destination, CallHeadSafe]
      | _ => simp [statement, expression, CCalls.callOperand, destination]

/-- Named-object lookup is supplied once for each fresh function scope. -/
def GlobalBindings (symbols : Symbols) : Prop := Bound symbols (fun _ => none)

theorem parameter_bindings (globals : GlobalBindings symbols)
    (fresh : ∀ p ∈ params, FreshName symbols p.name)
    (bound : CCalls.parameters params args = some env) :
    Bound symbols env ∧ FreshLocals symbols env := by
  induction params generalizing args env with
  | nil =>
      cases args with
      | nil =>
          cases Option.some.inj bound
          exact ⟨globals, fun _ _ _ => rfl⟩
      | cons => simp [CCalls.parameters] at bound
  | cons param rest ih =>
      cases args with
      | nil => simp [CCalls.parameters] at bound
      | cons value args =>
          simp only [CCalls.parameters, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff] at bound
          obtain ⟨tail, tailBound, bound⟩ := bound
          split at bound
          · contradiction
          · simp only [Option.bind_eq_some_iff, Option.some.injEq] at bound
            obtain ⟨converted, convertedEq, result⟩ := bound
            obtain ⟨names, locals⟩ := ih (fun p member => fresh p (List.mem_cons_of_mem _ member)) tailBound
            cases result
            exact ⟨names.bind (fresh param (by simp)) converted,
              locals.bind (fresh param (by simp)) converted⟩

def continuation (symbols : Symbols) : CCalls.Typed.Continuation → CCalls.Typed.Continuation
  | .done => .done
  | .caller dest rest env types resultType outer =>
      .caller (destination symbols dest) (rest.map (statement symbols)) env types resultType
        (continuation symbols outer)

def callState (symbols : Symbols) : CCalls.Typed.State → CCalls.Typed.State
  | .body state resultType stack => .body (loopState symbols state) resultType (continuation symbols stack)
  | .calling name args heap stack => .calling name args heap (continuation symbols stack)
  | .kernel state heap stack => .kernel state heap (continuation symbols stack)
  | .returning value heap stack => .returning value heap (continuation symbols stack)
  | .halted result => .halted result

def program (symbols : Symbols) (original : CCalls.Program) : CCalls.Program where
  definitions name := (original.definitions name).map fun
    | .tree fn => .tree (function symbols fn)
    | .kernel fn => .kernel fn
  kernel := original.kernel

def HeadsSafe : CLoops.State → Prop
  | .running code _ _ _ => ∀ stmt ∈ code, CallHeadSafe stmt
  | .returned _ => True

theorem enterCall_lowered (safe : NoIntrinsic symbols) (s : CLoops.State)
    (valid : loopSafe symbols s) (heads : HeadsSafe s) (resultType : String)
    (stack : CCalls.Typed.Continuation) :
    CCalls.Typed.enterCall (loopState symbols s) resultType (continuation symbols stack) =
      (CCalls.Typed.enterCall s resultType stack).map (callState symbols) := by
  cases s with
  | returned result => rfl
  | running code env types heap =>
      cases code with
      | nil =>
          by_cases isVoid : resultType = "void" <;>
            simp [loopState, CCalls.Typed.enterCall, isVoid, callState]
      | cons stmt rest =>
          have operand := callOperand_lowered symbols stmt (heads stmt (by simp))
          cases call : CCalls.callOperand stmt with
          | none => simp [loopState, CCalls.Typed.enterCall, operand, call]
          | some request =>
              obtain ⟨dest, name, args⟩ := request
              have arguments := arguments_correct valid.1 safe heap args
              cases shadow : env name with
              | some value => simp [loopState, CCalls.Typed.enterCall, operand, call, shadow]
              | none =>
                  by_cases intrinsic : name = "isfinite" <;>
                    simp [loopState, CCalls.Typed.enterCall, operand, call, shadow, intrinsic,
                      arguments, Option.map_bind, callState, continuation]

def FrameBound (symbols : Symbols) : CCalls.Typed.Continuation → Prop
  | .done => True
  | .caller _ _ env _ _ _ => Bound symbols env ∧ FreshLocals symbols env

theorem resume_lowered (safe : NoIntrinsic symbols) (value : Value) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (valid : FrameBound symbols stack) :
    CCalls.Typed.resume value heap (continuation symbols stack) =
      (CCalls.Typed.resume value heap stack).map (callState symbols) := by
  cases stack with
  | done => rfl
  | caller dest rest env types resultType outer =>
      cases dest with
      | discard => rfl
      | ret => simp [continuation, destination, CCalls.Typed.resume, Option.map_bind, callState]
      | declare type name =>
          cases defined : (env name).isSome <;>
            simp [continuation, destination, CCalls.Typed.resume, defined, Option.map_bind, callState, loopState]
      | assign target =>
          have targetEq := (expression_correct valid.1 safe heap target).2
          cases target with
          | str text =>
              cases found : symbols text with
              | none => simp [continuation, destination, expression, found, CCalls.Typed.resume, CBody.lvalue]
              | some name =>
                  simp [continuation, destination, expression, found, CCalls.Typed.resume,
                    valid.2 text name found, CBody.lvalue]
          | _ =>
              simp only [expression] at targetEq ⊢
              simp [continuation, destination, expression, CCalls.Typed.resume, targetEq,
                Option.map_bind, callState, loopState]

def CallsWellFormed : Stmt → Prop
  | .branch _ yes no => (∀ s ∈ yes, CallsWellFormed s) ∧ (∀ s ∈ no, CallsWellFormed s)
  | .whileLoop _ body => ∀ s ∈ body, CallsWellFormed s
  | stmt => CallHeadSafe stmt
termination_by s => sizeOf s
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_›
    simp only [Stmt.branch.sizeOf_spec, Stmt.whileLoop.sizeOf_spec]
    omega

def CallsReady : CLoops.State → Prop
  | .running code _ _ _ => ∀ stmt ∈ code, CallsWellFormed stmt
  | .returned _ => True

omit interface in
theorem CallsReady.heads (ready : CallsReady s) : HeadsSafe s := by
  cases s with
  | returned => trivial
  | running code env types heap =>
      intro stmt member
      have good := ready stmt member
      cases stmt <;> simp_all [CallsWellFormed, CallHeadSafe]

omit interface in
private theorem calls_branch (condition : Expr) (yes no : List Stmt) :
    CallsWellFormed (.branch condition yes no) =
      ((∀ s ∈ yes, CallsWellFormed s) ∧ ∀ s ∈ no, CallsWellFormed s) := by
  rw [CallsWellFormed]

omit interface in
private theorem calls_loop (condition : Expr) (body : List Stmt) :
    CallsWellFormed (.whileLoop condition body) = (∀ s ∈ body, CallsWellFormed s) := by
  rw [CallsWellFormed]

theorem calls_ready_next (ready : CallsReady s) (step : CLoops.next s = some t) : CallsReady t := by
  unfold CLoops.next at step
  split at step
  all_goals aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    CallsReady, calls_branch, calls_loop])

def DestinationFresh (symbols : Symbols) : CCalls.Destination → Prop
  | .assign (.id name) | .declare _ name => FreshName symbols name
  | _ => True

omit interface in
theorem destination_fresh (fresh : FreshWrites symbols stmt)
    (operand : CCalls.callOperand stmt = some (dest, name, args)) : DestinationFresh symbols dest := by
  unfold CCalls.callOperand at operand
  split at operand
  all_goals simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at operand
  all_goals rcases operand with ⟨rfl, rfl, rfl⟩
  all_goals try simp_all [FreshWrites, DestinationFresh]
  rename_i unused target fn args
  cases target <;> simp_all [FreshWrites]

inductive StackSafe (symbols : Symbols) : CCalls.Typed.Continuation → Prop
  | done : StackSafe symbols .done
  | caller : Bound symbols env → FreshLocals symbols env → DestinationFresh symbols dest →
      (∀ stmt ∈ rest, FreshWrites symbols stmt) → (∀ stmt ∈ rest, CallsWellFormed stmt) →
      StackSafe symbols outer →
      StackSafe symbols (.caller dest rest env types resultType outer)

def StateSafe (symbols : Symbols) : CCalls.Typed.State → Prop
  | .body state _ stack => loopSafe symbols state ∧ CallsReady state ∧ StackSafe symbols stack
  | .calling _ _ _ stack | .kernel _ _ stack | .returning _ _ stack => StackSafe symbols stack
  | .halted _ => True

def ProgramSafe (symbols : Symbols) (original : CCalls.Program) : Prop :=
  ∀ name fn, original.definitions name = some (.tree fn) →
    (∀ p ∈ fn.signature.parameters, FreshName symbols p.name) ∧
    (∀ stmt ∈ fn.body, FreshWrites symbols stmt) ∧ (∀ stmt ∈ fn.body, CallsWellFormed stmt)

theorem enterCall_safe (valid : loopSafe symbols s) (ready : CallsReady s)
    (stackSafe : StackSafe symbols stack) (step : CCalls.Typed.enterCall s resultType stack = some t) :
    StateSafe symbols t := by
  cases s with
  | returned => simp [CCalls.Typed.enterCall] at step
  | running code env types heap =>
      cases code with
      | nil =>
          simp only [CCalls.Typed.enterCall] at step
          split at step
          · cases Option.some.inj step; exact stackSafe
          · contradiction
      | cons stmt rest =>
          simp only [CCalls.Typed.enterCall, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff] at step
          obtain ⟨⟨dest, name, args⟩, operand, step⟩ := step
          split at step
          · contradiction
          · simp only [Option.bind_eq_some_iff, Option.some.injEq] at step
            obtain ⟨values, arguments, result⟩ := step
            cases result
            exact StackSafe.caller valid.1 valid.2.1
              (destination_fresh (valid.2.2 stmt (by simp)) operand)
              (fun s member => valid.2.2 s (List.mem_cons_of_mem _ member))
              (fun s member => ready s (List.mem_cons_of_mem _ member)) stackSafe

theorem StackSafe.frame (valid : StackSafe symbols stack) : FrameBound symbols stack := by
  cases valid with
  | done => trivial
  | caller bound fresh => exact ⟨bound, fresh⟩

theorem resume_safe (valid : StackSafe symbols stack)
    (step : CCalls.Typed.resume value heap stack = some t) : StateSafe symbols t := by
  cases valid with
  | done => cases Option.some.inj step; trivial
  | caller bound fresh destinationFresh codeFresh codeReady outerSafe =>
      rename_i env dest rest outer types resultType
      cases dest with
      | discard =>
          cases Option.some.inj step
          exact ⟨⟨bound, fresh, codeFresh⟩, codeReady, outerSafe⟩
      | ret =>
          simp only [CCalls.Typed.resume, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at step
          obtain ⟨converted, convertedEq, rfl⟩ := step
          exact outerSafe
      | declare type name =>
          simp only [CCalls.Typed.resume] at step
          split at step
          · contradiction
          · simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
              Option.some.injEq] at step
            obtain ⟨declared, declaredEq, converted, convertedEq, rfl⟩ := step
            exact ⟨⟨bound.bind destinationFresh converted, fresh.bind destinationFresh converted, codeFresh⟩,
              codeReady, outerSafe⟩
      | assign target =>
          cases target with
          | id name =>
              simp only [CCalls.Typed.resume, Option.bind_eq_bind, Option.pure_def,
                Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨old, oldEq, declared, declaredEq, converted, convertedEq, rfl⟩ := step
              exact ⟨⟨bound.bind destinationFresh converted, fresh.bind destinationFresh converted, codeFresh⟩,
                codeReady, outerSafe⟩
          | _ =>
              simp only [CCalls.Typed.resume, Option.bind_eq_bind, Option.pure_def,
                Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨address, addressEq, newHeap, stored, rfl⟩ := step
              exact ⟨⟨bound, fresh, codeFresh⟩, codeReady, outerSafe⟩

theorem next_lowered (safe : NoIntrinsic symbols) (original : CCalls.Program)
    (s : CCalls.Typed.State) (valid : StateSafe symbols s) :
    CCalls.Typed.next (program symbols original) (callState symbols s) =
      (CCalls.Typed.next original s).map (callState symbols) := by
  cases s with
  | halted result => rfl
  | returning value heap stack => exact resume_lowered safe value heap stack valid.frame
  | calling name args heap stack =>
      cases defined : original.definitions name with
      | none => simp [CCalls.Typed.next, callState, program, defined]
      | some fn =>
          cases fn <;> simp [CCalls.Typed.next, callState, program, defined, function, loopState, Option.map_bind]
  | kernel state heap stack =>
      cases state <;> simp [CCalls.Typed.next, callState, program, Option.map_bind]
  | body state resultType stack =>
      cases state with
      | returned result => simp [CCalls.Typed.next, callState, loopState, Option.map_bind]
      | running code env types heap =>
          have lowered := loop_next safe (.running code env types heap) valid.1
          have entered := enterCall_lowered safe (.running code env types heap) valid.1
            valid.2.1.heads resultType stack
          simp only [loopState] at lowered entered
          cases next : CLoops.next (.running code env types heap) with
          | none =>
              simpa only [callState, loopState, CCalls.Typed.next, lowered, next, Option.map_none] using entered
          | some state =>
              simp [callState, loopState, CCalls.Typed.next, lowered, next]

theorem next_safe (globals : GlobalBindings symbols) (checked : ProgramSafe symbols original)
    (valid : StateSafe symbols s) (step : CCalls.Typed.next original s = some t) :
    StateSafe symbols t := by
  cases s with
  | halted result => simp [CCalls.Typed.next] at step
  | returning value heap stack => exact resume_safe valid step
  | calling name args heap stack =>
      cases defined : original.definitions name with
      | none => simp [CCalls.Typed.next, defined] at step
      | some fn =>
          cases fn with
          | kernel fn =>
              simp only [CCalls.Typed.next, defined, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨state, entered, rfl⟩ := step
              exact valid
          | tree fn =>
              have ⟨paramsFresh, codeFresh, codeReady⟩ := checked name fn defined
              simp only [CCalls.Typed.next, defined, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at step
              obtain ⟨env, parameters, types, parameterTypes, rfl⟩ := step
              obtain ⟨bound, fresh⟩ := parameter_bindings globals paramsFresh parameters
              exact ⟨⟨bound, fresh, codeFresh⟩, codeReady, valid⟩
  | kernel state heap stack =>
      cases state <;>
        simp only [CCalls.Typed.next, Option.bind_eq_bind, Option.pure_def,
          Option.bind_eq_some_iff, Option.some.injEq] at step
      all_goals aesop (add simp StateSafe)
  | body state resultType stack =>
      cases state with
      | returned result =>
          simp only [CCalls.Typed.next, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at step
          obtain ⟨converted, conversion, rfl⟩ := step
          exact valid.2.2
      | running code env types heap =>
          cases next : CLoops.next (.running code env types heap) with
          | none =>
              exact enterCall_safe valid.1 valid.2.1 valid.2.2
                (by simpa only [CCalls.Typed.next, next] using step)
          | some state =>
              have result : CCalls.Typed.State.body state resultType stack = t :=
                Option.some.inj (by simpa only [CCalls.Typed.next, next] using step)
              cases result
              exact ⟨loop_safe_next valid.1 next, calls_ready_next valid.2.1 next, valid.2.2⟩

def callBisimulation (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Program) (checked : ProgramSafe symbols original) :
    Transition.FunctionalBisimulation (CCalls.Typed.machine original)
      (CCalls.Typed.machine (program symbols original)) where
  map := callState symbols
  Valid := StateSafe symbols
  step := by
    intro s t valid next
    refine ⟨next_safe globals checked valid next, ?_⟩
    change CCalls.Typed.next original s = some t at next
    change CCalls.Typed.next (program symbols original) (callState symbols s) = some (callState symbols t)
    simpa only [next, Option.map_some] using next_lowered safe original s valid
  reflect := by
    intro s t valid next
    have lowered : (CCalls.Typed.next original s).map (callState symbols) = some t :=
      (next_lowered safe original s valid).symm.trans next
    cases step : CCalls.Typed.next original s with
    | none => simp [step] at lowered
    | some u =>
        exact ⟨u, step, (Option.some.inj (by simpa only [step, Option.map_some] using lowered)).symm⟩
  final := by intro s valid; cases s <;> rfl

/-- Complete ordinary-call behavior preservation, including recursive calls,
failure and divergence. External callbacks are still outside the C machine. -/
theorem call_behaviors (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Program) (checked : ProgramSafe symbols original)
    (valid : StateSafe symbols s) (behavior : Transition.Observation CBody.Result) :
    (CCalls.Typed.machine (program symbols original)).Behaves (callState symbols s) behavior ↔
      (CCalls.Typed.machine original).Behaves s behavior :=
  (callBisimulation safe globals original checked).behaviors valid behavior

/-- At public entry the continuation invariant is empty. Only the program's
structural freshness and supplied global bindings remain as premises. -/
theorem invocation_behaviors (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Program) (checked : ProgramSafe symbols original)
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Observation CBody.Result) :
    (CCalls.Typed.machine (program symbols original)).Behaves (.calling name args heap .done) behavior ↔
      (CCalls.Typed.machine original).Behaves (.calling name args heap .done) behavior := by
  exact call_behaviors safe globals original checked (s := .calling name args heap .done)
    StackSafe.done behavior

end Rumoca.CLiteral.Lowering
