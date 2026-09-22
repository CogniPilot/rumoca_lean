import RumocaC.LiteralCallLowering
import RumocaC.CallEvents

/-! Literal lowering preserves and reflects all behaviors of the eventful C
machine. The ordinary and eventful call machines share the scheduler proof;
foreign relations, symbolic function addresses and event labels are unchanged. -/
noncomputable section
namespace Rumoca.CLiteral.Lowering.Events
open CTree CMemory
variable [interface : CInterface]

/-- Function-address and foreign definitions are retained by literal lowering. -/
def program (symbols : Symbols) (original : CCalls.Events.Program E) : CCalls.Events.Program E where
  internal := Lowering.program symbols original.internal
  addresses := original.addresses
  externals := original.externals
  disjoint name fn found := by simp [Lowering.program, original.disjoint name fn found]
  names := original.names

theorem target_lowered (bound : Bound symbols env) (safe : NoIntrinsic symbols)
    (callee : Expr) (notString : ∀ text, callee ≠ .str text) :
    CCalls.Indirect.resolve env heap (expression symbols callee) =
      CCalls.Indirect.resolve env heap callee := by
  have values := (expression_correct bound safe heap callee).1
  cases callee with
  | str text => exact False.elim (notString text rfl)
  | field | index =>
      simpa only [expression, CCalls.Indirect.resolve, CCalls.Indirect.resolveWith, CBody.legacyExpressions] using
        congrArg (fun value => value.bind CCalls.Indirect.valueTarget) values
  | _ => simp [expression, CCalls.Indirect.resolve, CCalls.Indirect.resolveWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]

theorem resolve_lowered (original : CCalls.Events.Program E)
    (bound : Bound symbols env) (safe : NoIntrinsic symbols)
    (callee : Expr) (notString : ∀ text, callee ≠ .str text) :
    CCalls.Events.resolve (program symbols original) env heap (expression symbols callee) =
      CCalls.Events.resolve original env heap callee := by
  simp only [CCalls.Events.resolve, CCalls.Events.resolveWith, target_lowered bound safe callee notString, program]

omit interface in
theorem operand_lowered (symbols : Symbols) (stmt : Stmt) :
    CCalls.Indirect.operand (statement symbols stmt) = (CCalls.Indirect.operand stmt).map
      (fun call => ⟨destination symbols call.destination, expression symbols call.callee,
        call.args.map (expression symbols)⟩) := by
  cases stmt with
  | branch | whileLoop => simp [statement, CCalls.Indirect.operand]
  | ret value =>
      cases value with
      | none => simp [statement, CCalls.Indirect.operand]
      | some value =>
          cases value with
          | str text => cases found : symbols text <;> simp [statement, expression, found, CCalls.Indirect.operand]
          | _ => simp [statement, expression, CCalls.Indirect.operand, destination]
  | assign target value | declare type name value | eval value =>
      cases value with
      | str text => cases found : symbols text <;> simp [statement, expression, found, CCalls.Indirect.operand]
      | _ => simp [statement, expression, CCalls.Indirect.operand, destination]

omit interface in
theorem operand_head_safe (found : CCalls.Indirect.operand stmt = some call)
    (safe : CallHeadSafe stmt) : ∀ text, call.callee ≠ .str text := by
  intro text
  cases stmt with
  | branch | whileLoop => simp [CCalls.Indirect.operand] at found
  | ret value =>
      cases value with
      | none => simp [CCalls.Indirect.operand] at found
      | some value =>
          cases value <;> simp [CCalls.Indirect.operand] at found
          cases found
          rename_i callee args
          cases callee <;> simp_all [CallHeadSafe]
  | assign target value | declare type name value | eval value =>
      cases value <;> simp [CCalls.Indirect.operand] at found
      all_goals
        cases found
        rename_i callee args
        cases callee <;> simp_all [CallHeadSafe]

theorem enter_lowered (original : CCalls.Events.Program E) (safe : NoIntrinsic symbols)
    (s : CLoops.State) (valid : loopSafe symbols s) (heads : HeadsSafe s)
    (resultType : String) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.enterCall (program symbols original) (loopState symbols s) resultType
      (continuation symbols stack) =
      (CCalls.Events.enterCall original s resultType stack).map (callState symbols) := by
  cases s with
  | returned result => rfl
  | running code env types heap =>
      cases code with
      | nil =>
          by_cases isVoid : resultType = "void" <;>
            simp [loopState, CCalls.Events.enterCall, CCalls.Events.enterCallWith, isVoid, callState]
      | cons stmt rest =>
          have operand := operand_lowered symbols stmt
          cases found : CCalls.Indirect.operand stmt with
          | none => simp [loopState, CCalls.Events.enterCall, CCalls.Events.enterCallWith, operand, found]
          | some call =>
              obtain ⟨dest, callee, args⟩ := call
              have resolved := resolve_lowered (heap := heap) original valid.1 safe callee
                (operand_head_safe found (heads stmt (by simp)))
              have values := arguments_correct valid.1 safe heap args
              simp only [CCalls.Events.resolve] at resolved
              simp only [CCalls.arguments] at values
              simp [loopState, CCalls.Events.enterCall, CCalls.Events.enterCallWith, operand, found, resolved, values,
                Option.map_bind, callState, continuation]

end Rumoca.CLiteral.Lowering.Events


namespace Rumoca.CLiteral.Lowering.Events
open CTree CMemory
variable [interface : CInterface]

omit interface in
theorem operand_fresh (fresh : FreshWrites symbols stmt)
    (found : CCalls.Indirect.operand stmt = some call) : DestinationFresh symbols call.destination := by
  unfold CCalls.Indirect.operand at found
  split at found
  all_goals simp only [Option.some.injEq, reduceCtorEq] at found
  all_goals cases found
  all_goals try simp_all [FreshWrites, DestinationFresh]
  rename_i unused target fn args
  cases target <;> simp_all [FreshWrites]

theorem enter_safe (original : CCalls.Events.Program E)
    (valid : loopSafe symbols s) (ready : CallsReady s)
    (stackSafe : StackSafe symbols stack)
    (step : CCalls.Events.enterCall original s resultType stack = some t) : StateSafe symbols t := by
  cases s with
  | returned => simp [CCalls.Events.enterCall, CCalls.Events.enterCallWith] at step
  | running code env types heap =>
      cases code with
      | nil =>
          simp only [CCalls.Events.enterCall, CCalls.Events.enterCallWith] at step
          split at step
          · cases Option.some.inj step; exact stackSafe
          · contradiction
      | cons stmt rest =>
          simp only [CCalls.Events.enterCall, CCalls.Events.enterCallWith, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at step
          obtain ⟨call, operand, name, resolved, values, evaluated, rfl⟩ := step
          exact StackSafe.caller valid.1 valid.2.1
            (operand_fresh (valid.2.2 stmt (by simp)) operand)
            (fun s member => valid.2.2 s (List.mem_cons_of_mem _ member))
            (fun s member => ready s (List.mem_cons_of_mem _ member)) stackSafe

theorem internal_lowered (safe : NoIntrinsic symbols) (original : CCalls.Events.Program E)
    (s : CCalls.Typed.State) (valid : StateSafe symbols s) :
    CCalls.Events.internalNext (program symbols original) (callState symbols s) =
      (CCalls.Events.internalNext original s).map (callState symbols) :=
  nextWith_lowered safe original.internal (CCalls.Events.enterCall original)
    (CCalls.Events.enterCall (program symbols original)) (enter_lowered original safe) s valid

theorem internal_safe (globals : GlobalBindings symbols)
    (original : CCalls.Events.Program E) (checked : ProgramSafe symbols original.internal)
    (valid : StateSafe symbols s) (step : CCalls.Events.internalNext original s = some t) :
    StateSafe symbols t :=
  nextWith_safe globals checked (CCalls.Events.enterCall original) (enter_safe original) valid step

theorem step_safe (globals : GlobalBindings symbols)
    (original : CCalls.Events.Program E) (checked : ProgramSafe symbols original.internal)
    (valid : StateSafe symbols s) (step : CCalls.Events.Step original s events t) :
    StateSafe symbols t := by
  cases step with
  | internal next => exact internal_safe globals original checked valid next
  | external found converted executed => exact valid

end Rumoca.CLiteral.Lowering.Events

namespace Rumoca.CLiteral.Lowering.Events
open CTree CMemory
variable [interface : CInterface]

theorem step_lowered (safe : NoIntrinsic symbols) (original : CCalls.Events.Program E)
    (valid : StateSafe symbols s) (step : CCalls.Events.Step original s events t) :
    CCalls.Events.Step (program symbols original) (callState symbols s) events (callState symbols t) := by
  cases step with
  | internal next =>
      apply CCalls.Events.Step.internal
      simpa only [next, Option.map_some] using internal_lowered safe original _ valid
  | external found converted executed => exact .external found converted executed

theorem internal_reflected (safe : NoIntrinsic symbols) (original : CCalls.Events.Program E)
    (valid : StateSafe symbols s)
    (next : CCalls.Events.internalNext (program symbols original) (callState symbols s) = some t) :
    ∃ u, CCalls.Events.Step original s [] u ∧ t = callState symbols u := by
  have lowered : (CCalls.Events.internalNext original s).map (callState symbols) = some t :=
    (internal_lowered safe original s valid).symm.trans next
  cases first : CCalls.Events.internalNext original s with
  | none => simp [first] at lowered
  | some u =>
      exact ⟨u, .internal first,
        (Option.some.inj (by simpa only [first, Option.map_some] using lowered)).symm⟩

theorem step_reflected (safe : NoIntrinsic symbols) (original : CCalls.Events.Program E)
    (valid : StateSafe symbols s)
    (step : CCalls.Events.Step (program symbols original) (callState symbols s) events t) :
    ∃ u, CCalls.Events.Step original s events u ∧ t = callState symbols u := by
  cases s with
  | calling name args heap stack =>
      cases step with
      | internal next => exact internal_reflected safe original valid next
      | external found converted executed => exact ⟨_, .external found converted executed, rfl⟩
  | _ => cases step with
      | internal next => exact internal_reflected safe original valid next

/-- Symbolic address resolution, converted foreign arguments, external effects,
return values and all event histories survive literal lowering. -/
def bisimulation (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Events.Program E) (checked : ProgramSafe symbols original.internal) :
    Transition.Events.FunctionalBisimulation (CCalls.Events.machine original)
      (CCalls.Events.machine (program symbols original)) where
  map := callState symbols
  Valid := StateSafe symbols
  step valid step := ⟨step_safe globals original checked valid step, step_lowered safe original valid step⟩
  reflect := step_reflected safe original
  final := by intro s valid; cases s <;> rfl

/-- Complete bidirectional behavior preservation for the authored eventful C
machine, including finite or infinite traces on divergent executions. This
does not assume callbacks are deterministic or that each call has an outcome. -/
theorem behaviors (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Events.Program E) (checked : ProgramSafe symbols original.internal)
    (valid : StateSafe symbols s) (behavior : Transition.Events.Observation E CBody.Result) :
    (CCalls.Events.machine (program symbols original)).Behaves (callState symbols s) behavior ↔
      (CCalls.Events.machine original).Behaves s behavior :=
  (bisimulation safe globals original checked).behaviors valid behavior

theorem invocation_behaviors (safe : NoIntrinsic symbols) (globals : GlobalBindings symbols)
    (original : CCalls.Events.Program E) (checked : ProgramSafe symbols original.internal)
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (CCalls.Events.machine (program symbols original)).Behaves (.calling name args heap .done) behavior ↔
      (CCalls.Events.machine original).Behaves (.calling name args heap .done) behavior :=
  behaviors safe globals original checked (s := .calling name args heap .done) .done behavior

end Rumoca.CLiteral.Lowering.Events
