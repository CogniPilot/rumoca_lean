import RumocaC.LiteralInterfaceCalls
import RumocaC.CallEvents

/-! Extending unused global bindings preserves every eventful behavior.
Foreign effects are transported with their signature types unchanged. -/
noncomputable section
namespace Rumoca.CLiteral.Interface.Events
open CTree CMemory

def external (types : before.types = after.types) (fn : @CCalls.Events.External before E) :
    @CCalls.Events.External after E where
  signature := (@CCalls.Events.External.signature before E fn)
  execute := (@CCalls.Events.External.execute before E fn)
  result_typed := by
    intro args heap events result final executed
    rw [← returnCast_agreement before after types]
    exact (@CCalls.Events.External.result_typed before E fn) args heap events result final executed
  readonly := (@CCalls.Events.External.readonly before E fn)

def program (types : before.types = after.types) (original : @CCalls.Events.Program before E) :
    @CCalls.Events.Program after E where
  internal := (@CCalls.Events.Program.internal before E original)
  addresses := (@CCalls.Events.Program.addresses before E original)
  externals name := ((@CCalls.Events.Program.externals before E original) name).map (external types)
  disjoint := by
    intro name fn found
    obtain ⟨originalFn, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact (@CCalls.Events.Program.disjoint before E original) name originalFn originalFound
  names := by
    intro name fn found
    obtain ⟨originalFn, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
    exact (@CCalls.Events.Program.names before E original) name originalFn originalFound

theorem target_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (env : CBody.Locals) (heap : Heap) (callee : Expr) (agree : ExprAgrees before after callee) :
    @CCalls.Indirect.resolve before env heap callee = @CCalls.Indirect.resolve after env heap callee := by
  have values := (expression_agreement before after types literals env heap callee agree).1
  cases callee with
  | id name =>
      have resolved : @CBody.resolve before env name = @CBody.resolve after env name := values
      simp only [CCalls.Indirect.resolve, CCalls.Indirect.resolveWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, resolved]
  | field | index =>
      simpa only [CCalls.Indirect.resolve, CCalls.Indirect.resolveWith, CBody.legacyExpressions] using
        congrArg (fun value => value.bind CCalls.Indirect.valueTarget) values
  | _ => rfl

theorem resolve_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E) (env : CBody.Locals) (heap : Heap)
    (callee : Expr) (agree : ExprAgrees before after callee) :
    @CCalls.Events.resolve E before original env heap callee =
      @CCalls.Events.resolve E after (program types original) env heap callee := by
  simp only [CCalls.Events.resolve, CCalls.Events.resolveWith, target_agreement before after types literals env heap callee agree,
    program]

theorem callee_agreement (agree : ExprAgrees before after (.call fn args)) :
    ExprAgrees before after fn := by
  intro name used
  apply agree name
  simp only [names, List.mem_append]
  exact Or.inl used

theorem operand_agreement (agree : StmtAgrees before after stmt)
    (operand : CCalls.Indirect.operand stmt = some call) :
    DestinationAgrees before after call.destination ∧ ExprAgrees before after call.callee ∧
      ∀ arg ∈ call.args, ExprAgrees before after arg := by
  unfold CCalls.Indirect.operand at operand
  split at operand
  all_goals simp only [Option.some.injEq, reduceCtorEq] at operand
  all_goals cases operand
  all_goals simp only [StmtAgrees] at agree
  · exact ⟨agree.1, (callee_agreement agree.2), agree.2.arguments⟩
  all_goals exact ⟨trivial, (callee_agreement agree), agree.arguments⟩

theorem enter_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E) (s : CLoops.State)
    (valid : LoopAgrees before after s) (resultType : String) (stack : CCalls.Typed.Continuation) :
    @CCalls.Events.enterCall E before original s resultType stack =
      @CCalls.Events.enterCall E after (program types original) s resultType stack := by
  cases s with
  | returned result => rfl
  | running code env locals heap =>
      cases code with
      | nil => rfl
      | cons stmt rest =>
          cases operand : CCalls.Indirect.operand stmt with
          | none => simp [CCalls.Events.enterCall, CCalls.Events.enterCallWith, operand]
          | some request =>
              have ⟨_, callee, args⟩ := operand_agreement (valid stmt (by simp)) operand
              have resolved := resolve_agreement before after types literals original env heap request.callee callee
              have values := arguments_agreement before after types literals env heap request.args args
              simp only [CCalls.Events.resolve] at resolved
              simp only [CCalls.arguments] at values
              simp [CCalls.Events.enterCall, CCalls.Events.enterCallWith, operand, resolved, values]

theorem enter_agrees_next (original : @CCalls.Events.Program before E)
    (valid : LoopAgrees before after s) (stackAgrees : StackAgrees before after stack)
    (step : @CCalls.Events.enterCall E before original s resultType stack = some t) :
    StateAgrees before after t := by
  cases s with
  | returned => simp [CCalls.Events.enterCall, CCalls.Events.enterCallWith] at step
  | running code env locals heap =>
      cases code with
      | nil =>
          simp only [CCalls.Events.enterCall, CCalls.Events.enterCallWith] at step
          split at step
          · cases Option.some.inj step; exact stackAgrees
          · contradiction
      | cons stmt rest =>
          simp only [CCalls.Events.enterCall, CCalls.Events.enterCallWith, Option.bind_eq_bind, Option.pure_def,
            Option.bind_eq_some_iff, Option.some.injEq] at step
          obtain ⟨call, operand, name, resolved, values, evaluated, rfl⟩ := step
          exact StackAgrees.caller (operand_agreement (valid stmt (by simp)) operand).1
            (fun s member => valid s (List.mem_cons_of_mem _ member)) stackAgrees

theorem internal_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E) (s : CCalls.Typed.State)
    (valid : StateAgrees before after s) :
    @CCalls.Events.internalNext E before original s =
      @CCalls.Events.internalNext E after (program types original) s :=
  nextWith_agreement before after types literals (@CCalls.Events.Program.internal before E original)
    (@CCalls.Events.enterCall E before original)
    (@CCalls.Events.enterCall E after (program types original))
    (enter_agreement before after types literals original) s valid

theorem internal_agrees (original : @CCalls.Events.Program before E)
    (checked : ProgramAgrees before after (@CCalls.Events.Program.internal before E original))
    (valid : StateAgrees before after s)
    (step : @CCalls.Events.internalNext E before original s = some t) : StateAgrees before after t :=
  nextWith_agrees checked (@CCalls.Events.enterCall E before original) (enter_agrees_next original) valid step

end Rumoca.CLiteral.Interface.Events

namespace Rumoca.CLiteral.Interface.Events
open CTree CMemory

theorem converted_agreement (before after : CInterface) (types : before.types = after.types)
    (params : List Parameter) (args : List Value) :
    @CCalls.Events.convertedArguments before params args =
      @CCalls.Events.convertedArguments after params args := by
  simp only [CCalls.Events.convertedArguments, parameters_agreement before after types]

theorem step_agrees (original : @CCalls.Events.Program before E)
    (checked : ProgramAgrees before after (@CCalls.Events.Program.internal before E original))
    (valid : StateAgrees before after s) (step : @CCalls.Events.Step E before original s events t) :
    StateAgrees before after t := by
  cases step with
  | internal next => exact internal_agrees original checked valid next
  | external found converted executed => exact valid

theorem step_forward (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E) (valid : StateAgrees before after s)
    (step : @CCalls.Events.Step E before original s events t) :
    @CCalls.Events.Step E after (program types original) s events t := by
  cases step with
  | internal next =>
      exact .internal ((internal_agreement before after types literals original _ valid).symm.trans next)
  | @external name fn args values beforeHeap events result afterHeap stack found converted executed =>
      apply CCalls.Events.Step.external (fn := external types fn)
      · simp only [program, found, Option.map_some]
      · exact (converted_agreement before after types _ _).symm.trans converted
      · exact executed

theorem step_backward (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E) (valid : StateAgrees before after s)
    (step : @CCalls.Events.Step E after (program types original) s events t) :
    @CCalls.Events.Step E before original s events t := by
  letI : CInterface := before
  cases step with
  | internal next =>
      exact .internal ((internal_agreement before after types literals original _ valid).trans next)
  | @external name fn args values beforeHeap events result afterHeap stack found converted executed =>
      obtain ⟨originalFn, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
      apply CCalls.Events.Step.external originalFound
      · exact (converted_agreement before after types _ _).trans converted
      · exact executed

def bisimulation (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E)
    (checked : ProgramAgrees before after (@CCalls.Events.Program.internal before E original)) :
    Transition.Events.FunctionalBisimulation (@CCalls.Events.machine E before original)
      (@CCalls.Events.machine E after (program types original)) where
  map := id
  Valid := StateAgrees before after
  step valid step := ⟨step_agrees original checked valid step,
    step_forward before after types literals original valid step⟩
  reflect valid step := ⟨_, step_backward before after types literals original valid step, rfl⟩
  final := by intro s valid; cases s <;> rfl

/-- Lookup agreement on original syntax suffices for all observable behaviors;
no specific callback name, success outcome or deterministic host is assumed. -/
theorem behaviors (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E)
    (checked : ProgramAgrees before after (@CCalls.Events.Program.internal before E original))
    (valid : StateAgrees before after s) (behavior : Transition.Events.Observation E CBody.Result) :
    (@CCalls.Events.machine E after (program types original)).Behaves s behavior ↔
      (@CCalls.Events.machine E before original).Behaves s behavior :=
  (bisimulation before after types literals original checked).behaviors valid behavior

theorem invocation_behaviors (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @CCalls.Events.Program before E)
    (checked : ProgramAgrees before after (@CCalls.Events.Program.internal before E original))
    (name : String) (args : List Value) (heap : Heap)
    (behavior : Transition.Events.Observation E CBody.Result) :
    (@CCalls.Events.machine E after (program types original)).Behaves (.calling name args heap .done) behavior ↔
      (@CCalls.Events.machine E before original).Behaves (.calling name args heap .done) behavior :=
  behaviors before after types literals original checked (s := .calling name args heap .done) .done behavior

end Rumoca.CLiteral.Interface.Events
