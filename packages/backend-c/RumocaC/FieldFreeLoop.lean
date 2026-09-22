import RumocaC.ContextCalls
import RumocaC.FieldFreeExpressions

/-! Field-free typed loop compatibility under arbitrary declared-object contexts.
No global all-scalar assumption and no successful-evaluation shortcut. -/
noncomputable section
namespace Rumoca.CContextMachine.FieldFree
open CTree CMemory
namespace Syntax
export CDeclaredMembers.FieldFree (expression argumentList expressions sites statement body AdmittedBody)
end Syntax
open CDeclaredMembers.FieldFree
variable [interface : CInterface]

theorem typed_eval_agreement (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (e : Expr) (free : expression e = true) :
    typedEval (declared declarations objects) env types heap e = CLoops.eval env types heap e := by
  have agree := (agreement declarations objects env heap e free).1
  cases e with
  | bin op a b =>
    have parts : expression a = true ∧ expression b = true := by
      simpa only [expression, Bool.and_eq_true] using free
    have left := (agreement declarations objects env heap a parts.1).1
    have right := (agreement declarations objects env heap b parts.2).1
    cases op <;> unfold typedEval CLoops.eval CLoops.evalWith
    all_goals split <;> simp_all [declared, CBody.declaredExpressions, CBody.legacyExpressions]
  | _ => exact agree

theorem arguments_agreement (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (env : CBody.Locals) (heap : Heap)
    (args : List Expr) (free : args.all expression = true) :
    arguments (declared declarations objects) env heap args = CCalls.arguments env heap args := by
  induction args with
  | nil => rfl
  | cons e es ih =>
    have parts : expression e = true ∧ es.all expression = true := by simpa using free
    have same := (agreement declarations objects env heap e parts.1).1
    simp only [arguments, CCalls.arguments, CCalls.argumentsWith, ih parts.2]
    simp only [declared, CBody.declaredExpressions, CBody.legacyExpressions, same]

def LoopFree : CLoops.State → Prop
  | .running code _ _ _ => AdmittedBody code
  | .returned _ => True

theorem loop_next_agreement (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (s : CLoops.State) (free : LoopFree s) :
    loopNext (declared declarations objects) s = CLoops.next s := by
  cases s with
  | returned => rfl
  | running code env types heap =>
    cases code with
    | nil => rfl
    | cons stmt rest =>
      have head := body_member free stmt List.mem_cons_self
      have ev : ∀ e ∈ CDeclaredMembers.FieldFree.expressions stmt,
          typedEval (declared declarations objects) env types heap e = CLoops.eval env types heap e := by
        intro e mem
        exact typed_eval_agreement declarations objects env types heap e (List.all_eq_true.mp head e mem)
      have lv : ∀ e ∈ CDeclaredMembers.FieldFree.expressions stmt,
          (declared declarations objects).address env heap e = CBody.lvalue env heap e := by
        intro e mem
        exact (agreement declarations objects env heap e (List.all_eq_true.mp head e mem)).2
      cases stmt with
      | declare type name expr => simp only [loopNext, CLoops.next, CLoops.nextWith, ev expr (by simp [CDeclaredMembers.FieldFree.expressions])]
      | assign target expr =>
        have value := ev expr (by simp [CDeclaredMembers.FieldFree.expressions])
        have address := lv target (by simp [CDeclaredMembers.FieldFree.expressions])
        cases target <;> simp only [loopNext, CLoops.next, CLoops.nextWith, value, address] <;> rfl
      | eval expr => simp only [loopNext, CLoops.next, CLoops.nextWith, ev expr (by simp [CDeclaredMembers.FieldFree.expressions])]
      | ret value => cases value with
        | none => rfl
        | some expr => simp only [loopNext, CLoops.next, CLoops.nextWith, ev expr (by simp [CDeclaredMembers.FieldFree.expressions])]
      | branch condition yes no => simp only [loopNext, CLoops.next, CLoops.nextWith,
          ev condition (by simp [CDeclaredMembers.FieldFree.expressions])]
      | whileLoop condition body => simp only [loopNext, CLoops.next, CLoops.nextWith,
          ev condition (by simp [CDeclaredMembers.FieldFree.expressions])]

set_option maxHeartbeats 1200000 in
theorem loop_free_next (free : LoopFree before)
    (step : CLoops.next before = some after) : LoopFree after := by
  unfold CLoops.next CLoops.nextWith at step
  split at step
  all_goals aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    LoopFree, AdmittedBody, body, CDeclaredMembers.FieldFree.expressions, sites_flatMap,
    List.flatMap_cons, List.flatMap_append, List.all_append, Bool.and_eq_true])

end Rumoca.CContextMachine.FieldFree
