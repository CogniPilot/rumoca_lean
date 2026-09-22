import RumocaC.ContextAppend
import RumocaC.FieldFreeCalls

/-! Closed helper behavior transported to declared contexts and arbitrary
saved callers; same heap, no field-free restriction on the external caller. -/
noncomputable section
namespace Rumoca.CContextMachine
open CTree CMemory CCalls
variable [interface : CInterface]

def CallResult (expressions : Expressions) (p : CCalls.Program) (name : String)
    (args : List Value) (heap finalHeap : Heap) : Prop :=
  (∀ stack, Transition.Reaches (machine expressions p).step
    (.calling name args heap stack) (.returning .void finalHeap stack)) ∧
  ∀ behavior, (machine expressions p).Behaves (.calling name args heap .done) behavior ↔
    behavior = .terminates ⟨.void, finalHeap⟩

theorem loop_terminates_context (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (definitions : CLoops.Calls.Definitions) (linked : Typed.Extends definitions p)
    (admitted : FieldFree.DefinitionsFree definitions) (ready : FieldFree.Ready s)
    (h : (CLoops.Calls.machine definitions).Behaves s (.terminates finalHeap)) :
    Transition.Reaches (machine (declared declarations objects) p).step
      (Typed.loopState s) (.halted ⟨.void, finalHeap⟩) := by
  cases h with
  | terminates ran final =>
    rename_i t
    cases t <;> simp [CLoops.Calls.machine, CLoops.Calls.machineWith] at final
    cases final
    exact FieldFree.loop_reaches_context declarations objects p definitions linked admitted ready ran

theorem loop_call_result_context (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (definitions : CLoops.Calls.Definitions) (linked : Typed.Extends definitions p)
    (admitted : FieldFree.DefinitionsFree definitions)
    (h : (CLoops.Calls.machine definitions).Behaves
      (.calling name args heap .done) (.terminates finalHeap)) :
    CallResult (declared declarations objects) p name args heap finalHeap := by
  have ran := loop_terminates_context declarations objects p definitions linked admitted (by trivial) h
  refine ⟨?_, fun _ => (machine (declared declarations objects) p).behavior_iff ran rfl⟩
  intro stack
  exact append_reaches (declared declarations objects) p ran stack

/-- Inline a proved call through this SAME expression context and restore the
saved body on its proved final heap. No successful-expression premise is dropped. -/
theorem invoke_reaches (expressions : Expressions) (p : CCalls.Program)
    (h : CallResult expressions p name values heap finalHeap)
    (args : List Expr) (rest : List Stmt) (env : CBody.Locals) (types : CLoops.Types)
    (type : String) (stack : Typed.Continuation)
    (ordinary : name ≠ "isfinite") (unshadowed : env name = none)
    (pureCall : expressions.value env heap (.call (.id name) args) = none)
    (evaluated : arguments expressions env heap args = some values) :
    Transition.Reaches (machine expressions p).step
      (.body (.running (.eval (.call (.id name) args) :: rest) env types heap) type stack)
      (.body (.running rest env types finalHeap) type stack) := by
  exact .next (invoke_step expressions p name args values rest env types heap type stack
      ordinary unshadowed pureCall evaluated)
    ((h.1 _).trans (.next rfl (.refl _)))

end Rumoca.CContextMachine
