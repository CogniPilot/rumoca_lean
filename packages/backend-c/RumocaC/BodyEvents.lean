import RumocaC.BodyEmbedding
import RumocaC.CallEvents

/-! Lift proved closed-body execution into the shared observable call machine.
Unused foreign bindings impose no termination or determinacy premise. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory
variable {E : Type}
variable [interface : CInterface]

theorem body_call_reaches (program : Program E) (fn : Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (stack : Typed.Continuation) (n : Nat)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (bound : parameters fn.signature.parameters args = some env)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (executed : CBody.run n (.running fn.body env heap) = some (.returned result))
    (cast : returnCast fn.signature.result result.value = some returned) :
    Transition.Reaches (fun s t => internalNext program s = some t)
      (.calling fn.signature.name args heap stack) (.returning returned result.heap stack) := by
  obtain ⟨types, typed, _⟩ := Parameters.parameters_typed _ _ _ bound
  obtain ⟨types', execution, _⟩ := CBodyEmbedding.run_refines n
    (.running fn.body env heap) (.returned result) types closed executed
  refine .next (tree_entry program fn.signature.name args heap stack fn env types defined bound typed) ?_
  exact (body_reaches program (CLoops.run_reaches execution) fn.signature.result stack).trans
    (.next (by simp [internalNext, Typed.nextWith, CBodyEmbedding.lift, cast]) (.refl _))

theorem body_call_prefix (program : Program E) (fn : Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (stack : Typed.Continuation) (n : Nat)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (bound : parameters fn.signature.parameters args = some env)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (executed : CBody.run n (.running fn.body env heap) = some (.returned result))
    (cast : returnCast fn.signature.result result.value = some returned)
    (rest : Transition.Events.Forced (machine program)
      (.returning returned result.heap stack) events final) :
    Transition.Events.Forced (machine program) (.calling fn.signature.name args heap stack) events final :=
  internal_prefix program
    (body_call_reaches program fn args env heap result returned stack n defined bound closed executed cast) rest

theorem body_call_behaviors (program : Program E) (fn : Function)
    (args : List Value) (env : CBody.Locals) (heap : Heap)
    (result : CBody.Result) (returned : Value) (n : Nat)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn))
    (bound : parameters fn.signature.parameters args = some env)
    (closed : fn.body.all CBodyEmbedding.closedBlocks = true)
    (executed : CBody.run n (.running fn.body env heap) = some (.returned result))
    (cast : returnCast fn.signature.result result.value = some returned) (behavior) :
    (machine program).Behaves (.calling fn.signature.name args heap .done) behavior ↔
      behavior = .terminates [] ⟨returned, result.heap⟩ :=
  (body_call_prefix program fn args env heap result returned .done n defined bound closed executed cast
    (return_forced program returned result.heap)).behaviors behavior

end Rumoca.CCalls.Events
