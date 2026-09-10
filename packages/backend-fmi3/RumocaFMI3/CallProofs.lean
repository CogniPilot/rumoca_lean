import RumocaFMI3.CInterface
import RumocaC.Calls
import RumocaFMI3.StateProofs

/-! Linking the emitted FMI helper bodies to the existing proved numerical
statement program. These results include actual call frames, typed parameters,
kernel execution, return conversion and memory writes. They are body-tree
contracts; printed adapter text, ABI layout and external calls remain open. -/
noncomputable section
namespace Rumoca.FMI3.CallProofs
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CCalls

def linked (m : Solve.FMI3Model source) : Program where
  definitions name :=
    if name = "rumoca_rhs" then some (.kernel .rhs)
    else if name = "rumoca_step" then some (.kernel .step)
    else if name = "rumoca_sample" then some (.kernel .sample)
    else (Runtime.helpers.find? (fun fn => fn.signature.name == name)).map Definition.tree
  kernel := Rumoca.CExecution.program m.solve

private def rhsLocals (p : Address) : CBody.Locals :=
  CBody.bind (fun _ => none) "model" (.pointer (some p))

set_option maxRecDepth 10000 in
theorem model_rhs_reaches (m : Solve.FMI3Model source) (heap : Heap) (p : Address) (stack) :
    Transition.Reaches (machine (linked m)).step
      (.calling "model_rhs" [.pointer (some p)] heap stack)
      (.returning (.finite m.solve.realRhs) heap stack) := by
  let env := rhsLocals p
  let k := Continuation.caller .ret [] env "double" stack
  have numerical := kernel_correct (linked m) m.solve rfl .rhs
    Binary64.positiveZero ⟨0, by decide⟩ heap k
  refine .next (t := .body (.running (Runtime.helpers[1].body) env heap) "double" stack) ?_ ?_
  · simp [machine, next, linked, Runtime.helpers, parameters, env, rhsLocals,
      CBody.cast, convert]
  refine .next (t := .calling "rumoca_rhs" [] heap k) ?_ ?_
  · simp [machine, next, Runtime.helpers, Runtime.ret, Runtime.call, Runtime.v,
      CBody.next, CBody.eval, enterCall, callOperand, arguments,
      env, rhsLocals, CBody.bind, k]
  refine .next (t := .kernel (.entry .rhs Binary64.positiveZero ⟨0, by decide⟩) heap k) ?_ ?_
  · simp [machine, next, linked, kernelEntry]
  exact numerical.trans (.next (by simp [machine, next, resume, k, returnCast,
    CStatements.result, CBody.cast, convert, Value.finite]) (.refl _))

private def advanceLocals (p : Address) (n : CStatements.Counter) : CBody.Locals :=
  CBody.bind (CBody.bind (fun _ => none) "count" (.integer n.val))
    "model" (.pointer (some p))

private def advanceContinuation (p : Address) (n : CStatements.Counter) (stack : Continuation) : Continuation :=
  .caller (.assign (.field (.id "model") "x" true)) [] (advanceLocals p n) "void" stack

private theorem advance_definition (m : Solve.FMI3Model source) :
    (linked m).definitions "model_advance" = some (.tree Runtime.helpers[2]) := by
  simp [linked, Runtime.helpers]

private theorem advance_parameters (p : Address) (n : CStatements.Counter) :
    parameters Runtime.helpers[2].signature.parameters [.pointer (some p), .integer n.val] =
      some (advanceLocals p n) := by
  have hc : CBody.cast "Model *" (.pointer (some p)) = some (.pointer (some p)) := by
    simp [CBody.cast, convert]
  simp [Runtime.helpers, parameters, hc, advanceLocals, CBody.bind]

set_option maxRecDepth 10000 in
private theorem advance_entry (m : Solve.FMI3Model source) (heap : Heap)
    (p : Address) (n : CStatements.Counter) (stack) :
    next (linked m) (.calling "model_advance" [.pointer (some p), .integer n.val] heap stack) =
      some (.body (.running Runtime.helpers[2].body (advanceLocals p n) heap) "void" stack) := by
  exact tree_entry (linked m) _ _ heap stack Runtime.helpers[2] (advanceLocals p n)
    (advance_definition m) (advance_parameters p n)

set_option maxRecDepth 10000 in
private theorem advance_call (m : Solve.FMI3Model source) (heap : Heap)
    (p : Address) (x : Binary64.Value) (n : CStatements.Counter) (stack)
    (hx : load heap (p.member "x") = some (.finite x)) :
    next (linked m) (.body (.running Runtime.helpers[2].body (advanceLocals p n) heap) "void" stack) =
      some (.calling "rumoca_sample" [.finite x, .integer n.val] heap (advanceContinuation p n stack)) := by
  simp [next, Runtime.helpers, Runtime.call, Runtime.v, CBody.next,
    CBody.eval, enterCall, callOperand, arguments, advanceLocals,
    CBody.bind, CBody.resolve, CBody.constants, Value.address, hx, advanceContinuation]

private theorem sample_entry (m : Solve.FMI3Model source) (heap : Heap)
    (x : Binary64.Value) (n : CStatements.Counter) (stack) :
    next (linked m) (.calling "rumoca_sample" [.finite x, .integer n.val] heap stack) =
      some (.kernel (.entry .sample x n) heap stack) := by
  simp [next, linked, kernelEntry]

set_option maxRecDepth 10000 in
private theorem advance_return (m : Solve.FMI3Model source) (heap : Heap)
    (p : Address) (x y : Binary64.Value) (n : CStatements.Counter) (stack)
    (hs : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩) :
    next (linked m) (.returning (.finite y) heap (advanceContinuation p n stack)) =
      some (.body (.running [] (advanceLocals p n)
        (StateProofs.written heap (p.member "x") (Binary64.toBits y).val)) "void" stack) := by
  simp [next, resume, advanceContinuation, CBody.lvalue,
    CBody.eval, CBody.resolve, CBody.constants, advanceLocals,
    CBody.bind, Value.address, Value.finite, store_float64 heap (p.member "x") _ _ hs,
    StateProofs.written]

theorem model_advance_reaches (m : Solve.FMI3Model source) (heap : Heap)
    (p : Address) (x : Binary64.Value) (n : CStatements.Counter) (stack)
    (hx : load heap (p.member "x") = some (.finite x))
    (hs : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩) :
    Transition.Reaches (machine (linked m)).step
      (.calling "model_advance" [.pointer (some p), .integer n.val] heap stack)
      (.returning .void
        (StateProofs.written heap (p.member "x") (Binary64.toBits (m.solve.run x n.val)).val) stack) := by
  let env := advanceLocals p n
  let k := advanceContinuation p n stack
  let output := StateProofs.written heap (p.member "x") (Binary64.toBits (m.solve.run x n.val)).val
  have numerical := kernel_correct (linked m) m.solve rfl .sample x n heap k
  refine .next (t := .body (.running (Runtime.helpers[2].body) env heap) "void" stack) ?_ ?_
  · exact advance_entry m heap p n stack
  refine .next (t := .calling "rumoca_sample" [.finite x, .integer n.val] heap k) ?_ ?_
  · exact advance_call m heap p x n stack hx
  refine .next (t := .kernel (.entry .sample x n) heap k) ?_ ?_
  · exact sample_entry m heap x n k
  refine numerical.trans (.next (t := .body (.running [] env output) "void" stack) ?_
    (.next ?_ (.refl _)))
  · exact advance_return m heap p x (m.solve.run x n.val) n stack hs
  · rfl

/-- The helper used inside CS updates exactly the shared ME model through the
verified internal unit solver, for every finite state and uint64 step count. -/
theorem model_advance_behaviors (m : Solve.FMI3Model source) (heap : Heap)
    (p : Address) (state : CoSimulation.State) (n : CStatements.Counter)
    (hx : load heap (p.member "x") = some (.finite state.model.x))
    (hs : heap (p.member "x") = some ⟨.float64, true, some (.finite state.model.x)⟩) (b) :
    (machine (linked m)).Behaves
      (.calling "model_advance" [.pointer (some p), .integer n.val] heap .done) b ↔
      b = .terminates ⟨.void, StateProofs.written heap (p.member "x")
        (Binary64.toBits (CoSimulation.run m.solve state n.val).model.x).val⟩ := by
  rw [CoSimulation.run_model_correct]
  exact (machine _).behavior_iff
    ((model_advance_reaches m heap p state.model.x n .done hx hs).trans
      (.next (by rfl) (.refl _))) rfl

end Rumoca.FMI3.CallProofs
