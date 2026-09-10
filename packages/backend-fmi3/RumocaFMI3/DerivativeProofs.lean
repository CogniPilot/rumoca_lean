import RumocaFMI3.LifecycleGuard
import RumocaFMI3.CallProofs

/-! The generated ME derivative getter executes its helper and numerical C
statements, then writes the exact shared ME derivative into caller storage.
This composes the memory and interprocedural contracts without assuming a
black-box derivative callback. -/
noncomputable section
namespace Rumoca.FMI3.DerivativeProofs
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CCalls CallProofs

def parameters (p buffer : Address) : CBody.Locals := fun name =>
  if name = "instance" then some (.pointer (some p))
  else if name = "derivatives" then some (.pointer (some buffer))
  else if name = "nContinuousStates" then some (.integer 1)
  else none

private def locals (p buffer : Address) : CBody.Locals :=
  CBody.bind (parameters p buffer) "m" (.pointer (some p))

private def target : Expr := .index (.id "derivatives") (.nat 0)
private def tailBody : List Stmt :=
  [.assign target (Runtime.call "model_rhs" [.address (Runtime.field "model")]), Runtime.ok]
private def continuation (p buffer : Address) : Continuation :=
  .caller (.assign target) [Runtime.ok] (locals p buffer) "fmi3Status" .done

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem prefix_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetContinuousStateDerivatives")
    (heap : Heap) (p buffer : Address) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode) :
    CBody.run 4 (.running (Runtime.body m sig) (parameters p buffer) heap) =
      some (.running tailBody (locals p buffer) heap) := by
  let tail := Runtime.scalarAccessCheck "derivatives" "nContinuousStates" ++ tailBody
  have hp := LifecycleGuard.accept (parameters p buffer) heap p .getDerivatives .me mode tail
    (by simp [parameters]) (by simp [parameters]) hk hm allowed
  have hb : Runtime.body m sig = Runtime.require .getDerivatives ++ tail := by
    simp [Runtime.body, hsig, tail, tailBody, target, Runtime.v, Runtime.n]
  rw [hb, show 4 = 3 + 1 from rfl, CBody.run_add, hp]
  simp [tail, Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch,
    Runtime.nev, Runtime.either, Runtime.negate, Runtime.v, Runtime.n,
    CBody.run, CBody.next, CBody.eval, parameters, locals, CBody.bind,
    CBody.resolve, CBody.constants, CBody.comparison, CBody.boolean, Value.truth]

private theorem enter_rhs (m : Solve.FMI3Model source) (heap : Heap) (p buffer : Address) :
    next (linked m) (.body (.running tailBody (locals p buffer) heap) "fmi3Status" .done) =
      some (.calling "model_rhs" [.pointer (some (p.member "model"))] heap (continuation p buffer)) := by
  simp [next, tailBody, CBody.next, CBody.eval, CBody.lvalue,
    enterCall, callOperand, arguments, Runtime.call, Runtime.field, Runtime.v,
    locals, parameters, CBody.bind, CBody.resolve, CBody.constants,
    Value.address, continuation]

private theorem return_rhs (m : Solve.FMI3Model source) (heap : Heap)
    (p buffer : Address) (y : Binary64.Value) (old : Option Value)
    (ho : heap buffer = some ⟨.float64, true, old⟩) :
    next (linked m) (.returning (.finite y) heap (continuation p buffer)) =
      some (.body (.running [Runtime.ok] (locals p buffer)
        (StateProofs.written heap buffer (Binary64.toBits y).val)) "fmi3Status" .done) := by
  simp [next, resume, continuation, target, CBody.lvalue, CBody.eval,
    locals, parameters, CBody.bind, CBody.resolve, CBody.constants,
    Value.address, Value.finite, store_float64 heap buffer old _ ho, StateProofs.written]

private theorem finish (program : Program) (heap : Heap) (env : CBody.Locals)
    (hok : env "fmi3OK" = none) :
    run program 3 (.body (.running [Runtime.ok] env heap) "fmi3Status" .done) =
      some (.halted ⟨.integer 0, heap⟩) := by
  simp [run, next, CBody.next, Runtime.ok, Runtime.ret, Runtime.v,
    CBody.eval, CBody.resolve, CBody.constants, hok, returnCast,
    CBody.cast, convert, resume]

theorem get_reaches (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetContinuousStateDerivatives")
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (ho : heap buffer = some ⟨.float64, true, old⟩) :
    Transition.Reaches (machine (linked m)).step
      (.body (.running (Runtime.body m sig) (parameters p buffer) heap) "fmi3Status" .done)
      (.halted ⟨.integer 0, StateProofs.written heap buffer
        (Binary64.toBits (ModelExchange.derivative m.solve state)).val⟩) := by
  have initial := body_reaches (linked m)
    (CBody.run_reaches (prefix_run m sig hsig heap p buffer mode hk hm allowed)) "fmi3Status" .done
  refine initial.trans (.next (enter_rhs m heap p buffer)
    ((model_rhs_reaches m heap (p.member "model") (continuation p buffer)).trans
      (.next (return_rhs m heap p buffer m.solve.realRhs old ho) ?_)))
  exact run_reaches (finish (linked m) _ (locals p buffer)
    (by simp [locals, parameters, CBody.bind]))

/-- The observation includes the entire heap. Only the output cell changes;
`StateProofs.written_frame` supplies the corresponding ownership theorem. -/
theorem get_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetContinuousStateDerivatives")
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives .me mode)
    (ho : heap buffer = some ⟨.float64, true, old⟩) (b) :
    (machine (linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p buffer) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, StateProofs.written heap buffer
        (Binary64.toBits (ModelExchange.derivative m.solve state)).val⟩ :=
  (machine _).behavior_iff (get_reaches m sig hsig heap p buffer mode state old hk hm allowed ho) rfl

end Rumoca.FMI3.DerivativeProofs
