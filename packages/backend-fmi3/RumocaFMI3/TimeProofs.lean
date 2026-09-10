import RumocaFMI3.CInterface
import RumocaFMI3.CallProofs
import RumocaCore.FMI3.Time

/-! Generated ME time validation and successful update, against independent
reference history bounds. This does not assume monotonically increasing
trial times. HistoryProofs supplies the generated history-block contracts;
their enclosing public bodies, logging/error returns and CS arithmetic
are distinct outstanding contracts. -/
namespace Rumoca.FMI3.TimeProofs
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody
open Binary64 (toBits)

def parameters (p : Address) (bits : BitVec 64) : Locals := fun name =>
  if name = "instance" then some (.pointer (some p))
  else if name = "time" then some (.float64 bits)
  else none

def locals (p : Address) (bits : BitVec 64) : Locals :=
  CBody.bind (parameters p bits) "m" (.pointer (some p))

def rejects (minimum : Binary64.Value) (stop : Option Binary64.Value) (time : Binary64.Value) : Bool :=
  Rumoca.Float64.test .lt (toBits time).val (toBits minimum).val ||
    match stop with
    | none => false
    | some bound => Rumoca.Float64.test .gt (toBits time).val (toBits bound).val

omit static in
theorem rejects_iff (window : Time.Window) (minimum time : Binary64.Value)
    (hmin : window.RepresentsLower minimum) :
    rejects minimum window.stopTime time = false ↔ window.Admissible time := by
  rw [Time.admissible_iff window minimum time hmin]
  cases window.stopTime <;>
    simp [rejects, Rumoca.Float64.test_finite_false, Rumoca.Float64.Relation.Holds]

set_option maxRecDepth 10000 in
private theorem guard_finite (heap : Heap) (p : Address) (minimum time : Binary64.Value)
    (stop : Option Binary64.Value)
    (hm : load heap (p.member "timeMin") = some (.finite minimum))
    (hd : load heap (p.member "stopDefined") = some (boolean stop.isSome))
    (hs : ∀ bound, stop = some bound → load heap (p.member "stop") = some (.finite bound)) :
    eval (locals p (toBits time).val) heap Runtime.invalidTime =
      some (boolean (rejects minimum stop time)) := by
  have hf := Value.isFinite_finite time
  change Value.isFinite (.float64 (toBits time).val) = some true at hf
  cases stop with
  | none =>
    cases hl : Rumoca.Float64.test .lt (toBits time).val (toBits minimum).val <;>
      simp [Runtime.invalidTime, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
      Runtime.finite, Runtime.call, Runtime.lt, Runtime.gt, Runtime.field, Runtime.v,
      eval, locals, parameters, CBody.bind, resolve, constants, Value.address,
      comparison, floatComparison, hm, hd, hf, Value.finite, rejects, Runtime.n, Value.truth, boolean, hl]
  | some bound =>
    have hb := hs bound rfl
    cases hl : Rumoca.Float64.test .lt (toBits time).val (toBits minimum).val <;>
      cases hu : Rumoca.Float64.test .gt (toBits time).val (toBits bound).val <;>
      simp [Runtime.invalidTime, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
      Runtime.finite, Runtime.call, Runtime.lt, Runtime.gt, Runtime.field, Runtime.v,
      eval, locals, parameters, CBody.bind, resolve, constants, Value.address,
      comparison, floatComparison, hm, hd, hf, hb, Value.finite, rejects, Runtime.n, Value.truth, boolean, hl, hu]

/-- The actual generated expression accepts precisely the reference time
window, conditional on the representation of its history and optional stop. -/
theorem guard_reference (heap : Heap) (p : Address) (window : Time.Window)
    (minimum time : Binary64.Value)
    (hr : window.RepresentsLower minimum)
    (hm : load heap (p.member "timeMin") = some (.finite minimum))
    (hd : load heap (p.member "stopDefined") = some (boolean window.stopTime.isSome))
    (hs : ∀ bound, window.stopTime = some bound → load heap (p.member "stop") = some (.finite bound)) :
    eval (locals p (toBits time).val) heap Runtime.invalidTime = some (boolean false) ↔
      window.Admissible time := by
  rw [guard_finite heap p minimum time window.stopTime hm hd hs]
  have hb : ∀ b, boolean b = boolean false ↔ b = false := by intro b; cases b <;> decide
  rw [Option.some.injEq, hb, rejects_iff window minimum time hr]

set_option maxRecDepth 10000 in
/-- Nonfinite input rejects before loading either time bound. The full
non-null error path still needs the logging/lifecycle body theorem. -/
theorem guard_nonfinite (heap : Heap) (p : Address) (bits : BitVec 64)
    (hn : (Value.float64 bits).isFinite = some false) :
    eval (locals p bits) heap Runtime.invalidTime = some (boolean true) := by
  simp [Runtime.invalidTime, Runtime.any, Runtime.either, Runtime.both, Runtime.negate,
    Runtime.finite, Runtime.call, Runtime.lt, Runtime.gt, Runtime.field, Runtime.v,
    eval, locals, parameters, CBody.bind, resolve, constants, hn, boolean, Value.truth]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem set_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3SetTime") (heap : Heap) (p : Address)
    (window : Time.Window) (minimum time : Binary64.Value) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hmode : load heap (p.member "mode") = some (.integer 3))
    (hr : window.RepresentsLower minimum)
    (hm : load heap (p.member "timeMin") = some (.finite minimum))
    (hd : load heap (p.member "stopDefined") = some (boolean window.stopTime.isSome))
    (hs : ∀ bound, window.stopTime = some bound → load heap (p.member "stop") = some (.finite bound))
    (ht : heap (p.member "time") = some ⟨.float64, true, old⟩)
    (ha : window.Admissible time) :
    run 6 (.running (Runtime.body m sig) (parameters p (toBits time).val) heap) =
      some (.returned ⟨.integer 0, StateProofs.written heap (p.member "time") (toBits time).val⟩) := by
  have guard := (guard_reference heap p window minimum time hr hm hd hs).mpr ha
  unfold locals at guard
  simp [Runtime.body, hsig, Runtime.require, Runtime.instancePrefix, Runtime.reject,
    Runtime.allowedExpression, Runtime.any, permittedModes, Runtime.mode, Mode.code,
    Runtime.branch, Runtime.ret, Runtime.fail, Runtime.ok, Runtime.put,
    Runtime.field, Runtime.eqv, Runtime.both, Runtime.either, Runtime.negate, Runtime.v, Runtime.n,
    run, next, eval, lvalue, parameters, CBody.bind, resolve, constants,
    CBody.cast, convert, comparison, boolean, Value.truth, Value.address,
    hk, hmode, guard, store_float64 heap (p.member "time") old _ ht, StateProofs.written]

omit static in
theorem model_frame (heap : Heap) (p : Address) (bits : BitVec 64) :
    StateProofs.written heap (p.member "time") bits (StateProofs.stateAddress p) =
      heap (StateProofs.stateAddress p) := by
  apply StateProofs.written_frame
  intro h
  have hl := congrArg (fun q : Address => q.members.length) h
  simp [StateProofs.stateAddress, Address.member] at hl

noncomputable section
theorem set_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3SetTime") (heap : Heap) (p : Address)
    (window : Time.Window) (minimum time : Binary64.Value) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hmode : load heap (p.member "mode") = some (.integer 3))
    (hr : window.RepresentsLower minimum)
    (hm : load heap (p.member "timeMin") = some (.finite minimum))
    (hd : load heap (p.member "stopDefined") = some (boolean window.stopTime.isSome))
    (hs : ∀ bound, window.stopTime = some bound → load heap (p.member "stop") = some (.finite bound))
    (ht : heap (p.member "time") = some ⟨.float64, true, old⟩)
    (ha : window.Admissible time) (b) :
    (CCalls.machine (CallProofs.linked m)).Behaves
      (.body (.running (Runtime.body m sig) (parameters p (toBits time).val) heap) "fmi3Status" .done) b ↔
      b = .terminates ⟨.integer 0, StateProofs.written heap (p.member "time") (toBits time).val⟩ :=
  CCalls.body_behaviors _ (set_run m sig hsig heap p window minimum time old hk hmode hr hm hd hs ht ha)
    (by simp [CCalls.returnCast, CBody.cast, convert]) b

end
end Rumoca.FMI3.TimeProofs
