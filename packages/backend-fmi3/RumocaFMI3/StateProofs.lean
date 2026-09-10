import RumocaFMI3.LifecycleGuard
import RumocaC.Body
import RumocaFMI3.Runtime
import RumocaCore.Solve.ModelExchange

/-! Contracts for the actual generated ME state-access bodies. Function entry
supplies the official parameter bindings. Valid instance/caller storage is
an explicit precondition; separate blocks express ownership and permit frame
conclusions. These are body-AST theorems, not emitted-text/ABI certificates. -/
namespace Rumoca.FMI3.StateProofs
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory CBody

def stateAddress (p : Address) : Address := (p.member "model").member "x"

def parameters (instanceAddress buffer : Address) (count : Int := 1) : Locals := fun name =>
  if name = "instance" then some (.pointer (some instanceAddress))
  else if name = "continuousStates" then some (.pointer (some buffer))
  else if name = "nContinuousStates" then some (.integer count)
  else none

def written (heap : Heap) (address : Address) (bits : BitVec 64) : Heap :=
  replace heap address ⟨.float64, true, some (.float64 bits)⟩

def nullParameters : Locals := fun name =>
  if name = "instance" then some (.pointer none) else none

theorem null_instance_run (heap : Heap) (rest : List Stmt) :
    run 3 (.running (Runtime.instancePrefix ++ rest) nullParameters heap) =
      some (.returned ⟨.integer 3, heap⟩) := by
  simp [run, next, eval, Runtime.instancePrefix, Runtime.branch, Runtime.ret,
    Runtime.negate, Runtime.v, nullParameters, CBody.bind, resolve, constants,
    CBody.cast, convert, Value.truth, boolean]

theorem null_instance_behaviors (heap : Heap) (rest : List Stmt) (b) :
    machine.Behaves (.running (Runtime.instancePrefix ++ rest) nullParameters heap) b ↔
      b = .terminates ⟨.integer 3, heap⟩ :=
  behaviors_of_run (null_instance_run heap rest) b

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem get_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetContinuousStates")
    (heap : Heap) (p buffer : Address) (mode : Mode) (x : Binary64.Value) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (hx : load heap (stateAddress p) = some (.finite x))
    (ho : heap buffer = some ⟨.float64, true, old⟩) :
    run 6 (.running (Runtime.body m sig) (parameters p buffer) heap) =
      some (.returned ⟨.integer 0, written heap buffer (Binary64.toBits x).val⟩) := by
  change load heap ((p.member "model").member "x") = some (.float64 (Binary64.toBits x).val) at hx
  let tail := Runtime.scalarAccessCheck "continuousStates" "nContinuousStates" ++
    [Stmt.assign (.index (Runtime.v "continuousStates") (Runtime.n 0)) Runtime.x, Runtime.ok]
  have hp := LifecycleGuard.accept (parameters p buffer) heap p .getStates .me mode tail
    (by simp [parameters]) (by simp [parameters]) hk hm allowed
  have hb : Runtime.body m sig = Runtime.require .getStates ++ tail := by
    simp [Runtime.body, hsig, tail]
  rw [hb, show 6 = 3 + 3 from rfl, run_add, hp]
  simp [tail, Runtime.scalarAccessCheck, Runtime.reject, Runtime.branch,
    Runtime.ret, Runtime.ok, Runtime.field, Runtime.x, Runtime.nev, Runtime.either,
    Runtime.negate, Runtime.v, Runtime.n, run, next, eval, lvalue, parameters,
    CBody.bind, resolve, constants, CBody.cast, convert, comparison, boolean,
    Value.truth, Value.address, hx, store_float64 heap buffer old _ ho, written]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem set_run (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3SetContinuousStates")
    (heap : Heap) (p buffer : Address) (x : Binary64.Value) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (hi : load heap buffer = some (.finite x))
    (hs : heap (stateAddress p) = some ⟨.float64, true, old⟩) :
    run 7 (.running (Runtime.body m sig) (parameters p buffer) heap) =
      some (.returned ⟨.integer 0, written heap (stateAddress p) (Binary64.toBits x).val⟩) := by
  change heap ((p.member "model").member "x") = some ⟨.float64, true, old⟩ at hs
  have storeState := store_float64 heap ((p.member "model").member "x") old (Binary64.toBits x).val hs
  have finiteInput := Value.isFinite_finite x
  change Value.isFinite (.float64 (Binary64.toBits x).val) = some true at finiteInput
  simp [Runtime.body, hsig, Runtime.require, Runtime.instancePrefix, Runtime.reject,
    Runtime.allowedExpression, Runtime.any, permittedModes, Runtime.mode, Mode.code,
    Runtime.scalarAccessCheck, Runtime.branch, Runtime.ret, Runtime.fail, Runtime.ok,
    Runtime.field, Runtime.x, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.v, Runtime.n, Runtime.call, Runtime.finite,
    run, next, eval, lvalue, parameters, CBody.bind, resolve, constants, CBody.cast, convert,
    comparison, boolean, Value.truth, Value.address,
    hk, hm, hi, finiteInput, Value.finite, storeState, written, stateAddress]

def Represents (heap : Heap) (p : Address) (state : ModelExchange.State) : Prop :=
  load heap (stateAddress p) = some (.finite state.x)

omit static in
theorem written_represents (heap : Heap) (p : Address) (state : ModelExchange.State)
    (x : Binary64.Value) :
    Represents (written heap (stateAddress p) (Binary64.toBits x).val) p
      (ModelExchange.setContinuousState state x) := by
  simp [Represents, ModelExchange.setContinuousState, written, load, convert, Value.finite]

/-- The complete observation includes the final heap, not just the OK status.
Every generated-body behavior returns the original model encoding in the
caller buffer; neither divergence nor stuck execution is possible. -/
theorem get_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3GetContinuousStates")
    (heap : Heap) (p buffer : Address) (mode : Mode) (state : ModelExchange.State) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates .me mode)
    (hx : Represents heap p state)
    (ho : heap buffer = some ⟨.float64, true, old⟩) (b) :
    machine.Behaves (.running (Runtime.body m sig) (parameters p buffer) heap) b ↔
      b = .terminates ⟨.integer 0, written heap buffer
        (Binary64.toBits (ModelExchange.getContinuousState state)).val⟩ :=
  behaviors_of_run (get_run m sig hsig heap p buffer mode state.x old hk hm allowed hx ho) b

/-- A state setter implements the shared ME state update with exact bit
preservation. Ownership/isolation is supplied by the frame theorem below. -/
theorem set_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3SetContinuousStates")
    (heap : Heap) (p buffer : Address) (state : ModelExchange.State) (x : Binary64.Value)
    (hk : load heap (p.member "kind") = some (.integer 0))
    (hm : load heap (p.member "mode") = some (.integer 3))
    (hi : load heap buffer = some (.finite x))
    (hs : heap (stateAddress p) = some ⟨.float64, true, some (.finite state.x)⟩) (b) :
    machine.Behaves (.running (Runtime.body m sig) (parameters p buffer) heap) b ↔
      b = .terminates ⟨.integer 0, written heap (stateAddress p)
        (Binary64.toBits (ModelExchange.setContinuousState state x).x).val⟩ :=
  behaviors_of_run (set_run m sig hsig heap p buffer x _ hk hm hi hs) b

omit static in
theorem written_frame (heap : Heap) (p q : Address) (bits : BitVec 64) (hne : q ≠ p) :
    written heap p bits q = heap q := replace_other _ _ _ _ hne

omit static in
theorem written_other_instance (heap : Heap) (p q : Address) (bits : BitVec 64)
    (hne : q.block ≠ p.block) : written heap (stateAddress p) bits q = heap q := by
  apply written_frame
  intro he
  apply hne
  simpa [stateAddress, Address.member] using congrArg Address.block he

end Rumoca.FMI3.StateProofs
