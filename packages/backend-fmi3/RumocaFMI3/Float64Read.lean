import RumocaFMI3.Float64Calls
import RumocaFMI3.Float64Validation
import RumocaC.TensorMemory

/-! One output iteration follows the actual branch tree. Derivative values call
the existing model helper and numerical C statements; other values read their
represented cells. Loop composition and actual-file binding remain separate. -/
noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops

inductive Variable where | time | state | derivative
  deriving DecidableEq

def Variable.code : Variable → Nat | .time => 0 | .state => 1 | .derivative => 2

def Variable.expression : Variable → Expr
  | .time => Runtime.field "time"
  | .state => Runtime.x
  | .derivative => Runtime.call "model_rhs" [.address (Runtime.field "model")]

def Variable.value (model : Solve.FMI3Model source) (state : ModelExchange.State)
    (time : Binary64.Value) : Variable → Binary64.Value
  | .time => time
  | .state => ModelExchange.getContinuousState state
  | .derivative => ModelExchange.derivative model.solve state

theorem variable_code_unique {a b : Variable} (same : a.code = b.code) : a = b := by
  cases a <;> cases b <;> simp_all [Variable.code]

theorem variable_of_valid (value : UInt32) (valid : value.toNat ≤ 2) :
    ∃ selected : Variable, selected.code = value.toNat := by
  have cases : value.toNat = 0 ∨ value.toNat = 1 ∨ value.toNat = 2 := by omega
  rcases cases with zero | one | two
  · exact ⟨.time, zero.symm⟩
  · exact ⟨.state, one.symm⟩
  · exact ⟨.derivative, two.symm⟩

section
variable [interface : CInterface]

theorem read_dispatch (env : Locals) (types : Types) (heap : Heap) (rest : List Stmt)
    (selected : Variable) (loaded : CBody.eval env heap reference = some (.integer selected.code)) :
    CLoops.run (if selected = .time then 1 else 2) (.running (readBody ++ rest) env types heap) =
      some (.running (.assign output selected.expression :: rest) env types heap) := by
  cases selected <;>
    simp [readBody, Variable.expression, Variable.code, Runtime.branch, Runtime.eqv,
      Runtime.n, CLoops.run, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CLoops.noDeclarations,
      CBody.eval, CBody.evalWith, loaded, comparison, boolean, Value.truth]

end

section
variable [static : StaticLiterals]
private local instance readInterface : CInterface := cInterface static.addresses

def readContinuation (env : Locals) (types : Types) (rest : List Stmt)
    (resultType : String) (stack : CCalls.Typed.Continuation) : CCalls.Typed.Continuation :=
  .caller (.assign output) rest env types resultType stack

theorem output_address (env : Locals) (heap : Heap) (buffer : Address) (i : Nat)
    (pointer : resolve env "values" = some (.pointer (some buffer)))
    (counter : resolve env "k" = some (.integer i)) :
    CBody.lvalue env heap output = some (buffer.index i) := by
  simp [output, Runtime.v, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, pointer, counter, Value.address]

theorem derivative_call (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (p : Address) (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (unshadowed : env "model_rhs" = none) :
    CCalls.Events.internalNext program
      (.body (.running (.assign output Variable.derivative.expression :: rest) env types heap) resultType stack) =
      some (.calling "model_rhs" [.pointer (some (p.member "model"))] heap
        (readContinuation env types rest resultType stack)) := by
  have named : resolve env "model_rhs" = none := by simp [resolve, constants, unshadowed]
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    Variable.expression, Runtime.call, Runtime.field, Runtime.v, output,
    CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith, instanceBound, CCalls.Events.enterCallWith, CCalls.Events.resolveWith,
    CCalls.Indirect.operand, CCalls.Indirect.resolveWith, CBody.legacyExpressions, named, CCalls.argumentsWith, CBody.legacyExpressions,
    Value.address, readContinuation]

theorem output_return (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (buffer : Address) (i : Nat) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation) (value : Binary64.Value) (old : Option Value)
    (address : CBody.lvalue env heap output = some (buffer.index i))
    (storage : heap (buffer.index i) = some ⟨.float64, true, old⟩) :
    CCalls.Events.internalNext program
      (.returning (.finite value) heap (readContinuation env types rest resultType stack)) =
      some (.body (.running rest env types (StateProofs.written heap (buffer.index i)
        (Binary64.toBits value).val)) resultType stack) := by
  simp only [output] at address
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith, CBody.legacyExpressions,
    readContinuation, output, address, Value.finite,
    store_float64 heap (buffer.index i) old _ storage, StateProofs.written]

theorem read_iteration (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (p buffer : Address) (i : Nat)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (selected : Variable) (state : ModelExchange.State) (time : Binary64.Value) (old : Option Value)
    (loaded : CBody.eval env heap reference = some (.integer selected.code))
    (instanceBound : resolve env "m" = some (.pointer (some p))) (unshadowed : env "model_rhs" = none)
    (address : CBody.lvalue env heap output = some (buffer.index i))
    (storage : heap (buffer.index i) = some ⟨.float64, true, old⟩)
    (stateStored : StateProofs.Represents heap p state)
    (timeStored : load heap (p.member "time") = some (.finite time))
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (readBody ++ rest) env types heap) resultType stack)
      (.body (.running rest env types (StateProofs.written heap (buffer.index i)
        (Binary64.toBits (selected.value model state time)).val)) resultType stack) := by
  refine (CCalls.Events.body_reaches program (CLoops.run_reaches
    (read_dispatch env types heap rest selected loaded)) resultType stack).trans ?_
  simp only [output, Runtime.v] at address
  cases selected with
  | time =>
      have evaluated : CLoops.eval env types heap (Runtime.field "time") = some (.finite time) := by
        simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, instanceBound, Value.address, timeStored]
      simp only [CLoops.eval, CBody.legacyExpressions] at evaluated
      refine .next (CCalls.Events.body_step program ?_ resultType stack) (.refl _)
      simp [CLoops.next, CLoops.nextWith, CBody.legacyExpressions, output, Variable.expression, Variable.value, Runtime.v, evaluated, address, Value.finite,
        store_float64 heap (buffer.index i) old _ storage, StateProofs.written]
  | state =>
      have stored := stateStored
      simp only [StateProofs.Represents, StateProofs.stateAddress] at stored
      have evaluated : CLoops.eval env types heap Runtime.x = some (.finite state.x) := by
        simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, Runtime.x, Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, CBody.lvalueWith,
          instanceBound, Value.address, stored]
      simp only [CLoops.eval, CBody.legacyExpressions] at evaluated
      refine .next (CCalls.Events.body_step program ?_ resultType stack) (.refl _)
      simp [CLoops.next, CLoops.nextWith, CBody.legacyExpressions, output, Variable.expression, Variable.value, Runtime.v, evaluated, address,
        ModelExchange.getContinuousState, Value.finite,
        store_float64 heap (buffer.index i) old _ storage, StateProofs.written]
  | derivative =>
      refine .next (derivative_call program env types heap p rest resultType stack instanceBound unshadowed) ?_
      exact (ModelRhs.reaches model program heap (some (p.member "model"))
        (readContinuation env types rest resultType stack) helper numerical same).trans
        (.next (output_return program env types heap buffer i rest resultType stack model.solve.realRhs old address storage)
          (.refl _))

end
end Rumoca.FMI3.Float64Calls

/-! Reuse the existing tensor-memory specification for the request's serialized
output vector. This is a semantic snapshot, not element enumeration during
compiler lowering. Output ownership remains an explicit range condition. -/
noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CMemory

def outputValues (model : Solve.FMI3Model source) (state : ModelExchange.State)
    (time : Binary64.Value) (shape : Tensor.Shape) (selected : Nat → Variable) : TensorView.Values shape :=
  ⟨Vector.ofFn (fun i : Fin shape.volume => (selected i.val).value model state time)⟩

theorem outputValues_at (model : Solve.FMI3Model source) (state : ModelExchange.State)
    (time : Binary64.Value) (shape : Tensor.Shape) (selected : Nat → Variable) (i : Nat) (inside : i < shape.volume) :
    (outputValues model state time shape selected)[i] = (selected i).value model state time := by
  change (Vector.ofFn (fun j : Fin shape.volume => (selected j.val).value model state time))[i] = _
  simp

theorem pending_output (heap : Heap) (buffer : Address) (values : TensorView.Values shape)
    (writable : TensorView.Writable heap buffer shape.volume) (i : Nat) (inside : i < shape.volume) :
    ∃ old, TensorView.written heap buffer values i (buffer.index i) = some ⟨.float64, true, old⟩ := by
  obtain ⟨old, stored⟩ := writable i inside
  refine ⟨old, ?_⟩
  simpa [inside] using
    (TensorView.written_at heap buffer values i (by omega) ⟨i, inside⟩).trans (by simpa using stored)

theorem write_next_output (model : Solve.FMI3Model source) (state : ModelExchange.State)
    (time : Binary64.Value) (shape : Tensor.Shape) (selected : Nat → Variable)
    (heap : Heap) (buffer : Address) (i : Nat) (inside : i < shape.volume) :
    StateProofs.written (TensorView.written heap buffer (outputValues model state time shape selected) i)
      (buffer.index i) (Binary64.toBits ((selected i).value model state time)).val =
    TensorView.written heap buffer (outputValues model state time shape selected) (i + 1) := by
  simp [TensorView.written, inside, StateProofs.written, outputValues_at, Value.finite]

theorem references_written (heap : Heap) (buffer : Address) (pointer : Option Address)
    (values : TensorView.Values shape) (references : Nat → UInt32) (k : Nat)
    (readable : References heap pointer shape.volume references)
    (separate : ∀ p, pointer = some p →
      ∀ i < shape.volume, ∀ j < shape.volume, p.index i ≠ buffer.index j) :
    References (TensorView.written heap buffer values k) pointer shape.volume references := by
  intro i inside
  obtain ⟨p, same, loaded⟩ := readable i inside
  refine ⟨p, same, ?_⟩
  simpa only [load, TensorView.written_frame heap buffer values k (p.index i) (separate p same i inside)] using loaded

theorem state_written (heap : Heap) (buffer p : Address) (values : TensorView.Values shape)
    (state : ModelExchange.State) (k : Nat) (represented : StateProofs.Represents heap p state)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) :
    StateProofs.Represents (TensorView.written heap buffer values k) p state := by
  simpa only [StateProofs.Represents, load,
    TensorView.written_frame heap buffer values k (StateProofs.stateAddress p) separate] using represented

theorem time_written (heap : Heap) (buffer p : Address) (values : TensorView.Values shape)
    (time : Binary64.Value) (k : Nat) (represented : load heap (p.member "time") = some (.finite time))
    (separate : ∀ i < shape.volume, p.member "time" ≠ buffer.index i) :
    load (TensorView.written heap buffer values k) (p.member "time") = some (.finite time) := by
  simpa only [load, TensorView.written_frame heap buffer values k (p.member "time") separate] using represented

end Rumoca.FMI3.Float64Calls

noncomputable section
namespace Rumoca.FMI3.Float64Calls
open CTree CMemory CBody CLoops

def selectReference (reference : UInt32) : Variable :=
  if reference.toNat = 0 then .time else if reference.toNat = 1 then .state else .derivative

theorem selectReference_correct (reference : UInt32) (valid : reference.toNat ≤ 2) :
    (selectReference reference).code = reference.toNat := by
  by_cases zero : reference.toNat = 0
  · simp [selectReference, zero, Variable.code]
  · by_cases one : reference.toNat = 1
    · simp [selectReference, one, Variable.code]
    · have two : reference.toNat = 2 := by omega
      simp [selectReference, two, Variable.code]

section
variable [static : StaticLiterals]
private local instance loopInterface : CInterface := cInterface static.addresses

/-- Every output iteration uses readiness derived from the original heap and
the shared tensor-memory frame. Request order and repeated references are
retained. No intermediate execution or heap invariant is supplied by the host. -/
theorem read_reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (env : Locals) (types : Types) (heap : Heap) (p buffer : Address) (pointer : Option Address)
    (shape : Tensor.Shape) (references : Nat → UInt32) (state : ModelExchange.State) (time : Binary64.Value)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer shape.volume))
    (referenceBound : resolve env "valueReferences" = some (.pointer pointer))
    (outputBound : resolve env "values" = some (.pointer (some buffer)))
    (instanceBound : resolve env "m" = some (.pointer (some p))) (unshadowed : env "model_rhs" = none)
    (readable : References heap pointer shape.volume references)
    (valid : ∀ i < shape.volume, (references i).toNat ≤ 2)
    (writable : TensorView.Writable heap buffer shape.volume)
    (referencesSeparate : ∀ base, pointer = some base →
      ∀ i < shape.volume, ∀ j < shape.volume, base.index i ≠ buffer.index j)
    (stateStored : StateProofs.Represents heap p state)
    (stateSeparate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i)
    (timeStored : load heap (p.member "time") = some (.finite time))
    (timeSeparate : ∀ i < shape.volume, p.member "time" ≠ buffer.index i)
    (helper : program.internal.definitions "model_rhs" = some (.tree Runtime.helpers[1]))
    (numerical : program.internal.definitions "rumoca_rhs" = some (.kernel .rhs))
    (same : program.internal.kernel = CExecution.program model.solve) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") readBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (TensorView.written heap buffer
          (outputValues model state time shape (fun i => selectReference (references i))) shape.volume)) resultType stack) := by
  let selected := fun i => selectReference (references i)
  let values := outputValues model state time shape selected
  let heaps := TensorView.written heap buffer values
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "nValueReferences") readBody rest
    (fun _ => env) types heaps shape.volume resultType stack typed bounded read_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := pending_output heap buffer values writable i inside
    have refs := references_written heap buffer pointer values references i readable referencesSeparate
    have evaluated := counter_reference_eval env (heaps i) pointer shape.volume references i refs inside referenceBound
    rw [← selectReference_correct (references i) (valid i inside)] at evaluated
    have states := state_written heap buffer p values state i stateStored stateSeparate
    have times := time_written heap buffer p values time i timeStored timeSeparate
    have executed := read_iteration model program (counterEnv env "k" i) types (heaps i) p buffer i
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") readBody :: rest) resultType stack
      (selected i) state time old evaluated
      (by simpa [counterEnv, CBody.bind, resolve] using instanceBound)
      (by simpa [counterEnv, CBody.bind] using unshadowed)
      (output_address _ _ buffer i (by simpa [counterEnv, CBody.bind, resolve] using outputBound)
        (by simp [counterEnv, CBody.bind, resolve]))
      storage states times helper numerical same
    simpa only [heaps, values, write_next_output model state time shape selected heap buffer i inside] using executed

end
end Rumoca.FMI3.Float64Calls
