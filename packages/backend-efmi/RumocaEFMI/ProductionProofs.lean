import RumocaEFMI.CInterface
import RumocaEFMI.ProductionCode
import RumocaC.Arithmetic
import RumocaEFMI.CHeaderProofs
import RumocaCore.GALEC.UnitProfile
import RumocaCore.GALEC.Binary64

/-! Execution of the actual Solve-generated unit-method bodies. The target
observation is the complete returned heap. Startup accepts allocated but
uninitialized storage; later methods require finite initialized state. -/
noncomputable section
namespace Rumoca.EFMI.Production
private local instance targetInterface : CInterface := cInterface
open Rumoca.CTree Rumoca.CMemory

def unitModule : Module :=
  ⟨function "UnitIntegrator_Startup"
    [.declare "double" "v0" (.cast "double" (.nat 0)),
     .assign (stateField "x") (.id "v0"),
     .declare "double" "v1" (.cast "double" (.nat 1)),
     .assign (stateField "samplePeriod") (.id "v1")],
   function "UnitIntegrator_Recalibrate" [.assign (stateField "x") (stateField "x")],
   function "UnitIntegrator_DoStep"
    [.declare "double" "v0" (.cast "double" (.nat 1)),
     .declare "double" "v1" (.bin .add (stateField "x") (.id "v0")),
     .assign (stateField "x") (.id "v1")]⟩

theorem lower_is_unit (model : Solve.Algorithm.Model source) :
    lower model = .ok unitModule := by
  unfold lower
  rw [model.block_is_unit]
  rfl

def parameters (p : Address) : CBody.Locals :=
  CBody.bind (fun _ => none) "self" (.pointer (some p))

theorem parameters_checked (method : GALEC.Method) (p : Address) :
    CCalls.parameters (unitModule.method method).signature.parameters [.pointer (some p)] =
      some (parameters p) := by
  cases method <;> rfl

theorem return_checked (method : GALEC.Method) :
    CHeader.returnValue (unitModule.method method).signature.result (.integer 0) =
      some (.integer 0) := by
  cases method <;> exact CHeader.success_return

def written (heap : Heap) (p : Address) (x : Binary64.Value) : Heap :=
  replace heap p ⟨.float64, true, some (.finite x)⟩

def initialized (heap : Heap) (p : Address) : Heap :=
  written (written heap (p.member "x") Binary64.positiveZero)
    (p.member "samplePeriod") Binary64.one

theorem written_frame (heap : Heap) (p q : Address) (x : Binary64.Value) (hne : q ≠ p) :
    written heap p x q = heap q := replace_other _ _ _ _ hne

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem startup_run (heap : Heap) (p : Address) (oldX oldPeriod : Option Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, oldX⟩)
    (hp : heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩) :
    CArithmetic.run 5 (.running unitModule.startup.body (parameters p) heap) =
      some (.returned ⟨.integer 0, initialized heap p⟩) := by
  have hxp : p.member "samplePeriod" ≠ p.member "x" := by simp
  have hp' : written heap (p.member "x") Binary64.positiveZero (p.member "samplePeriod") =
      some ⟨.float64, true, oldPeriod⟩ := (written_frame _ _ _ _ hxp).trans hp
  have sx := store_float64 heap (p.member "x") oldX (Binary64.toBits Binary64.positiveZero).val hx
  have sp := store_float64 (written heap (p.member "x") Binary64.positiveZero)
    (p.member "samplePeriod") oldPeriod (Binary64.toBits Binary64.one).val hp'
  simp [CArithmetic.run, CArithmetic.next, CBody.next, CBody.eval,
    CBody.lvalue, unitModule, function, stateField, parameters,
    CBody.bind, CBody.resolve, CBody.constants,
    CBody.cast, convert, Value.address, sx, sp, initialized, written,
    Value.finite] at *

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem recalibrate_run (heap : Heap) (p : Address) (x : Binary64.Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩) :
    CArithmetic.run 2 (.running unitModule.recalibrate.body (parameters p) heap) =
      some (.returned ⟨.integer 0, written heap (p.member "x") x⟩) := by
  have sx := store_float64 heap (p.member "x") (some (.finite x)) (Binary64.toBits x).val hx
  have lx : load heap (p.member "x") = some (.finite x) := by
    simp [load, hx, convert, Value.finite]
  simp [CArithmetic.run, CArithmetic.next, CBody.next, CBody.eval,
    CBody.lvalue, unitModule, function, stateField, parameters,
    CBody.bind, CBody.resolve, CBody.constants,
    CBody.cast, convert, Value.address, lx, sx, written, Value.finite]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem doStep_run (heap : Heap) (p : Address) (x : Binary64.Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, some (.finite x)⟩) :
    CArithmetic.run 4 (.running unitModule.doStep.body (parameters p) heap) =
      some (.returned ⟨.integer 0, written heap (p.member "x") (Binary64.advance x)⟩) := by
  have sx := store_float64 heap (p.member "x") (some (.finite x))
    (Binary64.toBits (Binary64.advance x)).val hx
  have lx : load heap (p.member "x") = some (.finite x) := by
    simp [load, hx, convert, Value.finite]
  have add := CArithmetic.floatAdd_one x
  simp [CArithmetic.run, CArithmetic.next, CBody.next, CBody.eval,
    CBody.lvalue, unitModule, function, stateField, parameters,
    CBody.bind, CBody.resolve, CBody.constants,
    CBody.cast, convert, Value.address, lx, add, sx, written, Value.finite] at *

def Represents (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value) : Prop :=
  heap (p.member "x") = some ⟨.float64, true, some (.finite state.x[0])⟩ ∧
  heap (p.member "samplePeriod") = some ⟨.float64, true, some (.finite state.samplePeriod[0])⟩

def resultHeap (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value) :
    GALEC.Method → Heap
  | .startup => initialized heap p
  | .recalibrate => written heap (p.member "x") state.x[0]
  | .doStep => written heap (p.member "x") (Binary64.advance state.x[0])

def methodFuel : GALEC.Method → Nat
  | .startup => 5 | .recalibrate => 2 | .doStep => 4

theorem method_run (model : Solve.Algorithm.Model source) (module : Module)
    (lowered : lower model = .ok module) (method : GALEC.Method)
    (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (h : Represents heap p state) :
    CArithmetic.run (methodFuel method) (.running (module.method method).body (parameters p) heap) =
      some (.returned ⟨.integer 0, resultHeap heap p state method⟩) := by
  have hm := (lower_is_unit model).symm.trans lowered
  cases Except.ok.inj hm
  cases method
  · exact startup_run heap p _ _ h.1 h.2
  · exact recalibrate_run heap p _ h.1
  · exact doStep_run heap p _ h.1

theorem result_represents (model : Solve.Algorithm.Model source) (method : GALEC.Method)
    (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (h : Represents heap p state) :
    Represents (resultHeap heap p state method) p
      (GALEC.UnitProfile.solveExecute model.block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method state) := by
  rw [model.block_is_unit, GALEC.UnitProfile.lower_correct]
  cases method <;>
    simp [Represents, resultHeap, initialized, written, replace, h.2,
      GALEC.UnitProfile.execute, GALEC.unitBlock, GALEC.Block.execute, GALEC.Block.body,
      GALEC.Expr.eval, GALEC.roundedAdd, Binary64.roundedAdd_one]

theorem result_frame (heap : Heap) (p q : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (method : GALEC.Method) (hx : q ≠ p.member "x") (hp : q ≠ p.member "samplePeriod") :
    resultHeap heap p state method q = heap q := by
  cases method <;> simp [resultHeap, initialized, written, replace, hx, hp]

theorem result_other_instance (heap : Heap) (p q : Address)
    (state : GALEC.UnitProfile.State Binary64.Value) (method : GALEC.Method)
    (h : q.block ≠ p.block) : resultHeap heap p state method q = heap q := by
  apply result_frame
  all_goals intro he; apply h; simpa only [Address.member] using congrArg Address.block he

/-- The generated method has exactly the terminating behavior specified by
Solve, including all state and clock storage and every unrelated heap cell.
This is C-body execution under explicit typed function entry, not a proof of
the host ABI, host scheduling, or subsequent C-to-machine compilation. -/
theorem method_correct (model : Solve.Algorithm.Model source) (module : Module)
    (lowered : lower model = .ok module) (method : GALEC.Method)
    (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (h : Represents heap p state) :
    (∀ behavior, CArithmetic.machine.Behaves
      (.running (module.method method).body (parameters p) heap) behavior ↔
      behavior = .terminates ⟨.integer 0, resultHeap heap p state method⟩) ∧
    Represents (resultHeap heap p state method) p
      (GALEC.UnitProfile.solveExecute model.block Binary64.positiveZero Binary64.one
        GALEC.roundedAdd method state) ∧
    (∀ q, q ≠ p.member "x" → q ≠ p.member "samplePeriod" →
      resultHeap heap p state method q = heap q) :=
  ⟨CArithmetic.behaviors_of_run (method_run model module lowered method heap p state h),
    result_represents model method heap p state h, fun q => result_frame heap p q state method⟩

theorem read_output (heap : Heap) (p : Address) (state : GALEC.UnitProfile.State Binary64.Value)
    (h : Represents heap p state) : load heap (p.member "x") = some (.finite state.x[0]) := by
  simp [load, h.1, convert, Value.finite]

end Rumoca.EFMI.Production
