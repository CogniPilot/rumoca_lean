import RumocaFMI3.Runtime
import RumocaFMI3.StepAdmission
import RumocaFMI3.StepAdvance
import RumocaC.Fenv

noncomputable section
namespace Rumoca.FMI3.StepGuards
open CTree CMemory CBody CCalls
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Stop and progress are properties of the rounded clock, including overflow.
They do not change the independently specified unit-grid duration policy. -/
def AboveStop (next : Float64.Number) (stop : Option Binary64.Value) : Prop :=
  match stop, next with
  | some limit, .finite value => Binary64.value limit < Binary64.value value
  | some _, .positiveInfinity => True
  | _, _ => False

def Progress (time : Binary64.Value) : Float64.Number → Prop
  | .finite candidate => Binary64.value time < Binary64.value candidate
  | _ => False

variable [interface : CInterface]

omit interface in
private theorem finite_comparison (relation : Float64.Relation) (a b : Binary64.Value) :
    Float64.test relation (Binary64.toBits a).val (Binary64.toBits b).val =
      decide (relation.Holds (Binary64.value a) (Binary64.value b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Float64.test_finite]

theorem stop_condition (env : Locals) (heap : Heap) (p : Address)
    (next : Float64.Number) (stop : Option Binary64.Value)
    (instanceValue : env "m" = some (.pointer (some p)))
    (nextValue : env "next" = some (.float64 next.encode))
    (enabled : load heap (p.member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) :
    eval env heap (Runtime.both (Runtime.field "stopDefined")
      (Runtime.gt (Runtime.v "next") (Runtime.field "stop"))) =
      some (boolean (decide (AboveStop next stop))) := by
  cases stop with
  | none => simp [Runtime.both, Runtime.field, Runtime.gt, Runtime.v, eval, resolve,
      instanceValue, nextValue, Value.address, enabled, AboveStop]
  | some stop =>
    have stored := limit stop rfl
    cases next with
    | finite next =>
      simp [Runtime.both, Runtime.field, Runtime.gt, Runtime.v, eval, resolve,
        instanceValue, nextValue, Value.address, enabled, stored, AboveStop,
        Float64.Number.encode, Value.finite, comparison, floatComparison,
        finite_comparison, Float64.Relation.Holds]
      rfl
    | negativeInfinity | positiveInfinity | nan =>
      simp [Runtime.both, Runtime.field, Runtime.gt, Runtime.v, eval, resolve,
        instanceValue, nextValue, Value.address, enabled, stored, AboveStop,
        Value.finite, comparison, floatComparison, Float64.test, Float64.compareBits,
        Float64.Number.compare]

theorem progress_condition (env : Locals) (heap : Heap) (p : Address)
    (time : Binary64.Value) (next : Float64.Number)
    (instanceValue : env "m" = some (.pointer (some p)))
    (nextValue : env "next" = some (.float64 next.encode))
    (clock : load heap (p.member "time") = some (.finite time)) :
    eval env heap (Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "next")),
      Runtime.le (Runtime.v "next") (Runtime.field "time")]) =
      some (boolean (decide (¬ Progress time next))) := by
  have negative : (Value.float64 Float64.Number.negativeInfinity.encode).isFinite = some false := by decide +kernel
  have positive : (Value.float64 Float64.Number.positiveInfinity.encode).isFinite = some false := by decide +kernel
  have unordered : (Value.float64 Float64.Number.nan.encode).isFinite = some false := by decide +kernel
  cases next with
  | finite next =>
    have finite : (Value.float64 (Binary64.toBits next).val).isFinite = some true :=
      Value.isFinite_finite next
    by_cases advances : Binary64.value time < Binary64.value next <;>
      simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.finite,
      Runtime.call, Runtime.v, Runtime.n, Runtime.le, Runtime.field, eval, resolve,
      instanceValue, nextValue, Value.address, clock, Float64.Number.encode,
      finite, comparison, floatComparison, Value.finite, boolean, Value.truth,
      finite_comparison, Float64.Relation.Holds, Progress, advances, not_lt.mp, not_le.mpr]
  | negativeInfinity | positiveInfinity | nan =>
    simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.finite,
      Runtime.call, Runtime.v, Runtime.n, Runtime.le, Runtime.field, eval, resolve,
      instanceValue, nextValue, Value.address, clock, negative, positive, unordered, Progress]

theorem grid_condition (env : Locals) (heap : Heap) (step : Binary64.Value)
    (stepValue : env "communicationStepSize" = some (.finite step))
    (floorValue : env "floored" = some (.finite (Binary64.floorValue step)))
    (positive : 0 < Binary64.value step) :
    eval env heap (Runtime.any [Runtime.nev (Runtime.v "floored") (Runtime.v "communicationStepSize"),
      Runtime.gt (Runtime.v "communicationStepSize") (Runtime.n 1000000)]) =
      some (boolean (decide (¬ StepAdmission.AdmittedDuration step))) := by
  by_cases integral : Binary64.value (Binary64.floorValue step) = Binary64.value step <;>
    by_cases bounded : Binary64.value step ≤ 1000000 <;>
    simp [Runtime.any, Runtime.either, Runtime.nev, Runtime.gt, Runtime.v, Runtime.n,
    eval, resolve, stepValue, floorValue, Value.finite, comparison, floatComparison,
    CIntegerConversions.integer_float64 1000000 (by decide +kernel),
    finite_comparison, Float64.Relation.Holds, Binary64.ofSmallInt_value,
    StepAdmission.AdmittedDuration, positive, integral, bounded, boolean, Value.truth,
    not_lt.mpr, lt_of_not_ge]

private theorem branch_path (program : Events.Program E) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (condition : Expr) (yes no rest : List Stmt) (choice : Bool)
    (resultType : String) (stack : Typed.Continuation)
    (yesClosed : yes.all CLoops.noDeclarations = true)
    (noClosed : no.all CLoops.noDeclarations = true)
    (evaluated : CLoops.eval env types heap condition = some (boolean choice)) :
    Transition.Events.Prefix (Events.machine program)
      (.body (.running (.branch condition yes no :: rest) env types heap) resultType stack) []
      (.body (.running ((if choice then yes else no) ++ rest) env types heap) resultType stack) := by
  apply Events.internal_path
  refine .next (Events.body_step program ?_ resultType stack) (.refl _)
  simp [CLoops.next, yesClosed, noClosed, evaluated]

/-- The first guarded library call covers every admitted int32 observation.
A rejected observation reaches the actual failure statement before addition. -/
theorem rounding_path (program : Events.Program E) (header : CFenv.Header)
    (env : Locals) (types : CLoops.Types) (heap : Heap) (observed : Int)
    (range : -(2^31) ≤ observed ∧ observed < 2^31) (rest : List Stmt)
    (resultType : String) (stack : Typed.Continuation)
    (integer : interface.types "int" = some .int32)
    (fresh : env "rounding" = none) (unshadowed : env "fegetround" = none)
    (macroUnshadowed : env "FE_TONEAREST" = none)
    (ordinary : interface.constants "fegetround" = none)
    (macroBound : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (found : program.externals "fegetround" = some (CMathCalls.roundingExternal integer observed range)) :
    Transition.Events.Prefix (Events.machine program)
      (.body (.running (Runtime.stepRounding ++ rest) env types heap) resultType stack) []
      (.body (.running ((if observed = header.nearest then [] else
        [Runtime.fail "Round-to-nearest arithmetic is required"]) ++ rest)
        (bind env "rounding" (.integer observed))
        (CLoops.bindType types "rounding" .int32) heap) resultType stack) := by
  exact CFenv.rounding_branch_path header program env types heap observed range _ rest
    resultType stack (by decide +kernel) integer fresh unshadowed macroUnshadowed ordinary macroBound found

def clockDestination (time : Binary64.Value) (candidate : Float64.Number)
    (stop : Option Binary64.Value) (rest : List Stmt) : List Stmt :=
  if AboveStop candidate stop then
    Runtime.fail "Step exceeds stopTime" :: Runtime.stepClock.drop 2 ++ rest
  else if Progress time candidate then rest else Runtime.stepDiscard ++ rest

/-- Every finite-input sum, including overflow, reaches its specified guard
destination. The heap is untouched and the remainder retains all behavior. -/
theorem clock_path (program : Events.Program E) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (time step : Binary64.Value) (stop : Option Binary64.Value)
    (rest : List Stmt) (resultType : String) (stack : Typed.Continuation)
    (double : interface.types "double" = some .float64)
    (fresh : env "next" = none) (instanceValue : env "m" = some (.pointer (some p)))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (clock : load heap (p.member "time") = some (.finite time))
    (enabled : load heap (p.member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value → load heap (p.member "stop") = some (.finite value)) :
    Transition.Events.Prefix (Events.machine program)
      (.body (.running (Runtime.stepClock ++ rest) env types heap) resultType stack) []
      (.body (.running (clockDestination time (Binary64.addResult time step) stop rest)
        (bind env "next" (.float64 (Binary64.addResult time step).encode))
        (CLoops.bindType types "next" .float64) heap) resultType stack) := by
  let candidate := Binary64.addResult time step
  let later := bind env "next" (.float64 candidate.encode)
  let laterTypes := CLoops.bindType types "next" .float64
  have sum := CArithmetic.eval_member_add env types heap (Runtime.v "m")
    (Runtime.v "communicationStepSize") "time" true time step
    (by simp [Runtime.v, eval, resolve, instanceValue, Value.address, clock])
    (by simp [Runtime.v, eval, resolve, stepValue])
  simp only [Runtime.v] at sum
  have declared : Events.internalNext program
      (.body (.running (Runtime.stepClock ++ rest) env types heap) resultType stack) =
      some (.body (.running (Runtime.stepClock.drop 1 ++ rest) later laterTypes heap) resultType stack) := by
    apply Events.body_step
    simp [Runtime.stepClock, Runtime.field, Runtime.v, CLoops.next, double,
      sum, convert, fresh, later, laterTypes, candidate]
  have entered := Events.internal_path program (.next declared (.refl _))
  have stopGuard := stop_condition later heap p candidate stop
    (by simpa [later, CBody.bind] using instanceValue) (by simp [later, CBody.bind]) enabled limit
  have stopPath := branch_path program later laterTypes heap
    (Runtime.both (Runtime.field "stopDefined") (Runtime.gt (Runtime.v "next") (Runtime.field "stop")))
    [Runtime.fail "Step exceeds stopTime"] [] (Runtime.stepClock.drop 2 ++ rest)
    (decide (AboveStop candidate stop)) resultType stack (by decide +kernel) rfl stopGuard
  have throughStop := entered.trans stopPath
  by_cases exceeds : AboveStop candidate stop
  · simpa [clockDestination, exceeds, Runtime.stepClock, Runtime.reject, Runtime.branch,
      List.append_assoc, later, laterTypes, candidate] using throughStop
  · have progressGuard := progress_condition later heap p time candidate
      (by simpa [later, CBody.bind] using instanceValue) (by simp [later, CBody.bind]) clock
    have progressPath := branch_path program later laterTypes heap
      (Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "next")),
        Runtime.le (Runtime.v "next") (Runtime.field "time")]) Runtime.stepDiscard [] rest
      (decide (¬ Progress time candidate)) resultType stack (by decide +kernel) rfl progressGuard
    have afterStop : Transition.Events.Prefix (Events.machine program)
        (.body (.running (Runtime.stepClock ++ rest) env types heap) resultType stack) []
        (.body (.running (Runtime.stepClock.drop 2 ++ rest) later laterTypes heap) resultType stack) := by
      simpa [exceeds, Runtime.stepClock, Runtime.reject, Runtime.branch, List.append_assoc] using throughStop
    have all := afterStop.trans progressPath
    by_cases progress : Progress time candidate <;>
      simpa [clockDestination, exceeds, progress, Runtime.stepClock, Runtime.branch,
        List.append_assoc, later, laterTypes, candidate] using all

/-- Floor is called only on a finite duration. Its mathematical result decides
admission; the solver count is derived by StepAdmission.duration_count. -/
theorem grid_path (program : Events.Program E) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (step : Binary64.Value) (rest : List Stmt)
    (resultType : String) (stack : Typed.Continuation)
    (double : interface.types "double" = some .float64)
    (fresh : env "floored" = none) (unshadowed : env "floor" = none)
    (ordinary : interface.constants "floor" = none)
    (stepValue : env "communicationStepSize" = some (.finite step))
    (positive : 0 < Binary64.value step)
    (found : program.externals "floor" = some (CMathCalls.floorExternal double)) :
    Transition.Events.Prefix (Events.machine program)
      (.body (.running (Runtime.stepGrid ++ rest) env types heap) resultType stack) []
      (.body (.running ((if StepAdmission.AdmittedDuration step then [] else Runtime.stepDiscard) ++ rest)
        (bind env "floored" (.finite (Binary64.floorValue step)))
        (CLoops.bindType types "floored" .float64) heap) resultType stack) := by
  let later := bind env "floored" (.finite (Binary64.floorValue step))
  let laterTypes := CLoops.bindType types "floored" .float64
  have entered := CMathCalls.floor_declaration_path program env types heap "floored"
    (Runtime.v "communicationStepSize") step (Runtime.stepGrid.drop 1 ++ rest)
    resultType stack double fresh unshadowed ordinary
    (by simp [Runtime.v, eval, resolve, stepValue]) found
  have condition := grid_condition later heap step
    (by simpa [later, CBody.bind] using stepValue) (by simp [later, CBody.bind]) positive
  have checked := branch_path program later laterTypes heap
    (Runtime.any [Runtime.nev (Runtime.v "floored") (Runtime.v "communicationStepSize"),
      Runtime.gt (Runtime.v "communicationStepSize") (Runtime.n 1000000)])
    Runtime.stepDiscard [] rest (decide (¬ StepAdmission.AdmittedDuration step))
    resultType stack (by decide +kernel) rfl condition
  have all := entered.trans checked
  by_cases admitted : StepAdmission.AdmittedDuration step <;>
    simpa [Runtime.stepGrid, Runtime.branch, Runtime.call, Runtime.v, List.append_assoc,
      admitted, later, laterTypes] using all

omit interface in
theorem actual_sections : Runtime.doStep.drop 9 =
    Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ StepAdvance.code := rfl

/-- The complete numerical suffix executes its actual guarded calls and
solver, deriving the count from duration admission. Public output setup,
lifecycle/input admission and rejected-call continuations are separate. -/
theorem accepted_execution (program : Events.Program E) (model : Solve.Model source)
    (header : CFenv.Header) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p output : Address) (x time step : Binary64.Value)
    (stop : Option Binary64.Value) (oldTime oldOutput : Option Value)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (status : interface.types "fmi3Status" = some .int32)
    (helperTypes : ModelAdvance.Types)
    (locals : ∀ name ∈ ["rounding", "next", "floored", "fegetround", "floor", "FE_TONEAREST",
      "model_advance", "fmi3OK"], env name = none)
    (ordinary : ∀ name ∈ ["fegetround", "floor", "model_advance"], interface.constants name = none)
    (macroBound : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (okBound : interface.constants "fmi3OK" = some (.integer 0))
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal integer
      header.nearest ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal double))
    (instanceValue : env "m" = some (.pointer (some p)))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (outputValue : env "lastSuccessfulTime" = some (.pointer (some output)))
    (clock : load heap (p.member "time") = some (.finite time))
    (enabled : load heap (p.member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value → load heap (p.member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value time < Binary64.value (Binary64.roundedAdd time step))
    (withinStop : ∀ value, stop = some value → Binary64.value (Binary64.roundedAdd time step) ≤ Binary64.value value)
    (kernel : program.internal.kernel = CExecution.program model)
    (helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]))
    (sample : program.internal.definitions "rumoca_sample" = some (.kernel .sample))
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩)
    (writableClock : heap (p.member "time") = some ⟨.float64, true, oldTime⟩)
    (buffer : heap output = some ⟨.float64, true, oldOutput⟩)
    (outside : output.block ≠ p.block) :
    ∃ count : CStatements.Counter, 0 < count.val ∧ count.val ≤ 1000000 ∧
      Binary64.value step = (count.val : ℝ) ∧
      ∀ behavior, (Events.machine program).Behaves
        (.body (.running (Runtime.doStep.drop 9) env types heap) "fmi3Status" .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          StepAdvance.written heap p output (model.run x count.val) (Binary64.roundedAdd time step)⟩ := by
  obtain ⟨count, countPositive, countBound, duration, _⟩ := StepAdmission.duration_count step admitted
  refine ⟨count, countPositive, countBound, duration, ?_⟩
  let rounded := Binary64.roundedAdd time step
  let roundingEnv := CBody.bind env "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType types "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.finite rounded)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) := locals name member
  have first := rounding_path program header env types heap header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ StepAdvance.code) "fmi3Status" .done
    integer (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp))
    (ordinary _ (by simp)) macroBound rounding
  simp only at first
  have second := clock_path program roundingEnv roundingTypes heap p time step stop
    (Runtime.stepGrid ++ StepAdvance.code) "fmi3Status" .done double
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepValue) clock enabled limit
  have noStop : ¬ AboveStop (.finite rounded) stop := by
    cases stop with
    | none => simp [AboveStop]
    | some stop => exact not_lt.mpr (withinStop stop rfl)
  have second' : Transition.Events.Prefix (Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ StepAdvance.code)
        roundingEnv roundingTypes heap) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ StepAdvance.code) clockEnv clockTypes heap) "fmi3Status" .done) := by
    simpa [StepAdmission.duration_sum time step admitted, clockDestination, noStop,
      Progress, progress, rounded, clockEnv, clockTypes, Value.finite] using second
  have third := grid_path program clockEnv clockTypes heap step StepAdvance.code "fmi3Status" .done
    double (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp))
    (ordinary _ (by simp)) (by simpa [clockEnv, roundingEnv, CBody.bind] using stepValue)
    admitted.1 floorBound
  have third' : Transition.Events.Prefix (Events.machine program)
      (.body (.running (Runtime.stepGrid ++ StepAdvance.code) clockEnv clockTypes heap) "fmi3Status" .done) []
      (.body (.running StepAdvance.code gridEnv gridTypes heap) "fmi3Status" .done) := by
    simpa [admitted, gridEnv, gridTypes] using third
  have last := StepAdvance.reaches program model gridEnv gridTypes heap p output x step rounded count
    oldTime oldOutput .done helperTypes status (ordinary _ (by simp))
    (by simpa [gridEnv, clockEnv, roundingEnv, CBody.bind] using fresh "model_advance" (by simp))
    (by simpa [gridEnv, clockEnv, roundingEnv, CBody.bind] using instanceValue)
    (by simpa [gridEnv, clockEnv, roundingEnv, CBody.bind] using stepValue)
    (by simp [gridEnv, clockEnv, CBody.bind])
    (by simpa [gridEnv, clockEnv, roundingEnv, CBody.bind] using outputValue)
    (by simp [resolve, constants, gridEnv, clockEnv, roundingEnv, CBody.bind,
      fresh "fmi3OK" (by simp), okBound])
    duration kernel helper sample stored writableClock buffer outside
  have guarded := first.trans (second'.trans third')
  have completed := guarded.forced (Events.internal_prefix program last
    (Events.return_forced program _ _))
  intro behavior
  simpa [actual_sections, List.append_assoc, roundingEnv, roundingTypes] using
    completed.behaviors behavior

end Rumoca.FMI3.StepGuards
end
