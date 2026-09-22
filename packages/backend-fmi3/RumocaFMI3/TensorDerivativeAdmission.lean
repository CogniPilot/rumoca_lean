import RumocaFMI3.TensorDerivativeContinuation
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.Discard

/-! Public getter admission through handle/lifecycle/count checks followed by
the shared numerical preflight. Both outcomes keep the same instance and caller
storage until successful RHS execution or a permitted logging callback. -/
noncomputable section
namespace Rumoca.FMI3.TensorDerivativeAdmission
open CTree CMemory CBody CLoops TensorInstance TensorContinuousStates
open CMemory.TensorView CTensor CTensor.Lowering Solve.Tensor
open TensorFloat64 (getCopyBody)
set_option maxRecDepth 10000

variable [static : StaticLiterals]
private local instance : CInterface := cInterface static.addresses

omit static in
theorem body_closed (shape : Tensor.Shape) (hasOutput : Bool) :
    (derivCheckedFunction shape hasOutput).body.all CBodyEmbedding.closedBlocks = true := by
  cases hasOutput <;>
    simp [derivCheckedFunction, derivCheckedBody, derivCheckedTail, jacobianCall, jacobianEntryArgs,
      derivCheckedCopyTail, derivCountReject, derivEntryArgs, getCopyBody, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail,
      Runtime.ret, Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.region, Runtime.call,
      CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep,
      TensorDerivativePreflight.body, TensorDerivativePreflight.code, TensorDerivativePreflight.reject,
      ProductPreflight.Inline.code, ProductPreflight.Inline.setup, FinitePreflight.segmentWith,
      FinitePreflight.iteration, FiniteScan.iterationFor, CLoops.counted, Discard.body, Runtime.log]

theorem parameters_bound (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters DerivativeCalls.signature.parameters (DerivativeCalls.values handle buffer count) =
      some (derivParameters handle buffer count) := by
  have cc : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [DerivativeCalls.signature, DerivativeCalls.values, CCalls.parameters, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, cc]
  rfl

theorem count_pass (heap : Heap) (p buffer : Address) (count : UInt64) (volume : Nat)
    (matched : count.toNat = volume) :
    eval (derivGuardEnv p buffer count) heap
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
        Runtime.negate (Runtime.v "derivatives")]) = some (.integer 0) := by
  simp [Runtime.any, Runtime.either, Runtime.nev, Runtime.negate, Runtime.v, Runtime.n,
    CBody.eval, CBody.evalWith, CBody.resolve, derivGuardEnv, derivParameters, CBody.bind,
    matched, CBody.comparison, Value.truth, boolean]

theorem entry (program : CCalls.Events.Program E) (shape : Tensor.Shape) (hasOutput : Bool)
    (heap : Heap) (p buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (stack : CCalls.Typed.Continuation) (matched : count.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivCheckedFunction shape hasOutput)))
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode) :
    ∃ prior, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetContinuousStateDerivatives"
        (DerivativeCalls.values (some p) (some buffer) count) heap stack)
      (.body (.running (TensorDerivativePreflight.body ++
          (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCheckedTail shape hasOutput))
        (derivGuardEnv p buffer count) prior heap) "fmi3Status" stack) := by
  let rest := TensorDerivativePreflight.body ++
    (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCheckedTail shape hasOutput)
  have accepted := LifecycleGuard.accept (derivParameters (some p) (some buffer) count) heap p
    .getDerivatives kind mode (derivCountReject shape.volume :: rest)
    (by simp [derivParameters, CBody.bind]) (by simp [derivParameters, CBody.bind])
    kindValue modeValue allowed
  have ran : CBody.run 4 (.running (derivCheckedBody shape hasOutput)
      (derivParameters (some p) (some buffer) count) heap) =
      some (.running rest (derivGuardEnv p buffer count) heap) := by
    rw [derivCheckedBody]
    rw [show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (derivGuardEnv p buffer count) heap
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n shape.volume),
        Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"
      rest (count_pass heap p buffer count shape.volume matched))
  exact CCalls.Events.body_prefix_reaches program (derivCheckedFunction shape hasOutput)
    (DerivativeCalls.values (some p) (some buffer) count) (derivParameters (some p) (some buffer) count)
    (derivGuardEnv p buffer count) heap heap rest stack 4 defined
    (parameters_bound _ _ _) (body_closed shape hasOutput) ran

theorem finite_pass (program : CCalls.Events.Program E) (shape oshape : Tensor.Shape)
    (backing : Heap) (pool : Address) (i : Nat) (time : Values Tensor.scalar)
    (state input result : Values shape) (output : Option (Values oshape)) (buffer : Address)
    (count : UInt64) (prior : Types) (rest : List Stmt) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result) :
    let heap := TensorInstance.store backing pool i shape oshape time state input output
    let p := TensorInstance.record pool i
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (TensorDerivativePreflight.body ++ rest) (derivGuardEnv p buffer count) prior heap)
        "fmi3Status" stack)
      (.body (.running rest (TensorDerivativePreflight.finalEnv (derivGuardEnv p buffer count) p input)
        (TensorDerivativePreflight.finalTypes prior) heap) "fmi3Status" stack) := by
  dsimp only
  apply CCalls.Events.body_reaches program (TensorDerivativePreflight.pass _ _ _ _ input rest
    (by simp [derivGuardEnv, CBody.bind])
    (by simp [derivGuardEnv, derivParameters, CBody.bind, matched])
    (by intro name member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [derivGuardEnv, derivParameters, CBody.bind])
    (TensorInstance.reads_input backing pool i shape oshape time state input output) bounded
    ((ProductPreflight.square_finite_execution state input).2 ⟨result, executed⟩))

end Rumoca.FMI3.TensorDerivativeAdmission
