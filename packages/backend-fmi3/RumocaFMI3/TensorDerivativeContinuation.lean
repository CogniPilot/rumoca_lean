import RumocaFMI3.TensorDerivativeCode
import RumocaFMI3.TensorDerivativePreflight

/-! The existing derivative/Jacobian/copy continuation under extra preflight
locals. Only the bindings the continuation actually uses are required; the
public success contract gains no library or buffer-separation premise. -/
noncomputable section
namespace Rumoca.FMI3.TensorDerivativeContinuation
open CTree CMemory CBody CLoops TensorInstance TensorContinuousStates CTensor
open CMemory.TensorView TensorFloat64
set_option maxRecDepth 10000

structure Ready (env : Locals) (p buffer : Address) (count : Nat) : Prop where
  instanceValue : env "m" = some (.pointer (some p))
  bufferValue : env "derivatives" = some (.pointer (some buffer))
  countValue : env "nContinuousStates" = some (.integer count)
  fresh : ∀ name ∈ ["src", "values", "expected", "fmi3OK", "rumoca_rhs", "rumoca_square_jacobian_diag"],
    env name = none

variable [static : StaticLiterals]
private local instance : CInterface := cInterface static.addresses

omit static in
theorem after_preflight (p buffer : Address) (count : UInt64) (input : Values shape) :
    Ready (TensorDerivativePreflight.finalEnv (derivGuardEnv p buffer count) p input)
      p buffer count.toNat := by
  have frame (name : String) (outside : name ∉ ["left", "right", "count", "sample", "valid", "k"]) :=
    ProductPreflight.Inline.final_frame (derivGuardEnv p buffer count)
      (some (p.member inputName)) (some (p.member inputName)) input input name outside
  unfold TensorDerivativePreflight.finalEnv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frame "m" (by simp)]; simp [derivGuardEnv, CBody.bind]
  · rw [frame "derivatives" (by simp)]; simp [derivGuardEnv, derivParameters, CBody.bind]
  · rw [frame "nContinuousStates" (by simp)]; simp [derivGuardEnv, derivParameters, CBody.bind]
  · intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [frame _ (by simp)]; simp [derivGuardEnv, derivParameters, CBody.bind]

theorem rhs_enter (program : CCalls.Events.Program E) (env : Locals) (prior : Types)
    (heap : Heap) (p buffer : Address) (count : Nat) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (ready : Ready env p buffer count) :
    CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: rest) env prior heap)
        "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (p.member stateName)), .pointer (some (p.member inputName)),
         .pointer (some (p.member derivativeName)), .integer count] heap
        (.caller .discard rest env prior "fmi3Status" stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
    CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, derivEntryArgs,
    Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith,
    CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, CBody.lvalueWith,
    CCalls.Events.enterCallWith, CCalls.Events.resolveWith, CCalls.Indirect.operand,
    CCalls.Indirect.resolveWith, CCalls.argumentsWith, CBody.resolve, CBody.constants,
    Value.address, ready.instanceValue, ready.countValue, ready.fresh "rumoca_rhs" (by simp)]

theorem jac_enter (program : CCalls.Events.Program E) (shape : Tensor.Shape)
    (env : Locals) (prior : Types) (heap : Heap) (p buffer : Address) (count : Nat) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (ready : Ready env p buffer count) :
    CCalls.Events.internalNext program
      (.body (.running (jacobianCall shape :: rest) env prior heap) "fmi3Status" stack) =
      some (.calling "rumoca_square_jacobian_diag"
        [.pointer (some (p.member inputName)), .pointer (some (p.member outputName)),
         .integer count, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] heap
        (.caller .discard rest env prior "fmi3Status" stack)) := by
  simp [jacobianCall, CCalls.Events.internalNext, CCalls.Events.internalNextWith,
    CCalls.Typed.nextWithExpressions, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions,
    jacobianEntryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n,
    CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
    CDeclaredMembers.fieldAt, CBody.lvalueWith, CCalls.Events.enterCallWith, CCalls.Events.resolveWith,
    CCalls.Indirect.operand, CCalls.Indirect.resolveWith, CCalls.argumentsWith, CBody.resolve,
    CBody.constants, Value.address, ready.instanceValue, ready.countValue,
    ready.fresh "rumoca_square_jacobian_diag" (by simp)]

theorem copy_reaches (program : CCalls.Events.Program E) (shape : Tensor.Shape)
    (heap : Heap) (p buffer : Address) (count : Nat) (env0 : Locals) (prior : Types)
    (result : Values shape) (oldCounter : Value) (stack : CCalls.Typed.Continuation)
    (ready : Ready env0 p buffer count) (counterValue : env0 "k" = some oldCounter)
    (counterType : prior "k" = some .size) (bounded : shape.volume < 2 ^ 64)
    (readable : Reads heap (p.member derivativeName) result)
    (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member derivativeName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCheckedCopyTail shape) env0 prior heap) "fmi3Status" stack)
      (.returning (.integer 0) (written heap buffer result shape.volume) stack) := by
  let copyLoop := [CLoops.loop "k" (Runtime.v "expected") getCopyBody, Runtime.ok]
  let afterSrc := bind env0 "src" (.pointer (some (p.member derivativeName)))
  let afterValues := bind afterSrc "values" (.pointer (some buffer))
  let env := bind afterValues "expected" (.integer shape.volume)
  let types := bindType (bindType (bindType prior "src" .pointer) "values" .pointer) "expected" .size
  have s_src := TensorFloat64.declare_step_e env0 prior heap "fmi3Float64 *" "src"
    (Runtime.region derivativeName) .pointer (.pointer (some (p.member derivativeName)))
    (.pointer (some (p.member derivativeName)))
    (.declare "fmi3Float64 *" "values" (Runtime.v "derivatives") ::
      .declare "size_t" "expected" (Runtime.n shape.volume) :: .assign (.id "k") (.nat 0) :: copyLoop)
    (ready.fresh "src" (by simp)) rfl
    (by apply CBodyEmbedding.eval_refines
        simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith,
          CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt,
          CBody.lvalueWith, CBody.resolve, Value.address, ready.instanceValue]) rfl
  have s_values := TensorFloat64.declare_step_e afterSrc (bindType prior "src" .pointer) heap
    "fmi3Float64 *" "values" (Runtime.v "derivatives") .pointer
    (.pointer (some buffer)) (.pointer (some buffer))
    (.declare "size_t" "expected" (Runtime.n shape.volume) :: .assign (.id "k") (.nat 0) :: copyLoop)
    (by simp [afterSrc, CBody.bind, ready.fresh "values" (by simp)]) rfl
    (by simp [Runtime.v, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval,
      CBody.evalWith, afterSrc, CBody.bind, CBody.resolve, ready.bufferValue]) rfl
  have s_count := TensorFloat64.declare_step_e afterValues
    (bindType (bindType prior "src" .pointer) "values" .pointer) heap
    "size_t" "expected" (Runtime.n shape.volume) .size (.integer shape.volume) (.integer shape.volume)
    (.assign (.id "k") (.nat 0) :: copyLoop)
    (by simp [afterValues, afterSrc, CBody.bind, ready.fresh "expected" (by simp)]) rfl
    (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
    (CLoops.convert_size_nat _ bounded)
  have reset := CLoops.assign_local env types heap "k" (.nat 0) copyLoop oldCounter (.integer 0)
    (.integer 0) .size (by simp [env, afterValues, afterSrc, CBody.bind, counterValue])
    (by simp [types, bindType, counterType]) rfl (by decide)
  refine .next (CCalls.Events.body_step program s_src _ stack)
    (.next (CCalls.Events.body_step program s_values _ stack)
    (.next (CCalls.Events.body_step program s_count _ stack)
    (.next (CCalls.Events.body_step program reset _ stack) ?_)))
  refine (getCopy_reaches program env types heap (p.member derivativeName) buffer result [Runtime.ok]
    _ stack bounded (by simp [types, bindType, counterType])
    (by simp [env, CBody.bind, CBody.resolve])
    (by simp [env, afterValues, afterSrc, CBody.bind, CBody.resolve])
    (by simp [env, afterValues, CBody.bind, CBody.resolve]) readable writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume) types stack
    (by simp [counterEnv, env, afterValues, afterSrc, CBody.bind, ready.fresh "fmi3OK" (by simp)])

end Rumoca.FMI3.TensorDerivativeContinuation
