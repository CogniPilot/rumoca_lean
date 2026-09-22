import RumocaFMI3.TensorDerivativeAdmission
import RumocaFMI3.TensorInstanceJacobian

/-! Finite-success execution of the checked derivative getter. This composes
preflight with the existing prepared RHS/Jacobian and copy proofs; all earlier
library, arithmetic, storage and alias premises and observations are retained. -/
noncomputable section
namespace Rumoca.FMI3.TensorDerivativeSuccess
open CTree CMemory CBody CLoops TensorInstance TensorContinuousStates
open CMemory.TensorView CTensor CTensor.Lowering Solve.Tensor
set_option maxRecDepth 10000
variable [static : StaticLiterals]
private local instance : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

theorem free_reaches (shape oshape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivCheckedFunction shape false)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape oshape time state input output) stack)
        (.returning (.integer 0)
          (written finalHeap buffer result shape.volume) stack) := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  set m := TensorInstance.record pool i with hm'
  obtain ⟨prior, guarded⟩ := TensorDerivativeAdmission.entry program shape false H m buffer count
    kind mode stack matched defined hk hm allowed
  let env := TensorDerivativePreflight.finalEnv (derivGuardEnv m buffer count) m input
  let types := TensorDerivativePreflight.finalTypes prior
  have ready := TensorDerivativeContinuation.after_preflight m buffer count input
  have counterValue : env "k" = some (.integer shape.volume) := rfl
  have counterType : types "k" = some .size := rfl
  have entered := guarded.trans (TensorDerivativeAdmission.finite_pass program shape oshape
    backing pool i time state input result output buffer count prior
    (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: (derivCheckedCopyTail shape)) stack matched bounded executed)
  have argsEq : [Value.pointer (some (m.member stateName)), .pointer (some (m.member inputName)),
      .pointer (some (m.member derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCheckedCopyTail shape)
        env types H) "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H
        (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)) := by
    rw [← argsEq]; exact TensorDerivativeContinuation.rhs_enter program env types H m buffer count.toNat (derivCheckedCopyTail shape) stack ready
  obtain ⟨finalHeap, reads, _writableDeriv, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i oshape time state input result output bounded executed resolves
      (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)
  have resumeStep : CCalls.Events.internalNext program
      (.returning .void finalHeap
        (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)) =
      some (.body (.running (derivCheckedCopyTail shape) env types finalHeap)
        "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith]
  have writableFinal : Writable finalHeap buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frameH (buffer.index b)
      (TensorInstanceRhs.buffer_outside pool i buffer b hb separate)).trans ho⟩
  have deliver := TensorDerivativeContinuation.copy_reaches program shape finalHeap m buffer count.toNat env types result
    (.integer shape.volume) stack ready counterValue counterType bounded
    reads writableFinal separate
  refine ⟨finalHeap, reads, others, entered.trans (.next enterStep (ran.trans (.next resumeStep deliver)))⟩

theorem output_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape)
    (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivCheckedFunction shape true)))
    (hk : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J)) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (separateOutput : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume, ∀ b < shape.volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b)
    (adds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v)
    (jacResolves : ∀ (H' : Heap) v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) H' .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      Reads finalHeap (TensorInstance.field pool i outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
            time state input (some J)) stack)
        (.returning (.integer 0)
          (written finalHeap buffer result shape.volume) stack) := by
  set H := TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
    time state input (some J) with hH
  set m := TensorInstance.record pool i with hm'
  -- guard, count check, then enter the typed body at the two entry calls plus the copy suffix
  obtain ⟨prior, guarded⟩ := TensorDerivativeAdmission.entry program shape true H m buffer count
    kind mode stack matched defined hk hm allowed
  let env := TensorDerivativePreflight.finalEnv (derivGuardEnv m buffer count) m input
  let types := TensorDerivativePreflight.finalTypes prior
  have ready := TensorDerivativeContinuation.after_preflight m buffer count input
  have counterValue : env "k" = some (.integer shape.volume) := rfl
  have counterType : types "k" = some .size := rfl
  have entered := guarded.trans (TensorDerivativeAdmission.finite_pass program shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
    backing pool i time state input result (some J) buffer count prior
    (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: (jacobianCall shape :: derivCheckedCopyTail shape)) stack matched bounded executed)
  have argsEq : [Value.pointer (some (m.member stateName)), .pointer (some (m.member inputName)),
      .pointer (some (m.member derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: jacobianCall shape :: derivCheckedCopyTail shape)
        env types H) "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H
        (.caller .discard (jacobianCall shape :: derivCheckedCopyTail shape) env types
          "fmi3Status" stack)) := by
    rw [← argsEq]
    exact TensorDerivativeContinuation.rhs_enter program env types H m buffer count.toNat (jacobianCall shape :: derivCheckedCopyTail shape) stack ready
  obtain ⟨finalHeap1, reads, _writableDeriv, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input result (some J)
      bounded executed resolves
      (.caller .discard (jacobianCall shape :: derivCheckedCopyTail shape) env types
        "fmi3Status" stack)
  have resumeStep1 : CCalls.Events.internalNext program
      (.returning .void finalHeap1
        (.caller .discard (jacobianCall shape :: derivCheckedCopyTail shape) env types
          "fmi3Status" stack)) =
      some (.body (.running (jacobianCall shape :: derivCheckedCopyTail shape) env types
        finalHeap1) "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith]
  -- the input region is readable and the output region writable on the post-RHS heap
  have readsInputFinal : Reads finalHeap1 (TensorInstance.field pool i inputName) input := by
    intro k
    have hpt := frameH ((TensorInstance.field pool i inputName).index k.val)
      (TensorInstanceRhs.field_outside pool i inputName k.val (by decide +kernel))
    have h := TensorInstance.reads_input backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J) k
    simp only [load] at h ⊢
    rw [hpt]; exact h
  have writableOutputFinal : Writable finalHeap1 (TensorInstance.field pool i outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume := by
    intro b hb
    obtain ⟨old, ho⟩ := TensorInstance.writable_output backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input J b hb
    exact ⟨old, (frameH _ (TensorInstanceRhs.field_outside pool i outputName b (by decide +kernel))).trans ho⟩
  -- the Jacobian entry `rumoca_square_jacobian_diag`
  have argsEqJac : [Value.pointer (some (m.member inputName)), .pointer (some (m.member outputName)),
      .integer count.toNat, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] =
      Diagonal.argumentValues (TensorInstance.field pool i inputName)
        (TensorInstance.field pool i outputName) shape := by
    rw [hm', matched]; rfl
  have jacEnterStep : CCalls.Events.internalNext program
      (.body (.running (jacobianCall shape :: derivCheckedCopyTail shape) env types finalHeap1)
        "fmi3Status" stack) =
      some (.calling "rumoca_square_jacobian_diag"
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) finalHeap1
        (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)) := by
    rw [← argsEqJac]
    exact TensorDerivativeContinuation.jac_enter program shape env types finalHeap1 m buffer count.toNat (derivCheckedCopyTail shape) stack ready
  obtain ⟨jacReads, jacFrame, jacRan⟩ :=
    TensorInstanceJacobian.jacobian_writes_events (shape := shape) definitions program linked library jacFound
      pool i input finalHeap1 bounded2 readsInputFinal writableOutputFinal adds (jacResolves finalHeap1)
      (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)
  set finalHeap2 := Diagonal.resultHeap finalHeap1 (TensorInstance.field pool i outputName)
    (SquareDiagonal.doubled input) with hfh2
  have resumeStep2 : CCalls.Events.internalNext program
      (.returning .void finalHeap2
        (.caller .discard (derivCheckedCopyTail shape) env types "fmi3Status" stack)) =
      some (.body (.running (derivCheckedCopyTail shape) env types finalHeap2)
        "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.Typed.resumeWith]
  -- der(x) survives the Jacobian write, and every other instance is preserved
  have derReadFinal : Reads finalHeap2 (TensorInstance.field pool i derivativeName) result := by
    intro k
    have hpt := jacFrame ((TensorInstance.field pool i derivativeName).index k.val)
      (fun a _ => TensorInstance.fields_separate pool i derivativeName outputName (by decide +kernel) k.val a)
    simp only [load] at reads ⊢
    rw [hpt]; exact reads k
  have others2 : ∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
      finalHeap2 ((TensorInstance.field pool j b).index k) = backing ((TensorInstance.field pool j b).index k) := by
    intro j b k hji
    rw [jacFrame ((TensorInstance.field pool j b).index k)
      (fun a _ => Address.instances_separate pool j i hji b outputName k a)]
    exact others j b k hji
  -- the caller buffer stays writable across both writes, then the copy suffix delivers der(x)
  have writableBufferFinal : Writable finalHeap2 buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    refine ⟨old, ?_⟩
    rw [jacFrame _ (fun a ha => (separateOutput a ha b hb).symm),
      frameH _ (TensorInstanceRhs.buffer_outside pool i buffer b hb separate)]
    exact ho
  have deliver := TensorDerivativeContinuation.copy_reaches program shape finalHeap2 m buffer count.toNat env types result
    (.integer shape.volume) stack ready counterValue counterType bounded
    derReadFinal writableBufferFinal separate
  exact ⟨finalHeap2, derReadFinal, jacReads, others2,
    entered.trans (.next enterStep (ran.trans (.next resumeStep1
      (.next jacEnterStep (jacRan.trans (.next resumeStep2 deliver))))))⟩

end Rumoca.FMI3.TensorDerivativeSuccess

