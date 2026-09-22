import RumocaC.TensorMultiplicationEntry
import RumocaC.AddressedIVP
import RumocaCore.Array.Numerical

/-! Total encoded outcomes of the prepared square RHS, through its actual
lowered wrapper and nested multiplication call. This extends, rather than
replaces, finite RHS execution. Interface error handling is not asserted. -/
noncomputable section
namespace Rumoca.CTensor.SquareRhsTotal
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering ProgramFixture AddressedIVP

def finalHeap (heap : Heap) (output : Address) (input : Values shape) : Heap :=
  EncodedTensor.written heap output (MultiplicationTotal.result input input) shape.volume

theorem reads (heap : Heap) (output : Address) (input : Values shape) :
    EncodedTensor.ReadsBits (finalHeap heap output input) output
      (Numerical.encode (Numerical.multiply input input)) := by
  rw [← MultiplicationTotal.result_core]
  exact EncodedTensor.written_reads heap output _

theorem frame (heap : Heap) (output : Address) (input : Values shape)
    (q : Address) (outside : ∀ i < shape.volume, q ≠ output.index i) :
    finalHeap heap output input q = heap q :=
  EncodedTensor.written_frame heap output _ shape.volume q outside

theorem writable (heap : Heap) (output : Address) (input : Values shape) :
    Writable (finalHeap heap output input) output shape.volume := by
  intro i hi
  refine ⟨some (.float64 (MultiplicationTotal.result input input)[i]), ?_⟩
  simpa only [finalHeap, EncodedTensor.written, if_pos hi] using
    ArrayStore.written_at heap output .float64
      (fun j => .float64 (MultiplicationTotal.result input input)[j]) shape.volume (Nat.le_refl _) ⟨i, hi⟩

theorem finite_heap (heap : Heap) (output : Address) (state input result : Values shape)
    (executed : Finite.Executes (IVPEntry.kernel shape).derivative
      (ArrayProfile.environment state input) result) :
    finalHeap heap output input = TensorView.written heap output result shape.volume := by
  have multiplies := (ArrayProfile.square_finite_correct state input result).1 executed
  rw [finalHeap, MultiplicationTotal.result_finite input input result multiplies,
    EncodedTensor.written_finite]

theorem finite_execution (heap : Heap) (output : Address) (state input : Values shape) :
    EncodedTensor.AllFinite (finalHeap heap output input) output shape ↔
      ∃ result, Finite.Executes (IVPEntry.kernel shape).derivative
        (ArrayProfile.environment state input) result := by
  rw [EncodedTensor.allFinite_iff _ _ _ (reads heap output input)]
  exact ArrayProfile.square_detection_finite_execution state input

theorem detects_overflow (input : Values shape) :
    Numerical.allFiniteBits (Numerical.encode (Numerical.multiply input input)) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.overflowValue ≤ Binary64.value input[i] * Binary64.value input[i] :=
  ArrayProfile.square_detection_overflow input

variable [interface : CInterface]

theorem call_reaches (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree)
    (heap : Heap) (addresses : String → Address) (state input : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (addresses "x") state) (readsInput : Reads heap (addresses "u") input)
    (writable : Writable heap (addresses "dx") shape.volume)
    (separate : ∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j)
    (stack : CLoops.Calls.Continuation) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (IVPEntry.plan shape).derivative.function.name
        (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape)) heap stack)
      (.returning (finalHeap heap (addresses "dx") input) stack) := by
  obtain ⟨bound, represented, ready⟩ :=
    derivative_setup heap addresses state input bounded readsState readsInput writable separate
  exact MultiplicationTotal.entry_reaches (.there .here) (.there .here)
    (IVPEntry.namedBuffer shape "dx").erase
    (Named.Layout.erase (IVPEntry.plan shape).derivative.layout)
    (IVPEntry.plan shape).derivative.function (IVPEntry.plan_valid shape).2.1
    (Named.function_matches _ _ _ _ _) definitions header helper found (args addresses shape)
    (derivative_arguments addresses shape bounded) (locations addresses)
    (ArrayProfile.environment state input) heap bound represented ready stack

theorem call_correct (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree)
    (heap : Heap) (addresses : String → Address) (state input : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (addresses "x") state) (readsInput : Reads heap (addresses "u") input)
    (writable : Writable heap (addresses "dx") shape.volume)
    (separate : ∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling (IVPEntry.plan shape).derivative.function.name
        (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape)) heap .done)
      behavior ↔ behavior = .terminates (finalHeap heap (addresses "dx") input) := by
  have ran := call_reaches definitions header helper found heap addresses state input bounded
    readsState readsInput writable separate .done
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

theorem call_context (definitions : CLoops.Calls.Definitions) (header : HeaderTypes interface)
    (helper : definitions (function .mul).signature.name = some (function .mul))
    (found : definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree)
    (heap : Heap) (addresses : String → Address) (state input : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (addresses "x") state) (readsInput : Reads heap (addresses "u") input)
    (writable : Writable heap (addresses "dx") shape.volume)
    (separate : ∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j)
    (declarations : CDeclaredMembers.Declarations) (objects : CDeclaredMembers.Objects)
    (p : CCalls.Program) (linked : CCalls.Typed.Extends definitions p)
    (free : CContextMachine.FieldFree.DefinitionsFree definitions) :
    CContextMachine.CallResult (CContextMachine.declared declarations objects) p
      (IVPEntry.plan shape).derivative.function.name
      (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape))
      heap (finalHeap heap (addresses "dx") input) := by
  apply CContextMachine.loop_call_result_context declarations objects p definitions linked free
  exact (call_correct definitions header helper found heap addresses state input bounded
    readsState readsInput writable separate _).2 rfl

end Rumoca.CTensor.SquareRhsTotal
