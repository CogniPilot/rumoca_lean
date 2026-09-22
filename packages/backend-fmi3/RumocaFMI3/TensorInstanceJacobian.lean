import RumocaFMI3.TensorInstanceStorage
import RumocaC.TensorSquareDiagonal
import RumocaC.TensorProgramCalls
import RumocaC.TypedEventsTransfer

/-! The prepared scratch-free square-Jacobian diagonal entry bound to static
instance storage.

The second prepared tensor kernel entry `rumoca_square_jacobian_diag`
(`Rumoca.CTensor.SquareDiagonal.function`) writes the dense Jacobian `diag(2*u)`
from the instance's input region `u` into its output region `J`, with no
intermediate coefficient buffer. It is executed through the same kernel-call path
as `rumoca_rhs`: the loop-call behavior of the certified helper
(`SquareDiagonal.helper_call_correct`) embeds into the observable call machine
under any saved caller through the typed-to-observable transfer
(`CCalls.Events.loop_call_reaches_events`), the identical bridge the derivative
entry uses. The header-type premises the helper needs are supplied by the shared
`Library definitions`, so no `fmi3Float64 *`/`double *` interface obligation is
imposed on the adapter's tree-call machine.

Universal in the tensor shape and the instance index: running the entry on an
instance writes `diag(2*u)` into that instance's `J` region and preserves every
other cell, including every tensor cell of every other instance in the pool. This
is a package-checked product; it emits no production artifact, adds no CLI or
grammar case, and changes no existing contract or the scalar adapter. -/
noncomputable section
namespace Rumoca.FMI3.TensorInstanceJacobian
open CTree CMemory CMemory.TensorView Rumoca.CTensor Rumoca.CTensor.Lowering Rumoca.Tensor
open Rumoca.CTensor.SquareDiagonal (doubled)

variable [interface : CInterface]

/-- The observable-machine execution of the prepared square-Jacobian diagonal
entry on instance `i`. Over any heap in which the instance's input region `u` is
readable and its output region `J` is a writable dense-matrix range, the entry
embeds into the observable call machine under any saved caller, reaching a final
heap in which `J` reads the dense matrix `diag(2*u)` and every cell outside the
`J` region is preserved. The `resolves` premise records that the nested helper
call (`rumoca_tensor_fill`) resolves directly by name, and the `adds` premise is
the explicit no-overflow condition on the doubled input cells. -/
theorem jacobian_writes_events_for {shape : Shape}
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (binaryHeader : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (found : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (pool : Address) (i : Nat) (input : Values shape) (heap : Heap)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableOutput : Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (matrixShape shape.volume shape.volume).volume)
    (adds : ∀ k : Fin shape.volume, Binary64.Adds input[k] input[k] (.finite (doubled input)[k]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) heap .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    Reads (Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input))
        (TensorInstance.field pool i TensorInstance.outputName) (Diagonal.matrix (doubled input)) ∧
      (∀ q, (∀ a < (matrixShape shape.volume shape.volume).volume,
          q ≠ (TensorInstance.field pool i TensorInstance.outputName).index a) →
        Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input) q = heap q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling SquareDiagonal.function.signature.name
          (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
            (TensorInstance.field pool i TensorInstance.outputName) shape) heap stack)
        (.returning .void
          (Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input))
          stack) := by
  have separate : Diagonal.Separate (TensorInstance.field pool i TensorInstance.outputName)
      (TensorInstance.field pool i TensorInstance.inputName) shape :=
    fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.outputName TensorInstance.inputName
      (by decide +kernel) a b
  refine ⟨SquareDiagonal.output_reads heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input),
    fun q outside => SquareDiagonal.output_frame heap (TensorInstance.field pool i TensorInstance.outputName)
      (doubled input) q outside, ?_⟩
  have behaves := (SquareDiagonal.helper_call_correct definitions
      (TensorInstance.field pool i TensorInstance.inputName)
      (TensorInstance.field pool i TensorInstance.outputName) (doubled input) input heap found
      fillDefined binaryHeader fillHeader separate readsInput adds writableOutput bounded
      (.terminates (Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName)
        (doubled input)))).mpr rfl
  exact CCalls.Events.loop_call_reaches_events program definitions linked behaves resolves stack

theorem jacobian_writes_events {shape : Shape}
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (pool : Address) (i : Nat) (input : Values shape) (heap : Heap)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableOutput : Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (matrixShape shape.volume shape.volume).volume)
    (adds : ∀ k : Fin shape.volume, Binary64.Adds input[k] input[k] (.finite (doubled input)[k]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) heap .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    Reads (Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input))
        (TensorInstance.field pool i TensorInstance.outputName) (Diagonal.matrix (doubled input)) ∧
      (∀ q, (∀ a < (matrixShape shape.volume shape.volume).volume,
          q ≠ (TensorInstance.field pool i TensorInstance.outputName).index a) →
        Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input) q = heap q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling SquareDiagonal.function.signature.name
          (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
            (TensorInstance.field pool i TensorInstance.outputName) shape) heap stack)
        (.returning .void
          (Diagonal.resultHeap heap (TensorInstance.field pool i TensorInstance.outputName) (doubled input))
          stack) :=
  jacobian_writes_events_for definitions program linked library.binaryHeader library.fillHeader library.fillDefined found pool i input heap bounded readsInput writableOutput adds resolves stack
end Rumoca.FMI3.TensorInstanceJacobian
