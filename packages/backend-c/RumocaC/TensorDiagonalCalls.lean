import RumocaC.TensorDiagonalProofs
import RumocaC.TensorCalls

/-! Complete ordinary calls: bind the signature, execute the existing fill
helper and diagonal copy loop, and restore the caller's scope on return. -/
noncomputable section
namespace Rumoca.CTensor.Diagonal
open CTree CMemory CMemory.TensorView Rumoca.Tensor
variable [interface : CInterface]

def argumentValues (input output : Address) (shape : Shape) : List Value :=
  [.pointer (some input), .pointer (some output), .integer shape.volume,
    .integer (matrixShape shape.volume shape.volume).volume]

theorem bind_parameters (input output : Address) (shape : Shape)
    (header : CTensor.HeaderTypes interface)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (argumentValues input output shape) =
      some (parameters input output shape) :=
  Lowering.Arguments.bind_parameters signatureParameters (arguments input output shape) header
    (by decide +kernel) (bind_valid input output shape bounded)

theorem bind_types (header : CTensor.HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some parameterTypes :=
  Lowering.Arguments.bind_types signatureParameters header (by decide +kernel)

theorem function_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : Fill.HeaderTypes interface)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running function.body (parameters input output shape) parameterTypes heap) stack)
      (.body (.returned ⟨.void, resultHeap heap output values⟩) stack) := by
  have filled := Fill.invoke_reaches definitions (matrixShape shape.volume shape.volume)
    Binary64.positiveZero output heap (CAlgorithm.literal .zero) (.id "out") (.id "cells")
    (parameters input output shape) parameterTypes tail stack fillDefined header
    (by simp [parameters, Lowering.Arguments.locals, signatureParameters, CBody.bind, Fill.function])
    (Fill.literal_eval .zero _ _ header.scalar)
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind])
    (by simp [CBody.eval, CBody.evalWith, CBody.resolve, parameters, Lowering.Arguments.locals, signatureParameters,
      arguments, CBody.bind]) writable bounded
  exact filled.trans (CLoops.Calls.body_reaches definitions
    (tail_reaches input output values heap separate reads bounded header.size
      (fun i hi => offset_eval input output shape _ bounded i hi)) stack)

theorem helper_call_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (argumentValues input output shape) heap stack)
      (.returning (resultHeap heap output values) stack) := by
  have entered : (CLoops.Calls.machine definitions).step
      (.calling function.signature.name (argumentValues input output shape) heap stack)
      (.body (.running function.body (parameters input output shape) parameterTypes heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith, found,
      show function.signature.result = "void" from rfl, ne_eq, not_true_eq_false, ↓reduceIte,
      bind_parameters input output shape header bounded, bind_types header, bind, Option.bind_some, pure]
  exact .next entered ((function_reaches definitions input output values heap stack fillDefined fillHeader
    separate reads writable bounded).trans (.next
      (by simp [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith]) (.refl _)))

theorem helper_call_correct (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (separate : Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling function.signature.name (argumentValues input output shape) heap .done) behavior ↔
      behavior = .terminates (resultHeap heap output values) := by
  have ran := helper_call_reaches definitions input output values heap .done found fillDefined header fillHeader
    separate reads writable bounded
  exact (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next rfl (.refl _))) rfl

theorem invoke_reaches (definitions : CLoops.Calls.Definitions)
    (input output : Address) (values : Values shape) (heap : Heap)
    (argInput argOutput argCount argCells : Expr) (env : CBody.Locals) (types : CLoops.Types)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation)
    (found : definitions function.signature.name = some function)
    (fillDefined : definitions Fill.function.signature.name = some Fill.function)
    (header : CTensor.HeaderTypes interface) (fillHeader : Fill.HeaderTypes interface)
    (unshadowed : env function.signature.name = none)
    (hc : CBody.eval env heap argInput = some (.pointer (some input)))
    (ho : CBody.eval env heap argOutput = some (.pointer (some output)))
    (hn : CBody.eval env heap argCount = some (.integer shape.volume))
    (ha : CBody.eval env heap argCells = some (.integer (matrixShape shape.volume shape.volume).volume))
    (separate : Separate output input shape) (reads : Reads heap input values)
    (writable : Writable heap output (matrixShape shape.volume shape.volume).volume)
    (bounded : (matrixShape shape.volume shape.volume).volume < 2 ^ 64) :
    Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running (invoke argInput argOutput argCount argCells :: rest) env types heap) stack)
      (.body (.running rest env types (resultHeap heap output values)) stack) := by
  have started : CLoops.Calls.next definitions
      (.body (.running (invoke argInput argOutput argCount argCells :: rest) env types heap) stack) =
      some (.calling function.signature.name (argumentValues input output shape) heap
        (.caller rest env types stack)) := by
    simp only [function] at unshadowed
    simp [invoke, function, CLoops.Calls.next, CLoops.Calls.nextWith, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith,
      CLoops.Calls.enterCallWith, CCalls.argumentsWith, CBody.legacyExpressions, hc, ho, hn, ha, argumentValues, unshadowed]
  exact .next started ((helper_call_reaches definitions input output values heap _ found fillDefined
    header fillHeader separate reads writable bounded).trans (.next rfl (.refl _)))

end Rumoca.CTensor.Diagonal
