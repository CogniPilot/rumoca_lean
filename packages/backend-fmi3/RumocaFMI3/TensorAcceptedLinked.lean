import RumocaFMI3.TensorDoStep
import RumocaFMI3.TensorLinkedProgram
import RumocaC.TensorSquareCallSites

/-! Accepted tensor steps on the exact numerical table. Public execution products
retain all storage, lifecycle, alias, external-math and finite-arithmetic inputs,
but no caller-supplied numerical lookup, library or intermediate resolution.
Concrete FMI header instantiation belongs to the runtime constructor. -/
noncomputable section
namespace Rumoca.FMI3.TensorAcceptedLinked
open CTree CMemory CBody CLoops StepGuards TensorDoStep
open Rumoca.CMemory.TensorView Rumoca.CTensor.Lowering Solve.Tensor
open Rumoca.ArrayProfile Rumoca.CTensor
open CCalls CCallSites CCallSites.LoopCalls

def ExecutionFree (shape : Tensor.Shape) (header : CFenv.Header)
    (target : CInterface) (fenv : TensorFenv target) (internal : CCalls.Program) : Prop :=
    letI : CInterface := target
    ∀ {E} (program : CCalls.Events.Program E) (linked : program.internal = internal)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64), shape.volume < 2 ^ 64 → count.toNat = shape.volume →
    program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType) →
    load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
    load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
    heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩ →
    Binary64.value point = Binary64.value (times 0) →
    load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
    StepAdmission.AdmittedDuration step →
    Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step) →
    (∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value) →
    Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial →
    Reads heap (TensorInstance.field pool i TensorInstance.inputName) input →
    Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume →
    HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
    HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
    (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
    (∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n)) →
    (∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a])) →
    (∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1)))) →
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      StepEntry.SuccessState heap finalHeap (TensorInstance.record pool i) buffers ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩

theorem execution_free (shape : Tensor.Shape) (header : CFenv.Header)
    (target : CInterface) (fenv : TensorFenv target)
    (ptypes : @StepEntry.Types target)
    (binaryHeader : CTensor.HeaderTypes target) (fillHeader : Fill.HeaderTypes target)
    (nearest : target.constants "FE_TONEAREST" = some (.integer header.nearest))
    (clear : ∀ name ∈ TensorKernel.helperNames, target.constants name = none ∧ name ≠ "isfinite")
    (internal : CCalls.Program) (extended : CCalls.Typed.Extends TensorKernel.definitions internal)
    (stepDefinition : internal.definitions "fmi3DoStep" = some (.tree (function shape false))) :
    ExecutionFree shape header target fenv internal := by
  letI : CInterface := target
  intro E program linked heap pool i buffers point step flag stop oldOutput initial input results sums times
    count bounded matched rounding floorBound kindValue modeValue timeCell same enabled limit
    admitted progress withinStop readsState readsInput writableState writableDeriv
    event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast executes adds timeAdds
  have linked' : CCalls.Typed.Extends TensorKernel.definitions program.internal := by
    rw [linked]; exact extended
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape false)) := by
    rw [linked]; exact stepDefinition
  have library : LibraryFor (TensorInstanceRhs.kernel shape).derivative TensorKernel.definitions :=
    TensorKernel.derivative_library shape binaryHeader fillHeader
  have found : TensorKernel.definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree :=
    TensorKernel.derivative_defined shape
  have resolves := fun (H : Heap) =>
    call_resolves program TensorKernel.functions_admitted clear
      (TensorInstanceRhs.plan shape).derivative.function.name
      (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape)) H
  exact (TensorDoStep.execution_free_for shape header target fenv nearest)
    program ptypes TensorKernel.definitions linked' library found
    heap pool i buffers point step flag stop oldOutput initial input results sums times count
    bounded matched rounding floorBound defined kindValue modeValue timeCell same enabled limit
    admitted progress withinStop readsState readsInput writableState writableDeriv
    event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast executes adds timeAdds
    resolves

def ExecutionOutput (shape : Tensor.Shape) (header : CFenv.Header)
    (target : CInterface) (fenv : TensorFenv target) (internal : CCalls.Program) : Prop :=
    letI : CInterface := target
    ∀ {E} (program : CCalls.Events.Program E) (linked : program.internal = internal)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64), shape.volume < 2 ^ 64 → count.toNat = shape.volume →
    (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType) →
    load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
    load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
    heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩ →
    Binary64.value point = Binary64.value (times 0) →
    load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
    StepAdmission.AdmittedDuration step →
    Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step) →
    (∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value) →
    Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial →
    Reads heap (TensorInstance.field pool i TensorInstance.inputName) input →
    Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume →
    HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
    HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
    (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
    (∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n)) →
    (∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a])) →
    (∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1)))) →
    (∀ k : Fin shape.volume, Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k])) →
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      StepEntry.SuccessState heap finalHeap (TensorInstance.record pool i) buffers ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩

theorem execution_output (shape : Tensor.Shape) (header : CFenv.Header)
    (target : CInterface) (fenv : TensorFenv target)
    (ptypes : @StepEntry.Types target)
    (binaryHeader : CTensor.HeaderTypes target) (fillHeader : Fill.HeaderTypes target)
    (nearest : target.constants "FE_TONEAREST" = some (.integer header.nearest))
    (clear : ∀ name ∈ TensorKernel.helperNames, target.constants name = none ∧ name ≠ "isfinite")
    (internal : CCalls.Program) (extended : CCalls.Typed.Extends TensorKernel.definitions internal)
    (stepDefinition : internal.definitions "fmi3DoStep" = some (.tree (function shape true))) :
    ExecutionOutput shape header target fenv internal := by
  letI : CInterface := target
  intro E program linked heap pool i buffers point step flag stop oldOutput initial input results sums times
    count bounded matched bounded2 rounding floorBound kindValue modeValue timeCell same enabled limit
    admitted progress withinStop readsState readsInput writableState writableDeriv writableOutput
    event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast executes adds timeAdds jacAdds
  have linked' : CCalls.Typed.Extends TensorKernel.definitions program.internal := by
    rw [linked]; exact extended
  have defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape true)) := by
    rw [linked]; exact stepDefinition
  have library : LibraryFor (TensorInstanceRhs.kernel shape).derivative TensorKernel.definitions :=
    TensorKernel.derivative_library shape binaryHeader fillHeader
  have found : TensorKernel.definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree :=
    TensorKernel.derivative_defined shape
  have resolves := fun (H : Heap) =>
    call_resolves program TensorKernel.functions_admitted clear
      (TensorInstanceRhs.plan shape).derivative.function.name
      (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape)) H
  have jacResolves := fun (H : Heap) =>
    call_resolves program TensorKernel.functions_admitted clear SquareDiagonal.function.signature.name
      (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
        (TensorInstance.field pool i TensorInstance.outputName) shape) H
  exact (TensorDoStep.execution_output_for shape header target fenv nearest)
    program ptypes TensorKernel.definitions linked' library found TensorKernel.square_diagonal_defined
    heap pool i buffers point step flag stop oldOutput initial input results sums times count
    bounded matched bounded2 rounding floorBound defined kindValue modeValue timeCell same enabled limit
    admitted progress withinStop readsState readsInput writableState writableDeriv writableOutput
    event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast executes adds timeAdds jacAdds
    resolves jacResolves

end Rumoca.FMI3.TensorAcceptedLinked
