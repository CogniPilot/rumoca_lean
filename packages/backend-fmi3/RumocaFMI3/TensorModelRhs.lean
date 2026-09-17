import RumocaC.TensorIVPContract
import RumocaC.TensorTypedContract
import RumocaC.TensorProgramPrinter
import RumocaC.TypedEventsTransfer

/-! Typed-call execution contract for the prepared tensor model right-hand
side. The derivative entry of a `Solve.PointwiseIVP` runs under the typed
tensor call machine and writes the finite tensor derivative into its output
region. Every result is universal in the tensor shape, the heap and the
backing storage; tensor rank and extents stay symbolic and no coordinate is
enumerated. Storage validity is supplied at entry, mirroring the scalar model
right-hand-side contract so an adapter contract can consume the printed
function, its tokenization and its execution behavior unchanged.

The tensor right-hand side returns `void` and delivers its output through the
derivative buffer, rather than returning a scalar as the scalar helper does;
the finite derivative therefore appears as a heap read of that buffer while the
returning value is empty. -/
noncomputable section
namespace Rumoca.FMI3.TensorModelRhs
open CTree CMemory CMemory.TensorView Solve.Tensor Rumoca.CTensor.Lowering

variable [interface : CInterface]

/-- Erased storage plan of the derivative entry. -/
abbrev derivativePlan {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape)
    (plan : PointwisePlan p) : Plan p.derivative :=
  Named.Plan.erase p.derivative plan.derivative.plan

/-- Erased input layout of the derivative entry. -/
abbrev derivativeLayout {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape)
    (plan : PointwisePlan p) : Layout [shape, shape] :=
  Named.Layout.erase plan.derivative.layout

/-- Address of the derivative output buffer under the supplied call storage. -/
abbrev derivativeBuffer {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape)
    (plan : PointwisePlan p) (locations : Locations) : Address :=
  locations (emit p.derivative (derivativePlan p plan) (derivativeLayout p plan)).result

/-- Actual derivative-entry execution in the typed tensor call machine. Given a
program whose derivative definition is the prepared entry of the pointwise IVP
and storage satisfying the entry predicates, the typed machine reaches a
returning state whose derivative buffer holds the finite tensor derivative
result, under any saved caller. Cells outside the derivative output region are
preserved. -/
theorem reaches {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape) (plan : PointwisePlan p)
    (valid : plan.derivative.function.valid = true)
    (definitions : CLoops.Calls.Definitions) (target : CCalls.Program)
    (linked : CCalls.Typed.Extends definitions target) (library : Library definitions)
    (found : definitions plan.derivative.function.name = some plan.derivative.function.tree)
    (args : Arguments.Values) (arguments : Arguments.Valid plan.derivative.function.parameters args)
    (locations : Locations) (values : Env Binary64.Value [shape, shape]) (result : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals plan.derivative.function.parameters args) locations
      (derivativeLayout p plan))
    (represented : Represents locations (derivativeLayout p plan) heap values)
    (ready : Ready (Arguments.locals plan.derivative.function.parameters args) locations
      p.derivative (derivativePlan p plan) (derivativeLayout p plan) heap)
    (executed : Finite.Executes p.derivative values result) (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (derivativeBuffer p plan locations) result ∧
      (∀ q, Outside locations p.derivative (derivativePlan p plan) q → finalHeap q = heap q) ∧
      Transition.Reaches (CCalls.Typed.machine target).step
        (.calling plan.derivative.function.name
          (Arguments.values plan.derivative.function.parameters args) heap stack)
        (.returning .void finalHeap stack) := by
  obtain ⟨finalHeap, reads, _resultBound, frame, _writableResult, callResult⟩ :=
    (plan.derivative.correct valid).2 definitions target linked library found args arguments
      locations values result heap bound represented ready executed
  exact ⟨finalHeap, reads, frame, callResult.1 stack⟩

/-- The typed machine behaves exactly with the terminating derivative behavior:
its sole outcome writes the finite tensor derivative into the output buffer and
preserves every cell outside that region. -/
theorem behaviors {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape) (plan : PointwisePlan p)
    (valid : plan.derivative.function.valid = true)
    (definitions : CLoops.Calls.Definitions) (target : CCalls.Program)
    (linked : CCalls.Typed.Extends definitions target) (library : Library definitions)
    (found : definitions plan.derivative.function.name = some plan.derivative.function.tree)
    (args : Arguments.Values) (arguments : Arguments.Valid plan.derivative.function.parameters args)
    (locations : Locations) (values : Env Binary64.Value [shape, shape]) (result : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals plan.derivative.function.parameters args) locations
      (derivativeLayout p plan))
    (represented : Represents locations (derivativeLayout p plan) heap values)
    (ready : Ready (Arguments.locals plan.derivative.function.parameters args) locations
      p.derivative (derivativePlan p plan) (derivativeLayout p plan) heap)
    (executed : Finite.Executes p.derivative values result) :
    ∃ finalHeap,
      Reads finalHeap (derivativeBuffer p plan locations) result ∧
      (∀ q, Outside locations p.derivative (derivativePlan p plan) q → finalHeap q = heap q) ∧
      (Writable heap (derivativeBuffer p plan locations) shape.volume →
        Writable finalHeap (derivativeBuffer p plan locations) shape.volume) ∧
      ∀ behavior, (CCalls.Typed.machine target).Behaves
        (.calling plan.derivative.function.name
          (Arguments.values plan.derivative.function.parameters args) heap .done) behavior ↔
        behavior = .terminates ⟨.void, finalHeap⟩ := by
  obtain ⟨finalHeap, reads, _resultBound, frame, writableResult, callResult⟩ :=
    (plan.derivative.correct valid).2 definitions target linked library found args arguments
      locations values result heap bound represented ready executed
  exact ⟨finalHeap, reads, frame, writableResult, callResult.2⟩

/-- Observable-machine execution of the prepared tensor derivative entry. The
entry runs in the void loop-call machine (`CLoops.Calls.machine`, the level of
the tensor `CallCorrect`); its nested calls are the emitted tensor helper
functions, direct calls by identifier. Under the direct-resolution premise for
the call sites the run visits (`resolves`), the transfer lemma
`CCalls.Events.loop_call_reaches_events` embeds the same execution into the
observable machine under any saved caller, reaching the identical final heap. -/
theorem events_reaches {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape) (plan : PointwisePlan p)
    (valid : plan.derivative.function.valid = true)
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal) (library : Library definitions)
    (found : definitions plan.derivative.function.name = some plan.derivative.function.tree)
    (args : Arguments.Values) (arguments : Arguments.Valid plan.derivative.function.parameters args)
    (locations : Locations) (values : Env Binary64.Value [shape, shape]) (result : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals plan.derivative.function.parameters args) locations
      (derivativeLayout p plan))
    (represented : Represents locations (derivativeLayout p plan) heap values)
    (ready : Ready (Arguments.locals plan.derivative.function.parameters args) locations
      p.derivative (derivativePlan p plan) (derivativeLayout p plan) heap)
    (executed : Finite.Executes p.derivative values result)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling plan.derivative.function.name
        (Arguments.values plan.derivative.function.parameters args) heap .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (derivativeBuffer p plan locations) result ∧
      (∀ q, Outside locations p.derivative (derivativePlan p plan) q → finalHeap q = heap q) ∧
      (Writable heap (derivativeBuffer p plan locations) shape.volume →
        Writable finalHeap (derivativeBuffer p plan locations) shape.volume) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling plan.derivative.function.name
          (Arguments.values plan.derivative.function.parameters args) heap stack)
        (.returning .void finalHeap stack) := by
  obtain ⟨finalHeap, reads, _boundResult, frame, writableResult, behaviorIff⟩ :=
    (plan.derivative.correct valid).1.2 definitions library found args arguments
      locations values result heap bound represented ready executed
  exact ⟨finalHeap, reads, frame, writableResult,
    CCalls.Events.loop_call_reaches_events program definitions linked ((behaviorIff _).mpr rfl) resolves stack⟩

end Rumoca.FMI3.TensorModelRhs

noncomputable section
namespace Rumoca.FMI3.TensorModelRhs
open CTree CMemory CMemory.TensorView Solve.Tensor Rumoca.CTensor.Lowering

/-- Printed derivative function, its lexical denotation and its typed execution
behavior. This mirrors the scalar `ModelRhs.FunctionContract` so a future tensor
adapter contract can carry the tensor right-hand side unchanged. The execution
field internalizes the C interface, keeping the contract independent of any
particular address environment. -/
structure FunctionContract {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape)
    (plan : PointwisePlan p) (text : String) : Prop where
  valid : plan.derivative.function.valid = true
  printed : text = plan.derivative.function.tree.render
  denotes : Rumoca.CTensor.Lowering.Syntax.Denotes text plan.derivative.function
  execution : ∀ [CInterface] (definitions : CLoops.Calls.Definitions) (target : CCalls.Program),
    CCalls.Typed.Extends definitions target → Library definitions →
    definitions plan.derivative.function.name = some plan.derivative.function.tree →
    ∀ (args : Arguments.Values), Arguments.Valid plan.derivative.function.parameters args →
    ∀ (locations : Locations) (values : Env Binary64.Value [shape, shape]) (result : Values shape) (heap : Heap),
    LayoutBound (Arguments.locals plan.derivative.function.parameters args) locations
      (derivativeLayout p plan) →
    Represents locations (derivativeLayout p plan) heap values →
    Ready (Arguments.locals plan.derivative.function.parameters args) locations
      p.derivative (derivativePlan p plan) (derivativeLayout p plan) heap →
    Finite.Executes p.derivative values result →
    ∃ finalHeap,
      Reads finalHeap (derivativeBuffer p plan locations) result ∧
      (∀ q, Outside locations p.derivative (derivativePlan p plan) q → finalHeap q = heap q) ∧
      ∀ behavior, (CCalls.Typed.machine target).Behaves
        (.calling plan.derivative.function.name
          (Arguments.values plan.derivative.function.parameters args) heap .done) behavior ↔
        behavior = .terminates ⟨.void, finalHeap⟩

/-- The rendered derivative function satisfies its contract whenever the entry's
syntax is valid. -/
theorem rendered_contract {shape : Tensor.Shape} (p : Solve.PointwiseIVP shape) (plan : PointwisePlan p)
    (valid : plan.derivative.function.valid = true) :
    FunctionContract p plan plan.derivative.function.tree.render := by
  refine ⟨valid, rfl, ?_, ?_⟩
  · exact Rumoca.CTensor.Lowering.Syntax.render_denotes plan.derivative.function valid
  · intro interface definitions target linked library found args arguments locations values result heap
      bound represented ready executed
    obtain ⟨finalHeap, reads, frame, _writableResult, behaviorIff⟩ :=
      behaviors p plan valid definitions target linked library found args arguments
        locations values result heap bound represented ready executed
    exact ⟨finalHeap, reads, frame, behaviorIff⟩

end Rumoca.FMI3.TensorModelRhs
