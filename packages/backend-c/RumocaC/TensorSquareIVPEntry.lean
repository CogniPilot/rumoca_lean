import RumocaC.TensorSquareDiagonalEntry
import RumocaC.TensorIVPContract
import RumocaC.TensorSquareDiagonal
import RumocaCore.Array.SquareIVP

/-! Production-owned square IVP target plan and complete storage contracts.
Extracted from TensorCChecks with existing declaration names retained for API
compatibility. The ProgramFixture namespace is historical; implementation and
proof ownership is backend-c. Tensor shapes and programs remain indexed, and
heap constructors specify supplied storage rather than allocator execution. -/
namespace Rumoca.CTensor.ProgramFixture.IVPEntry
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering

def kernel (shape : Tensor.Shape) : Solve.PointwiseIVP shape :=
  ArrayProfile.squareIVP shape

def namedBuffer (shape : Tensor.Shape) (name : String) : Named.Buffer shape := ⟨name, "count"⟩

def namedLayout (shape : Tensor.Shape) : Named.Layout [shape, shape]
  | _, .here => namedBuffer shape "x"
  | _, .there .here => namedBuffer shape "u"

def coefficientPlan (shape : Tensor.Shape) : Named.Plan (ArrayProfile.squareJacobianProgram shape).coefficients :=
  ⟨namedBuffer shape "zero", ⟨namedBuffer shape "one", ⟨namedBuffer shape "primal",
    ⟨namedBuffer shape "left", ⟨namedBuffer shape "right", ⟨namedBuffer shape "result", ()⟩⟩⟩⟩⟩⟩

def initialParameters : List Syntax.Parameter := [⟨.output, "x"⟩, ⟨.count, "count"⟩]
def derivativeParameters : List Syntax.Parameter :=
  [⟨.input, "x"⟩, ⟨.input, "u"⟩, ⟨.output, "dx"⟩, ⟨.count, "count"⟩]

def plan (shape : Tensor.Shape) : PointwisePlan (kernel shape) where
  initial := ⟨"rumoca_initialize", initialParameters,
    ⟨namedBuffer shape "x", ()⟩, fun ref => nomatch ref⟩
  derivative := ⟨"rumoca_rhs", derivativeParameters,
    ⟨namedBuffer shape "dx", ()⟩, namedLayout shape⟩
  diagonal := ⟨"rumoca_square_jacobian", ProgramFixture.DiagonalEntry.parameters,
    coefficientPlan shape, namedLayout shape, ⟨"J", "cells"⟩⟩

theorem plan_valid (shape : Tensor.Shape) : (plan shape).Valid := by
  change (plan ArrayProfile.stateShape).Valid
  dsimp only [PointwisePlan.Valid, plan, kernel, ArrayProfile.squareIVP, OptionalDiagonalEntry.Valid,
    Lowering.DiagonalEntry.Valid, DiagonalScope]
  decide +kernel

theorem initial_result (shape : Tensor.Shape) : (plan shape).initial.result = namedBuffer shape "x" := rfl
theorem derivative_result (shape : Tensor.Shape) : (plan shape).derivative.result = namedBuffer shape "dx" := rfl

theorem jacobian_function (shape : Tensor.Shape) :
    Lowering.DiagonalEntry.function (plan shape).diagonal = ProgramFixture.DiagonalEntry.profile := rfl

def sources : PointwiseSources := (plan ArrayProfile.stateShape).sources

theorem sources_shape (shape : Tensor.Shape) : sources = (plan shape).sources := rfl

def ProgramContract (actual : PointwiseSources) : Prop :=
  (∀ shape, (plan shape).Contract actual) ∧
  ∃ diagonal, actual.diagonal = some diagonal ∧ ProgramFixture.DiagonalEntry.ArtifactContract diagonal

theorem program_correct (actual : PointwiseSources) (printed : actual = sources) : ProgramContract actual := by
  constructor
  · intro shape
    rw [printed, sources_shape shape]
    exact PointwisePlan.correct _ (plan_valid shape)
  · refine ⟨ProgramFixture.DiagonalEntry.code, ?_, ProgramFixture.DiagonalEntry.artifact_correct _ rfl⟩
    rw [printed]
    rfl

macro "tensor_expand_ivp_fixture" : tactic => `(tactic|
  simp [sources, PointwisePlan.sources, ProgramEntry.function, OptionalDiagonalEntry.function,
    Lowering.DiagonalEntry.function, Named.function, Named.diagonalFunction, Named.emit,
    kernel, ArrayProfile.squareIVP, plan, initialParameters, derivativeParameters, namedBuffer, namedLayout, coefficientPlan, ArrayProfile.squareProgram,
    ArrayProfile.squareJacobianProgram, Program.forward, fill,
    ProgramFixture.DiagonalEntry.parameters, ProgramFixture.profile,
    Syntax.Function.tree, Syntax.Parameter.tree, Syntax.ParamKind.type,
    Syntax.Statement.tree, Syntax.binaryName,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render])

noncomputable section

theorem initial_arguments (base : Address) (shape : Tensor.Shape) (bounded : shape.volume < 2 ^ 64) :
    Arguments.Valid (plan shape).initial.function.parameters (Entry.args base shape) := by
  intro p member
  change p ∈ [⟨.output, "x"⟩, ⟨.count, "count"⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .output _
  · exact .count _ bounded

theorem derivative_arguments (base : Address) (shape : Tensor.Shape) (bounded : shape.volume < 2 ^ 64) :
    Arguments.Valid (plan shape).derivative.function.parameters (Entry.args base shape) := by
  intro p member
  change p ∈ [⟨.input, "x"⟩, ⟨.input, "u"⟩, ⟨.output, "dx"⟩, ⟨.count, "count"⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .input _
  · exact .input _
  · exact .output _
  · exact .count _ bounded

variable [interface : CInterface]

theorem parameter_bound (parameters : List Syntax.Parameter) (base : Address) (shape : Tensor.Shape)
    (name : String) (member : name ∈ parameters.map Syntax.Parameter.name)
    (countMember : "count" ∈ parameters.map Syntax.Parameter.name) (different : name ≠ "count") :
    Bound (Arguments.locals parameters (Entry.args base shape)) (Entry.locations base)
      (ProgramFixture.buffer shape name) := by
  have pointer := Arguments.locals_present parameters (Entry.args base shape) name member
  have count := Arguments.locals_present parameters (Entry.args base shape) "count" countMember
  intro heap
  simp only [ProgramFixture.buffer, CBody.eval, CBody.evalWith, CBody.resolve, pointer, count, Entry.args,
    if_neg different, ↓reduceIte, Option.orElse_some, Entry.locations, and_self]

theorem initial_call_correct (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (found : definitions (plan shape).initial.function.name = some (plan shape).initial.function.tree)
    (heap : Heap) (base : Address) (bounded : shape.volume < 2 ^ 64)
    (writable : Writable heap (base.member "x") shape.volume) :
    ∃ finalHeap, Reads finalHeap (base.member "x")
        ((kernel shape).problem.initial Finite.ops Binary64.positiveZero Binary64.one) ∧
      (∀ q, (∀ i < shape.volume, q ≠ (base.member "x").index i) → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling (plan shape).initial.function.name
          (Arguments.values (plan shape).initial.function.parameters (Entry.args base shape)) heap .done) behavior ↔
        behavior = .terminates finalHeap := by
  have bound := parameter_bound initialParameters base shape "x"
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ready : Ready (Arguments.locals (plan shape).initial.function.parameters (Entry.args base shape))
      (Entry.locations base) (kernel shape).initialProgram
      (Named.Plan.erase _ (plan shape).initial.plan) (Named.Layout.erase (plan shape).initial.layout) heap := by
    exact ⟨writable, bounded, bound, (fun r => nomatch r), True.intro⟩
  obtain ⟨finalHeap, reads, _, frame, _, behaviors⟩ :=
    program_call_refines (plan shape).initial.function (plan_valid shape).1 _ _ _
      (Named.function_matches _ _ _ _ _) definitions library found (Entry.args base shape)
      (initial_arguments base shape bounded) (Entry.locations base) Env.empty
      (Tensor.Value.fill shape Binary64.positiveZero) heap (fun r => nomatch r)
      (fun r => nomatch r) ready (Finite.Executes.fill Finite.Executes.ret)
  exact ⟨finalHeap, reads, fun q h => frame q ⟨h, True.intro⟩, behaviors⟩

theorem derivative_call_correct (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (found : definitions (plan shape).derivative.function.name = some (plan shape).derivative.function.tree)
    (heap : Heap) (base : Address) (state input result : Values shape) (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (base.member "x") state) (readsInput : Reads heap (base.member "u") input)
    (writable : Writable heap (base.member "dx") shape.volume)
    (executed : Finite.Executes (kernel shape).derivative (ArrayProfile.environment state input) result) :
    ∃ finalHeap, Reads finalHeap (base.member "dx") result ∧
      (∀ q, (∀ i < shape.volume, q ≠ (base.member "dx").index i) → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling (plan shape).derivative.function.name
          (Arguments.values (plan shape).derivative.function.parameters (Entry.args base shape)) heap .done) behavior ↔
        behavior = .terminates finalHeap := by
  have layoutBound : LayoutBound
      (Arguments.locals (plan shape).derivative.function.parameters (Entry.args base shape))
      (Entry.locations base) (Named.Layout.erase (plan shape).derivative.layout) := by
    intro s r
    cases r with
    | here => exact parameter_bound derivativeParameters base shape "x" (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there r => cases r with
      | here => exact parameter_bound derivativeParameters base shape "u" (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | there r => nomatch r
  have represented : Represents (Entry.locations base) (Named.Layout.erase (plan shape).derivative.layout)
      heap (ArrayProfile.environment state input) := by
    intro s r
    cases r with
    | here => exact readsState
    | there r => cases r with
      | here => exact readsInput
      | there r => nomatch r
  have ready : Ready (Arguments.locals (plan shape).derivative.function.parameters (Entry.args base shape))
      (Entry.locations base) (kernel shape).derivative (Named.Plan.erase _ (plan shape).derivative.plan)
      (Named.Layout.erase (plan shape).derivative.layout) heap := by
    refine ⟨writable, bounded, parameter_bound derivativeParameters base shape "dx"
      (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, True.intro⟩
    intro s r i hi j hj
    casesm* Ref _ _
    all_goals exact TensorRegion.member_separate base _ _ (by simp [plan, namedLayout, namedBuffer]) i j
  obtain ⟨finalHeap, reads, _, frame, _, behaviors⟩ :=
    program_call_refines (plan shape).derivative.function (plan_valid shape).2.1 _ _ _
      (Named.function_matches _ _ _ _ _) definitions library found (Entry.args base shape)
      (derivative_arguments base shape bounded) (Entry.locations base) (ArrayProfile.environment state input)
      result heap layoutBound represented ready executed
  exact ⟨finalHeap, reads, fun q h => frame q ⟨h, True.intro⟩, behaviors⟩

end

def InitialStorageContract : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions), @Library interface definitions →
  ∀ (shape : Tensor.Shape),
  definitions (plan shape).initial.function.name = some (plan shape).initial.function.tree →
  ∀ (heap : Heap) (base : Address), shape.volume < 2 ^ 64 → Writable heap (base.member "x") shape.volume →
  ∃ finalHeap, Reads finalHeap (base.member "x")
      ((kernel shape).problem.initial Finite.ops Binary64.positiveZero Binary64.one) ∧
    (∀ q, (∀ i < shape.volume, q ≠ (base.member "x").index i) → finalHeap q = heap q) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling (plan shape).initial.function.name
        (Arguments.values (plan shape).initial.function.parameters (Entry.args base shape)) heap .done) behavior ↔
      behavior = .terminates finalHeap

def DerivativeStorageContract : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions), @Library interface definitions →
  ∀ (shape : Tensor.Shape),
  definitions (plan shape).derivative.function.name = some (plan shape).derivative.function.tree →
  ∀ (heap : Heap) (base : Address) (state input result : Values shape), shape.volume < 2 ^ 64 →
  Reads heap (base.member "x") state → Reads heap (base.member "u") input →
  Writable heap (base.member "dx") shape.volume →
  Finite.Executes (kernel shape).derivative (ArrayProfile.environment state input) result →
  ∃ finalHeap, Reads finalHeap (base.member "dx") result ∧
    (∀ q, (∀ i < shape.volume, q ≠ (base.member "dx").index i) → finalHeap q = heap q) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling (plan shape).derivative.function.name
        (Arguments.values (plan shape).derivative.function.parameters (Entry.args base shape)) heap .done) behavior ↔
      behavior = .terminates finalHeap

/-! ### The scratch-free square-Jacobian diagonal entry

Alongside the initial, derivative and full coefficient Jacobian entries, the
prepared kernel product carries the reusable scratch-free materializer
`rumoca_square_jacobian_diag` (`Rumoca.CTensor.SquareDiagonal.function`), which
writes the dense Jacobian `diag(2*u)` from the input tensor with no coefficient
buffer. This is a second prepared kernel entry: it is defined in the certified
kernel product and called directly by the tensor FMI adapter through the
kernel-call path, mirroring `rumoca_rhs`. Its certified source is the rendered
function; its storage behavior is the standalone helper's call correctness. -/

/-- The certified source of the scratch-free square-Jacobian diagonal entry. -/
def jacobianDiagSource : String := SquareDiagonal.function.render

/-- Normalize `jacobianDiagSource` (the rendered `rumoca_square_jacobian_diag`
function) to a string literal, mirroring `tensor_expand_diagonal_printer` for the
diagonal-copy helper whose structure it shares. -/
macro "tensor_expand_jacobian_diag" : tactic => `(tactic|
  simp [jacobianDiagSource, Rumoca.CTensor.SquareDiagonal.function,
    Rumoca.CTensor.SquareDiagonal.tail, Rumoca.CTensor.SquareDiagonal.operation,
    Rumoca.CTensor.Diagonal.signatureParameters, Lowering.Syntax.Parameter.tree,
    Lowering.Syntax.ParamKind.type, Rumoca.CTensor.Fill.invoke, Rumoca.CTensor.Fill.function,
    Rumoca.CAlgorithm.literal, Rumoca.CTensor.indexed, CLoops.counted, CLoops.loop,
    CLoops.counterStep, CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render, CTree.BinOp.render])

/-- The prepared square-Jacobian diagonal entry's storage behavior: the ordinary
call writes the dense diagonal matrix `diag(2*coeff)` into the output region and
that region then reads the matrix, with every cell outside it preserved. This
bundles `SquareDiagonal.helper_call_correct`, `output_reads` and `output_frame`,
mirroring `DerivativeStorageContract` for the derivative entry `rumoca_rhs`. -/
def JacobianDiagStorageContract : Prop :=
  ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions) {shape : Tensor.Shape}
    (input output : Address) (result values : Values shape) (heap : Heap),
  definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function →
  definitions Fill.function.signature.name = some Fill.function →
  CTensor.HeaderTypes interface → Fill.HeaderTypes interface →
  Diagonal.Separate output input shape → Reads heap input values →
  (∀ i : Fin shape.volume, Binary64.Adds values[i] values[i] (.finite result[i])) →
  Writable heap output (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume →
  (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    (∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling SquareDiagonal.function.signature.name
          (Diagonal.argumentValues input output shape) heap .done) behavior ↔
        behavior = .terminates (Diagonal.resultHeap heap output result)) ∧
      Reads (Diagonal.resultHeap heap output result) output (Diagonal.matrix result) ∧
      (∀ q, (∀ i < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume, q ≠ output.index i) →
        Diagonal.resultHeap heap output result q = heap q)

theorem jacobianDiag_correct : JacobianDiagStorageContract := by
  intro interface definitions shape input output result values heap found fillDefined header fillHeader
    separate reads adds writable bounded
  exact ⟨SquareDiagonal.helper_call_correct definitions input output result values heap found fillDefined
      header fillHeader separate reads adds writable bounded,
    SquareDiagonal.output_reads heap output result,
    SquareDiagonal.output_frame heap output result⟩

def ArtifactContract (actual : PointwiseSources) (actualDiag : String) : Prop :=
  ProgramContract actual ∧ InitialStorageContract ∧ DerivativeStorageContract ∧
    actualDiag = jacobianDiagSource ∧ JacobianDiagStorageContract

theorem artifact_correct (actual : PointwiseSources) (actualDiag : String)
    (printed : actual = sources) (printedDiag : actualDiag = jacobianDiagSource) :
    ArtifactContract actual actualDiag := by
  refine ⟨program_correct actual printed, ?_, ?_, printedDiag, jacobianDiag_correct⟩
  · intro interface definitions library shape found heap base bounded writable
    exact initial_call_correct definitions library found heap base bounded writable
  · intro interface definitions library shape found heap base state input result bounded rs ri writable executed
    exact derivative_call_correct definitions library found heap base state input result bounded rs ri writable executed

end Rumoca.CTensor.ProgramFixture.IVPEntry
