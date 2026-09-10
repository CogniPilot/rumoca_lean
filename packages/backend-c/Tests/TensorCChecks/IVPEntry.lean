import TensorCChecks.DiagonalEntry
import RumocaC.TensorIVPContract

/-! The existing square/Jacobian example now checks the complete IVP product.
Initial and RHS calls derive storage premises from the actual arguments and
named objects. The previous Jacobian file/storage contract remains required.
This development fixture does not admit a new production grammar case. -/
namespace Rumoca.CTensor.ProgramFixture.IVPEntry
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering

def kernel (shape : Tensor.Shape) : Solve.PointwiseIVP shape :=
  ⟨fill shape .zero, ArrayProfile.squareProgram shape, some (ArrayProfile.squareJacobianProgram shape)⟩

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
  dsimp only [PointwisePlan.Valid, plan, kernel, OptionalDiagonalEntry.Valid,
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
    kernel, plan, initialParameters, derivativeParameters, namedBuffer, namedLayout, coefficientPlan, ArrayProfile.squareProgram,
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
  simp only [ProgramFixture.buffer, CBody.eval, CBody.resolve, pointer, count, Entry.args,
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
  obtain ⟨finalHeap, reads, _, frame, behaviors⟩ :=
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
  obtain ⟨finalHeap, reads, _, frame, behaviors⟩ :=
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

def ArtifactContract (actual : PointwiseSources) : Prop :=
  ProgramContract actual ∧ InitialStorageContract ∧ DerivativeStorageContract

theorem artifact_correct (actual : PointwiseSources) (printed : actual = sources) : ArtifactContract actual := by
  refine ⟨program_correct actual printed, ?_, ?_⟩
  · intro interface definitions library shape found heap base bounded writable
    exact initial_call_correct definitions library found heap base bounded writable
  · intro interface definitions library shape found heap base state input result bounded rs ri writable executed
    exact derivative_call_correct definitions library found heap base state input result bounded rs ri writable executed

end Rumoca.CTensor.ProgramFixture.IVPEntry
