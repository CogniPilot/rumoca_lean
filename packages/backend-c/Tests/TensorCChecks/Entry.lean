import TensorCChecks.Fixture
import RumocaC.TensorProgramCallContract
import RumocaC.TensorRegions
import RumocaCore.Array.Lowering

/-! Concrete named call-entry storage for the existing coefficient program.
The heap construction specifies initial objects, not a C allocator execution. -/
noncomputable section
namespace Rumoca.CTensor.ProgramFixture.Entry
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering

def scratchNames : List String := ["zero", "one", "primal", "left", "right", "result"]

def inputHeap (backing : Heap) (base : Address) (state input : Values shape) : Heap :=
  TensorRegion.place (TensorRegion.place backing (base.member "x") shape true (some state))
    (base.member "u") shape false (some input)

def initialHeap (backing : Heap) (base : Address) (state input : Values shape) : Heap :=
  TensorRegion.scratch (inputHeap backing base state input) base shape scratchNames

def args (base : Address) (shape : Tensor.Shape) : Arguments.Values := fun name =>
  if name = "count" then .integer shape.volume else .pointer (some (base.member name))

def locations (base : Address) : Locations := fun buffer =>
  match buffer.pointer with
  | .id name => base.member name
  | _ => base

theorem reads_input (backing : Heap) (base : Address) (state input : Values shape) :
    Reads (initialHeap backing base state input) (base.member "u") input := by
  intro i
  have atInput : initialHeap backing base state input ((base.member "u").index i.val) =
      some ⟨.float64, false, some (.finite input[i])⟩ := by
    rw [initialHeap, TensorRegion.scratch_other _ _ _ _ _ (by decide +kernel), inputHeap,
      TensorRegion.place_at]
    rfl
  simp only [load, atInput, bind, Option.bind_some, convert, Value.finite,
    show (CType.float64 = CType.atomicBoolean) = False from by decide +kernel, ↓reduceIte, pure]

theorem reads_state (backing : Heap) (base : Address) (state input : Values shape) :
    Reads (initialHeap backing base state input) (base.member "x") state := by
  intro i
  have atState : initialHeap backing base state input ((base.member "x").index i.val) =
      some ⟨.float64, true, some (.finite state[i])⟩ := by
    rw [initialHeap, TensorRegion.scratch_other _ _ _ _ _ (by decide +kernel), inputHeap,
      TensorRegion.place_other_member _ _ _ _ _ _ _ (by decide +kernel), TensorRegion.place_at]
    rfl
  simp only [load, atState, bind, Option.bind_some, convert, Value.finite,
    show (CType.float64 = CType.atomicBoolean) = False from by decide +kernel, ↓reduceIte, pure]

theorem writable (backing : Heap) (base : Address) (state input : Values shape)
    (name : String) (member : name ∈ scratchNames) :
    Writable (initialHeap backing base state input) (base.member name) shape.volume :=
  TensorRegion.scratch_writable _ _ _ _ _ member

theorem arguments_valid (base : Address) (shape : Tensor.Shape) (bounded : shape.volume < 2 ^ 64) :
    Arguments.Valid profile.parameters (args base shape) := by
  intro p member
  simp only [profile, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .input _
    | exact .output _
    | exact .count shape.volume bounded

variable [interface : CInterface]

theorem named_bound (base : Address) (shape : Tensor.Shape) (name : String)
    (member : name ∈ ["x", "u", "zero", "one", "primal", "left", "right", "result"]) :
    Bound (Arguments.locals profile.parameters (args base shape)) (locations base) (buffer shape name) := by
  have declared : name ∈ profile.parameters.map Syntax.Parameter.name := by
    simpa [profile, List.mem_cons, List.mem_singleton, or_assoc] using Or.inl member
  have notCount : name ≠ "count" := by
    intro eq
    subst name
    contradiction
  have pointer := Arguments.locals_present profile.parameters (args base shape) name declared
  have count := Arguments.locals_present profile.parameters (args base shape) "count" (by decide +kernel)
  intro heap
  simp only [buffer, CBody.eval, CBody.resolve, pointer, count, args, if_neg notCount,
    ↓reduceIte, Option.orElse_some, locations, and_self]

theorem layout_bound (base : Address) (shape : Tensor.Shape) :
    LayoutBound (Arguments.locals profile.parameters (args base shape)) (locations base) (layout shape) := by
  intro s ref
  cases ref with
  | here => exact named_bound base shape "x" (by decide +kernel)
  | there ref => cases ref with
    | here => exact named_bound base shape "u" (by decide +kernel)
    | there ref => nomatch ref

omit interface in
theorem represented (backing : Heap) (base : Address) (state input : Values shape) :
    Represents (locations base) (layout shape) (initialHeap backing base state input)
      (ArrayProfile.environment state input) := by
  intro s ref
  cases ref with
  | here => exact reads_state backing base state input
  | there ref => cases ref with
    | here => exact reads_input backing base state input
    | there ref => nomatch ref

theorem ready (backing : Heap) (base : Address) (state input : Values shape)
    (bounded : shape.volume < 2 ^ 64) :
    Ready (Arguments.locals profile.parameters (args base shape)) (locations base)
      (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape)
      (initialHeap backing base state input) := by
  simp only [ArrayProfile.squareJacobianProgram, ArrayProfile.squareProgram, Program.forward,
    Ready, plan]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact bounded
    | exact writable backing base state input _ (by decide +kernel)
    | exact named_bound base shape _ (by decide +kernel)
    | skip
  all_goals
    intro s ref i hi j hj
    casesm* Ref _ _
    all_goals exact TensorRegion.member_separate base _ _ (by decide +kernel) i j

theorem call_correct (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (found : definitions profile.name = some profile.tree) (backing : Heap) (base : Address)
    (state input result : Values shape) (bounded : shape.volume < 2 ^ 64)
    (executed : Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) result) :
    ∃ finalHeap, Reads finalHeap (base.member "result") result ∧
      (∀ q, Outside (locations base) (ArrayProfile.squareJacobianProgram shape).coefficients
        (plan shape) q → finalHeap q = initialHeap backing base state input q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling profile.name (Arguments.values profile.parameters (args base shape))
          (initialHeap backing base state input) .done) behavior ↔ behavior = .terminates finalHeap := by
  obtain ⟨finalHeap, readResult, _, frame, _, behaviors⟩ := program_call_refines profile valid
    (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape) (body_matches shape)
    definitions library found (args base shape) (arguments_valid base shape bounded) (locations base)
    (ArrayProfile.environment state input) result (initialHeap backing base state input)
    (layout_bound base shape) (represented backing base state input) (ready backing base state input bounded) executed
  exact ⟨finalHeap, by simpa only [result_buffer, buffer, locations] using readResult, frame, behaviors⟩

def StorageContract : Prop := ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions),
  @Library interface definitions → definitions profile.name = some profile.tree →
  ∀ (shape : Tensor.Shape) (backing : Heap) (base : Address) (state input result : Values shape),
  shape.volume < 2 ^ 64 →
  Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
    (ArrayProfile.environment state input) result →
  ∃ finalHeap, Reads finalHeap (base.member "result") result ∧
    (∀ q, Outside (locations base) (ArrayProfile.squareJacobianProgram shape).coefficients
      (plan shape) q → finalHeap q = initialHeap backing base state input q) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling profile.name (Arguments.values profile.parameters (args base shape))
        (initialHeap backing base state input) .done) behavior ↔ behavior = .terminates finalHeap

def ArtifactContract (source : String) : Prop :=
  ProgramFixture.ArtifactContract source ∧
  (∀ shape : Tensor.Shape,
    Lowering.CallArtifactContract source profile (ArrayProfile.squareJacobianProgram shape).coefficients
      (plan shape) (layout shape)) ∧ StorageContract

omit interface in
theorem artifact_correct (source : String) (printed : source = code) : ArtifactContract source := by
  refine ⟨ProgramFixture.artifact_correct source printed, ?_, ?_⟩
  · intro shape
    exact Lowering.call_artifact_correct source profile _ (plan shape) (layout shape)
      (printed.trans (congrArg CTree.Function.render (function_tree _))) valid (body_matches shape)
  · intro interface definitions library found shape backing base state input result bounded executed
    exact call_correct definitions library found backing base state input result bounded executed

end Rumoca.CTensor.ProgramFixture.Entry
