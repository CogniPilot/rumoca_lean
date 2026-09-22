import RumocaC.TensorSquareEntry
import RumocaC.TensorDiagonalProgramContract

/-! Production-owned square diagonal entry and storage proofs.
Extracted from TensorCChecks with existing declaration names retained for API
compatibility. The ProgramFixture namespace is historical; implementation and
proof ownership is backend-c. Tensor shapes and programs remain indexed, and
heap constructors specify supplied storage rather than allocator execution. -/
namespace Rumoca.CTensor.ProgramFixture.DiagonalEntry
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering

def parameters : List Syntax.Parameter :=
  ProgramFixture.profile.parameters ++ [⟨.output, "J"⟩, ⟨.count, "cells"⟩]

def output (shape : Tensor.Shape) : Buffer (ArrayProfile.squareJacobianProgram shape).shape :=
  ⟨.id "J", .id "cells"⟩

def backingHeap (backing : Heap) (base : Address) (shape : Tensor.Shape) : Heap :=
  TensorRegion.place backing (base.member "J") (ArrayProfile.squareJacobianProgram shape).shape true none

def initialHeap (backing : Heap) (base : Address) (state input : Values shape) : Heap :=
  Entry.initialHeap (backingHeap backing base shape) base state input

def args (base : Address) (shape : Tensor.Shape) : Arguments.Values := fun name =>
  if name = "cells" then .integer (ArrayProfile.squareJacobianProgram shape).shape.volume
  else Entry.args base shape name

theorem arguments_valid (base : Address) (shape : Tensor.Shape)
    (bounded : (ArrayProfile.squareJacobianProgram shape).shape.volume < 2 ^ 64) :
    Arguments.Valid parameters (args base shape) := by
  intro p member
  simp only [parameters, ProgramFixture.profile, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .input _
    | exact .output _
    | exact .count shape.volume (Diagonal.counter_bounds shape bounded).1
    | exact .count _ bounded

theorem output_writable (backing : Heap) (base : Address) (state input : Values shape) :
    Writable (initialHeap backing base state input) (base.member "J")
      (ArrayProfile.squareJacobianProgram shape).shape.volume := by
  intro i hi
  refine ⟨none, ?_⟩
  rw [initialHeap, Entry.initialHeap,
    TensorRegion.scratch_other _ _ _ _ _ (by decide +kernel), Entry.inputHeap,
    TensorRegion.place_other_member _ _ _ _ _ _ _ (by decide +kernel),
    TensorRegion.place_other_member _ _ _ _ _ _ _ (by decide +kernel)]
  exact TensorRegion.place_at backing (base.member "J") _ true none ⟨i, hi⟩

theorem represented (backing : Heap) (base : Address) (state input : Values shape) :
    Represents (Entry.locations base) (layout shape) (initialHeap backing base state input)
      (ArrayProfile.environment state input) :=
  Entry.represented (backingHeap backing base shape) base state input

theorem reserved (base : Address) (shape : Tensor.Shape) :
    Reserved (Entry.locations base) (output shape) (ArrayProfile.squareJacobianProgram shape).coefficients
      (plan shape) (layout shape) := by
  constructor
  · intro s ref i hi j hj
    casesm* Ref _ _
    all_goals exact TensorRegion.member_separate base _ _ (by decide +kernel) i j
  · intro i hi
    simp only [ArrayProfile.squareJacobianProgram, ArrayProfile.squareProgram, Program.forward,
      Outside, plan]
    repeat' apply And.intro
    all_goals first | exact True.intro | skip
    all_goals
      intro j hj
      exact TensorRegion.member_separate base _ _ (by decide +kernel) i j

noncomputable section
variable [interface : CInterface]

theorem named_bound (base : Address) (shape : Tensor.Shape) (name : String)
    (member : name ∈ parameters.map Syntax.Parameter.name) (notCount : name ≠ "count") (notCells : name ≠ "cells") :
    Bound (Arguments.locals parameters (args base shape)) (Entry.locations base) (buffer shape name) := by
  have pointer := Arguments.locals_present parameters (args base shape) name member
  have count := Arguments.locals_present parameters (args base shape) "count" (by decide +kernel)
  intro heap
  simp only [buffer, CBody.eval, CBody.evalWith, CBody.resolve, pointer, count, args, Entry.args, if_neg notCount,
    if_neg notCells, if_neg (by decide +kernel : "count" ≠ "cells"),
    ↓reduceIte, Option.orElse_some, Entry.locations, and_self]

theorem output_bound (base : Address) (shape : Tensor.Shape) :
    Bound (Arguments.locals parameters (args base shape)) (Entry.locations base) (output shape) := by
  have pointer := Arguments.locals_present parameters (args base shape) "J" (by decide +kernel)
  have count := Arguments.locals_present parameters (args base shape) "cells" (by decide +kernel)
  intro heap
  simp only [output, CBody.eval, CBody.evalWith, CBody.resolve, pointer, count, args, Entry.args,
    if_neg (by decide +kernel : "J" ≠ "cells"), if_neg (by decide +kernel : "J" ≠ "count"),
    ↓reduceIte, Option.orElse_some, Entry.locations, and_self]

theorem layout_bound (base : Address) (shape : Tensor.Shape) :
    LayoutBound (Arguments.locals parameters (args base shape)) (Entry.locations base) (layout shape) := by
  intro s ref
  cases ref with
  | here => exact named_bound base shape "x" (by decide +kernel) (by decide +kernel) (by decide +kernel)
  | there ref => cases ref with
    | here => exact named_bound base shape "u" (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there ref => nomatch ref

theorem ready (backing : Heap) (base : Address) (state input : Values shape)
    (bounded : (ArrayProfile.squareJacobianProgram shape).shape.volume < 2 ^ 64) :
    Ready (Arguments.locals parameters (args base shape)) (Entry.locations base)
      (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape)
      (initialHeap backing base state input) := by
  simp only [ArrayProfile.squareJacobianProgram, ArrayProfile.squareProgram, Program.forward,
    Ready, plan]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact (Diagonal.counter_bounds shape bounded).1
    | exact Entry.writable (backingHeap backing base shape) base state input _ (by decide +kernel)
    | exact named_bound base shape _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | skip
  all_goals
    intro s ref i hi j hj
    casesm* Ref _ _
    all_goals exact TensorRegion.member_separate base _ _ (by decide +kernel) i j

end

def profile : Syntax.Function where
  name := "rumoca_square_jacobian"
  parameters := parameters
  statements := ProgramFixture.profile.statements ++ [.diagonal "result" "J" "count" "cells"]

def function (shape : Tensor.Shape) : CTree.Function :=
  ⟨profile.tree.signature,
    (emitDiagonal (ArrayProfile.squareJacobianProgram shape) (plan shape) (layout shape) (output shape)).code ++
      [.ret none], false⟩

theorem body_matches (shape : Tensor.Shape) :
    DiagonalMatches profile (ArrayProfile.squareJacobianProgram shape) (plan shape) (layout shape) (output shape) := rfl

theorem function_tree (shape : Tensor.Shape) : function shape = profile.tree := rfl

theorem valid : profile.valid = true := by decide +kernel

theorem scope : DiagonalScope profile := by
  unfold DiagonalScope
  decide +kernel

def code : String := (function ArrayProfile.stateShape).render

noncomputable section
variable [interface : CInterface]

theorem call_correct (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (found : definitions profile.name = some profile.tree) (backing : Heap) (base : Address)
    (state input coefficients : Values shape)
    (bounded : (ArrayProfile.squareJacobianProgram shape).shape.volume < 2 ^ 64)
    (executed : Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
      (ArrayProfile.environment state input) coefficients) :
    ∃ finalHeap, Reads finalHeap (base.member "J")
        ((ArrayProfile.squareJacobianProgram shape).eval Finite.ops Binary64.positiveZero Binary64.one
          (ArrayProfile.environment state input)) ∧
      Reads finalHeap (base.member "result") coefficients ∧
      (∀ q, DiagonalOutside (Entry.locations base) (ArrayProfile.squareJacobianProgram shape) (plan shape)
        (output shape) q → finalHeap q = initialHeap backing base state input q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling profile.name (Arguments.values parameters (args base shape))
          (initialHeap backing base state input) .done) behavior ↔ behavior = .terminates finalHeap := by
  obtain ⟨finalHeap, matrixReads, coefficientReads, frame, behavior⟩ :=
    diagonal_call_refines profile valid scope (ArrayProfile.squareJacobianProgram shape) (plan shape)
      (layout shape) (output shape) (body_matches shape) definitions library diagonalDefined found
      (args base shape) (arguments_valid base shape bounded) (Entry.locations base)
      (ArrayProfile.environment state input) coefficients (initialHeap backing base state input)
      (layout_bound base shape) (represented backing base state input) (ready backing base state input bounded)
      (reserved base shape) (output_bound base shape) (output_writable backing base state input) bounded executed
  exact ⟨finalHeap, matrixReads, by simpa only [result_buffer, buffer, Entry.locations] using coefficientReads,
    frame, behavior⟩

def StorageContract : Prop := ∀ [interface : CInterface] (definitions : CLoops.Calls.Definitions),
  @Library interface definitions → definitions Diagonal.function.signature.name = some Diagonal.function →
  definitions profile.name = some profile.tree →
  ∀ (shape : Tensor.Shape) (backing : Heap) (base : Address) (state input coefficients : Values shape),
  (ArrayProfile.squareJacobianProgram shape).shape.volume < 2 ^ 64 →
  Finite.Executes (ArrayProfile.squareJacobianProgram shape).coefficients
    (ArrayProfile.environment state input) coefficients →
  ∃ finalHeap, Reads finalHeap (base.member "J")
      ((ArrayProfile.squareJacobianProgram shape).eval Finite.ops Binary64.positiveZero Binary64.one
        (ArrayProfile.environment state input)) ∧
    Reads finalHeap (base.member "result") coefficients ∧
    (∀ q, DiagonalOutside (Entry.locations base) (ArrayProfile.squareJacobianProgram shape) (plan shape)
      (output shape) q → finalHeap q = initialHeap backing base state input q) ∧
    ∀ behavior, (CLoops.Calls.machine definitions).Behaves
      (.calling profile.name (Arguments.values parameters (args base shape))
        (initialHeap backing base state input) .done) behavior ↔ behavior = .terminates finalHeap

def ArtifactContract (source : String) : Prop :=
  (∀ shape : Tensor.Shape,
    DiagonalArtifactContract source profile (ArrayProfile.squareJacobianProgram shape)
      (plan shape) (layout shape) (output shape)) ∧ StorageContract

omit interface in
theorem artifact_correct (source : String) (printed : source = code) : ArtifactContract source := by
  constructor
  · intro shape
    exact diagonal_artifact_correct source profile _ (plan shape) (layout shape) (output shape)
      (printed.trans (congrArg CTree.Function.render (function_tree _))) valid scope (body_matches shape)
  · intro interface definitions library diagonalDefined found shape backing base state input coefficients bounded executed
    exact call_correct definitions library diagonalDefined found backing base state input coefficients bounded executed

end

macro "tensor_expand_diagonal_fixture" : tactic => `(tactic|
  simp [code, function_tree, profile, parameters, ProgramFixture.profile, Lowering.Syntax.Function.tree,
    Lowering.Syntax.Parameter.tree, Lowering.Syntax.ParamKind.type,
    Lowering.Syntax.Statement.tree, Lowering.Syntax.binaryName,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render])

end Rumoca.CTensor.ProgramFixture.DiagonalEntry
