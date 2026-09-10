import RumocaC.TensorProgramContract
import RumocaCore.Array.Solve

/-! One artifact boundary fixture: the existing AD-generated square coefficient
program. Storage annotations enumerate instructions, never tensor coordinates.
This is not an additional production source profile or an allocator. -/
namespace Rumoca.CTensor.ProgramFixture
open CTree Solve.Tensor Lowering

def buffer (shape : Tensor.Shape) (name : String) : Buffer shape := ⟨.id name, .id "count"⟩

def layout (shape : Tensor.Shape) : Layout [shape, shape]
  | _, .here => buffer shape "x"
  | _, .there .here => buffer shape "u"

def plan (shape : Tensor.Shape) : Plan (ArrayProfile.squareJacobianProgram shape).coefficients :=
  ⟨buffer shape "zero", ⟨buffer shape "one", ⟨buffer shape "primal",
    ⟨buffer shape "left", ⟨buffer shape "right", ⟨buffer shape "result", ()⟩⟩⟩⟩⟩⟩

/-- Independent target profile; matching it to the real AD program is checked below. -/
def profile : Lowering.Syntax.Function where
  name := "rumoca_square_jacobian_coefficients"
  parameters := [⟨.input, "x"⟩, ⟨.input, "u"⟩,
    ⟨.output, "zero"⟩, ⟨.output, "one"⟩, ⟨.output, "primal"⟩,
    ⟨.output, "left"⟩, ⟨.output, "right"⟩, ⟨.output, "result"⟩, ⟨.count, "count"⟩]
  statements := [.fill .zero "zero" "count", .fill .one "one" "count",
    .binary .mul "u" "u" "primal" "count", .binary .mul "u" "one" "left" "count",
    .binary .mul "u" "one" "right" "count", .binary .add "left" "right" "result" "count"]

/-- Production emitter under test consumes the prepared Solve instruction sequence. -/
def function (shape : Tensor.Shape) : CTree.Function :=
  ⟨profile.tree.signature,
    (emit (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape)).code ++
      [.ret none], false⟩

theorem body_matches (shape : Tensor.Shape) :
    Lowering.Syntax.Matches profile (ArrayProfile.squareJacobianProgram shape).coefficients
      (plan shape) (layout shape) := rfl

theorem function_tree (shape : Tensor.Shape) : function shape = profile.tree := rfl

theorem result_buffer (shape : Tensor.Shape) :
    (emit (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape)).result =
      buffer shape "result" := rfl

theorem six_calls (shape : Tensor.Shape) : (function shape).body.length = 7 := rfl

theorem valid : profile.valid = true := by decide +kernel

def code : String := (function ArrayProfile.stateShape).render

/-- Exact actual-file contract, universal over rank, extents and finite inputs.
The result parameter is fixed explicitly rather than inferred from a comment. -/
def ArtifactContract (source : String) : Prop := ∀ shape : Tensor.Shape,
  Lowering.ArtifactContract source profile (ArrayProfile.squareJacobianProgram shape).coefficients
    (plan shape) (layout shape) ∧
  (emit (ArrayProfile.squareJacobianProgram shape).coefficients (plan shape) (layout shape)).result =
    buffer shape "result"

theorem artifact_correct (source : String) (printed : source = code) : ArtifactContract source := by
  intro shape
  refine ⟨Lowering.artifact_correct source profile _ (plan shape) (layout shape) ?_ valid (body_matches shape),
    result_buffer shape⟩
  exact printed.trans (congrArg CTree.Function.render (function_tree _))

/-- Normalize only the fixed structured printer before kernel literal reduction. -/
macro "tensor_expand_program_fixture" : tactic => `(tactic|
  simp [code, function_tree, profile, Lowering.Syntax.Function.tree,
    Lowering.Syntax.Parameter.tree, Lowering.Syntax.ParamKind.type,
    Lowering.Syntax.Statement.tree, Lowering.Syntax.binaryName,
    CTree.Function.render, CTree.Signature.render, CTree.Parameter.render,
    CTree.Stmt.render, CTree.Expr.render])

end Rumoca.CTensor.ProgramFixture
