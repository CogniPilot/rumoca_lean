import RumocaC.TensorNamedCode
import RumocaC.TensorProgramCallContract
import RumocaC.TensorDiagonalProgramContract

/-! Structural correspondence of the named emitter to the existing C lowering,
composed with its printer, complete-call and finite execution contracts. -/
namespace Rumoca.CTensor.Lowering.Named
open CTree Solve.Tensor

theorem Layout.erase_push (b : Buffer shape) (layout : Layout Γ) :
    @Layout.erase (shape :: Γ) (Layout.push b layout) =
      @Lowering.Layout.push shape Γ b.erase (Layout.erase layout) := by
  funext shape r
  cases r <;> rfl

theorem emit_correct (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) :
    (emit p plan layout).statements.map Syntax.Statement.tree =
      (Lowering.emit p (Plan.erase p plan) layout.erase).code ∧
    (emit p plan layout).result.erase = (Lowering.emit p (Plan.erase p plan) layout.erase).result := by
  induction p with
  | ret r => exact ⟨rfl, rfl⟩
  | fill s value next ih =>
    obtain ⟨hc, hr⟩ := ih plan.2 (layout.push plan.1)
    rw [Layout.erase_push] at hc hr
    constructor
    · cases value <;> simp only [emit, Lowering.emit, Plan.erase, List.map_cons,
        Syntax.Statement.tree, Fill.invoke, Fill.function, CAlgorithm.literal, Buffer.erase, hc]
    · exact hr
  | binary op left right next ih =>
    obtain ⟨hc, hr⟩ := ih plan.2 (layout.push plan.1)
    rw [Layout.erase_push] at hc hr
    constructor
    · cases op <;> simp only [emit, Lowering.emit, Plan.erase, List.map_cons,
        Syntax.Statement.tree, CTensor.invoke, Syntax.binaryName, CTensor.function, Layout.erase,
        Buffer.erase, hc]
    · exact hr

theorem function_matches (name : String) (parameters : List Syntax.Parameter)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) :
    Syntax.Matches (function name parameters p plan layout) p (Plan.erase p plan) layout.erase := by
  exact congrArg (· ++ [.ret none]) (emit_correct p plan layout).1

theorem diagonal_matches (name : String) (parameters : List Syntax.Parameter)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) :
    DiagonalMatches (diagonalFunction name parameters p plan layout output) p
      (Plan.erase p.coefficients plan) layout.erase output.erase := by
  obtain ⟨hc, hr⟩ := emit_correct p.coefficients plan layout
  simp only [DiagonalMatches, diagonalFunction, Syntax.Function.tree, List.map_append,
    List.map_cons, List.map_nil, emitDiagonal, hc, List.append_assoc]
  have hp := congrArg Lowering.Buffer.pointer hr
  have hn := congrArg Lowering.Buffer.count hr
  simp only [Syntax.Statement.tree, Diagonal.invoke, Buffer.erase] at hp hn ⊢
  rw [hp, hn]
  rfl

theorem artifact_correct (name : String) (parameters : List Syntax.Parameter)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (valid : (function name parameters p plan layout).valid = true) :
    CallArtifactContract (function name parameters p plan layout).tree.render
      (function name parameters p plan layout) p (Plan.erase p plan) layout.erase :=
  call_artifact_correct _ _ p _ _ rfl valid (function_matches name parameters p plan layout)

theorem diagonal_artifact_correct (name : String) (parameters : List Syntax.Parameter)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape)
    (valid : (diagonalFunction name parameters p plan layout output).valid = true)
    (scope : DiagonalScope (diagonalFunction name parameters p plan layout output)) :
    DiagonalArtifactContract (diagonalFunction name parameters p plan layout output).tree.render
      (diagonalFunction name parameters p plan layout output) p (Plan.erase p.coefficients plan)
      layout.erase output.erase :=
  Lowering.diagonal_artifact_correct _ _ p _ _ _ rfl valid scope
    (diagonal_matches name parameters p plan layout output)

end Rumoca.CTensor.Lowering.Named
