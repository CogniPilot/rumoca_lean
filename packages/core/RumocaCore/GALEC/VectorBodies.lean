import RumocaCore.GALEC.CoefficientTerms
import RumocaCore.GALEC.StoreIteration

/-! Rank-one typed loop templates. Extents remain parameters and each loop
body is built once, not once per tensor element. Higher-rank values retain
their existing general semantics; these particular templates are rank one. -/
namespace Rumoca.GALEC.VectorBodies
open Rumoca.Tensor Rumoca.Solve.Tensor Coefficients

def vectorIndex (i : Fin extent) : Fin (Shape.mk [extent]).volume :=
  Coordinate.index (.cons i .nil)

theorem vectorIndex_eq (i : Fin extent) :
    vectorIndex i = ⟨i.val, by simpa only [Shape.volume, List.foldr, Nat.mul_one] using i.isLt⟩ :=
  Fin.ext (Coordinate.vector i)

theorem vectorIndex_reindex (i : Fin extent) :
    vectorIndex i = (finCongr (by simp [Shape.volume] : (Shape.mk [extent]).volume = extent)).symm i :=
  Fin.ext (Coordinate.vector i)

theorem vectorIndex_injective : Function.Injective (vectorIndex (extent := extent)) := by
  intro i j same
  apply Fin.ext
  exact (Coordinate.vector i).symm.trans ((congrArg Fin.val same).trans (Coordinate.vector j))

def vectorSubscripts : Subscripts (extent :: bounds) [extent] :=
  .cons (.iterator .here) .nil

def pointwise (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs ⟨[extent]⟩)
    (expression : ScalarExpr) : Statement inputs outputs bounds :=
  .bounded extent (.assign target vectorSubscripts (expression.toTerm source vectorSubscripts))

def diagonalSubscripts : Subscripts (extent :: bounds) [extent, extent] :=
  .cons (.iterator .here) (.cons (.iterator .here) .nil)

def scatter (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs (matrixShape extent extent))
    (expression : ScalarExpr) : Statement inputs outputs bounds :=
  .bounded extent (.assign target diagonalSubscripts (expression.toTerm source vectorSubscripts))

noncomputable section

theorem pointwise_body_executes (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs ⟨[extent]⟩)
    (expression : ScalarExpr) (input : Env Binary64.Value inputs)
    (iterators : IteratorEnv bounds) (i : Fin extent) (before after : Env Binary64.Value outputs) :
    (Statement.assign target vectorSubscripts (expression.toTerm source vectorSubscripts)).Executes
      Finite.Result Binary64.positiveZero Binary64.one input (iterators.push i) before after ↔
    ∃ tensor, expression.Writes (input source)[vectorIndex i] (vectorIndex i) (before target) tensor ∧
      Env.Updates before target tensor after :=
  expression.assignment_executes source vectorSubscripts target vectorSubscripts input before after
    (iterators.push i)

theorem tensor_pointwise_executes (expression : ScalarExpr)
    (input before after : Value Binary64.Value ⟨[extent]⟩) :
    Iteration.Executes (fun i : Fin extent => expression.Writes (input[vectorIndex i]) (vectorIndex i))
      extent before after ↔
    ∀ i : Fin (Shape.mk [extent]).volume, expression.Executes input[i] after[i] := by
  simp only [vectorIndex_reindex]
  exact (Iteration.executes_reindex
    (by simp [Shape.volume] : (Shape.mk [extent]).volume = extent)
    (fun i => expression.Writes input[i] i) before after).symm.trans
      (expression.pointwise_executes_iff input before after)

/-- Exact partial finite execution of the typed loop, with the whole-store
frame. No total-arithmetic premise or assumed successful execution is used. -/
theorem pointwise_executes (source : Ref inputs ⟨[extent]⟩) (target : Ref outputs ⟨[extent]⟩)
    (expression : ScalarExpr) (input : Env Binary64.Value inputs)
    (iterators : IteratorEnv bounds) (before after : Env Binary64.Value outputs) :
    (pointwise source target expression).Executes Finite.Result Binary64.positiveZero Binary64.one
      input iterators before after ↔
    ∃ tensor, (∀ i : Fin (Shape.mk [extent]).volume, expression.Executes (input source)[i] tensor[i]) ∧
      Env.Updates before target tensor after := by
  change Iteration.Executes (σ := Env Binary64.Value outputs)
    (fun i current next =>
      (Statement.assign target vectorSubscripts (expression.toTerm source vectorSubscripts)).Executes
        Finite.Result Binary64.positiveZero Binary64.one input (iterators.push i) current next)
    extent @before @after ↔ _
  simp_rw [pointwise_body_executes]
  rw [StoreIteration.executes_iff]
  simp only [tensor_pointwise_executes]

theorem scatter_body_executes (source : Ref inputs ⟨[extent]⟩)
    (target : Ref outputs (matrixShape extent extent)) (expression : ScalarExpr)
    (input : Env Binary64.Value inputs) (iterators : IteratorEnv bounds) (i : Fin extent)
    (before after : Env Binary64.Value outputs) :
    (Statement.assign target diagonalSubscripts (expression.toTerm source vectorSubscripts)).Executes
      Finite.Result Binary64.positiveZero Binary64.one input (iterators.push i) before after ↔
    ∃ tensor, expression.Writes (input source)[vectorIndex i] (matrixIndex (i, i)) (before target) tensor ∧
      Env.Updates before target tensor after := by
  simpa only [diagonalSubscripts, vectorSubscripts, Subscripts.eval, IndexTerm.eval,
    IteratorEnv.push, Coordinate.matrix, vectorIndex] using
    expression.assignment_executes source vectorSubscripts target diagonalSubscripts
      input before after (iterators.push i)

/-- The diagonal loop retains all finite scalar domains and the complete
store frame. The target matrix dimensions and input vector rank stay explicit. -/
theorem scatter_executes (source : Ref inputs ⟨[extent]⟩)
    (target : Ref outputs (matrixShape extent extent)) (expression : ScalarExpr)
    (input : Env Binary64.Value inputs) (iterators : IteratorEnv bounds)
    (before after : Env Binary64.Value outputs) :
    (scatter source target expression).Executes Finite.Result Binary64.positiveZero Binary64.one
      input iterators before after ↔
    (∀ i : Fin extent, expression.inDomain (input source)[vectorIndex i]) ∧
    Env.Updates before target
      (TensorWrites.scatterWith
        (fun i => expression.eval Finite.ops Binary64.positiveZero Binary64.one (input source)[vectorIndex i])
        (before target)) after := by
  change Iteration.Executes (σ := Env Binary64.Value outputs)
    (fun i current next =>
      (Statement.assign target diagonalSubscripts (expression.toTerm source vectorSubscripts)).Executes
        Finite.Result Binary64.positiveZero Binary64.one input (iterators.push i) current next)
    extent @before @after ↔ _
  simp_rw [scatter_body_executes]
  rw [StoreIteration.executes_iff]
  have scalarLoop := Iteration.run_guarded_correct
    (fun i state => TensorWrites.write state (matrixIndex (i, i))
      (expression.eval Finite.ops Binary64.positiveZero Binary64.one (input source)[vectorIndex i]))
    (fun i => expression.Writes (input source)[vectorIndex i] (matrixIndex (i, i)))
    (fun i => expression.inDomain (input source)[vectorIndex i])
    (fun i first last => expression.write_iff (input source)[vectorIndex i] (matrixIndex (i, i)) first last)
    (before target)
  simp only [scalarLoop]
  constructor
  · rintro ⟨tensor, ⟨domain, rfl⟩, frame⟩
    exact ⟨domain, frame⟩
  · rintro ⟨domain, frame⟩
    exact ⟨_, ⟨domain, rfl⟩, frame⟩

end
end Rumoca.GALEC.VectorBodies
