import RumocaCore.IR
import RumocaCore.Solve.IVP
import RumocaCore.Solve.FMI3OriginLowering

/-! Prepared deployment data for the existing unit profile. Names and the
executable kernel have one owner. Choosing the numerical policy happens here,
before the backend serializes the model. No new source cases are admitted. -/
namespace Rumoca.Solve

inductive IntegrationPolicy where
  | unitEuler
  deriving Repr, BEq, DecidableEq

structure FMI3Model (source : AST.Model) where
  solve : Model source
  origins : FMI3Origins.Data solve

def Model.prepareFMI3 (m : Model source) : FMI3Model source :=
  ⟨m, FMI3Origins.Lowering.lower m⟩
def FMI3Model.name (_ : FMI3Model source) : String := source.name
def FMI3Model.stateName (_ : FMI3Model source) : String := source.state
def FMI3Model.timeName (m : FMI3Model source) : String :=
  if m.stateName = "time" then "_rumoca_time" else "time"
def FMI3Model.derivativeName (m : FMI3Model source) : String := "der(" ++ m.stateName ++ ")"
def FMI3Model.policy (_ : FMI3Model source) : IntegrationPolicy := .unitEuler

/-- Tensor representation of the same unit RHS. The initialization program
supplies the default; the unit source contract also permits a host start value. -/
def FMI3Model.problem (_ : FMI3Model source) : IVP := unitIVP

def FMI3Model.originTrace (m : FMI3Model source) : IVP.Origins m.origins.table m.problem :=
  m.origins.references.trace

theorem FMI3Model.time_distinct (m : FMI3Model source) : m.timeName ≠ m.stateName := by
  unfold timeName
  split
  · rename_i h
    rw [h]
    decide
  · exact Ne.symm ‹m.stateName ≠ "time"›

theorem FMI3Model.prepared_solve (m : Model source) : m.prepareFMI3.solve = m := rfl

theorem FMI3Model.rhs_correct (m : FMI3Model source) (ops : Rumoca.Tensor.ScalarOps α) (zero one : α)
    (x : Rumoca.Tensor.Value α Rumoca.Tensor.scalar)
    (u : Rumoca.Tensor.Value α ⟨[0]⟩) :
    m.problem.rhs ops zero one x u = Rumoca.Tensor.Value.fill _ one := rfl

end Rumoca.Solve
