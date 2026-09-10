import RumocaC.TensorIVPCode
import RumocaC.TensorNamedProofs

/-! Every emitted IVP member has a complete-call contract for its indexed
Solve program. Naming conditions prevent entry/helper collisions. These
contracts require valid storage and ordered finite execution, not an allocator,
solver, FMI lifecycle or native ABI theorem. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor

def ProgramEntry.Contract (entry : ProgramEntry p) (source : String) : Prop :=
  CallArtifactContract source entry.function p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)

theorem ProgramEntry.correct (entry : ProgramEntry p) (valid : entry.function.valid = true) :
    entry.Contract entry.function.tree.render :=
  Named.artifact_correct entry.name entry.parameters p entry.plan entry.layout valid

def DiagonalEntry.Valid (entry : DiagonalEntry p) : Prop :=
  entry.function.valid = true ∧ DiagonalScope entry.function

def DiagonalEntry.Contract (entry : DiagonalEntry p) (source : String) : Prop :=
  DiagonalArtifactContract source entry.function p (Named.Plan.erase p.coefficients entry.plan)
    (Named.Layout.erase entry.layout) entry.output.erase

theorem DiagonalEntry.correct (entry : DiagonalEntry p) (valid : entry.Valid) :
    entry.Contract entry.function.tree.render :=
  Named.diagonal_artifact_correct entry.name entry.parameters p entry.plan entry.layout entry.output valid.1 valid.2

def OptionalDiagonalEntry.Valid : (p : Option (DiagonalProgram Γ shape)) → OptionalDiagonalEntry p → Prop
  | none, _ => True
  | some _, entry => DiagonalEntry.Valid entry

def OptionalDiagonalEntry.Contract : (p : Option (DiagonalProgram Γ shape)) →
    OptionalDiagonalEntry p → Option String → Prop
  | none, _, source => source = none
  | some _, entry, source => ∃ text, source = some text ∧ DiagonalEntry.Contract entry text

theorem OptionalDiagonalEntry.correct (p : Option (DiagonalProgram Γ shape)) (entry : OptionalDiagonalEntry p)
    (valid : OptionalDiagonalEntry.Valid p entry) :
    OptionalDiagonalEntry.Contract p entry ((OptionalDiagonalEntry.function p entry).map (fun f => f.tree.render)) := by
  cases p with
  | none => rfl
  | some p => exact ⟨_, rfl, DiagonalEntry.correct entry valid⟩

def PointwisePlan.Valid (plan : PointwisePlan p) : Prop :=
  plan.initial.function.valid = true ∧ plan.derivative.function.valid = true ∧
    OptionalDiagonalEntry.Valid p.diagonal plan.diagonal ∧
    (plan.functions.map Syntax.Function.name).Nodup ∧
    Diagonal.function.signature.name ∉ plan.functions.map Syntax.Function.name

def PointwisePlan.Contract (plan : PointwisePlan p) (sources : PointwiseSources) : Prop :=
  plan.initial.Contract sources.initial ∧ plan.derivative.Contract sources.derivative ∧
    OptionalDiagonalEntry.Contract p.diagonal plan.diagonal sources.diagonal ∧
    (plan.functions.map Syntax.Function.name).Nodup ∧
    Diagonal.function.signature.name ∉ plan.functions.map Syntax.Function.name

theorem PointwisePlan.correct (plan : PointwisePlan p) (valid : plan.Valid) : plan.Contract plan.sources :=
  ⟨plan.initial.correct valid.1, plan.derivative.correct valid.2.1,
    OptionalDiagonalEntry.correct _ plan.diagonal valid.2.2.1, valid.2.2.2⟩

end Rumoca.CTensor.Lowering
