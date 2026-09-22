import RumocaC.TensorIVPCode
import RumocaC.TensorNamedProofs
import RumocaC.TensorTypedContract

/-! Every emitted IVP member has a complete-call contract for its indexed
Solve program. Naming conditions prevent entry/helper collisions. These
contracts require valid storage and ordered finite execution, not an allocator,
solver, FMI lifecycle or native ABI theorem. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor

def ProgramEntry.Contract (entry : ProgramEntry p) (source : String) : Prop :=
  CallArtifactContract source entry.function p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout) ∧
    TypedCallCorrect entry.function p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)

def ProgramEntry.ContractFor (entry : ProgramEntry p) (source : String) : Prop :=
  CallArtifactContractFor source entry.function p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout) ∧
    TypedCallCorrectFor entry.function p (Named.Plan.erase p entry.plan) (Named.Layout.erase entry.layout)

theorem ProgramEntry.correct_for (entry : ProgramEntry p) (valid : entry.function.valid = true) :
    entry.ContractFor entry.function.tree.render := by
  have checked := Named.artifact_correct_for entry.name entry.parameters p entry.plan entry.layout valid
  exact ⟨checked, typed_call_correct_for checked.2⟩

theorem ProgramEntry.ContractFor.to_full {entry : ProgramEntry p}
    (h : entry.ContractFor source) : entry.Contract source :=
  ⟨CallArtifactContractFor.to_full h.1, TypedCallCorrectFor.to_full h.2⟩

theorem ProgramEntry.correct (entry : ProgramEntry p) (valid : entry.function.valid = true) :
    entry.Contract entry.function.tree.render :=
  ProgramEntry.ContractFor.to_full (ProgramEntry.correct_for entry valid)

def DiagonalEntry.Valid (entry : DiagonalEntry p) : Prop :=
  entry.function.valid = true ∧ DiagonalScope entry.function

def DiagonalEntry.Contract (entry : DiagonalEntry p) (source : String) : Prop :=
  DiagonalArtifactContract source entry.function p (Named.Plan.erase p.coefficients entry.plan)
    (Named.Layout.erase entry.layout) entry.output.erase ∧
    TypedDiagonalCallCorrect entry.function p (Named.Plan.erase p.coefficients entry.plan)
      (Named.Layout.erase entry.layout) entry.output.erase

def DiagonalEntry.ContractFor (entry : DiagonalEntry p) (source : String) : Prop :=
  DiagonalArtifactContractFor source entry.function p (Named.Plan.erase p.coefficients entry.plan)
    (Named.Layout.erase entry.layout) entry.output.erase ∧
    TypedDiagonalCallCorrectFor entry.function p (Named.Plan.erase p.coefficients entry.plan)
      (Named.Layout.erase entry.layout) entry.output.erase

theorem DiagonalEntry.correct_for (entry : DiagonalEntry p) (valid : entry.Valid) :
    entry.ContractFor entry.function.tree.render := by
  have checked :=
    Named.diagonal_artifact_correct_for entry.name entry.parameters p entry.plan entry.layout entry.output valid.1 valid.2
  exact ⟨checked, typed_diagonal_call_correct_for checked.2.2.2⟩

theorem DiagonalEntry.ContractFor.to_full {entry : DiagonalEntry p}
    (h : entry.ContractFor source) : entry.Contract source :=
  ⟨DiagonalArtifactContractFor.to_full h.1, TypedDiagonalCallCorrectFor.to_full h.2⟩

theorem DiagonalEntry.correct (entry : DiagonalEntry p) (valid : entry.Valid) :
    entry.Contract entry.function.tree.render :=
  DiagonalEntry.ContractFor.to_full (DiagonalEntry.correct_for entry valid)

def OptionalDiagonalEntry.Valid : (p : Option (DiagonalProgram Γ shape)) → OptionalDiagonalEntry p → Prop
  | none, _ => True
  | some _, entry => DiagonalEntry.Valid entry

def OptionalDiagonalEntry.Contract : (p : Option (DiagonalProgram Γ shape)) →
    OptionalDiagonalEntry p → Option String → Prop
  | none, _, source => source = none
  | some _, entry, source => ∃ text, source = some text ∧ DiagonalEntry.Contract entry text

def OptionalDiagonalEntry.ContractFor : (p : Option (DiagonalProgram Γ shape)) →
    OptionalDiagonalEntry p → Option String → Prop
  | none, _, source => source = none
  | some _, entry, source => ∃ text, source = some text ∧ DiagonalEntry.ContractFor entry text

theorem OptionalDiagonalEntry.correct_for (p : Option (DiagonalProgram Γ shape)) (entry : OptionalDiagonalEntry p)
    (valid : OptionalDiagonalEntry.Valid p entry) :
    OptionalDiagonalEntry.ContractFor p entry ((OptionalDiagonalEntry.function p entry).map (fun f => f.tree.render)) := by
  cases p with
  | none => rfl
  | some p => exact ⟨_, rfl, DiagonalEntry.correct_for entry valid⟩

theorem OptionalDiagonalEntry.ContractFor.to_full (p : Option (DiagonalProgram Γ shape))
    (entry : OptionalDiagonalEntry p) (source : Option String)
    (h : OptionalDiagonalEntry.ContractFor p entry source) : OptionalDiagonalEntry.Contract p entry source := by
  cases p with
  | none => exact h
  | some p =>
      obtain ⟨text, same, contract⟩ := h
      exact ⟨text, same, DiagonalEntry.ContractFor.to_full contract⟩

theorem OptionalDiagonalEntry.correct (p : Option (DiagonalProgram Γ shape)) (entry : OptionalDiagonalEntry p)
    (valid : OptionalDiagonalEntry.Valid p entry) :
    OptionalDiagonalEntry.Contract p entry ((OptionalDiagonalEntry.function p entry).map (fun f => f.tree.render)) :=
  OptionalDiagonalEntry.ContractFor.to_full p entry _ (OptionalDiagonalEntry.correct_for p entry valid)

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

def PointwisePlan.ContractFor (plan : PointwisePlan p) (sources : PointwiseSources) : Prop :=
  plan.initial.ContractFor sources.initial ∧ plan.derivative.ContractFor sources.derivative ∧
    OptionalDiagonalEntry.ContractFor p.diagonal plan.diagonal sources.diagonal ∧
    (plan.functions.map Syntax.Function.name).Nodup ∧
    Diagonal.function.signature.name ∉ plan.functions.map Syntax.Function.name

theorem PointwisePlan.correct_for (plan : PointwisePlan p) (valid : plan.Valid) : plan.ContractFor plan.sources :=
  ⟨plan.initial.correct_for valid.1, plan.derivative.correct_for valid.2.1,
    OptionalDiagonalEntry.correct_for _ plan.diagonal valid.2.2.1, valid.2.2.2⟩

theorem PointwisePlan.ContractFor.to_full {plan : PointwisePlan p} {sources : PointwiseSources}
    (h : plan.ContractFor sources) : plan.Contract sources :=
  ⟨ProgramEntry.ContractFor.to_full h.1, ProgramEntry.ContractFor.to_full h.2.1,
    OptionalDiagonalEntry.ContractFor.to_full _ _ _ h.2.2.1, h.2.2.2⟩

theorem PointwisePlan.correct (plan : PointwisePlan p) (valid : plan.Valid) : plan.Contract plan.sources :=
  PointwisePlan.ContractFor.to_full (PointwisePlan.correct_for plan valid)

end Rumoca.CTensor.Lowering
