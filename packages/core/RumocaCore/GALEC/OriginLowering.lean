import RumocaCore.GALEC.UnitOrigins

/-! One append constructs the required generated origins. This is a tensor
operation graph; its size does not depend on any tensor extent. -/
namespace Rumoca.GALEC.OriginLowering
open _root_.Parser.Provenance (Ref Node)
open UnitOrigins (Field References)

private def batch (dae : DAE.Model source) :
    Array (Node (_root_.Parser.Provenance.SourceRef dae.flat.context.input.inputs) Provenance.Rule) :=
  let first := dae.origins.table.nodes.size
  #[.derived .algorithmAdmission dae.origins.expression.root.index.val
      #[dae.flat.origins.model.index.val],
    .generated .unitSamplingPeriod first #[],
    .generated .samplingPeriodValue (first + 1) #[],
    .generated .realStartFallback dae.initializationOrigin.index.val #[],
    .generated .selectUnfixedStart (first + 3) #[],
    .generated .algorithmStartup first #[first + 4, first + 1],
    .generated .algorithmStateInitialization (first + 4) #[dae.flat.origins.state.index.val],
    .generated .algorithmStateWrite (first + 6) #[dae.flat.origins.state.index.val],
    .generated .algorithmRecalibrate first #[dae.flat.origins.declaration.index.val],
    .generated .algorithmDoStep first #[dae.origins.expression.root.index.val, first + 2],
    .generated .algorithmStateRead (first + 9) #[dae.flat.origins.state.index.val],
    .derived .unitAlgorithmIncrement dae.origins.expression.root.index.val #[first + 2],
    .derived .unitAlgorithmStep dae.origins.expression.root.index.val #[first + 10, first + 11],
    .generated .algorithmStateUpdate (first + 12) #[dae.flat.origins.state.index.val],
    .generated .algorithmStateWrite (first + 13) #[dae.flat.origins.state.index.val],
    .generated .algorithmPeriodInitialization (first + 5) #[first + 2],
    .generated .algorithmPeriodWrite (first + 15) #[first + 1]]

private theorem batch_prior (dae : DAE.Model source) (index : Nat)
    (bound : index < (batch dae).size) (parent : Nat)
    (member : parent ∈ (batch dae)[index].parents) :
    parent < dae.origins.table.nodes.size + index := by
  have count : index < 17 := by simpa [batch] using bound
  have prior := dae.origins.extension.size_le
  have residual := dae.origins.expression.root.index.isLt
  have initialization := dae.initializationOrigin.index.isLt
  have model := dae.flat.origins.model.index.isLt
  have declaration := dae.flat.origins.declaration.index.isLt
  have state := dae.flat.origins.state.index.isLt
  have index_cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 := by omega
  rcases index_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [batch, Node.parents] at member <;> omega

def table (dae : DAE.Model source) : Provenance.Table dae.flat.context :=
  dae.origins.table.append (batch dae) (batch_prior dae)

theorem extension (dae : DAE.Model source) : dae.origins.table.Extension (table dae) :=
  dae.origins.table.append_extension (batch dae) (batch_prior dae)

private def atField (dae : DAE.Model source) (field : Field) : Ref (table dae) :=
  dae.origins.table.appendedRef (batch dae) (batch_prior dae)
    ⟨field.index.val, by simp [batch]⟩

def references (dae : DAE.Model source) : References (table dae) where
  origin := atField dae
  stateDeclaration := (extension dae).ref
    (dae.origins.extension.ref dae.flat.origins.declaration)

theorem references_correct (dae : DAE.Model source) : (references dae).Correct dae := by
  constructor
  · simp only [references, _root_.Parser.Provenance.Table.Extension.ref]
  · intro field
    have found := dae.origins.table.appended_lookup (batch dae) (batch_prior dae)
      ⟨field.index.val, by simp [batch]⟩
    cases field <;>
      simpa only [references, References.expected, table, atField, Field.index, batch,
        _root_.Parser.Provenance.Table.appendedRef, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using found

end Rumoca.GALEC.OriginLowering
