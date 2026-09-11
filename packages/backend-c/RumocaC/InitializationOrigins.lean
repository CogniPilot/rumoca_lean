import RumocaC.Provenance
import RumocaCore.IR.Solve
import Parser.ProvenanceExtension

/-! Origins for the existing scalar initialization write. Literal conversion,
storage access and assignment are explicit C generation steps, all derived
from the already selected Solve initial plan and declared state. -/
namespace Rumoca.CInitialization
open _root_.Parser.Provenance (Ref Node)

def baseOrigins (model : Solve.Model source) : CProvenance.Table model.dae.flat.context :=
  CProvenance.fromCore model.origins.table

structure Origins (model : Solve.Model source) where
  table : CProvenance.Table model.dae.flat.context
  extension : (baseOrigins model).Extension table
  literal : Ref table
  conversion : Ref table
  target : Ref table
  write : Ref table
  literal_correct : table.get literal =
    .generated .initialLiteral model.origins.completion.index.val #[]
  conversion_correct : table.get conversion =
    .derived .initialConversion literal.index.val #[(model.sourceOrigin .declaration).index.val]
  target_correct : table.get target =
    .generated .stateStorage (model.sourceOrigin .stateName).index.val
      #[(model.sourceOrigin .declaration).index.val]
  write_correct : table.get write =
    .generated .initializeState model.origins.completion.index.val
      #[conversion.index.val, target.index.val]

namespace OriginLowering

private def batch (model : Solve.Model source) :
    Array (Node (_root_.Parser.Provenance.SourceRef model.dae.flat.context.input.inputs)
      CProvenance.Rule) :=
  let first := (baseOrigins model).nodes.size
  #[.generated .initialLiteral model.origins.completion.index.val #[],
    .derived .initialConversion first #[(model.sourceOrigin .declaration).index.val],
    .generated .stateStorage (model.sourceOrigin .stateName).index.val
      #[(model.sourceOrigin .declaration).index.val],
    .generated .initializeState model.origins.completion.index.val #[first + 1, first + 2]]

private theorem batch_prior (model : Solve.Model source) (index : Nat)
    (bound : index < (batch model).size) (parent : Nat)
    (member : parent ∈ (batch model)[index].parents) :
    parent < (baseOrigins model).nodes.size + index := by
  have size : (baseOrigins model).nodes.size = model.origins.table.nodes.size := by
    simp [baseOrigins, CProvenance.fromCore, _root_.Parser.Provenance.Table.mapRule]
  have count : index < 4 := by simpa [batch] using bound
  have initial := model.origins.completion.index.isLt
  have state := (model.sourceOrigin .stateName).index.isLt
  have declaration := (model.sourceOrigin .declaration).index.isLt
  have index_cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases index_cases with rfl | rfl | rfl | rfl <;>
    simp [batch, Node.parents] at member <;> omega

def table (model : Solve.Model source) : CProvenance.Table model.dae.flat.context :=
  (baseOrigins model).append (batch model) (batch_prior model)

private def atIndex (model : Solve.Model source) (index : Fin 4) : Ref (table model) :=
  (baseOrigins model).appendedRef (batch model) (batch_prior model) ⟨index.val, by simp [batch]⟩

def lower (model : Solve.Model source) : Origins model where
  table := table model
  extension := (baseOrigins model).append_extension (batch model) (batch_prior model)
  literal := atIndex model 0
  conversion := atIndex model 1
  target := atIndex model 2
  write := atIndex model 3
  literal_correct := by
    simpa only [table, atIndex, batch] using
      (baseOrigins model).appended_lookup (batch model) (batch_prior model) ⟨0, by simp [batch]⟩
  conversion_correct := by
    simpa only [table, atIndex, batch, _root_.Parser.Provenance.Table.appendedRef, Nat.add_zero,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] using
      (baseOrigins model).appended_lookup (batch model) (batch_prior model) ⟨1, by simp [batch]⟩
  target_correct := by
    simpa only [table, atIndex, batch] using
      (baseOrigins model).appended_lookup (batch model) (batch_prior model) ⟨2, by simp [batch]⟩
  write_correct := by
    simpa only [table, atIndex, batch, _root_.Parser.Provenance.Table.appendedRef,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] using
      (baseOrigins model).appended_lookup (batch model) (batch_prior model) ⟨3, by simp [batch]⟩

end OriginLowering
end Rumoca.CInitialization
