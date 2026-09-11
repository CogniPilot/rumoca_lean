import RumocaCore.Solve.FMI3Origins

/-! One bounded append constructs the unit IVP's operation graph. Canonical
source references are retained without copying source leaves or scalarizing
tensor operations. -/
namespace Rumoca.Solve.FMI3Origins.Lowering
open _root_.Parser.Provenance (Ref Node)

private def batch (solve : Model source) :
    Array (Node (_root_.Parser.Provenance.SourceRef solve.dae.flat.context.input.inputs) Provenance.Rule) :=
  let first := solve.origins.table.nodes.size
  #[.derived .prepareIVP solve.origins.derivative.root.index.val
      #[(solve.sourceOrigin .model).index.val],
    .generated .emptyInputChannel first #[],
    .generated .stateObservation (solve.sourceOrigin .stateName).index.val
      #[(solve.sourceOrigin .declaration).index.val],
    .generated .unitEulerPolicy first #[solve.origins.derivative.root.index.val],
    .generated .independentTime first #[],
    .generated .derivativeName (solve.sourceOrigin .stateName).index.val
      #[solve.origins.derivative.root.index.val],
    .derived .tensorInitial solve.origins.completion.index.val #[],
    .generated .tensorReturn (first + 6) #[],
    .generated .tensorRead (first + 6) #[],
    .derived .tensorDerivative solve.origins.derivative.root.index.val #[],
    .generated .tensorReturn (first + 9) #[],
    .generated .tensorRead (first + 9) #[],
    .generated .tensorReturn (first + 2) #[],
    .generated .tensorRead (solve.sourceOrigin .stateName).index.val #[first + 2]]

private theorem batch_prior (solve : Model source) (index : Nat)
    (bound : index < (batch solve).size) (parent : Nat)
    (member : parent ∈ (batch solve)[index].parents) :
    parent < solve.origins.table.nodes.size + index := by
  have count : index < 14 := by simpa [batch] using bound
  have derivative := solve.origins.derivative.root.index.isLt
  have initial := solve.origins.completion.index.isLt
  have model := (solve.sourceOrigin .model).index.isLt
  have state := (solve.sourceOrigin .stateName).index.isLt
  have declaration := (solve.sourceOrigin .declaration).index.isLt
  have index_cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨
      index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨
      index = 11 ∨ index = 12 ∨ index = 13 := by omega
  rcases index_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;>
    simp [batch, Node.parents] at member <;> omega

def table (solve : Model source) : Provenance.Table solve.dae.flat.context :=
  solve.origins.table.append (batch solve) (batch_prior solve)

theorem extension (solve : Model source) : solve.origins.table.Extension (table solve) :=
  solve.origins.table.append_extension (batch solve) (batch_prior solve)

private def atField (solve : Model source) (field : Field) : Ref (table solve) :=
  solve.origins.table.appendedRef (batch solve) (batch_prior solve)
    ⟨field.index.val, by simp [batch]⟩

def references (solve : Model source) : References (table solve) where
  origin := atField solve
  sourceOrigin field := (extension solve).ref (solve.sourceOrigin field)

theorem references_correct (solve : Model source) : (references solve).Correct solve := by
  constructor
  · intro field; rfl
  · intro field
    have found := solve.origins.table.appended_lookup (batch solve) (batch_prior solve)
      ⟨field.index.val, by simp [batch]⟩
    cases field <;>
      simpa only [references, References.expected, table, atField, Field.index, batch,
        _root_.Parser.Provenance.Table.appendedRef, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] using found

def lower (solve : Model source) : Data solve where
  table := table solve
  extension := extension solve
  references := references solve
  correct := references_correct solve

end Rumoca.Solve.FMI3Origins.Lowering
