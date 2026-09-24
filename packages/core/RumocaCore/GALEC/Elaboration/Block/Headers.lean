import RumocaCore.GALEC.Elaboration.Methods.Headers

/-! Header-only validation of the current three-method block interface.
Bodies are retained untouched. No method execution, initialization, source
permissions, or whole-block standards conformance follows from these checks. -/
namespace Rumoca.GALEC.Elaboration.Block.Headers
open _root_.Parser
open Elaboration.Methods

def blockName (block : AST.Block) : Option String :=
  match block.name, block.endName with
  | .ident name, .ident ending => if name = ending then some name else none
  | _, _ => none

inductive Named : AST.Block → String → Prop where
  | matched : Named ⟨.ident name, visible, hidden, methods, .ident name⟩ name

theorem blockName_iff (block : AST.Block) (name : String) :
    blockName block = some name ↔ Named block name := by
  constructor
  · intro found
    cases block with
    | mk first visible hidden methods last =>
      cases first <;> cases last <;> simp only [blockName] at found <;> try contradiction
      split at found
      · rename_i same
        cases same
        cases Option.some.inj found
        exact .matched
      · contradiction
  · intro named
    cases named
    simp [blockName]

def Known (name : Token) : Prop :=
  name = .ident "Startup" ∨ name = .ident "Recalibrate" ∨ name = .ident "DoStep"

instance knownDecidable (name : Token) : Decidable (Known name) := by unfold Known; infer_instance

structure Interface where
  name : String
  startup : AST.Method
  recalibrate : AST.Method
  doStep : AST.Method

def read (block : AST.Block) : Option Interface := do
  let name ← blockName block
  let startup ← Headers.select (.ident "Startup") block.methods
  let recalibrate ← Headers.select (.ident "Recalibrate") block.methods
  let doStep ← Headers.select (.ident "DoStep") block.methods
  if ∀ method ∈ block.methods, Known method.name then
    some ⟨name, startup, recalibrate, doStep⟩
  else none

structure Valid (block : AST.Block) (interface : Interface) : Prop where
  name : Named block interface.name
  startup : Headers.Selects (.ident "Startup") block.methods interface.startup
  recalibrate : Headers.Selects (.ident "Recalibrate") block.methods interface.recalibrate
  doStep : Headers.Selects (.ident "DoStep") block.methods interface.doStep
  known : ∀ method ∈ block.methods, Known method.name

theorem read_iff (block : AST.Block) (interface : Interface) :
    read block = some interface ↔ Valid block interface := by
  constructor
  · intro found
    obtain ⟨name, named, remaining⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨startup, started, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨recalibrate, recalibrated, remaining⟩ := Option.bind_eq_some_iff.mp remaining
    obtain ⟨doStep, stepped, checked⟩ := Option.bind_eq_some_iff.mp remaining
    split at checked
    · rename_i known
      cases Option.some.inj checked
      exact ⟨(blockName_iff _ _).mp named, (Headers.select_iff _ _ _).mp started,
        (Headers.select_iff _ _ _).mp recalibrated, (Headers.select_iff _ _ _).mp stepped, known⟩
    · contradiction
  · rintro ⟨named, startup, recalibrate, doStep, known⟩
    simp only [read, (blockName_iff _ _).mpr named,
      (Headers.select_iff _ _ _).mpr startup, (Headers.select_iff _ _ _).mpr recalibrate,
      (Headers.select_iff _ _ _).mpr doStep, if_pos known]
    rfl

/-- Every original method is one of the three exact selected methods. This is
not merely membership of a name in a vocabulary or a check of three prefixes. -/
theorem method_covered (valid : Valid block interface) (member : method ∈ block.methods) :
    method = interface.startup ∨ method = interface.recalibrate ∨ method = interface.doStep := by
  have unique_member (name : Token) {chosen : AST.Method} (selected : Headers.Selects name block.methods chosen)
      (same : method.name = name) : method = chosen := by
    have filtered := (_root_.Parser.UniqueSelection.selects_iff_filter AST.Method.name name _ _).mp selected.1
    have inFilter : method ∈ block.methods.filter (fun m => decide (m.name = name)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨member, same⟩
    rw [filtered] at inFilter
    simpa using inFilter
  rcases valid.known method member with startup | recalibrate | doStep
  · exact Or.inl (unique_member _ valid.startup startup)
  · exact Or.inr (Or.inl (unique_member _ valid.recalibrate recalibrate))
  · exact Or.inr (Or.inr (unique_member _ valid.doStep doStep))

end Rumoca.GALEC.Elaboration.Block.Headers
