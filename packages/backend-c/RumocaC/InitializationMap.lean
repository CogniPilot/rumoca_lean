import RumocaC.InitializationOriginProofs
import RumocaC.MappedStatement

/-! Source maps for the actual shared initialization statement. Exact text
and universal execution share the same required emission. Enclosing function,
file and archive maps are separate composition obligations. -/
namespace Rumoca.CInitialization
open CTree CMemory Printed
open Printed.Document (text mark)
local infixl:65 " <+> " => Document.append

def Emission.document (emission : Emission model target) (depth : Nat := 1) :
    Document (Origin emission.origins.table) :=
  emission.statementOrigins.document depth

theorem Emission.document_render (emission : Emission model target) (depth : Nat) :
    (emission.document depth).render = emission.statement.render depth :=
  emission.statementOrigins.document_render depth

theorem Emission.write_region (emission : Emission model target) (depth : Nat) :
    Region (emission.document depth).body emission.origins.write ""
      (emission.statement.render depth) "" := by
  rw [← emission.document_render depth]
  exact .here _ _

theorem Emission.target_region (emission : Emission model target) (depth : Nat) :
    Region (emission.document depth).body emission.targetOrigins.root
      (String.ofList (List.replicate (2 * depth) ' ')) target.render
      (" = " ++ (value model).render ++ ";\n") := by
  have region := Region.marked (outer := emission.origins.write)
    (Region.left (Region.left (Region.left
      (Region.right (text (Origin := Origin emission.origins.table)
        (String.ofList (List.replicate (2 * depth) ' '))).body emission.targetOrigins.root_region)
      (text " = ").body) emission.valueOrigins.document.body) (text ";\n").body)
  simpa only [Document.body_render, Document.render_text,
    Expr.Origins.document_render, String.append_empty, String.empty_append] using region

theorem Emission.value_region (emission : Emission model target) (depth : Nat) :
    Region (emission.document depth).body emission.valueOrigins.root
      (String.ofList (List.replicate (2 * depth) ' ') ++ target.render ++ " = ")
      (value model).render ";\n" := by
  have region := Region.marked (outer := emission.origins.write)
    (Region.left (Region.right
      (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        emission.targetOrigins.document <+> text " = ").body emission.valueOrigins.root_region)
      (text ";\n").body)
  simpa only [Document.body_render, Document.render_append, Document.render_text,
    Expr.Origins.document_render, String.append_empty, String.empty_append] using region

theorem Emission.value_literal_region (emission : Emission model target) :
    Region emission.valueOrigins.document.body emission.origins.literal
      "((double)" (toString model.initial.initial) ")" := by
  rw [emission.value_checked]
  have region := Region.marked (outer := emission.origins.conversion)
    (Region.left (Region.right
      (text "((" <+> mark emission.origins.conversion (text "double") <+> text ")").body
      (Region.here emission.origins.literal (text (toString model.initial.initial)).body))
      (text ")").body)
  simpa only [Expr.Origins.document, Document.body_render, Document.render_mark,
    Document.render_append, Document.render_text, String.append_empty,
    String.empty_append] using region

theorem Emission.literal_region (emission : Emission model target) (depth : Nat) :
    Region (emission.document depth).body emission.origins.literal
      (String.ofList (List.replicate (2 * depth) ' ') ++ target.render ++ " = " ++ "((double)")
      (toString model.initial.initial) (")" ++ ";\n") := by
  have region := Region.marked (outer := emission.origins.write)
    (Region.left (Region.right
      (text (String.ofList (List.replicate (2 * depth) ' ')) <+>
        emission.targetOrigins.document <+> text " = ").body emission.value_literal_region)
      (text ";\n").body)
  simpa only [Document.body_render, Document.render_append, Document.render_text,
    Expr.Origins.document_render] using region

theorem Emission.document_every (emission : Emission model target) (depth : Nat)
    (check : Origin emission.origins.table → Prop)
    (write : check emission.origins.write) (target : check emission.origins.target)
    (literal : check emission.origins.literal) (conversion : check emission.origins.conversion) :
    (emission.document depth).body.EveryOrigin check := by
  have targetCheck : emission.targetOrigins.Every check :=
    emission.targetOrigins.every_mono (fun ref => ref = emission.origins.target) check
      (fun ref same => by rw [same]; exact target) emission.target_checked
  have valueCheck : emission.valueOrigins.Every check := by
    rw [emission.value_checked]
    simp only [value, Expr.Origins.Every]
    exact ⟨conversion, conversion, literal⟩
  apply (emission.statementOrigins.document_every depth check).mpr
  simp only [statementOrigins, statement, Stmt.Origins.Every]
  exact ⟨write, targetCheck, valueCheck⟩

/-- Every mapped origin is one of the initializer's checked semantic roles,
including all syntax of a generated target access. -/
theorem Emission.map_origins (emission : Emission model target) (depth : Nat)
    (entry : Entry (Origin emission.origins.table))
    (member : entry ∈ (emission.document depth).entries) :
    entry.origin = emission.origins.write ∨ entry.origin = emission.origins.target ∨
      entry.origin = emission.origins.literal ∨ entry.origin = emission.origins.conversion := by
  let check := fun ref => ref = emission.origins.write ∨ ref = emission.origins.target ∨
    ref = emission.origins.literal ∨ ref = emission.origins.conversion
  exact (emission.document depth).body.map_every check
    (emission.document_every depth check (Or.inl rfl) (.inr (.inl rfl))
      (.inr (.inr (.inl rfl))) (.inr (.inr (.inr rfl)))) entry member

theorem Emission.map_ancestry (emission : Emission model target) (depth : Nat)
    (entry : Entry (Origin emission.origins.table))
    (member : entry ∈ (emission.document depth).entries) :
    _root_.Parser.Provenance.TracesTo emission.origins.table entry.origin
        (model.dae.flat.context.site .declaration) ∨
      _root_.Parser.Provenance.TracesTo emission.origins.table entry.origin
        (model.dae.flat.context.site .stateName) := by
  rcases emission.map_origins depth entry member with same | same | same | same
  · exact .inl (same ▸ emission.origins.write_ancestry)
  · exact .inr (same ▸ emission.origins.target_ancestry)
  · exact .inl (same ▸ emission.origins.initial_ancestry)
  · exact .inl (same ▸ emission.origins.conversion_ancestry)

theorem Emission.map_exact (emission : Emission model target) (depth : Nat)
    (entry : Entry (Origin emission.origins.table)) :
    entry ∈ (emission.document depth).entries ↔
    ∃ beforeText segment suffix,
      Region (emission.document depth).body entry.origin beforeText segment suffix ∧
      emission.statement.render depth = beforeText ++ segment ++ suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize ∧
      (emission.statement.render depth).toByteArray.extract entry.start entry.stop =
        segment.toByteArray :=
  emission.statementOrigins.map_exact depth entry

variable [interface : CInterface]

/-- Exact map and text for the same statement whose complete behavior is
proved. This does not assume that an external printer supplied a correct map. -/
theorem Emission.printed_preserves (emission : Emission model target) (depth : Nat)
    (env : CBody.Locals) (heap : Heap) (address : Address) (old : Option Value)
    (double : interface.types "double" = some .float64)
    (located : CBody.lvalue env heap target = some address)
    (storage : heap address = some ⟨.float64, true, old⟩) :
    emission.TraceCorrect ∧
    _root_.Parser.Provenance.TracesTo emission.origins.table emission.origins.write
      (model.dae.flat.context.site .declaration) ∧
    (emission.document depth).render = emission.statement.render depth ∧
    (∀ entry, entry ∈ (emission.document depth).entries →
      _root_.Parser.Provenance.TracesTo emission.origins.table entry.origin
          (model.dae.flat.context.site .declaration) ∨
        _root_.Parser.Provenance.TracesTo emission.origins.table entry.origin
          (model.dae.flat.context.site .stateName)) ∧
    (∀ entry, entry ∈ (emission.document depth).entries ↔
      ∃ beforeText segment suffix,
        Region (emission.document depth).body entry.origin beforeText segment suffix ∧
        emission.statement.render depth = beforeText ++ segment ++ suffix ∧
        entry.start = beforeText.utf8ByteSize ∧
        entry.stop = entry.start + segment.utf8ByteSize ∧
        (emission.statement.render depth).toByteArray.extract entry.start entry.stop =
          segment.toByteArray) ∧
    (∀ behavior, CBody.machine.Behaves
      (.running [emission.statement, .ret none] env heap) behavior ↔
      behavior = .terminates ⟨.void, written heap address⟩) := by
  obtain ⟨trace, ancestry, behaviors⟩ := emission.preserves env heap address old double located storage
  exact ⟨trace, ancestry, emission.document_render depth, emission.map_ancestry depth,
    emission.map_exact depth, behaviors⟩

end Rumoca.CInitialization
