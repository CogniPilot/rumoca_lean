import ModelicaParser.Origins
import ModelicaParser.LocatedProofs
import Init.Data.List.Nat.Pairwise

/-! Origin lookup identifies actual parser occurrences, not merely in-bounds
spans. These source facts will be premises of per-IR origin preservation. -/
namespace Rumoca
open _root_.Parser
open _root_.Parser.Provenance

namespace LocatedParsed

theorem field_before (p : LocatedParsed source) (a b : Fin 16) (order : a < b) :
    (p.fieldSpan a).stop ≤ (p.fieldSpan b).start :=
  List.pairwise_iff_getElem.mp p.disjoint a.val b.val
    (by rw [p.location_count]; exact a.isLt)
    (by rw [p.location_count]; exact b.isLt) order

private theorem field_monotone (p : LocatedParsed source) (a b : Fin 16) (order : a ≤ b) :
    (p.fieldSpan a).start ≤ (p.fieldSpan b).start ∧
    (p.fieldSpan a).stop ≤ (p.fieldSpan b).stop := by
  by_cases same : a = b
  · subst b; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · have before := p.field_before a b (by
      have different : a.val ≠ b.val := fun equal => same (Fin.ext equal)
      omega)
    exact ⟨Nat.le_trans (p.fieldSpan a).ordered before,
      Nat.le_trans before (p.fieldSpan b).ordered⟩

/-- The action range includes every intervening terminal, even across trivia. -/
theorem field_range_contains (p : LocatedParsed source) (a b field : Fin 16)
    (left : a ≤ field) (right : field ≤ b) :
    ((p.fieldSpan a).cover (p.fieldSpan b)).Contains (p.fieldSpan field) := by
  have first := p.field_monotone a field left
  have last := p.field_monotone field b right
  exact ⟨Nat.le_trans ((p.fieldSpan a).cover_left (p.fieldSpan b)).1 first.1,
    Nat.le_trans last.2 ((p.fieldSpan a).cover_right (p.fieldSpan b)).2⟩

/-- Composing a production range uses exactly its boundary terminals. -/
theorem field_range_bounds (p : LocatedParsed source) (a b : Fin 16) (order : a ≤ b) :
    ((p.fieldSpan a).cover (p.fieldSpan b)).start = (p.fieldSpan a).start ∧
    ((p.fieldSpan a).cover (p.fieldSpan b)).stop = (p.fieldSpan b).stop := by
  have monotone := p.field_monotone a b order
  simp [Source.Span.cover, monotone.1, monotone.2]

end LocatedParsed

namespace Origins

/-- Every mandatory field reference names the exact source occurrence in the
checked file, including when another input has the same name or contents. -/
theorem lookup (Rule : Type) (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) (field : Field) :
    (table Rule inputs file parsed).get (ref Rule inputs file parsed field) =
      .source (site inputs file parsed field) := by
  cases field <;> simp [table, Table.get, Table.fromSources, ref, sites, Field.index] <;> rfl

theorem source_ancestry (Rule : Type) (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) (field : Field) :
    TracesTo (table Rule inputs file parsed) (ref Rule inputs file parsed field)
      (site inputs file parsed field) := .source (lookup Rule inputs file parsed field)

/-- Identifier leaves match their AST fields; the literal leaf is the written
unit RHS. This is independent of the later name-resolution equalities. -/
theorem leaf_text (p : LocatedParsed source) :
    (span p .modelName).text = p.parsed.ast.name ∧
    (span p .stateName).text = p.parsed.ast.state ∧
    (span p .derivativeName).text = p.parsed.ast.derivativeName ∧
    (span p .constant).text = "1" ∧
    (span p .endName).text = p.parsed.ast.endName := by
  simp only [span, LocatedParsed.fieldSpan_eq_tokenSpan]
  refine ⟨p.modelName_text, p.state_text, p.derivativeName_text, ?_, p.endName_text⟩
  apply p.tokenSpan_text 11 (.literal "1")
  rw [parseTokens_sound _ _ p.parsed.syntactic]
  rfl

/-- Composite source origins contain the terminals of their actual production.
The ranges for the declaration and the equation are deliberately separate. -/
theorem production_ranges (p : LocatedParsed source) :
    (∀ field : Fin 16, (span p .model).Contains (p.fieldSpan field)) ∧
    (∀ field : Fin 16, 2 ≤ field.val → field.val ≤ 4 →
      (span p .declaration).Contains (p.fieldSpan field)) ∧
    (∀ field : Fin 16, 6 ≤ field.val → field.val ≤ 12 →
      (span p .equation).Contains (p.fieldSpan field)) ∧
    (∀ field : Fin 16, 6 ≤ field.val → field.val ≤ 9 →
      (span p .derivative).Contains (p.fieldSpan field)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro field
    exact p.field_range_contains 0 15 field (by omega) (by have := field.isLt; omega)
  · intro field left right; exact p.field_range_contains 2 4 field left right
  · intro field left right; exact p.field_range_contains 6 12 field left right
  · intro field left right; exact p.field_range_contains 6 9 field left right

/-- Exact action boundaries supplement containment: replacing a declaration or
operand range with the whole model would violate this contract. -/
theorem production_boundaries (p : LocatedParsed source) :
    ((span p .model).start = (p.fieldSpan 0).start ∧
      (span p .model).stop = (p.fieldSpan 15).stop) ∧
    ((span p .declaration).start = (p.fieldSpan 2).start ∧
      (span p .declaration).stop = (p.fieldSpan 4).stop) ∧
    ((span p .equation).start = (p.fieldSpan 6).start ∧
      (span p .equation).stop = (p.fieldSpan 12).stop) ∧
    ((span p .derivative).start = (p.fieldSpan 6).start ∧
      (span p .derivative).stop = (p.fieldSpan 9).stop) :=
  ⟨p.field_range_bounds 0 15 (by decide +kernel),
    p.field_range_bounds 2 4 (by decide +kernel),
    p.field_range_bounds 6 12 (by decide +kernel),
    p.field_range_bounds 6 9 (by decide +kernel)⟩

end Origins
end Rumoca
