import Parser.Provenance

/-! Batch construction preserves all old references and permits dependencies
within the appended block. A lowering need not retain or copy a table prefix
for every generated operation. -/
namespace Parser.Provenance
namespace Table

structure Extension (before after : Table Site Rule) : Prop where
  size_le : before.nodes.size ≤ after.nodes.size
  preserved : ∀ (ref : Ref before),
    after.nodes[ref.index.val]'(Nat.lt_of_lt_of_le ref.index.isLt size_le) = before.get ref

def Extension.ref (extension : Extension before after) (ref : Ref before) : Ref after :=
  ⟨⟨ref.index.val, Nat.lt_of_lt_of_le ref.index.isLt extension.size_le⟩⟩

theorem Extension.lookup (extension : Extension before after) (ref : Ref before) :
    after.get (extension.ref ref) = before.get ref := extension.preserved ref

def append (before : Table Site Rule) (batch : Array (Node Site Rule))
    (prior : ∀ (index : Nat) (bound : index < batch.size) (parent : Nat),
      parent ∈ batch[index].parents → parent < before.nodes.size + index) : Table Site Rule where
  nodes := before.nodes ++ batch
  prior := by
    intro index bound parent member
    by_cases old : index < before.nodes.size
    · rw [Array.getElem_append_left old] at member
      exact before.prior index old parent member
    · have newer : before.nodes.size ≤ index := Nat.le_of_not_lt old
      rw [Array.getElem_append_right newer] at member
      have offset : index - before.nodes.size < batch.size := by
        simp only [Array.size_append] at bound
        omega
      have checked := prior (index - before.nodes.size) offset parent member
      omega

theorem append_extension (before : Table Site Rule) (batch : Array (Node Site Rule)) (prior) :
    Extension before (before.append batch prior) where
  size_le := by simp [append]
  preserved := by intro ref; simp [append, get, Array.getElem_append_left ref.index.isLt]

def appendedRef (before : Table Site Rule) (batch : Array (Node Site Rule)) (prior)
    (index : Fin batch.size) : Ref (before.append batch prior) :=
  ⟨⟨before.nodes.size + index.val, by simp only [append, Array.size_append]; omega⟩⟩

theorem appended_lookup (before : Table Site Rule) (batch : Array (Node Site Rule)) (prior)
    (index : Fin batch.size) :
    (before.append batch prior).get (before.appendedRef batch prior index) = batch[index] := by
  simp [append, get, appendedRef, Array.getElem_append_right]

end Table

theorem TracesTo.extend {before after : Table Site Rule} {ref : Ref before} {site : Site}
    (trace : TracesTo before ref site) (extension : before.Extension after) :
    TracesTo after (extension.ref ref) site := by
  induction trace with
  | source found => exact .source ((extension.lookup _).trans found)
  | @parent ref parent site member trace ih =>
      apply TracesTo.parent (parent := extension.ref parent) _ ih
      change parent.index.val ∈ (after.get (extension.ref ref)).parents
      rw [extension.lookup]
      exact member

end Parser.Provenance
