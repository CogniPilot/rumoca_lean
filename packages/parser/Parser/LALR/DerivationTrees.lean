import Parser.LALR.Soundness

/-! Every word in the independent CFG semantics has a valid derivation tree.
This converse of `Tree.valid_derives` is independent of LR tables and their
generator. It supplies the tree used by execution completeness, rather than
requiring callers to supply an unproved tree oracle. -/
namespace Parser.LALR

variable {g : Grammar}

theorem Grammar.produces_valid (wf : g.wellFormed = true)
    (step : g.semantics.Produces before after)
    (valid : ∀ symbol ∈ before, g.atomValid symbol = true) :
    ∀ symbol ∈ after, g.atomValid symbol = true := by
  obtain ⟨p, member, rewrite⟩ := step
  obtain ⟨pre, post, rfl, rfl⟩ := rewrite.exists_parts
  simp only [Grammar.wellFormed, Bool.and_eq_true] at wf
  have rules := wf.2
  have member : p ∈ g.productions := by
    change p ∈ g.productions.toList.toFinset at member
    simpa using (List.mem_toFinset (l := g.productions.toList)).mp member
  have rule := Array.all_eq_true_iff_forall_mem.mp rules p member
  simp only [Bool.and_eq_true] at rule
  have rhs := rule.2
  intro symbol hs
  simp only [List.mem_append] at hs
  rcases hs with (hp | hr) | ht
  · exact valid symbol (by simp only [List.mem_append]; exact Or.inl (Or.inl hp))
  · exact List.all_eq_true.mp rhs symbol hr
  · exact valid symbol (by simp only [List.mem_append]; exact Or.inr ht)

theorem Grammar.derives_valid (wf : g.wellFormed = true)
    (derives : g.semantics.Derives before after)
    (valid : ∀ symbol ∈ before, g.atomValid symbol = true) :
    ∀ symbol ∈ after, g.atomValid symbol = true := by
  induction derives with
  | refl => exact valid
  | tail _ hs ih => exact g.produces_valid wf hs ih

/-- Fold one backwards CFG rewrite into a forest. Prefix/suffix splitting
uses the actual production's symbol sequence, including empty productions. -/
theorem Grammar.produces_forest (step : g.semantics.Produces before after)
    (trees : List Tree) (symbols : trees.map Tree.symbol = after)
    (valid : ∀ tree ∈ trees, tree.valid g = true) :
    ∃ previous : List Tree, previous.map Tree.symbol = before ∧
      previous.flatMap Tree.word = trees.flatMap Tree.word ∧
      ∀ tree ∈ previous, tree.valid g = true := by
  obtain ⟨p, member, rewrite⟩ := step
  obtain ⟨pre, post, rfl, rfl⟩ := rewrite.exists_parts
  obtain ⟨front, back, rfl, hfront, hback⟩ := List.map_eq_append_iff.mp symbols
  obtain ⟨left, children, rfl, hleft, hchildren⟩ := List.map_eq_append_iff.mp hfront
  have member : p ∈ g.productions := by
    change p ∈ g.productions.toList.toFinset at member
    simpa using (List.mem_toFinset (l := g.productions.toList)).mp member
  obtain ⟨index, bound, same⟩ := Array.mem_iff_getElem.mp member
  have lookup : g.productions[index]? = some p := by
    exact (Array.getElem?_eq_getElem bound).trans (congrArg some same)
  refine ⟨left ++ [.node index p.input children] ++ back, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, Tree.symbol,
      hleft, hback]
    rfl
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      Tree.word, List.append_nil]
  · intro tree ht
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with (hl | rfl) | hr
    · exact valid tree (by simp only [List.mem_append]; exact Or.inl (Or.inl hl))
    · simp only [Tree.valid, lookup, ← hchildren]
      apply List.all_eq_true.mpr
      intro child _
      exact valid child.val (by
        simp only [List.mem_append]
        exact Or.inl (Or.inr child.property))
    · exact valid tree (by simp only [List.mem_append]; exact Or.inr hr)

/-- Reconstruct a forest from any CFG derivation to a terminal word. This
holds for arbitrary sentential forms, not just a distinguished start symbol. -/
theorem Grammar.derives_forest (derives : g.semantics.Derives symbols
      (word.map _root_.Symbol.terminal))
    (valid : ∀ token ∈ word, token < g.terminals) :
    ∃ trees : List Tree, trees.map Tree.symbol = symbols ∧
      trees.flatMap Tree.word = word ∧ ∀ tree ∈ trees, tree.valid g = true := by
  induction derives using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨word.map Tree.terminal, ?_, ?_, ?_⟩
    · simp only [List.map_map, Function.comp_def, Tree.symbol]
      rfl
    · simp [List.flatMap_map, Tree.word]
    · intro tree ht
      obtain ⟨token, hmem, rfl⟩ := List.mem_map.mp ht
      simpa only [Tree.valid, decide_eq_true_eq] using valid token hmem
  | head hs _ ih =>
    obtain ⟨trees, symbols, yield, checked⟩ := ih
    obtain ⟨previous, symbols, words, checked⟩ := g.produces_forest hs trees symbols checked
    exact ⟨previous, symbols, words.trans yield, checked⟩

theorem Grammar.accepts_tree (wf : g.wellFormed = true) (accepted : g.Accepts word) :
    ∃ tree : Tree, tree.valid g = true ∧ tree.symbol = .nonterminal g.start ∧
      tree.word = word := by
  have derives : g.semantics.Derives [.nonterminal g.start]
      (word.map _root_.Symbol.terminal) := accepted
  have initial : ∀ symbol ∈ [.nonterminal g.start], g.atomValid symbol = true := by
    intro symbol hs
    obtain rfl := List.mem_singleton.mp hs
    have h := wf
    simp only [Grammar.wellFormed, Bool.and_eq_true] at h
    exact h.1
  have terminals := g.derives_valid wf derives initial
  have valid : ∀ token ∈ word, token < g.terminals := by
    intro token ht
    have bound := terminals (.terminal token) (List.mem_map.mpr ⟨token, ht, rfl⟩)
    exact of_decide_eq_true bound
  obtain ⟨trees, symbols, words, checked⟩ := g.derives_forest derives valid
  obtain ⟨tree, rest, rfl, symbol, empty⟩ := List.map_eq_cons_iff.mp symbols
  have empty : rest = [] := List.map_eq_nil_iff.mp empty
  subst rest
  exact ⟨tree, checked tree (by simp), symbol, by simpa using words⟩

end Parser.LALR
