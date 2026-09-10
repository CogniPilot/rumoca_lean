import Parser.LALR.Runtime

/-! The initial LR contract: any returned tree derives exactly the supplied
word in mathlib's CFG semantics, for arbitrary tables and fuel. These proofs
do not assert completeness or rule out internal table errors. -/
namespace Parser.LALR

theorem Tree.prependWord_eq (tree : Tree) :
    ∀ tail, tree.prependWord tail = tree.word ++ tail := by
  refine Tree.rec (motive_1 := fun tree =>
    ∀ tail, tree.prependWord tail = tree.word ++ tail)
    (motive_2 := fun children => ∀ tail,
      children.foldr Tree.prependWord tail = children.flatMap Tree.word ++ tail) ?_ ?_ ?_ ?_ tree
  · intro token tail
    simp only [Tree.prependWord, Tree.word, List.singleton_append]
  · intro index n children ih tail
    simpa only [Tree.prependWord, Tree.word] using ih tail
  · intro tail
    rfl
  · intro head rest ih ir tail
    simp only [List.foldr_cons, ih, ir, List.flatMap_cons, List.append_assoc]

theorem Tree.valid_derives (g : Grammar) (tree : Tree) :
    tree.valid g = true →
      g.semantics.Derives [tree.symbol] (tree.word.map _root_.Symbol.terminal) := by
  refine Tree.rec (motive_1 := fun tree => tree.valid g = true →
    g.semantics.Derives [tree.symbol] (tree.word.map _root_.Symbol.terminal))
    (motive_2 := fun children =>
    (∀ child ∈ children, child.valid g = true) →
      g.semantics.Derives (children.map Tree.symbol)
        ((children.flatMap Tree.word).map _root_.Symbol.terminal)) ?_ ?_ ?_ ?_ tree
  · intro token _
    simp only [Tree.symbol, Tree.word, List.map_cons, List.map_nil]
    exact .refl _
  · intro index n children ih hv
    unfold Tree.valid at hv
    split at hv
    · contradiction
    · rename_i p hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hl, hr⟩, hc⟩ := hv
      have hm : p ∈ g.semantics.rules := by
        exact List.mem_toFinset.mpr (by simpa using Array.mem_of_getElem? hp)
      have hchildren : ∀ child ∈ children, child.valid g = true := by
        simpa using (List.all_eq_true.mp hc)
      have hstep : g.semantics.Produces [.nonterminal p.input] p.output :=
        ⟨p, hm, ContextFreeRule.Rewrites.input_output⟩
      have hstep' : g.semantics.Produces [.nonterminal n] (children.map Tree.symbol) := by
        simpa only [hl, hr] using hstep
      simpa only [Tree.symbol, Tree.word] using hstep'.trans_derives (ih hchildren)
  · intro _
    exact .refl _
  · intro head rest ih ir hv
    have hh := ih (hv head (by simp))
    have ht := ir (fun child hc => hv child (by simp [hc]))
    simpa only [List.map_cons, List.flatMap_cons, List.map_append, List.singleton_append] using
      (hh.append_right (rest.map Tree.symbol)).trans
        (ht.append_left (head.word.map _root_.Symbol.terminal))

theorem checkTree_sound (g : Grammar) (input : List Nat) (tree : Tree)
    (h : checkTree g input tree = true) :
    tree.word = input ∧ tree.symbol = .nonterminal g.start ∧ g.Accepts input := by
  simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hs⟩, hw⟩ := h
  rw [tree.prependWord_eq, List.append_nil] at hw
  refine ⟨hw, hs, ?_⟩
  have hd := Tree.valid_derives g tree hv
  simpa only [hs, hw, Grammar.Accepts, ContextFreeGrammar.mem_language_iff,
    Grammar.semantics] using hd

/-- Soundness is universal in the candidate tables. A generator bug cannot
make a successful checked parse certify a word outside the grammar. -/
theorem parse_sound (g : Grammar) (tables : Tables) (fuel : Nat) (input : List Nat)
    (tree : Tree) (h : parse g tables fuel input = .ok tree) :
    tree.word = input ∧ tree.symbol = .nonterminal g.start ∧ g.Accepts input := by
  unfold parse at h
  cases hr : run g tables fuel ⟨[], input⟩ with
  | error e =>
    rw [hr] at h
    contradiction
  | ok candidate =>
    rw [hr] at h
    change (if checkTree g input candidate then Except.ok candidate
      else Except.error Failure.invalidTree) = Except.ok tree at h
    split at h
    · cases Except.ok.inj h
      exact checkTree_sound g input tree (by assumption)
    · contradiction

/-- Resource monotonicity: increasing fuel cannot change a completed result. -/
theorem run_more_fuel (g : Grammar) (tables : Tables) (fuel extra : Nat)
    (c : Configuration) (tree : Tree) (h : run g tables fuel c = .ok tree) :
    run g tables (fuel + extra) c = .ok tree := by
  induction fuel generalizing c with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run] at h
    rw [Nat.succ_add, run]
    split at h <;> simp only [*]

end Parser.LALR
