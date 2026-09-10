import Parser.LALR.Soundness

/-! Raw execution preserves parse-tree validity and the complete token word.
Consequently the final tree check cannot fail, even for arbitrary candidate
tables. Structural table safety is a separate, complementary invariant. -/
namespace Parser.LALR.RuntimeProofs

def word (stack : List Frame) : List Nat :=
  stack.reverse.flatMap (fun frame => frame.tree.word)

def Valid (g : Grammar) (stack : List Frame) : Prop :=
  ∀ frame ∈ stack, frame.tree.valid g = true

def Invariant (g : Grammar) (input : List Nat) (c : Configuration) : Prop :=
  Valid g c.stack ∧ word c.stack ++ c.remaining = input

theorem word_append (left right : List Frame) :
    word (left ++ right) = word right ++ word left := by
  simp only [word, List.reverse_append, List.flatMap_append]

theorem word_cons (frame : Frame) (rest : List Frame) :
    word (frame :: rest) = word rest ++ frame.tree.word := by
  simp only [word, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The data effects of successful interpreter steps. This is a sound
abstraction of `step`, not an alternative parsing algorithm. -/
inductive Effect (g : Grammar) : Configuration → StepResult → Prop
  | fail (c : Configuration) (reason : Failure) : Effect g c (.failed reason)
  | shift (stack : List Frame) (token : Nat) (rest : List Nat) (target : Nat)
      (finite : token < g.terminals) :
      Effect g ⟨stack, token :: rest⟩ (.next ⟨⟨target, .terminal token⟩ :: stack, rest⟩)
  | reduce (c : Configuration) (index target : Nat) (p : Production)
      (rule : g.productions[index]? = some p)
      (symbols : p.output = (c.stack.take p.output.length).reverse.map (fun f => f.tree.symbol)) :
      Effect g c (.next ⟨⟨target, .node index p.input
        ((c.stack.take p.output.length).reverse.map (·.tree))⟩ ::
          c.stack.drop p.output.length, c.remaining⟩)
  | accept (frame : Frame) (start : frame.tree.symbol = .nonterminal g.start) :
      Effect g ⟨[frame], []⟩ (.accepted frame.tree)

theorem step_effect (g : Grammar) (tables : Tables) (c : Configuration) :
    Effect g c (step g tables c) := by
  simp only [step, Id.run, bind, pure]
  -- Discharge all error exits; the three remaining cases are data effects.
  repeat' first | exact Effect.fail _ _ | split
  · rename_i token rest hr
    have ht : token < g.terminals := by
      have hi : ¬(!c.remaining.isEmpty && decide (c.remaining.headD g.terminals ≥ g.terminals)) = true :=
        by assumption
      simpa [hr] using hi
    cases c with
    | mk stack remaining =>
      dsimp only [Configuration.remaining] at hr
      subst remaining
      exact .shift _ _ _ _ ht
  · rename_i p hp hlen hs optTarget target htarget hbound
    simp only [List.splitAt_eq]
    apply Effect.reduce _ _ _ _ hp
    simpa [List.splitAt_eq, List.map_map, Function.comp_def] using hs
  · rename_i frame hrem hstack hstart
    cases c with
    | mk stack remaining =>
      dsimp only [Configuration.remaining, Configuration.stack] at hrem hstack
      subst remaining
      subst stack
      exact .accept _ hstart

theorem Effect.preserves (he : Effect g c (.next next)) (hi : Invariant g input c) :
    Invariant g input next := by
  cases he with
  | shift stack token rest target ht =>
    refine ⟨?_, ?_⟩
    · intro frame hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · simpa only [Tree.valid, decide_eq_true_eq] using ht
      · exact hi.1 frame hf
    · simpa only [word_cons, Tree.word, List.singleton_append, List.append_assoc] using hi.2
  | reduce c index target p hp hs =>
    refine ⟨?_, ?_⟩
    · intro frame hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · simp only [Tree.valid, hp, Bool.and_eq_true, decide_eq_true_eq, List.map_map,
          Function.comp_def]
        refine ⟨⟨trivial, hs⟩, ?_⟩
        apply List.all_eq_true.mpr
        intro child _
        have hmem := child.property
        obtain ⟨frame, hf, heq⟩ := List.mem_map.mp hmem
        rw [← heq]
        exact hi.1 frame (List.mem_of_mem_take (List.mem_reverse.mp hf))
      · exact hi.1 frame (List.mem_of_mem_drop hf)
    · have hsplit := word_append (c.stack.take p.output.length) (c.stack.drop p.output.length)
      rw [List.take_append_drop] at hsplit
      change word (⟨target, .node index p.input
        ((c.stack.take p.output.length).reverse.map (·.tree))⟩ ::
          c.stack.drop p.output.length) ++ c.remaining = input
      rw [word_cons]
      have hn : (.node index p.input
          ((c.stack.take p.output.length).reverse.map (·.tree)) : Tree).word =
          word (c.stack.take p.output.length) := by
        simp only [Tree.word, word, List.flatMap_map]
      rw [hn, ← hsplit]
      exact hi.2

theorem Effect.accepts (he : Effect g c (.accepted tree)) (hi : Invariant g input c) :
    checkTree g input tree = true := by
  cases he with
  | accept frame hstart =>
    have hv := hi.1 frame (by simp)
    have hw : frame.tree.word = input := by
      simpa only [word, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] using hi.2
    simp only [checkTree, hv, hstart, Tree.prependWord_eq, List.append_nil, hw,
      decide_true, Bool.and_self]

/-- The runtime's final validity/input check is guaranteed by execution,
independently of whether the candidate table is structurally safe or complete. -/
theorem run_checked (hi : Invariant g input c) (h : run g tables fuel c = .ok tree) :
    checkTree g input tree = true := by
  induction fuel generalizing c with
  | zero => contradiction
  | succ fuel ih =>
    have he := step_effect g tables c
    unfold run at h
    cases hs : step g tables c with
    | next next =>
      rw [hs] at h he
      exact ih (he.preserves hi) h
    | accepted result =>
      rw [hs] at h he
      cases Except.ok.inj h
      exact he.accepts hi
    | failed reason => rw [hs] at h; contradiction

theorem initial (g : Grammar) (input : List Nat) : Invariant g input ⟨[], input⟩ := by
  simp [Invariant, Valid, word]

end Parser.LALR.RuntimeProofs
