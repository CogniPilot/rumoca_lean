import Parser.LALR.Located
import Parser.LALR.Progress

/-! Automatic location attachment cannot reject a successful LR parse.
The proof is independent of the grammar, parser tables and source language;
it preserves the complete supplied token payloads, including their spans. -/
namespace Parser.LALR
open Source

variable {source : String}

/-- A tree consumes exactly its corresponding input fragment. Keeping the
prefix and suffix explicit also covers empty nodes at every token boundary. -/
theorem decorate_fragment (input : Array (Located source Nat)) (tree : Tree) :
    ∀ before fragment after,
      input.toList = before ++ fragment ++ after →
      tree.word = fragment.map (·.value) →
      (decorate input tree before.length).2 = (before ++ fragment).length ∧
      ∀ tail, (decorate input tree before.length).1.prependTokens tail = fragment ++ tail := by
  refine Tree.rec
    (motive_1 := fun tree => ∀ before fragment after,
      input.toList = before ++ fragment ++ after →
      tree.word = fragment.map (·.value) →
      (decorate input tree before.length).2 = (before ++ fragment).length ∧
      ∀ tail, (decorate input tree before.length).1.prependTokens tail = fragment ++ tail)
    (motive_2 := fun trees => ∀ before fragment after,
      input.toList = before ++ fragment ++ after →
      trees.flatMap Tree.word = fragment.map (·.value) →
      (decorateForest input trees before.length).2 = (before ++ fragment).length ∧
      ∀ tail, (decorateForest input trees before.length).1.foldr LocatedTree.prependTokens tail =
        fragment ++ tail) ?_ ?_ ?_ ?_ tree
  · intro token before fragment after split words
    cases fragment with
    | nil => simp [Tree.word] at words
    | cons located rest =>
      have parts : token = located.value ∧ [] = rest.map (·.value) := by
        simpa only [Tree.word, List.map_cons, List.cons.injEq] using words
      have empty := List.map_eq_nil_iff.mp parts.2.symm
      subst rest
      have entry : input[before.length]? = some located := by
        rw [← Array.getElem?_toList, split]
        simp only [List.append_assoc, List.singleton_append]
        rw [List.getElem?_append_right (Nat.le_refl _)]
        simp
      rw [parts.1]
      simp [decorate, entry, LocatedTree.prependTokens]
  · intro production nonterminal children ih before fragment after split words
    have result := ih before fragment after split (by simpa only [Tree.word] using words)
    simpa only [decorate, LocatedTree.nodeWithSpan, LocatedTree.prependTokens] using result
  · intro before fragment after _ words
    have empty : fragment = [] := by simpa using words.symm
    subst fragment
    simp [decorateForest]
  · intro tree trees first rest before fragment after split words
    obtain ⟨left, right, equal, leftWord, rightWord⟩ := List.map_eq_append_iff.mp
      (by simpa only [List.flatMap_cons] using words.symm)
    subst fragment
    have leftResult := first before left (right ++ after)
      (by simpa only [List.append_assoc] using split) leftWord.symm
    have rightResult := rest (before ++ left) right after
      (by simpa only [List.append_assoc] using split) rightWord.symm
    constructor
    · simp only [decorateForest, leftResult.1]
      simpa only [List.length_append, Nat.add_assoc] using rightResult.1
    · intro tail
      simp only [decorateForest, leftResult.1, List.foldr_cons,
        rightResult.2, leftResult.2, List.append_assoc]

/-- The actual annotation pass consumes the whole word once and preserves
every leaf's supplied value and span. No well-formedness oracle is required. -/
theorem decorate_complete (input : List (Located source Nat)) (tree : Tree)
    (word : tree.word = input.map (·.value)) :
    (decorate input.toArray tree 0).2 = input.length ∧
      (decorate input.toArray tree 0).1.prependTokens [] = input := by
  have result := decorate_fragment input.toArray tree [] input [] (by simp) word
  exact ⟨by simpa using result.1, by simpa using result.2 []⟩

/-- Every successful parse has a located result for the same concrete tree.
Adding locations has no additional failure or resource precondition. -/
theorem parseLocated_complete {g tables fuel} {input : List (Located source Nat)} {tree}
    (parsed : parse g tables fuel (input.map (·.value)) = .ok tree) :
    ∃ result, parseLocated g tables fuel input = .ok result ∧ result.tree = tree := by
  unfold parseLocated
  split
  · rename_i reason failed
    rw [parsed] at failed
    contradiction
  · rename_i candidate accepted
    have same : candidate = tree := Except.ok.inj (accepted.symm.trans parsed)
    subst candidate
    dsimp only
    split
    · exact ⟨_, rfl, rfl⟩
    · rename_i missing
      exact False.elim (missing ((decorate_complete input tree
        (parse_sound _ _ _ _ _ parsed).1).2))

theorem parseLocated_of_error {g tables fuel} {input : List (Located source Nat)} {reason}
    (failed : parse g tables fuel (input.map (·.value)) = .error reason) :
    parseLocated g tables fuel input = .error reason := by
  unfold parseLocated
  split
  · rename_i error parsed
    have same : error = reason := Except.error.inj (parsed.symm.trans failed)
    subst error
    rfl
  · rename_i tree parsed
    rw [parsed] at failed
    contradiction

/-- The public located entry erases to the exact parser result, including
every error case. This is equality of the executable APIs, not just languages. -/
theorem parseLocated_erases (g tables fuel) (input : List (Located source Nat)) :
    (parseLocated g tables fuel input).map (·.tree) =
      parse g tables fuel (input.map (·.value)) := by
  cases parsed : parse g tables fuel (input.map (·.value)) with
  | error reason => rw [parseLocated_of_error parsed]; rfl
  | ok tree =>
    obtain ⟨result, located, same⟩ := parseLocated_complete parsed
    simp only [located, Except.map, same]

theorem parseLocated_success_iff (g tables fuel) (input : List (Located source Nat)) :
    (∃ result, parseLocated g tables fuel input = .ok result) ↔
      ∃ tree, parse g tables fuel (input.map (·.value)) = .ok tree := by
  constructor
  · rintro ⟨result, _⟩
    exact ⟨result.tree, result.parsed⟩
  · rintro ⟨tree, parsed⟩
    obtain ⟨result, located, _⟩ := parseLocated_complete parsed
    exact ⟨result, located⟩

theorem parseLocated_error_iff (g tables fuel) (input : List (Located source Nat)) (reason) :
    parseLocated g tables fuel input = .error reason ↔
      parse g tables fuel (input.map (·.value)) = .error reason := by
  cases parsed : parse g tables fuel (input.map (·.value)) with
  | error error => simp only [parseLocated_of_error parsed, Except.error.injEq]
  | ok tree =>
    obtain ⟨result, located, _⟩ := parseLocated_complete parsed
    simp [located]

/-- The existing table/resource certificates also certify complete located
parsing at the same transition bound. No location-specific certificate or
extra fuel is required; each successful result retains exact supplied spans. -/
theorem parseLocated_correct
    (items : ItemCheck.validate g tables facts states = true)
    (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : Progress.validate tables edges budget credits = true)
    (input : List (Located source Nat)) :
    (g.Accepts (input.map (·.value)) ↔ ∃ result,
      parseLocated g tables (Progress.bound budget credits (input.map (·.value))) input =
        .ok result) ∧
    ((∃ result,
      parseLocated g tables (Progress.bound budget credits (input.map (·.value))) input =
        .ok result) ∨
      parseLocated g tables (Progress.bound budget credits (input.map (·.value))) input =
        .error .rejected) := by
  constructor
  · exact (Progress.accepts_iff_parse items grammarBudget safety resource _).trans
      (parseLocated_success_iff _ _ _ input).symm
  · rcases Progress.parse_terminates grammarBudget safety resource (input.map (·.value)) with
      accepted | rejected
    · exact .inl ((parseLocated_success_iff _ _ _ input).mpr accepted)
    · exact .inr (parseLocated_of_error rejected)

end Parser.LALR

