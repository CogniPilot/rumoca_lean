import Parser.LALR.Progress

/-! Exact candidate-tree correspondence for the existing bounded LR parser.
No tree uniqueness premise, parser replay, payload reconstruction or frontend
policy is used. Candidate validity and full yield are independent of the tables;
the existing item, safety and resource certificates connect them to execution. -/
namespace Parser.LALR.ExactTree

variable {g : Grammar} {tables : Tables} {facts : Array First} {states : Array ItemSet}
  {edges : List Edge} {budget : Fuel.Budget} {credits : Progress.Credits}

/-- Every independently valid start tree with this exact full yield is the
result of the actual parser at its validated input-size resource bound. -/
theorem parse_valid_tree
    (items : ItemCheck.validate g tables facts states = true)
    (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : Progress.validate tables edges budget credits = true)
    (input : List Nat) (tree : Tree)
    (valid : tree.valid g = true)
    (start : tree.symbol = .nonterminal g.start)
    (yield : tree.word = input) :
    parse g tables (Progress.bound budget credits input) input = .ok tree := by
  have executed := Completeness.parse_tree items tree valid start
  rw [yield, parse_eq_run] at executed
  have later := run_more_fuel g tables (tree.steps + 1)
    (Progress.bound budget credits input) _ tree executed
  have completed := run_more_completed g tables (Progress.bound budget credits input)
    (tree.steps + 1) _
    (Progress.initial_not_exhausted grammarBudget safety resource input)
  rw [Nat.add_comm] at completed
  rw [parse_eq_run, ← completed]
  exact later

/-- Certificate-facing wrapper: `checkTree` checks validity, start symbol and
the entire encoded input, not only a prefix or an existential accepted word.
Encoded terminal numbers establish no inverse token-classifier or AST equality. -/
theorem parse_checked_tree
    (items : ItemCheck.validate g tables facts states = true)
    (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : Progress.validate tables edges budget credits = true)
    (input : List Nat) (tree : Tree)
    (checked : checkTree g input tree = true) :
    parse g tables (Progress.bound budget credits input) input = .ok tree := by
  have parts := checked
  simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at parts
  obtain ⟨⟨valid, start⟩, yield⟩ := parts
  rw [Tree.prependWord_eq, List.append_nil] at yield
  exact parse_valid_tree items grammarBudget safety resource input tree valid start yield

end Parser.LALR.ExactTree
