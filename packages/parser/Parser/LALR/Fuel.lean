import Parser.LALR.Completeness

/-! A grammar-level certificate for a linear fuel bound on valid words.
Nonterminal credits account for unit/empty productions, so the bound does not
assume that every reduction consumes a token. Candidate credits have no proof
authority; every production must satisfy the checked inequality. -/
namespace Parser.LALR.Fuel

structure Budget where
  perToken : Nat
  nonterminals : Array Nat
  deriving Repr

def Budget.weight (b : Budget) : Atom → Int
  | .terminal _ => (b.perToken : Int) - 1
  | .nonterminal n => -((b.nonterminals[n]?.getD 0 : Nat) : Int)

def RuleOK (b : Budget) (p : Production) : Prop :=
  1 + b.weight (.nonterminal p.input) ≤ (p.output.map b.weight).sum

def Conditions (g : Grammar) (b : Budget) : Prop :=
  0 < b.perToken ∧ b.nonterminals.size = g.nonterminals ∧
    ∀ p ∈ g.productions.toList, RuleOK b p

instance : Decidable (Conditions g b) := by
  unfold Conditions RuleOK
  infer_instance

def validate (g : Grammar) (b : Budget) : Bool := decide (Conditions g b)

theorem validate_iff : validate g b = true ↔ Conditions g b := by
  simp only [validate, decide_eq_true_eq]

variable {g : Grammar} {b : Budget}

/-- Universal amortized bound for every valid tree, including recursive and
nullable derivations. The finite production inequalities justify the bound. -/
theorem tree_bound (checked : validate g b = true) (tree : Tree) :
    tree.valid g = true →
      (tree.steps : Int) + b.weight tree.symbol ≤ b.perToken * (tree.word.length : Int) := by
  refine Tree.rec (motive_1 := fun tree => tree.valid g = true →
    (tree.steps : Int) + b.weight tree.symbol ≤ b.perToken * (tree.word.length : Int))
    (motive_2 := fun trees => (∀ tree ∈ trees, tree.valid g = true) →
    ((trees.map Tree.steps).sum : Int) + (trees.map (fun tree => b.weight tree.symbol)).sum ≤
      b.perToken * ((trees.flatMap Tree.word).length : Int)) ?_ ?_ ?_ ?_ tree
  · intro token _
    simp only [Tree.steps, Tree.symbol, Tree.word, Budget.weight, List.length_singleton,
      Int.natCast_one, Int.mul_one]
    omega
  · intro index n children ih valid
    unfold Tree.valid at valid
    split at valid
    · contradiction
    · rename_i p rule
      simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
      obtain ⟨⟨lhs, rhs⟩, childValid⟩ := valid
      have childValid : ∀ child ∈ children, child.valid g = true := by
        simpa using List.all_eq_true.mp childValid
      have production := (validate_iff.mp checked).2.2 p
        (by simpa using Array.mem_of_getElem? rule)
      simp only [RuleOK, lhs, rhs, List.map_map, Function.comp_def] at production
      have childrenBound := ih childValid
      simp only [Tree.steps, Tree.word, Tree.symbol, Int.natCast_add, Int.natCast_one]
      omega
  · intro _
    simp
  · intro tree rest it ir valid
    have ht := it (valid tree (by simp))
    have hr := ir (fun t h => valid t (by simp [h]))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      Int.natCast_add, Int.mul_add]
    omega

def bound (g : Grammar) (b : Budget) (input : List Nat) : Nat :=
  b.perToken * input.length + b.nonterminals[g.start]?.getD 0 + 1

theorem sufficient (checked : validate g b = true) (tree : Tree)
    (valid : tree.valid g = true) (start : tree.symbol = .nonterminal g.start) :
    tree.steps + 1 ≤ bound g b tree.word := by
  have h := tree_bound checked tree valid
  rw [start] at h
  simp only [Budget.weight] at h
  simp only [bound]
  have cast : (b.perToken : Int) * (tree.word.length : Int) =
      ((b.perToken * tree.word.length : Nat) : Int) := by simp
  rw [cast] at h
  omega

end Fuel

theorem parse_more_fuel (g : Grammar) (tables : Tables) (fuel extra : Nat)
    (input : List Nat) (tree : Tree) (parsed : parse g tables fuel input = .ok tree) :
    parse g tables (fuel + extra) input = .ok tree := by
  unfold parse at parsed ⊢
  cases running : run g tables fuel ⟨[], input⟩ with
  | error error => rw [running] at parsed; contradiction
  | ok candidate =>
    rw [running] at parsed
    rw [run_more_fuel g tables fuel extra _ candidate running]
    exact parsed

namespace Fuel

/-- The parser's chosen fuel depends only on the input length and a checked
grammar budget, never on an oracle derivation tree. -/
theorem parse_complete (items : ItemCheck.validate g tables facts states = true)
    (budget : validate g b = true) (accepted : g.Accepts input) :
    ∃ tree, parse g tables (bound g b input) input = .ok tree := by
  obtain ⟨tree, valid, start, yield⟩ :=
    g.accepts_tree (ItemCheck.validate_iff.mp items).1 accepted
  have enough := sufficient budget tree valid start
  have parsed := Completeness.parse_tree items tree valid start
  have more := parse_more_fuel g tables (tree.steps + 1)
    (bound g b tree.word - (tree.steps + 1)) tree.word tree parsed
  rw [Nat.add_sub_of_le enough, yield] at more
  exact ⟨tree, more⟩

theorem accepts_iff_parse (items : ItemCheck.validate g tables facts states = true)
    (budget : validate g b = true) :
    g.Accepts input ↔ ∃ tree, parse g tables (bound g b input) input = .ok tree := by
  constructor
  · exact parse_complete items budget
  · rintro ⟨tree, parsed⟩
    exact (parse_sound g tables _ input tree parsed).2.2

end Fuel
end Parser.LALR
