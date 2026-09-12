import Parser.LALR.Fuel
import Parser.LALR.SafetyProofs

/-! A finite potential certificate for progress on all inputs, including
malformed words. Grammar credits pay for reductions; state credits bound the
potential of every concrete stack path. Each actual shift/reduction decreases
the potential, so an input-size fuel bound suffices without trying examples. -/
namespace Parser.LALR.Progress

structure Credits where
  states : Array Nat
  ceiling : Nat
  deriving Repr

def Credits.get (credits : Credits) (q : Nat) : Nat := credits.states[q]?.getD 0

def Conditions (tables : Tables) (edges : List Edge) (budget : Fuel.Budget)
    (credits : Credits) : Prop :=
  credits.states.size = tables.actions.size ∧
  (∀ value ∈ credits.states.toList, value ≤ credits.ceiling) ∧
  ∀ edge ∈ edges, (credits.get edge.source : Int) ≤
    (credits.get edge.target : Int) + budget.weight edge.symbol

instance : Decidable (Conditions tables edges budget credits) := by
  unfold Conditions
  infer_instance

def validate (tables : Tables) (edges : List Edge) (budget : Fuel.Budget)
    (credits : Credits) : Bool := decide (Conditions tables edges budget credits)

theorem validate_iff : validate tables edges budget credits = true ↔
    Conditions tables edges budget credits := by simp only [validate, decide_eq_true_eq]

variable {g : Grammar} {tables : Tables} {edges : List Edge}
  {budget : Fuel.Budget} {credits : Credits}

def weight (budget : Fuel.Budget) (stack : List Frame) : Int :=
  (stack.map fun frame => budget.weight frame.tree.symbol).sum

def potential (budget : Fuel.Budget) (credits : Credits) (c : Configuration) : Int :=
  budget.perToken * (c.remaining.length : Int) + weight budget c.stack + credits.ceiling

theorem vertex_bound (checked : validate tables edges budget credits = true) (q : Nat) :
    credits.get q ≤ credits.ceiling := by
  cases h : credits.states[q]? with
  | none => simp [Credits.get, h]
  | some value =>
    have hv : value ∈ credits.states.toList := by simpa using Array.mem_of_getElem? h
    simpa only [Credits.get, h, Option.getD_some] using (validate_iff.mp checked).2.1 value hv

theorem path_weight (checked : validate tables edges budget credits = true)
    (path : Safety.Path edges stack) :
    (credits.get 0 : Int) - credits.get (Safety.state stack) ≤ weight budget stack := by
  induction path with
  | nil => simp [Safety.state, weight]
  | cons frame rest path edge ih =>
    have bound := (validate_iff.mp checked).2.2 _ edge
    change (credits.get (Safety.state rest) : Int) ≤
      (credits.get frame.state : Int) + budget.weight frame.tree.symbol at bound
    change (credits.get 0 : Int) - credits.get frame.state ≤
      budget.weight frame.tree.symbol + weight budget rest
    omega

theorem potential_nonnegative (checked : validate tables edges budget credits = true)
    (path : Safety.Path edges c.stack) : 0 ≤ potential budget credits c := by
  have stackBound := path_weight checked path
  have vertexBound := vertex_bound checked (Safety.state c.stack)
  have remaining : 0 ≤ (budget.perToken : Int) * (c.remaining.length : Int) :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  unfold potential
  omega

/-- This decrease is about the existing interpreter's data effect. The
production inequality accounts for all popped frames, including empty rules. -/
theorem effect_decreases (checked : Fuel.validate g budget = true)
    (effect : RuntimeProofs.Effect g c (.next next)) :
    potential budget credits next + 1 ≤ potential budget credits c := by
  cases effect with
  | shift stack token rest target finite =>
    simp only [potential, weight, List.map_cons, List.sum_cons, Tree.symbol,
      Fuel.Budget.weight, List.length_cons, Int.natCast_add, Int.natCast_one, Int.mul_add,
      Int.mul_one]
    omega
  | reduce c index target p rule symbols =>
    have production := (Fuel.validate_iff.mp checked).2.2 p
      (by simpa using Array.mem_of_getElem? rule)
    have rhs : (p.output.map budget.weight).sum = weight budget (c.stack.take p.output.length) := by
      have h := congrArg (fun (symbols : List Atom) => (symbols.map budget.weight).sum) symbols
      simpa only [List.map_map, Function.comp_def, List.map_reverse, List.sum_reverse, weight] using h
    have split : weight budget c.stack = weight budget (c.stack.take p.output.length) +
        weight budget (c.stack.drop p.output.length) := by
      have h := congrArg (weight budget) (List.take_append_drop p.output.length c.stack)
      simpa only [weight, List.map_append, List.sum_append] using h.symm
    simp only [Fuel.RuleOK, rhs] at production
    change (budget.perToken : Int) * (c.remaining.length : Int) +
      (budget.weight (.nonterminal p.input) + weight budget (c.stack.drop p.output.length)) +
      credits.ceiling + 1 ≤
      (budget.perToken : Int) * (c.remaining.length : Int) + weight budget c.stack + credits.ceiling
    omega

/-- No well-formed stack path can exhaust this many interpreter iterations,
regardless of whether its remaining tokens belong to the grammar. -/
theorem run_not_exhausted {fuel : Nat} (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : validate tables edges budget credits = true)
    (path : Safety.Path edges c.stack) (bound : potential budget credits c < (fuel : Int)) :
    run g tables fuel c ≠ .error .exhausted := by
  induction fuel generalizing c with
  | zero => have h := potential_nonnegative resource path; omega
  | succ fuel ih =>
    have safe := Safety.step_safe (Safety.validate_iff.mp safety) path
    cases hs : step g tables c with
    | next next =>
      have pathNext : Safety.Path edges next.stack := by
        simpa only [hs, Safety.OutcomeSafe] using safe
      have effect := RuntimeProofs.step_effect g tables c
      rw [hs] at effect
      have decrease := effect_decreases (credits := credits) grammarBudget effect
      simpa only [run, hs] using ih pathNext (by omega)
    | accepted tree => simp [run, hs]
    | failed reason =>
      have reasonEq : reason = .rejected := by simpa only [hs, Safety.OutcomeSafe] using safe
      simp [run, hs, reasonEq]

def bound (budget : Fuel.Budget) (credits : Credits) (input : List Nat) : Nat :=
  budget.perToken * input.length + credits.ceiling + 1

theorem initial_not_exhausted (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : validate tables edges budget credits = true) (input : List Nat) :
    run g tables (bound budget credits input) ⟨[], input⟩ ≠ .error .exhausted := by
  apply run_not_exhausted grammarBudget safety resource .nil
  simp [potential, weight, bound, Int.natCast_add, Int.natCast_mul]
  omega

end Progress

/-- The final tree check is redundant on the actual interpreter's output,
for arbitrary tables. Its invariant supplies the exact input and valid tree. -/
theorem parse_eq_run (g : Grammar) (tables : Tables) (fuel : Nat) (input : List Nat) :
    parse g tables fuel input = run g tables fuel ⟨[], input⟩ := by
  unfold parse
  cases running : run g tables fuel ⟨[], input⟩ with
  | error error => rfl
  | ok tree =>
    have certificate := RuntimeProofs.run_checked (RuntimeProofs.initial g input) running
    change (if checkTree g input tree then Except.ok tree else Except.error Failure.invalidTree) = .ok tree
    rw [certificate]
    rfl

/-- Every completed result, including syntax rejection, is stable under
additional fuel. Exhaustion alone can change when the budget increases. -/
theorem run_more_completed (g : Grammar) (tables : Tables) (fuel extra : Nat)
    (c : Configuration) (finished : run g tables fuel c ≠ .error .exhausted) :
    run g tables (fuel + extra) c = run g tables fuel c := by
  induction fuel generalizing c with
  | zero => exact False.elim (finished rfl)
  | succ fuel ih =>
    cases hs : step g tables c with
    | next next =>
      simp only [run, hs] at finished
      simpa only [Nat.succ_add, run, hs] using ih next finished
    | accepted tree => simp only [Nat.succ_add, run, hs]
    | failed reason => simp only [Nat.succ_add, run, hs]

namespace Progress

variable {g : Grammar} {tables : Tables} {edges : List Edge}
  {budget : Fuel.Budget} {credits : Credits}

theorem parse_not_exhausted (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : validate tables edges budget credits = true) (input : List Nat) :
    parse g tables (bound budget credits input) input ≠ .error .exhausted := by
  rw [parse_eq_run]
  exact initial_not_exhausted grammarBudget safety resource input

theorem parse_terminates (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : validate tables edges budget credits = true) (input : List Nat) :
    (∃ tree, parse g tables (bound budget credits input) input = .ok tree) ∨
      parse g tables (bound budget credits input) input = .error .rejected := by
  have finished := parse_not_exhausted grammarBudget safety resource input
  cases parsed : parse g tables (bound budget credits input) input with
  | ok tree => exact Or.inl ⟨tree, rfl⟩
  | error reason =>
    rcases Safety.validated_parse_safe safety parsed with exhausted | rejected
    · exact False.elim (finished (exhausted ▸ parsed))
    · exact Or.inr (congrArg Except.error rejected)

/-- Complete parsing at the input-size resource bound: all valid words are
accepted, and all invalid words reject without internal errors or exhaustion. -/
theorem accepts_iff_parse (items : ItemCheck.validate g tables facts states = true)
    (grammarBudget : Fuel.validate g budget = true)
    (safety : Safety.validate g tables edges = true)
    (resource : validate tables edges budget credits = true) (input : List Nat) :
    g.Accepts input ↔ ∃ tree, parse g tables (bound budget credits input) input = .ok tree := by
  constructor
  · intro accepted
    obtain ⟨fuel, tree, parsed⟩ := Completeness.parse_complete items accepted
    have runParsed := parsed
    rw [parse_eq_run] at runParsed
    have later := run_more_fuel g tables fuel (bound budget credits input) _ tree runParsed
    have completed := run_more_completed g tables (bound budget credits input) fuel _
      (initial_not_exhausted grammarBudget safety resource input)
    rw [Nat.add_comm] at completed
    refine ⟨tree, ?_⟩
    rw [parse_eq_run, ← completed]
    exact later
  · rintro ⟨tree, parsed⟩
    exact (parse_sound g tables _ input tree parsed).2.2

end Parser.LALR.Progress
