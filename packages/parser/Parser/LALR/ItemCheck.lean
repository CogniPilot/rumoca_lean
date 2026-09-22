import Parser.LALR.Item
import Parser.LALR.LookaheadCandidates

/-! Finite LR-item coverage obligations for the actual action/goto tables.
The annotations are untrusted candidates. Validation requires the augmented
start item, closure, dot advancement, every completed reduction and EOF
acceptance. These conditions are grammar-parametric; no token profile or
language frontend appears here. Execution completeness is a separate theorem
to derive from these obligations, not part of this validator's current claim. -/
namespace Parser.LALR.ItemCheck

def items (states : Array ItemSet) (q : Nat) : ItemSet := states[q]?.getD []

def Valid (g : Grammar) (item : Item) : Prop :=
  match (augment g).productions[item.production]? with
  | none => False
  | some p => item.dot ≤ p.output.length ∧ item.lookahead ≤ g.terminals

instance : Decidable (Valid g item) := by
  unfold Valid
  split <;> infer_instance

def Closed (g : Grammar) (facts : Array First) (state : ItemSet) (item : Item) : Prop :=
  match (augment g).productions[item.production]? with
  | none => False
  | some p => match p.output[item.dot]? with
    | some (.nonterminal n) =>
      ∀ index : Fin g.productions.size, g.productions[index].input = n →
        ∀ lookahead ∈ lookaheads facts (p.output.drop (item.dot + 1)) item.lookahead,
          (⟨index.val, 0, lookahead⟩ : Item) ∈ state
    | _ => True

/-- Decide the same closure proposition using equal-membership structural
candidates. Kernel reduction need not evaluate well-founded sorting; the
generator's ordered lookahead metadata and this proposition stay unchanged. -/
instance : Decidable (Closed g facts state item) := by
  unfold Closed
  split
  · infer_instance
  · rename_i p found
    split
    · rename_i n next
      let candidates : Prop :=
        ∀ index : Fin g.productions.size, g.productions[index].input = n →
          ∀ lookahead ∈ lookaheadCandidates facts (p.output.drop (item.dot + 1)) item.lookahead,
            (⟨index.val, 0, lookahead⟩ : Item) ∈ state
      have candidateDecision : Decidable candidates := by unfold candidates; infer_instance
      exact @decidable_of_iff _ candidates
        (by unfold candidates; simp only [forall_lookaheadCandidates_iff]) candidateDecision
    · infer_instance

/-- A terminal edge must be the actual shift action, not merely an annotation
edge. A nonterminal edge must be the actual goto. Both retain the advanced
item and its lookahead in an existing target state. -/
def Advances (g : Grammar) (tables : Tables) (states : Array ItemSet)
    (q : Nat) (item : Item) : Prop :=
  match nextSymbol (augment g) item with
  | some (.terminal token) => ∃ target : Fin states.size,
      tables.action q token = some (.shift target.val) ∧
        { item with dot := item.dot + 1 } ∈ items states target.val
  | some (.nonterminal n) => ∃ target : Fin states.size,
      tables.goto q n = some target.val ∧
        { item with dot := item.dot + 1 } ∈ items states target.val
  | none =>
    if item.production = g.productions.size then
      item.lookahead = g.terminals ∧ tables.action q g.terminals = some .accept
    else tables.action q item.lookahead = some (.reduce item.production)

instance : Decidable (Advances g tables states q item) := by
  unfold Advances
  split <;> infer_instance

def Conditions (g : Grammar) (tables : Tables) (facts : Array First)
    (states : Array ItemSet) : Prop :=
  g.wellFormed = true ∧
  states.size = tables.actions.size ∧
  FirstCheck.validate g facts = true ∧
  (⟨g.productions.size, 0, g.terminals⟩ : Item) ∈ items states 0 ∧
  ∀ q : Fin states.size, ∀ item ∈ states[q],
    Valid g item ∧ Closed g facts states[q] item ∧ Advances g tables states q.val item

instance : Decidable (Conditions g tables facts states) := by
  unfold Conditions
  infer_instance

def validate (g : Grammar) (tables : Tables) (facts : Array First)
    (states : Array ItemSet) : Bool := decide (Conditions g tables facts states)

theorem validate_iff : validate g tables facts states = true ↔ Conditions g tables facts states := by
  simp only [validate, decide_eq_true_eq]

theorem initial (checked : validate g tables facts states = true) :
    (⟨g.productions.size, 0, g.terminals⟩ : Item) ∈ items states 0 :=
  (validate_iff.mp checked).2.2.2.1

theorem entry (checked : validate g tables facts states = true)
    (q : Fin states.size) (item : Item) (member : item ∈ states[q]) :
    Valid g item ∧ Closed g facts states[q] item ∧ Advances g tables states q.val item :=
  (validate_iff.mp checked).2.2.2.2 q item member

theorem state_bound (member : item ∈ items states q) : q < states.size := by
  by_contra bad
  have outside : states[q]? = none := Array.getElem?_eq_none (by omega)
  simp [items, outside] at member

theorem entry_at (checked : validate g tables facts states = true)
    (member : item ∈ items states q) :
    Valid g item ∧ Closed g facts (items states q) item ∧
      Advances g tables states q item := by
  have bound := state_bound member
  have row : items states q = states[q] := by simp [items, bound]
  rw [row] at member ⊢
  exact entry checked ⟨q, bound⟩ item member

/-- Closure covers a suffix's actual next token, using the existing universal
FIRST theorem rather than trusting the candidate FIRST computation. -/
theorem closure_lookahead (checked : validate g tables facts states = true)
    (q : Fin states.size) (item : Item) (member : item ∈ states[q])
    (p : Production) (production : (augment g).productions[item.production]? = some p)
    (n : Nat) (next : p.output[item.dot]? = some (.nonterminal n))
    (index : Fin g.productions.size) (lhs : g.productions[index].input = n)
    (word : List Nat)
    (derives : g.semantics.Derives (p.output.drop (item.dot + 1))
      (word.map _root_.Symbol.terminal)) :
    (⟨index.val, 0, word.headD item.lookahead⟩ : Item) ∈ states[q] := by
  have closed := (entry checked q item member).2.1
  simp only [Closed, production, next] at closed
  exact closed index lhs (word.headD item.lookahead)
    (FirstProofs.lookahead_complete (validate_iff.mp checked).2.2.1 derives)

end Parser.LALR.ItemCheck
