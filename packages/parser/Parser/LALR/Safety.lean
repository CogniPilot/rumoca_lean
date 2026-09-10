import Parser.LALR.Runtime

/-! A finite structural-safety validator, independent of LR table construction.
Edges are candidate annotations, checked to cover every actual shift and goto.
A backwards calculation verifies reduction symbols and availability of gotos
for every possible predecessor path. State zero is exclusively the stack bottom.
This does not check LR items, completeness, or termination/progress. -/
namespace Parser.LALR.Safety

def state (stack : List Frame) : Nat :=
  (stack.head?).map (·.state) |>.getD 0

/-- States for which a continuation condition holds after popping `symbols`
from the stack, in top-first order. Every incoming edge is checked. Sharing
the recursive vector avoids enumerating exponentially many stack paths. -/
def popStates (count : Nat) (edges : List Edge) : List Atom → Array Bool → Array Bool
  | [], after => after
  | symbol :: rest, after =>
    let next := popStates count edges rest after
    Array.ofFn fun q : Fin count => q.val != 0 && edges.all fun edge =>
      edge.target != q.val || (decide (edge.symbol = symbol) && next[edge.source]?.getD false)

def gotoStates (tables : Tables) (n : Nat) : Array Bool :=
  Array.ofFn fun q : Fin tables.actions.size => (tables.goto q.val n).isSome

def reductionStates (g : Grammar) (tables : Tables) (edges : List Edge) : Array (Array Bool) :=
  g.productions.map fun p =>
    popStates tables.actions.size edges p.output.reverse (gotoStates tables p.input)

def acceptStates (g : Grammar) (tables : Tables) (edges : List Edge) : Array Bool :=
  popStates tables.actions.size edges [.nonterminal g.start]
    (Array.ofFn fun q : Fin tables.actions.size => q.val == 0)

def row (tables : Tables) (q : Nat) : Array (Option Action) :=
  tables.actions[q]?.getD #[]

def gotoRow (tables : Tables) (q : Nat) : Array (Option Nat) :=
  tables.gotos[q]?.getD #[]

def entryOK (g : Grammar) (tables : Tables) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool)
    (q lookahead : Nat) : Prop :=
  match tables.action q lookahead with
  | none => True
  | some (.shift target) => lookahead < g.terminals ∧ ⟨q, .terminal lookahead, target⟩ ∈ edges
  | some (.reduce index) =>
    match g.productions[index]? with
    | none => False
    | some _ => ((reductions[index]?.getD #[])[q]?).getD false = true
  | some .accept => lookahead = g.terminals ∧ (acceptance[q]?).getD false = true

instance : Decidable (entryOK g tables edges reductions acceptance q lookahead) := by
  unfold entryOK
  split <;> try infer_instance
  split <;> infer_instance

def gotoOK (tables : Tables) (edges : List Edge) (q n : Nat) : Prop :=
  match tables.goto q n with
  | none => True
  | some target => ⟨q, .nonterminal n, target⟩ ∈ edges

instance : Decidable (gotoOK tables edges q n) := by
  unfold gotoOK
  split <;> infer_instance

/-- Explicit finite obligations. Extra annotation edges are conservative:
they can make a check fail, but cannot hide an actual table transition. -/
def TableConditions (g : Grammar) (tables : Tables) (edges : List Edge)
    (reductions : Array (Array Bool)) (acceptance : Array Bool) : Prop :=
  g.wellFormed = true ∧ 0 < tables.actions.size ∧
  tables.gotos.size = tables.actions.size ∧
  (∀ edge ∈ edges, edge.source < tables.actions.size ∧
    edge.target < tables.actions.size ∧ edge.target ≠ 0) ∧
  (∀ q : Fin tables.actions.size,
    (row tables q.val).size = g.terminals + 1 ∧
    (gotoRow tables q.val).size = g.nonterminals) ∧
  (∀ q : Fin tables.actions.size, ∀ a : Fin (g.terminals + 1),
    entryOK g tables edges reductions acceptance q.val a.val) ∧
  (∀ q : Fin tables.actions.size, ∀ n : Fin g.nonterminals,
    gotoOK tables edges q.val n.val)

instance : Decidable (TableConditions g tables edges reductions acceptance) := by
  unfold TableConditions
  infer_instance

def Conditions (g : Grammar) (tables : Tables) (edges : List Edge) : Prop :=
  TableConditions g tables edges (reductionStates g tables edges) (acceptStates g tables edges)

instance : Decidable (Conditions g tables edges) :=
  inferInstanceAs (Decidable (TableConditions g tables edges
    (reductionStates g tables edges) (acceptStates g tables edges)))

def validate (g : Grammar) (tables : Tables) (edges : List Edge) : Bool :=
  let reductions := reductionStates g tables edges
  let acceptance := acceptStates g tables edges
  decide (TableConditions g tables edges reductions acceptance)

theorem validate_iff : validate g tables edges = true ↔ Conditions g tables edges := by
  simp only [validate, Conditions, decide_eq_true_eq]

/-- An unbounded concrete stack follows checked automaton edges. This relation
is independent of the finite backwards calculation above. -/
inductive Path (edges : List Edge) : List Frame → Prop
  | nil : Path edges []
  | cons (frame : Frame) (rest : List Frame) (tail : Path edges rest)
      (edge : ⟨state rest, frame.tree.symbol, frame.state⟩ ∈ edges) :
      Path edges (frame :: rest)

theorem Path.tail (h : Path edges (frame :: rest)) : Path edges rest := by
  cases h with | cons _ _ tail _ => exact tail

theorem Path.edge (h : Path edges (frame :: rest)) :
    ⟨state rest, frame.tree.symbol, frame.state⟩ ∈ edges := by
  cases h with | cons _ _ _ edge => exact edge

theorem path_state_lt (hc : Conditions g tables edges) (hp : Path edges stack) :
    state stack < tables.actions.size := by
  cases hp with
  | nil => exact hc.2.1
  | cons frame rest tail he => exact (hc.2.2.2.1 _ he).2.1

theorem path_state_zero (hc : Conditions g tables edges) (hp : Path edges stack) :
    state stack = 0 ↔ stack = [] := by
  cases hp with
  | nil => simp [state]
  | cons frame rest tail he =>
    have hn := (hc.2.2.2.1 _ he).2.2
    simp [state, hn]

/-- Every prefix remaining after a reduction is still a valid automaton path. -/
theorem Path.drop (h : Path edges stack) (count : Nat) : Path edges (stack.drop count) := by
  induction count generalizing stack with
  | zero => exact h
  | succ count ih =>
    cases stack with
    | nil => exact .nil
    | cons frame rest => exact ih h.tail

end Parser.LALR.Safety
