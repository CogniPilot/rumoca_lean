import Parser.LALR.Grammar

/-! A total table-driven shift/reduce machine. Exhaustion, syntax rejection,
and malformed-table failures are distinct. Candidate trees are checked against
the grammar and exact input. This establishes soundness independently of table
construction; a separate table certificate is still required for completeness
and absence of internal errors. This module is not the production parser yet. -/
namespace Parser.LALR

inductive Action where
  | shift (state : Nat)
  | reduce (production : Nat)
  | accept
  deriving Repr, DecidableEq, BEq

structure Tables where
  actions : Array (Array (Option Action))
  gotos : Array (Array (Option Nat))
  deriving Repr, DecidableEq, BEq

/-- Candidate automaton edge annotations. Validators must check them against
the actual action/goto tables before using them in a proof. -/
structure Edge where
  source : Nat
  symbol : Atom
  target : Nat
  deriving Repr, DecidableEq

def Tables.action (t : Tables) (state lookahead : Nat) : Option Action :=
  (t.actions[state]?).bind (·[lookahead]?) |>.join

def Tables.goto (t : Tables) (state nonterminal : Nat) : Option Nat :=
  (t.gotos[state]?).bind (·[nonterminal]?) |>.join

structure Frame where
  state : Nat
  tree : Tree
  deriving Repr

structure Configuration where
  stack : List Frame
  remaining : List Nat
  deriving Repr

def Configuration.state (c : Configuration) : Nat :=
  (c.stack.head?).map (·.state) |>.getD 0

inductive Failure where
  | exhausted
  | rejected
  | invalidTable
  | invalidTree
  deriving Repr, DecidableEq, BEq

inductive StepResult where
  | next (config : Configuration)
  | accepted (tree : Tree)
  | failed (reason : Failure)
  deriving Repr

def step (g : Grammar) (tables : Tables) (c : Configuration) : StepResult := Id.run do
  let lookahead := c.remaining.headD g.terminals
  if !c.remaining.isEmpty && lookahead ≥ g.terminals then return .failed .rejected
  let some row := tables.actions[c.state]? | return .failed .invalidTable
  let some entry := row[lookahead]? | return .failed .invalidTable
  match entry with
  | none => return .failed .rejected
  | some (.shift state) =>
    if state ≥ tables.actions.size then return .failed .invalidTable
    match c.remaining with
    | [] => return .failed .invalidTable
    | token :: rest => return .next ⟨⟨state, .terminal token⟩ :: c.stack, rest⟩
  | some (.reduce index) =>
    let some p := g.productions[index]? | return .failed .invalidTable
    let count := p.output.length
    let (popped, rest) := c.stack.splitAt count
    if popped.length != count then return .failed .invalidTable
    let children := popped.reverse.map (·.tree)
    if p.output != children.map Tree.symbol then return .failed .invalidTable
    let state := (rest.head?).map (·.state) |>.getD 0
    let some next := tables.goto state p.input | return .failed .invalidTable
    if next ≥ tables.actions.size then return .failed .invalidTable
    return .next ⟨⟨next, .node index p.input children⟩ :: rest, c.remaining⟩
  | some .accept =>
    match c.remaining, c.stack with
    | [], [frame] =>
      if frame.tree.symbol = .nonterminal g.start then return .accepted frame.tree
      else return .failed .invalidTable
    | _, _ => return .failed .invalidTable

def run (g : Grammar) (tables : Tables) : Nat → Configuration → Except Failure Tree
  | 0, _ => .error .exhausted
  | fuel + 1, c =>
    match step g tables c with
    | .next next => run g tables fuel next
    | .accepted tree => .ok tree
    | .failed reason => .error reason

/-- The certificate check binds the tree to the complete input, including EOF.
It is independent of how the candidate tables were constructed. -/
def checkTree (g : Grammar) (input : List Nat) (tree : Tree) : Bool :=
  tree.valid g && decide (tree.symbol = .nonterminal g.start) &&
    decide (tree.prependWord [] = input)

def parse (g : Grammar) (tables : Tables) (fuel : Nat) (input : List Nat) :
    Except Failure Tree := do
  let tree ← run g tables fuel ⟨[], input⟩
  if checkTree g input tree then return tree else throw .invalidTree

end Parser.LALR
