import Mathlib.Computability.ContextFreeGrammar

/-! Executable context-free grammars for the in-tree LR parser. Terminal and
nonterminal numbers are separate namespaces. The grammar's terminal count is
reserved for EOF in tables, and is never a token. Language semantics reuse
mathlib's context-free rewriting relation; they do not mention parsing tables. -/
namespace Parser.LALR

abbrev Atom := _root_.Symbol Nat Nat
abbrev Production := ContextFreeRule Nat Nat

structure Grammar where
  terminals : Nat
  nonterminals : Nat
  start : Nat
  productions : Array Production
  deriving Repr, DecidableEq

def Grammar.atomValid (g : Grammar) : Atom → Bool
  | .terminal t => t < g.terminals
  | .nonterminal n => n < g.nonterminals

def Grammar.wellFormed (g : Grammar) : Bool :=
  g.start < g.nonterminals && g.productions.all fun p =>
    p.input < g.nonterminals && p.output.all g.atomValid

def Grammar.semantics (g : Grammar) : ContextFreeGrammar Nat where
  NT := Nat
  initial := g.start
  rules := g.productions.toList.toFinset

def Grammar.Accepts (g : Grammar) (word : List Nat) : Prop :=
  word ∈ g.semantics.language

/-- Parse trees retain production identities and ordered children. These are
candidate syntax values, not proof objects; validity is specified separately. -/
inductive Tree where
  | terminal (token : Nat)
  | node (production nonterminal : Nat) (children : List Tree)
  deriving Repr

def Tree.symbol : Tree → Atom
  | .terminal t => .terminal t
  | .node _ n _ => .nonterminal n

def Tree.word : Tree → List Nat
  | .terminal t => [t]
  | .node _ _ children => children.flatMap Tree.word
  termination_by tree => sizeOf tree

/-- Accumulator traversal avoids repeatedly appending child yields. -/
def Tree.prependWord : Tree → List Nat → List Nat
  | .terminal t, tail => t :: tail
  | .node _ _ children, tail => children.foldr Tree.prependWord tail
  termination_by tree _ => sizeOf tree

def Tree.valid (g : Grammar) : Tree → Bool
  | .terminal t => t < g.terminals
  | .node index n children =>
    match g.productions[index]? with
    | none => false
    | some p => decide (p.input = n ∧ p.output = children.map Tree.symbol) &&
        children.attach.all (fun child => Tree.valid g child.val)
  termination_by tree => sizeOf tree
  decreasing_by
    have h := List.sizeOf_lt_of_mem child.property
    simp only [Tree.node.sizeOf_spec]
    omega

end Parser.LALR
