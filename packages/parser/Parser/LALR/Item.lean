import Parser.LALR.Runtime

/-! LR item identities shared by candidate construction and independent table
validation. The augmented rule is used only for EOF acceptance; the runtime
never reduces it. -/
namespace Parser.LALR

structure Item where
  production : Nat
  dot : Nat
  lookahead : Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

abbrev ItemSet := List Item

def nextSymbol (g : Grammar) (item : Item) : Option Atom := do
  let p ← g.productions[item.production]?
  p.output[item.dot]?

def augment (g : Grammar) : Grammar :=
  { g with
    nonterminals := g.nonterminals + 1
    productions := g.productions.push ⟨g.nonterminals, [.nonterminal g.start]⟩ }

end Parser.LALR
