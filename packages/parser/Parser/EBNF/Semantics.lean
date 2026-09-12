import Parser.EBNF

/-! Independent language semantics for the supported EBNF expression syntax.
References use finite derivations, including mutually recursive rules. Neither
parser tables, regular-expression expansion nor preprocessing fuel occur here.
The empty quoted literal denotes epsilon; every other terminal denotes exactly
one lexical symbol. The EBNF text reader's metalanguage contract is separate. -/
namespace Parser.EBNF

inductive Derives (grammar : Grammar) : Expr → List Symbol → Prop where
  | empty : Derives grammar (.terminal (.literal "")) []
  | terminal {symbol} (nonempty : symbol ≠ .literal "") :
      Derives grammar (.terminal symbol) [symbol]
  | ref {name body word} (rule : (name, body) ∈ grammar)
      (derivation : Derives grammar body word) : Derives grammar (.ref name) word
  | seq {left right a b} (first : Derives grammar left a)
      (second : Derives grammar right b) : Derives grammar (.seq left right) (a ++ b)
  | altLeft {left right word} (derivation : Derives grammar left word) :
      Derives grammar (.alt left right) word
  | altRight {left right word} (derivation : Derives grammar right word) :
      Derives grammar (.alt left right) word
  | optionalEmpty {body} : Derives grammar (.optional body) []
  | optionalSome {body word} (derivation : Derives grammar body word) :
      Derives grammar (.optional body) word
  | manyEmpty {body} : Derives grammar (.many body) []
  | manyCons {body first rest} (head : Derives grammar body first)
      (tail : Derives grammar (.many body) rest) :
      Derives grammar (.many body) (first ++ rest)

/-- A grammar starts at its first named rule. Empty grammars accept no words. -/
def Accepts (grammar : Grammar) (word : List Symbol) : Prop :=
  ∃ name body tail, grammar = (name, body) :: tail ∧
    Derives grammar (.ref name) word

/-- Adding rules preserves every finite derivation, even with recursion. -/
theorem Derives.mono {grammar other : Grammar} {expr word}
    (rules : ∀ rule ∈ grammar, rule ∈ other) (derivation : Derives grammar expr word) :
    Derives other expr word := by
  induction derivation with
  | empty => exact .empty
  | terminal nonempty => exact .terminal nonempty
  | ref rule _ ih => exact .ref (rules _ rule) ih
  | seq _ _ left right => exact .seq left right
  | altLeft _ ih => exact .altLeft ih
  | altRight _ ih => exact .altRight ih
  | optionalEmpty => exact .optionalEmpty
  | optionalSome _ ih => exact .optionalSome ih
  | manyEmpty => exact .manyEmpty
  | manyCons _ _ first rest => exact .manyCons first rest

/-- The epsilon spelling is never an actual token in an EBNF word. -/
theorem Derives.nonempty_tokens {grammar expr word}
    (derivation : Derives grammar expr word) :
    ∀ symbol ∈ word, symbol ≠ .literal "" := by
  induction derivation with
  | empty | optionalEmpty | manyEmpty => simp
  | terminal nonempty => simpa using nonempty
  | ref _ _ ih | altLeft _ ih | altRight _ ih | optionalSome _ ih => exact ih
  | seq _ _ left right | manyCons _ _ left right =>
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · exact left symbol member
    · exact right symbol member

end Parser.EBNF
