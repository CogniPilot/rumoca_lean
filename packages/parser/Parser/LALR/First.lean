import Parser.LALR.Grammar

/-! Nullable/FIRST data and an independent finite closure check. The candidate
fixed-point search lives in Generator. Validation requires a conservative
solution of the grammar equations, not equality to that search's output. -/
namespace Parser.LALR

def mergeTerminals (xs ys : List Nat) : List Nat :=
  ((xs ++ ys).mergeSort (· ≤ ·)).eraseDups

structure First where
  nullable : Bool := false
  terminals : List Nat := []
  deriving Repr, DecidableEq, BEq

def firstSequence (facts : Array First) : List Atom → First
  | [] => ⟨true, []⟩
  | .terminal t :: _ => ⟨false, [t]⟩
  | .nonterminal n :: tail =>
    let f := facts[n]?.getD {}
    if f.nullable then
      let rest := firstSequence facts tail
      ⟨rest.nullable, mergeTerminals f.terminals rest.terminals⟩
    else f

def lookaheads (facts : Array First) (symbols : List Atom) (following : Nat) : List Nat :=
  let f := firstSequence facts symbols
  if f.nullable then mergeTerminals f.terminals [following] else f.terminals

namespace FirstCheck

def included (a b : First) : Bool :=
  (!a.nullable || b.nullable) && a.terminals.all b.terminals.contains

/-- A finite closure check. Overapproximations are allowed; omitting
an actual nullable derivation or possible leading terminal is not. -/
def validate (g : Grammar) (facts : Array First) : Bool :=
  g.wellFormed && facts.size == g.nonterminals &&
    facts.all (fun f => f.terminals.all (fun t => t < g.terminals)) &&
    g.productions.all (fun p =>
      included (firstSequence facts p.output) (facts[p.input]?.getD {}))

end FirstCheck
end Parser.LALR
