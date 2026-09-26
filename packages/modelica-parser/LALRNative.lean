import Parser.LALR.Generator
import Parser.LALR.EBNF
import Parser.LALR.Safety
import ModelicaParser.Lexer

open _root_.Parser

/-! Native execution evidence for the complete current EBNF on the lexed tokens
of the example sources, plus deeper recursive parser-only fixtures. These tests
are not completeness proofs. -/
open Rumoca Parser.LALR

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def prepare (source : String) : IO (LALR.Frontend.Prepared × LALR.Candidate) := do
  let p ← IO.ofExcept (LALR.Frontend.compile source)
  let c ← IO.ofExcept (LALR.generate p.grammar)
  let facts ← IO.ofExcept (LALR.firstSets p.grammar)
  check (LALR.FirstCheck.validate p.grammar facts) "candidate failed nullable/FIRST validation"
  check (LALR.Safety.validate p.grammar c.tables c.collection.edges.toList)
    "candidate failed structural safety validation"
  return (p, c)

private def parseWord (p : LALR.Frontend.Prepared) (c : LALR.Candidate)
    (word : List Nat) : Except LALR.Failure (List Nat) := do
  let tree ← LALR.parse p.grammar c.tables (20 * (word.length + 1)) word
  return tree.prependWord []

private def sources : List String :=
  ["model M Real x; equation der(x) = 1; end M;",
   "model TensorSquare input Real u[2]; output Real x[2](each start=0, each fixed=true); " ++
     "output Real J[2,2]; equation der(x) = u .* u; J = jacobian (u .* u, u); end TensorSquare;",
   "model ConstantRates Real x; Real y; equation der(x) = 2.5; der(y) = -1; end ConstantRates;",
   "model Nested input Real u[2, n]; output Real x(start = -1.5e3, each fixed = true) = .a.b[1]; " ++
     "equation der(x) = -f(u .* u, (g), true) + 2 * x / (3 - y); z = (); end Nested;"]

def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | throw (IO.userError "usage: lalr-tests Modelica.ebnf")
    let (p, c) ← prepare (← IO.FS.readFile path)
    for source in sources do
      let tokens ← match Rumoca.lex source with
        | .ok tokens => pure tokens
        | .error error => throw (IO.userError (toString error))
      let word := tokens.map (p.encode ∘ Token.symbol)
      check (parseWord p c word == .ok word) s!"Modelica source failed LALR parsing: {source}"
      for i in [:word.length] do
        check (!(parseWord p c (word.take i ++ [p.encode (.literal "unknown")])).isOk)
          s!"accepted an unknown token after {i} tokens"
      check (!(parseWord p c (word ++ [p.grammar.terminals])).isOk) "accepted embedded EOF"
      check (!(parseWord p c (word ++ [p.encode (.literal "end")])).isOk) "accepted a trailing token"
    IO.println s!"Modelica EBNF: {c.canonicalStates} canonical LR(1) states, {c.collection.states.size} LALR(1) states; {sources.length} sources passed"
    let (nested, nc) ← prepare "s : '(' s ')' s | '';"
    for depth in [0, 1, 10, 100, 500] do
      let word := List.replicate depth 0 ++ List.replicate depth 1
      check (parseWord nested nc word == .ok word) s!"recursive parser failed at depth {depth}"
    IO.println "Recursive LALR parser passed through depth 500"
    return (0 : UInt32)
  catch e => IO.eprintln (toString e); return (1 : UInt32)
