import Parser.LALR.Soundness

/-! Grammar-independent typed semantic actions over the actual LR tree and
original token payloads. The frontend supplies an AST relation; it need not use
the concrete grammar tree as its compiler AST, or discard punctuation in a
particular way. All contract fields erase from execution. -/
namespace Parser.LALR

/-- The token-level interface, before a language's lexer and source spans.
Completeness and total rejection must describe this same executable entry. -/
structure TokenParser (Token : Type) where
  grammar : Grammar
  encode : Token → Nat
  run : List Token → Except Failure Tree
  accepts_iff : ∀ tokens, grammar.Accepts (tokens.map encode) ↔
    ∃ tree, run tokens = .ok tree
  checked : ∀ tokens tree, run tokens = .ok tree →
    checkTree grammar (tokens.map encode) tree = true
  terminates : ∀ tokens, (∃ tree, run tokens = .ok tree) ∨
    run tokens = .error .rejected

namespace TokenParser

variable (parser : TokenParser Token)

/-- Retain lexer payloads while selecting their terminal category for LR
execution. This changes neither acceptance nor the returned concrete tree. -/
def contramap (symbol : Other → Token) : TokenParser Other where
  grammar := parser.grammar
  encode := parser.encode ∘ symbol
  run tokens := parser.run (tokens.map symbol)
  accepts_iff tokens := by
    simpa only [List.map_map] using parser.accepts_iff (tokens.map symbol)
  checked tokens tree parsed := by
    simpa only [List.map_map] using parser.checked (tokens.map symbol) tree parsed
  terminates tokens := parser.terminates (tokens.map symbol)

/-- Actions may consume the CST and token payloads. Their independent relation
can retain parentheses, locations and syntactic choices omitted from the AST. -/
structure Actions (AST : Type) where
  Denotes : List Token → AST → Prop
  build : Tree → List Token → Option AST
  language : ∀ tokens ast, Denotes tokens ast →
    parser.grammar.Accepts (tokens.map parser.encode)
  sound : ∀ tree tokens ast,
    checkTree parser.grammar (tokens.map parser.encode) tree = true →
    build tree tokens = some ast → Denotes tokens ast
  complete : ∀ tree tokens ast,
    checkTree parser.grammar (tokens.map parser.encode) tree = true →
    Denotes tokens ast → build tree tokens = some ast

def parseWith (actions : parser.Actions AST) (tokens : List Token) : Option AST :=
  match parser.run tokens with
  | .error _ => none
  | .ok tree => actions.build tree tokens

theorem parseWith_execution (actions : parser.Actions AST)
    (accepted : parser.parseWith actions tokens = some ast) :
    ∃ tree, parser.run tokens = .ok tree ∧
      checkTree parser.grammar (tokens.map parser.encode) tree = true ∧
      actions.build tree tokens = some ast := by
  unfold parseWith at accepted
  split at accepted
  · contradiction
  · rename_i tree parsed
    exact ⟨tree, parsed, parser.checked tokens tree parsed, accepted⟩

theorem parseWith_sound (actions : parser.Actions AST)
    (accepted : parser.parseWith actions tokens = some ast) : actions.Denotes tokens ast := by
  unfold parseWith at accepted
  split at accepted
  · contradiction
  · rename_i tree parsed
    exact actions.sound tree tokens ast (parser.checked tokens tree parsed) accepted

theorem parseWith_complete (actions : parser.Actions AST)
    (denotes : actions.Denotes tokens ast) : parser.parseWith actions tokens = some ast := by
  obtain ⟨tree, parsed⟩ := (parser.accepts_iff tokens).mp (actions.language tokens ast denotes)
  simp only [parseWith, parsed]
  exact actions.complete tree tokens ast (parser.checked tokens tree parsed) denotes

/-- Soundness and completeness reach a user-defined AST relation, with the
actual reusable parser in the conclusion. No profile execution example occurs. -/
theorem parseWith_iff (actions : parser.Actions AST) :
    parser.parseWith actions tokens = some ast ↔ actions.Denotes tokens ast :=
  ⟨parser.parseWith_sound actions, parser.parseWith_complete actions⟩

theorem parseWith_grammar (actions : parser.Actions AST)
    (accepted : parser.parseWith actions tokens = some ast) :
    parser.grammar.Accepts (tokens.map parser.encode) :=
  actions.language tokens ast (parser.parseWith_sound actions accepted)

end TokenParser
end Parser.LALR
