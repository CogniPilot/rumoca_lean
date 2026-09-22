import GALECParser.Parser

/-! GJ02 positional rejection, for all profile names and sources. The legacy
token forms below are proof specifications, never executable parser fallbacks.
Corrected acceptance is the universal `parseTensor_complete` theorem. -/
namespace Rumoca.GALEC.Syntax.DeclarationOrder
open _root_.Parser

inductive Site where
  | input | state | jacobian

def Site.position : Site → Nat
  | .input => 4
  | .state => 11
  | .jacobian => 18

def Site.name : Site → TensorBlock → String
  | .input, b => b.input
  | .state, b => b.state
  | .jacobian, b => b.jacobian

/-- Move just one declaration's dimensions before its name. All other tokens
are retained, including every unresolved name and the entire method bodies. -/
noncomputable def misplaced (site : Site) (b : TensorBlock) : List Token :=
  match site with
  | .input => b.tokens.take 4 ++
      [.literal "[", .literal "2", .literal "]", .ident b.input] ++ b.tokens.drop 8
  | .state => b.tokens.take 11 ++
      [.literal "[", .literal "2", .literal "]", .ident b.state] ++ b.tokens.drop 15
  | .jacobian => b.tokens.take 18 ++
      [.literal "[", .literal "2", .literal ",", .literal "2", .literal "]",
        .ident b.jacobian] ++ b.tokens.drop 24

theorem misplaced_position (site : Site) (b : TensorBlock) :
    (misplaced site b)[site.position]? = some (.literal "[") := by
  cases site <;> rfl

theorem declared_name_position (site : Site) (b : TensorBlock) :
    b.tokens[site.position]? = some (.ident (site.name b)) := by
  cases site <;> rfl

/-- Each old-order spelling differs from every accepted tensor profile, not
just from the same-named corrected block. No resolution premise is needed. -/
theorem misplaced_not_tokens (site : Site) (b candidate : TensorBlock) :
    misplaced site b ≠ candidate.tokens := by
  intro h
  have different := congrArg (fun ts : List Token => ts[site.position]?) h
  dsimp only at different
  rw [misplaced_position, declared_name_position] at different
  cases different

/-- Reject an opening dimension bracket in any declaration-name slot, with
arbitrary other tokens. This also covers combinations of misplaced declarations,
including the previous emitter's spelling with all three declarations misplaced. -/
theorem source_rejected_at_position (site : Site) (tokens : List Token) (source : String)
    (atName : tokens[site.position]? = some (.literal "["))
    (lexical : Scanner.Lexes tensorScanner source.toList tokens) :
    (parseTensor source).isOk = false := by
  cases success : parseTensor source with
  | error _ => rfl
  | ok parsed =>
    have actual := (Scanner.lex_correct tensorScanner source tokens).mpr lexical
    have current := (Scanner.lex_correct tensorScanner source parsed.ast.tokens).mpr parsed.lexical
    have same := Except.ok.inj (actual.symm.trans current)
    have different := congrArg (fun ts : List Token => ts[site.position]?) same
    dsimp only at different
    rw [atName, declared_name_position] at different
    cases different

/-- The actual source entrypoint cannot return any successful result on a
source whose scanner output is any one of the old declaration spellings. -/
theorem source_rejected (site : Site) (b : TensorBlock) (source : String)
    (lexical : Scanner.Lexes tensorScanner source.toList (misplaced site b))
    (parsed : TensorParsed source) : parseTensor source ≠ .ok parsed := by
  intro _
  have old := (Scanner.lex_correct tensorScanner source (misplaced site b)).mpr lexical
  have current := (Scanner.lex_correct tensorScanner source parsed.ast.tokens).mpr parsed.lexical
  exact misplaced_not_tokens site b parsed.ast (Except.ok.inj (old.symm.trans current))

end Rumoca.GALEC.Syntax.DeclarationOrder
