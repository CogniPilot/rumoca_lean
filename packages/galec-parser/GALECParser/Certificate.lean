import GALECParser.Parser
import Parser.LALR.ExactTree
import Parser.LALR.ActionCertificate
import Parser.Quotation
import Lean

/-! Kernel-checked parse certificates for concrete GALEC text. Native execution
only proposes constructor data; every equation is submitted to the kernel as
reflexivity, and the typed-action result is certified by syntax-directed
`Denotes` constructors. Quotation instances give no semantic authority. -/
namespace Rumoca.GALEC.Certificate
open Lean Elab Command
open _root_.Parser Parser.Quotation

deriving instance ToExpr for AST.Expr, AST.Reference, AST.Component
deriving instance ToExpr for AST.Condition
deriving instance ToExpr for AST.Statement
deriving instance ToExpr for AST.Kind
deriving instance ToExpr for AST.Declaration
deriving instance ToExpr for AST.Method
deriving instance ToExpr for AST.Block

/-- The original payload tokens are retained; terminal encoding is not inverted. -/
theorem token_tree (tokens : List Token) (tree : LALR.Tree)
    (checked : LALR.checkTree Generated.grammar
      (tokens.map (Generated.encode ∘ Token.symbol)) tree = true) :
    StructureBridge.parser.run tokens = .ok tree := by
  have result := LALR.ExactTree.parse_checked_tree Generated.items_checked
    Generated.budget_checked Generated.safety_checked Generated.progress_checked
    (tokens.map (Generated.encode ∘ Token.symbol)) tree checked
  simpa only [StructureBridge.parser, LALR.TokenParser.contramap,
    Generated.tokenParser, Generated.parseSymbols, Generated.parse,
    Generated.fuel_eq, List.map_map] using result

/-- Compose separately kernel-checked equations without replaying LR tables in
definitional equality. The action result denotes the actual accepted tree. -/
theorem witness_of_certificates (source : String) (tokens : List Token)
    (tree : LALR.Tree) (value : LALR.Frontend.Structure.Value Token) (ast : AST.Block)
    (lexed : Scanner.lex Syntax.scanner source = .ok tokens)
    (checked : LALR.checkTree Generated.grammar
      (tokens.map (Generated.encode ∘ Token.symbol)) tree = true)
    (built : StructureBridge.build tree tokens = some value)
    (denotes : LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
      (.ref "block") value ast) :
    Syntax.Witness source ast :=
  ⟨tokens, tree, value, (Scanner.lex_correct _ _ _).mp lexed, token_tree tokens tree checked,
    built, denotes⟩

theorem parse_of_certificates (source : String) (tokens : List Token)
    (tree : LALR.Tree) (value : LALR.Frontend.Structure.Value Token) (ast : AST.Block)
    (lexed : Scanner.lex Syntax.scanner source = .ok tokens)
    (checked : LALR.checkTree Generated.grammar
      (tokens.map (Generated.encode ∘ Token.symbol)) tree = true)
    (built : StructureBridge.build tree tokens = some value)
    (denotes : LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
      (.ref "block") value ast) :
    ∃ result, Syntax.parse source = .ok result ∧ result.ast = ast :=
  (Syntax.success_iff source ast).mpr
    (witness_of_certificates source tokens tree value ast lexed checked built denotes)

/-- Native evaluation of the closed source term, used only to propose tokens,
tree, structural value and AST. It is confined to this elaborator; a wrong
result can only make certification fail, because every equation below is
stated about the elaborated term itself and checked by the kernel. -/
private unsafe def evaluateSource (source : Expr) : TermElabM String :=
  Meta.evalExpr String (mkConst ``String) source

/-- `certify_source name text` evaluates the closed `String` term `text`,
proposes its tokens, tree, structural value and AST, and adds the kernel-checked
declarations `name.lexed`, `name.checked`, `name.structure_built`,
`name.denotes`, `name.witness` and `name.parsed` about `name.source := text`. -/
elab "certify_source " certificateName:ident text:term : command => do
  let root := (← getCurrNamespace) ++ certificateName.getId
  let sourceId := mkIdent (root.str "source")
  let sourceExpr ← liftTermElabM do
    let e ← Term.elabTermEnsuringType text (mkConst ``String)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  liftTermElabM do
    addDecl (.defnDecl {
      name := sourceId.getId
      levelParams := []
      type := mkConst ``String
      value := sourceExpr
      hints := .abbrev
      safety := .safe })
  let source ← liftTermElabM (unsafe evaluateSource sourceExpr)
  let tokens ← match Scanner.lex Syntax.scanner source with
    | .ok tokens => pure tokens
    | .error diagnostic => throwError "scanner rejected source: {diagnostic}"
  let tree ← match StructureBridge.parser.run tokens with
    | .ok tree => pure tree
    | .error _ => throwError "parser rejected source"
  let structuralValue ← match StructureBridge.build tree tokens with
    | some structuralValue => pure structuralValue
    | none => throwError "structural conversion rejected tree"
  let ast ← match LALR.Frontend.StructuralActions.run Structural.rules
      Token.symbol (.ref "block") structuralValue with
    | some ast => pure ast
    | none => throwError "actions rejected structural value"
  let tokensId := mkIdent (root.str "tokens")
  let treeId := mkIdent (root.str "tree")
  let valueId := mkIdent (root.str "value")
  let astId := mkIdent (root.str "ast")
  quoteDefinition tokensId.getId tokens
  quoteDefinition treeId.getId tree
  quoteDefinition valueId.getId structuralValue
  quoteDefinition (α := AST.Block) astId.getId ast
  let lexId := mkIdent (root.str "lexed")
  let checkedId := mkIdent (root.str "checked")
  let builtId := mkIdent (root.str "structure_built")
  -- Declared by `elabCommand` inside the current namespace, hence relative.
  let denotesId := mkIdent (certificateName.getId.str "denotes")
  let witnessId := mkIdent (certificateName.getId.str "witness")
  let parsedId := mkIdent (certificateName.getId.str "parsed")
  checkEquation lexId.getId
    (← `(term| Scanner.lex Syntax.scanner $sourceId = Except.ok $tokensId))
    (← `(term| (Except.ok $tokensId : Except Diagnostic (List Token))))
  checkEquation checkedId.getId
    (← `(term| LALR.checkTree Generated.grammar
      (List.map (Generated.encode ∘ Token.symbol) $tokensId) $treeId = true))
    (← `(term| true))
  checkEquation builtId.getId
    (← `(term| StructureBridge.build $treeId $tokensId = some $valueId))
    (← `(term| some $valueId))
  elabCommand (← `(command|
    theorem $denotesId : LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
        (.ref "block") $valueId $astId := by action_certificate))
  elabCommand (← `(command|
    theorem $witnessId : Syntax.Witness $sourceId $astId :=
      witness_of_certificates _ _ _ _ _ $lexId $checkedId $builtId $denotesId))
  elabCommand (← `(command|
    theorem $parsedId : ∃ result, Syntax.parse $sourceId = .ok result ∧ result.ast = $astId :=
      parse_of_certificates _ _ _ _ _ $lexId $checkedId $builtId $denotesId))

end Rumoca.GALEC.Certificate
