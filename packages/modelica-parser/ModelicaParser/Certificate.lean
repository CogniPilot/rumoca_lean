import ModelicaParser.Parser
import Parser.LALR.ExactTree
import Parser.LALR.ActionCertificate
import Parser.Quotation
import Lean

/-! Kernel-checked parse certificates for concrete Modelica text. Native
execution only proposes constructor data; every equation is submitted to the
kernel as reflexivity, and the typed-action result is certified by
syntax-directed `Denotes` constructors. Quotation instances give no semantic
authority. -/
namespace Rumoca.Modelica.Certificate
open Lean Elab Command
open _root_.Parser Parser.Quotation

deriving instance ToExpr for AST.Expr, AST.Callee, AST.ComponentReference, AST.Part
deriving instance ToExpr for AST.Modification, AST.Argument, AST.ElementModification
deriving instance ToExpr for AST.Declaration
deriving instance ToExpr for AST.ComponentClause
deriving instance ToExpr for AST.Element
deriving instance ToExpr for AST.Equation
deriving instance ToExpr for AST.EquationSection
deriving instance ToExpr for AST.Composition
deriving instance ToExpr for AST.ClassSpecifier
deriving instance ToExpr for AST.ClassDefinition
deriving instance ToExpr for AST.StoredDefinition

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
theorem syntactic_of_certificates (tokens : List Token) (tree : LALR.Tree)
    (value : LALR.Frontend.Structure.Value Token) (ast : AST.StoredDefinition)
    (checked : LALR.checkTree Generated.grammar
      (tokens.map (Generated.encode ∘ Token.symbol)) tree = true)
    (built : StructureBridge.build tree tokens = some value)
    (denotes : LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
      (.ref "stored_definition") value ast) :
    Structural.parse tokens = some ast :=
  (Structural.parse_iff tokens ast).mpr ⟨tree, value, token_tree tokens tree checked, built, denotes⟩

/-- Add `name : α := value` as a closed, compiled definition of the quoted value,
so executable fixtures may use the certified parse. Quotation gives no semantic
authority; every equation about the value is checked by the kernel. -/
private def quoteCompiled {α : Type} [ToExpr α] (name : Name) (value : α) : CommandElabM Unit :=
  liftTermElabM do
    addAndCompile (.defnDecl {
      name := name
      levelParams := []
      type := toTypeExpr α
      value := toExpr value
      hints := .abbrev
      safety := .safe })

/-- Native evaluation of the closed source term, used only to propose tokens,
tree, structural value and AST. It is confined to this elaborator; a wrong
result can only make certification fail, because every equation below is
stated about the elaborated term itself and checked by the kernel. -/
private unsafe def evaluateSource (source : Expr) : TermElabM String :=
  Meta.evalExpr String (mkConst ``String) source

/-- Evaluate the closed `String` term `text`, propose its tokens, tree,
structural value and syntax tree, and add the kernel-checked declarations
`name.lexed`, `name.checked`, `name.structure_built`, `name.denotes`,
`name.syntactic` and the certified parse `name.parsed : Modelica.Parsed
name.source`, relative to the current namespace. -/
def certify (certificateName : Ident) (text : Term) : CommandElabM Unit := do
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
  let tokens ← match lex source with
    | .ok tokens => pure tokens
    | .error diagnostic => throwError "lexer rejected source: {diagnostic}"
  let tree ← match StructureBridge.parser.run (code tokens) with
    | .ok tree => pure tree
    | .error _ => throwError "parser rejected source"
  let structuralValue ← match StructureBridge.build tree (code tokens) with
    | some structuralValue => pure structuralValue
    | none => throwError "structural conversion rejected tree"
  let ast ← match LALR.Frontend.StructuralActions.run Structural.rules
      Token.symbol (.ref "stored_definition") structuralValue with
    | some ast => pure ast
    | none => throwError "actions rejected structural value"
  let tokensId := mkIdent (root.str "tokens")
  let treeId := mkIdent (root.str "tree")
  let valueId := mkIdent (root.str "value")
  let astId := mkIdent (root.str "ast")
  quoteCompiled tokensId.getId tokens
  quoteDefinition treeId.getId tree
  quoteDefinition valueId.getId structuralValue
  quoteCompiled (α := AST.StoredDefinition) astId.getId ast
  let lexId := mkIdent (root.str "lexed")
  let checkedId := mkIdent (root.str "checked")
  let builtId := mkIdent (root.str "structure_built")
  -- Declared by `elabCommand` inside the current namespace, hence relative.
  let denotesId := mkIdent (certificateName.getId.str "denotes")
  let syntacticId := mkIdent (certificateName.getId.str "syntactic")
  let parsedId := mkIdent (certificateName.getId.str "parsed")
  checkEquation lexId.getId
    (← `(term| lex $sourceId = Except.ok $tokensId))
    (← `(term| (Except.ok $tokensId : Except Diagnostic (List Token))))
  checkEquation checkedId.getId
    (← `(term| LALR.checkTree Generated.grammar
      (List.map (Generated.encode ∘ Token.symbol) (code $tokensId)) $treeId = true))
    (← `(term| true))
  checkEquation builtId.getId
    (← `(term| StructureBridge.build $treeId (code $tokensId) = some $valueId))
    (← `(term| some $valueId))
  elabCommand (← `(command|
    theorem $denotesId : LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
        (.ref "stored_definition") $valueId $astId := by action_certificate))
  elabCommand (← `(command|
    theorem $syntacticId : Structural.parse (code $tokensId) = some $astId :=
      syntactic_of_certificates _ _ _ _ $checkedId $builtId $denotesId))
  elabCommand (← `(command|
    def $parsedId : Modelica.Parsed $sourceId :=
      ⟨$tokensId, $astId, $lexId, $syntacticId⟩))

/-- `certify_source name text` certifies the parse of the source text `text`. -/
elab "certify_source " certificateName:ident text:term : command =>
  certify certificateName text

/-- Distinct placeholder strings for the parameters of a token family. They
contain a NUL character, so no fixed token of the family spells one. -/
private def placeholders (count : Nat) : Array String :=
  (Array.range count).map fun index => s!"\u0000parameter{index}"

/-- Replace every placeholder string literal of `e` by the corresponding
parameter and abstract the parameters. -/
private def abstractPlaceholders (count : Nat) (e : Expr) : MetaM Expr :=
  let names := placeholders count
  Meta.withLocalDeclsDND ((Array.range count).map fun _ => (`x, mkConst ``String)) fun fvars =>
    Meta.mkLambdaFVars fvars (e.replace fun sub => match sub with
      | .lit (.strVal s) => (names.idxOf? s).map fun index => fvars[index]!
      | _ => none)

/-- Add `name : String → … → String → result := value` as a definition. -/
private def familyDefinition (name : Name) (count : Nat) (result value : Expr) :
    CommandElabM Unit :=
  liftTermElabM do
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := (List.range count).foldr (fun _ body => mkForall `x .default (mkConst ``String) body)
        result
      value := value
      hints := .abbrev
      safety := .safe })
    enableRealizationsForConst name

/-- Native evaluation of one closed instance of a token family, used only to
propose the tree, structural value and syntax tree. -/
private unsafe def evaluateTokens (tokens : Expr) : TermElabM (List Token) :=
  Meta.evalExpr (List Token) (toTypeExpr (List Token)) tokens

/-- Certify, for every value of the string parameters, the parse of a token
family whose grammar symbols do not depend on the parameters: the parameters
occur only in retained payloads. Native execution of one instance, with
placeholder strings for the parameters, proposes the LR tree, the structural
value and the syntax tree; their payloads are abstracted over the parameters,
and every equation is checked by the kernel for all parameter values. Adds
`name.tokens`, `name.tree`, `name.value`, `name.ast` and the theorems
`name.checked`, `name.built`, `name.denotes` and
`name.syntactic : ∀ xs, Structural.parse (name.tokens xs) = some (name.ast xs)`. -/
def certifyFamily (certificateName : Ident) (parameters : Array Ident) (tokens : Term) :
    CommandElabM Unit := do
  let root := (← getCurrNamespace) ++ certificateName.getId
  let count := parameters.size
  let family ← liftTermElabM do
    let e ← Term.elabTerm (← `(fun $[($parameters : String)]* => ($tokens : List Token))) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let tokensId := mkIdent (root.str "tokens")
  familyDefinition tokensId.getId count (toTypeExpr (List Token)) family
  let sample ← liftTermElabM
    (unsafe evaluateTokens (family.beta ((placeholders count).map mkStrLit)))
  let tree ← match StructureBridge.parser.run sample with
    | .ok tree => pure tree
    | .error _ => throwError "parser rejected the token family"
  let structuralValue ← match StructureBridge.build tree sample with
    | some structuralValue => pure structuralValue
    | none => throwError "structural conversion rejected tree"
  let ast ← match LALR.Frontend.StructuralActions.run Structural.rules
      Token.symbol (.ref "stored_definition") structuralValue with
    | some (ast : AST.StoredDefinition) => pure ast
    | none => throwError "actions rejected structural value"
  let treeId := mkIdent (root.str "tree")
  let valueId := mkIdent (root.str "value")
  let astId := mkIdent (root.str "ast")
  quoteDefinition treeId.getId tree
  familyDefinition valueId.getId count (toTypeExpr (LALR.Frontend.Structure.Value Token))
    (← liftTermElabM (abstractPlaceholders count (toExpr structuralValue)))
  familyDefinition astId.getId count (toTypeExpr AST.StoredDefinition)
    (← liftTermElabM (abstractPlaceholders count (toExpr ast)))
  let checkedId := mkIdent (root.str "checked")
  let builtId := mkIdent (root.str "built")
  let denotesId := mkIdent (certificateName.getId.str "denotes")
  let syntacticId := mkIdent (certificateName.getId.str "syntactic")
  checkUniversalEquation checkedId.getId (← `(term| ∀ $[($parameters : String)]*,
    LALR.checkTree Generated.grammar
      (List.map (Generated.encode ∘ Token.symbol) ($tokensId $parameters*)) $treeId = true))
  checkUniversalEquation builtId.getId (← `(term| ∀ $[($parameters : String)]*,
    StructureBridge.build $treeId ($tokensId $parameters*) = some ($valueId $parameters*)))
  elabCommand (← `(command|
    theorem $denotesId $[($parameters : String)]* :
        LALR.Frontend.StructuralActions.Denotes Structural.rules Token.symbol
          (.ref "stored_definition") ($valueId $parameters*) ($astId $parameters*) := by
      action_certificate))
  elabCommand (← `(command|
    theorem $syntacticId $[($parameters : String)]* :
        Structural.parse ($tokensId $parameters*) = some ($astId $parameters*) :=
      syntactic_of_certificates _ _ _ _ ($checkedId $parameters*) ($builtId $parameters*)
        ($denotesId $parameters*)))

/-- `certify_family name (x₁ … xₙ) tokens` certifies the parse of the token
family `tokens` for all strings `x₁ … xₙ`. -/
elab "certify_family " certificateName:ident " (" parameters:ident* ") " tokens:term : command =>
  certifyFamily certificateName parameters tokens

end Rumoca.Modelica.Certificate
