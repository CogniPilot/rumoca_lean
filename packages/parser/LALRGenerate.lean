import Parser.LALR.Generator
import Parser.LALR.EBNF
import Parser.EBNF.SourceText
import Parser.LALR.Safety
import Parser.LALR.ItemCheck
import Parser.LALR.Resources

/-! Grammar-parametric table emitter. All implementation is Lean and lives in the
parser package. It does not publish the complete source `CertifiedParser`:
Frontend actions still need their own contracts. The generated token parser
has checked EBNF preservation, safety, completeness and resource bounds.

The certificates are split across a directory of modules per grammar so that
each obligation group elaborates in its own Lean process (kernel decision terms
are reclaimed per module) and Lake builds the groups in parallel. A data module
carries the table literals and source; independent certificate modules import
only the data module; the umbrella module imports them all and states the final
theorems, whose names and statements are unchanged for downstream consumers. -/
open Parser.LALR

namespace LALRGenerator

private def array (xs : Array String) : String :=
  "#[" ++ String.intercalate ", " xs.toList ++ "]"

private def atom : Atom → String
  | .terminal t => s!".terminal {t}"
  | .nonterminal n => s!".nonterminal {n}"

private def production (p : Production) : String :=
  s!"⟨{p.input}, [" ++ String.intercalate ", " (p.output.map atom) ++ "]⟩"

private def action : Option Action → String
  | none => "none"
  | some (.shift n) => s!"some (.shift {n})"
  | some (.reduce n) => s!"some (.reduce {n})"
  | some .accept => "some .accept"

private def edge (e : Edge) : String := s!"⟨{e.source}, {atom e.symbol}, {e.target}⟩"

private def firstFact (f : First) : String :=
  s!"⟨{f.nullable}, [" ++ String.intercalate ", " (f.terminals.map toString) ++ "]⟩"

private def item (i : Item) : String := s!"⟨{i.production}, {i.dot}, {i.lookahead}⟩"

/-- Parser-package modules every generated module transitively needs. Only the
data module imports them directly; certificate modules import the data module. -/
private def parserImports : List String :=
  ["Parser.LALR.SafetyProofs", "Parser.LALR.MaskedSafety", "Parser.LALR.RowSafety",
   "Parser.LALR.FirstProofs", "Parser.LALR.Progress", "Parser.Token",
   "Parser.LALR.LocatedCompleteness", "Parser.LALR.EBNFEncoding",
   "Parser.EBNF.ReaderCorrectness", "Parser.EBNF.Rules", "Parser.LALR.Actions"]

/-- Wrap one module's declaration text with its lead comment, imports, the shared
`open`/`namespace` and the module-level elaboration options. -/
private def moduleText (moduleNamespace leadComment : String) (imports : List String)
    (body : String) : String :=
  leadComment ++
  String.join (imports.map (fun m => s!"import {m}\n")) ++
  "\nopen Parser\n\n" ++
  s!"namespace {moduleNamespace}\n\n" ++
  "set_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n\n" ++
  body ++
  s!"end {moduleNamespace}\n"

/-! Per-declaration elaboration options reused throughout the certificates. -/
private def options : String :=
  "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n"

/-- One-step source equations support language-owned AST proofs, including
inductive proofs for recursive grammars. They are deliberately not global simp
rules: a recursive rule must only unfold when its frontend requests it. -/
private def ruleCertificates (grammar : Parser.EBNF.Grammar) : String := Id.run do
  let mut text := ""
  for (name, body) in grammar do
    text := text ++ s!"theorem «rule_{name}» (word : List Parser.Symbol) :\n" ++
      s!"    Parser.EBNF.Derives sourceGrammar (.ref {reprStr name}) word ↔\n" ++
      s!"      Parser.EBNF.Derives sourceGrammar ({reprStr body}) word :=\n" ++
      "  Parser.EBNF.Derives.ref_iff_of_filter (by decide +kernel) word\n\n"
  if let (name, body) :: _ := grammar then
    text := text ++ "theorem start_rule (word : List Parser.Symbol) :\n" ++
      "    Parser.EBNF.Accepts sourceGrammar word ↔\n" ++
      s!"      Parser.EBNF.Derives sourceGrammar (.ref {reprStr name}) word :=\n" ++
      s!"  Parser.EBNF.accepts_iff_of_head (body := {reprStr body}) (by decide +kernel) word\n\n"
  return text

private structure EbnfPieces where
  /-- Data placed in the shared module: grammar/witness literals and `encode`. -/
  data : String
  /-- Proofs placed in the source module. -/
  proofs : String

/-- Split a token stream into blocks of whole rules near a rule target. Each
`.punct ';'` is a top-level rule terminator, so a block boundary after one is a
clean parse boundary and the block grammars concatenate to the whole grammar. -/
private def ruleBlocks (tokens : List Parser.EBNF.Lexeme) (target : Nat := 8) :
    Array (List Parser.EBNF.Lexeme) := Id.run do
  let mut blocks : Array (List Parser.EBNF.Lexeme) := #[]
  let mut current : List Parser.EBNF.Lexeme := []
  let mut rules : Nat := 0
  for t in tokens do
    current := t :: current
    if t == Parser.EBNF.Lexeme.punct ';' then
      rules := rules + 1
      if rules ≥ target then
        blocks := blocks.push current.reverse
        current := []
        rules := 0
  if !current.isEmpty then
    blocks := blocks.push current.reverse
  return blocks

/-- Bind the actual grammar text and generated CFG through a finite structural
witness. These constants are proof-only; the runtime retains its token alphabet
and the ordinary LR tables. The lexing and parsing certificates are composed
from per-block certificates, so no single kernel decision term ranges over the
whole source text or token stream: each block is checked on its own bounded
input, and the reusable `Lexes.append`/`Rules.append` engine lemmas join them
against the unchanged final statements. -/
private def ebnfCertificates (source : String) (tokens : List Parser.EBNF.Lexeme)
    (sourceGrammar : Parser.EBNF.Grammar)
    (certificate : Frontend.Certified sourceGrammar) : Except String EbnfPieces := do
  -- Character blocks shared with the source-text certificate, and their tokens.
  let charBlocks := Parser.EBNF.Emission.sourceBlocks source
  let mut lexToks : Array (List Parser.EBNF.Lexeme) := #[]
  for block in charBlocks do
    match Parser.EBNF.Reader.tokenize (block.length + 1) block with
    | .ok toks => lexToks := lexToks.push toks
    | .error e => throw s!"source block failed to tokenize: {e}"
  if lexToks.toList.flatten != tokens then
    throw "source blocks do not compose to the token stream"
  -- Rule blocks and their grammars.
  let tokBlocks := ruleBlocks tokens
  let mut ruleGrammars : Array Parser.EBNF.Grammar := #[]
  for block in tokBlocks do
    match Parser.EBNF.Reader.rules (block.length + 1) block with
    | .ok g => ruleGrammars := ruleGrammars.push g
    | .error e => throw s!"rule block failed to parse: {e}"
  if ruleGrammars.toList.flatten != sourceGrammar then
    throw "rule blocks do not compose to the grammar"
  let lexCount := charBlocks.size
  let ruleCount := tokBlocks.size
  -- Per-block lexer certificates.
  let mut lexBody := ""
  for i in [:lexCount] do
    let block := charBlocks[i]!
    let toks := lexToks[i]!
    lexBody := lexBody ++ s!"private def lexToks{i} : List Parser.EBNF.Lexeme := {reprStr toks}\n\n" ++
      options ++ s!"private theorem lexBlock{i}_lexes : " ++
        s!"Parser.EBNF.Metalanguage.Lexes sourceChars{i} lexToks{i} := by\n" ++
      s!"  apply Parser.EBNF.Reader.tokenize_sound (fuel := {block.length + 1})\n" ++
      "  decide +kernel\n\n"
  -- Fold the block certificates into the whole-text lexer certificate. The join
  -- is left-nested to match the left-associative list append, so each appended
  -- block is a single literal whose newline lead discharges the boundary.
  let mut lexTerm := "lexBlock0_lexes"
  for i in [1:lexCount] do
    lexTerm := s!"Parser.EBNF.Metalanguage.Lexes.append ({lexTerm}) lexBlock{i}_lexes (Or.inl (by decide))"
  let lexJoin := String.intercalate " ++ " ((List.range lexCount).map fun i => s!"lexToks{i}")
  lexBody := lexBody ++
    options ++ "private theorem lexes_source : Parser.EBNF.Metalanguage.Lexes sourceChars sourceTokens := by\n" ++
    s!"  have h := {lexTerm}\n" ++
    s!"  have ht : {lexJoin} = sourceTokens := by decide +kernel\n" ++
    "  rw [ht] at h\n  exact h\n\n" ++
    options ++ "private theorem lexing_checked : Parser.EBNF.lex source = .ok sourceTokens := by\n" ++
    "  unfold Parser.EBNF.lex\n  rw [source_toList]\n" ++
    "  exact Parser.EBNF.Reader.tokenize_complete lexes_source (Nat.le_refl _)\n\n"
  -- Per-block parser certificates.
  let mut ruleBody := ""
  for i in [:ruleCount] do
    let block := tokBlocks[i]!
    let g := ruleGrammars[i]!
    ruleBody := ruleBody ++
      s!"private def ruleToks{i} : List Parser.EBNF.Lexeme := {reprStr block}\n\n" ++
      s!"private def ruleGrammar{i} : Parser.EBNF.Grammar := {reprStr g}\n\n" ++
      options ++ s!"private theorem ruleBlock{i}_rules : " ++
        s!"Parser.EBNF.Metalanguage.Rules ruleGrammar{i} ruleToks{i} :=\n" ++
      s!"  (Parser.EBNF.Reader.rules_sound (fuel := {block.length + 1}) (by decide +kernel)).1\n\n"
  let mut ruleTerm := "ruleBlock0_rules"
  for i in [1:ruleCount] do
    ruleTerm := s!"Parser.EBNF.Metalanguage.Rules.append ({ruleTerm}) ruleBlock{i}_rules"
  let gJoin := String.intercalate " ++ " ((List.range ruleCount).map fun i => s!"ruleGrammar{i}")
  let rtJoin := String.intercalate " ++ " ((List.range ruleCount).map fun i => s!"ruleToks{i}")
  ruleBody := ruleBody ++
    options ++ "private theorem rules_source : Parser.EBNF.Metalanguage.Rules sourceGrammar sourceTokens := by\n" ++
    s!"  have h := {ruleTerm}\n" ++
    s!"  have hg : {gJoin} = sourceGrammar := by decide +kernel\n" ++
    s!"  have ht : {rtJoin} = sourceTokens := by decide +kernel\n" ++
    "  rw [hg, ht] at h\n  exact h\n\n" ++
    options ++ "private theorem source_names_valid : Parser.EBNF.Metalanguage.NamesValid sourceGrammar := by\n" ++
    "  unfold Parser.EBNF.Metalanguage.NamesValid\n  exact (by decide +kernel)\n\n" ++
    options ++ "private theorem parsing_checked : Parser.EBNF.parseTokens sourceTokens = .ok sourceGrammar :=\n" ++
    "  Parser.EBNF.parseTokens_complete ⟨rules_source, source_names_valid, by decide +kernel⟩\n\n"
  let dataBody :=
      "noncomputable def sourceGrammar : Parser.EBNF.Grammar := " ++ reprStr sourceGrammar ++ "\n\n" ++
      "noncomputable def prepared : LALR.Frontend.Prepared := ⟨alphabet, " ++
        reprStr certificate.prepared.names ++ ", grammar⟩\n\n" ++
      "noncomputable def loweringWitness : LALR.Frontend.Witness := ⟨" ++
        reprStr certificate.witness.meanings ++ ",\n" ++
        reprStr certificate.witness.roots ++ ",\n" ++
        reprStr certificate.witness.rules ++ "⟩\n\n" ++
      "noncomputable def sourceTokens : List Parser.EBNF.Lexeme := " ++ reprStr tokens ++ "\n\n" ++
      "def encode (symbol : Parser.Symbol) : Nat :=\n" ++
        "  (alphabet.findIdx? (· == symbol)).getD (alphabet.size + 1)\n\n"
  let proofBody :=
      lexBody ++ ruleBody ++
      "theorem source_read_checked : Parser.EBNF.parse source = .ok sourceGrammar :=\n" ++
        "  (Parser.EBNF.parse_of_lex lexing_checked).trans parsing_checked\n\n" ++
      "theorem source_notation_checked : Parser.EBNF.Metalanguage.Denotes source sourceGrammar :=\n" ++
        "  Parser.EBNF.parse_sound source_read_checked\n\n" ++
      options ++ "theorem lowering_checked : loweringWitness.validate sourceGrammar prepared = true :=\n" ++
        "  by decide +kernel\n\n" ++
      "theorem ebnf_correct (word : List Parser.Symbol) :\n" ++
        "    Parser.EBNF.Accepts sourceGrammar word ↔ grammar.Accepts (word.map encode) :=\n" ++
        "  loweringWitness.accepts_iff (LALR.Frontend.Witness.validate_iff.mp lowering_checked)\n" ++
        "    (by decide +kernel) word\n\n"
  return ⟨dataBody, proofBody⟩

private def sourceParserContract : String :=
  "def parseSymbols (word : List Parser.Symbol) : Except LALR.Failure LALR.Tree :=\n" ++
    "  parse (word.map encode)\n\n" ++
  "theorem source_parse_correct (word : List Parser.Symbol) :\n" ++
    "    Parser.EBNF.Metalanguage.Denotes source sourceGrammar ∧\n" ++
    "    (Parser.EBNF.Accepts sourceGrammar word ↔ ∃ tree, parseSymbols word = .ok tree) ∧\n" ++
    "    ((∃ tree, parseSymbols word = .ok tree) ∨ parseSymbols word = .error .rejected) :=\n" ++
    "  ⟨source_notation_checked, (ebnf_correct word).trans (parse_correct (word.map encode)).1,\n" ++
    "    (parse_correct (word.map encode)).2⟩\n\n" ++
  "def tokenParser : LALR.TokenParser Parser.Symbol where\n" ++
    "  grammar := grammar\n  encode := encode\n  run := parseSymbols\n" ++
    "  accepts_iff word := (parse_correct (word.map encode)).1\n" ++
    "  checked word tree parsed := parsed_tree (word.map encode) tree parsed\n" ++
    "  terminates word := (parse_correct (word.map encode)).2\n\n"

private def locatedParserContract : String :=
  "-- Every grammar gets the same bounded production/terminal span API.\n" ++
  "def encodeLocatedTokens {text : String} (tokens : List (Source.Located text Token)) :\n" ++
  "    List (Source.Located text Nat) :=\n" ++
  "  tokens.map fun token => ⟨encode token.value.symbol, token.span⟩\n" ++
  "\n" ++
  "def parseLocated (text : String) (tokens : List (Source.Located text Token)) :=\n" ++
  "  LALR.parseLocated grammar tables (fuelForLength tokens.length) (encodeLocatedTokens tokens)\n" ++
  "\n" ++
  "theorem located_fuel {text : String} (tokens : List (Source.Located text Token)) :\n" ++
  "    fuelForLength tokens.length =\n" ++
  "      LALR.Progress.bound fuelBudget progressCredits ((encodeLocatedTokens tokens).map (·.value)) := by\n" ++
  "  simpa only [fuel, encodeLocatedTokens, List.length_map] using\n" ++
  "    fuel_eq ((encodeLocatedTokens tokens).map (·.value))\n" ++
  "\n" ++
  "theorem source_parseLocated_correct (text : String) (tokens : List (Source.Located text Token)) :\n" ++
  "    Parser.EBNF.Metalanguage.Denotes source sourceGrammar ∧\n" ++
  "    (Parser.EBNF.Accepts sourceGrammar (tokens.map (fun token => token.value.symbol)) ↔\n" ++
  "      ∃ result, parseLocated text tokens = .ok result) ∧\n" ++
  "    ((∃ result, parseLocated text tokens = .ok result) ∨\n" ++
  "      parseLocated text tokens = .error .rejected) := by\n" ++
  "  have checked := LALR.parseLocated_correct items_checked budget_checked safety_checked\n" ++
  "    progress_checked (encodeLocatedTokens tokens)\n" ++
  "  rw [← located_fuel tokens] at checked\n" ++
  "  refine ⟨source_notation_checked, ?_, checked.2⟩\n" ++
  "  exact (ebnf_correct (tokens.map (fun token => token.value.symbol))).trans\n" ++
  "    (by simpa only [encodeLocatedTokens, List.map_map, Function.comp_def, parseLocated]\n" ++
  "      using checked.1)\n" ++
  "\n" ++
  "theorem parseLocated_erases (text : String) (tokens : List (Source.Located text Token)) :\n" ++
  "    (parseLocated text tokens).map (·.tree) =\n" ++
  "      parseSymbols (tokens.map (fun token => token.value.symbol)) := by\n" ++
  "  have erased := LALR.parseLocated_erases grammar tables\n" ++
  "    (fuelForLength tokens.length) (encodeLocatedTokens tokens)\n" ++
  "  simpa only [parseLocated, parseSymbols, parse, fuel,\n" ++
  "    encodeLocatedTokens, List.map_map, List.length_map, Function.comp_def] using erased\n" ++
  "\n"

private structure ItemPieces where
  /-- The `itemStates` literal for the data module. -/
  data : String
  /-- The chunked item obligations and their join, for the items module. -/
  proofs : String

/-- Item obligations are grouped into fixed-size chunks, one certificate per
chunk, so the elaborator retains a handful of decision terms rather than one per
state; the final theorem composes all chunks against the unchanged
grammar-parametric item validator. -/
private def itemCertificates (states : Array ItemSet) : ItemPieces := Id.run do
  let chunkSize := 10
  let data := "noncomputable def itemStates : Array LALR.ItemSet := " ++
    array (states.map fun state => "[" ++ String.intercalate ", " (state.map item) ++ "]") ++ "\n\n"
  let mut text := ""
  let mut base := 0
  while base < states.size do
    let c := min chunkSize (states.size - base)
    let stateExpr := s!"({base} + j.val)"
    let row := s!"(LALR.ItemCheck.items itemStates {stateExpr})"
    text := text ++ options ++ s!"private theorem items_chunk_{base}_checked :\n" ++
      s!"    ∀ j : Fin {c}, ∀ i ∈ {row}, LALR.ItemCheck.Valid grammar i ∧\n" ++
      s!"      LALR.ItemCheck.Closed grammar firstFacts {row} i ∧\n" ++
      s!"      LALR.ItemCheck.Advances grammar tables itemStates {stateExpr} i := by decide +kernel\n\n"
    base := base + chunkSize
  let mut cases := ""
  for q in [:states.size] do
    let b := (q / chunkSize) * chunkSize
    cases := cases ++ s!"    | {q} => exact items_chunk_{b}_checked ⟨{q - b}, by decide⟩\n"
  text := text ++ options ++ "theorem items_checked :\n" ++
    "    LALR.ItemCheck.validate grammar tables firstFacts itemStates = true := by\n" ++
    "  apply LALR.ItemCheck.validate_iff.mpr\n" ++
    "  refine ⟨by decide +kernel, by decide +kernel, first_checked, by decide +kernel, ?_⟩\n" ++
    "  intro q\n" ++
    "  rcases q with ⟨q, bound⟩\n" ++
    s!"  change q < {states.size} at bound\n" ++
    "  match q with\n" ++ cases ++ s!"    | n+{states.size} => omega\n\n"
  return { data, proofs := text }

private structure BudgetPieces where
  /-- Budget/credit literals for the data module. -/
  data : String
  /-- `budget_checked` and `progress_checked` for the progress module. -/
  progress : String
  /-- Runtime parse contracts joining every group, for the umbrella module. -/
  rest : String

/-- Only the two scalar budget coefficients are used by runtime parsing.
The complete per-production credit witness remains proof-only metadata. -/
private def budgetCertificates (budget : Fuel.Budget) (credits : Progress.Credits) : BudgetPieces :=
  { data :=
      "noncomputable def fuelBudget : LALR.Fuel.Budget := ⟨" ++
        toString budget.perToken ++ ", " ++ reprStr budget.nonterminals ++ "⟩\n\n" ++
      "noncomputable def progressCredits : LALR.Progress.Credits := ⟨" ++
        reprStr credits.states ++ ", " ++ toString credits.ceiling ++ "⟩\n\n",
    progress :=
      "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
      "theorem budget_checked : LALR.Fuel.validate grammar fuelBudget = true := by decide +kernel\n\n" ++
      "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
      "theorem progress_checked : LALR.Progress.validate tables edges fuelBudget progressCredits = true :=\n" ++
      "  by decide +kernel\n\n",
    rest :=
      "def fuelForLength (count : Nat) : Nat := " ++ toString budget.perToken ++
        " * count + " ++ toString credits.ceiling ++ " + 1\n\n" ++
      "def fuel (input : List Nat) : Nat := fuelForLength input.length\n\n" ++
      "theorem fuel_eq (input : List Nat) :\n" ++
      "    fuel input = LALR.Progress.bound fuelBudget progressCredits input := by rfl\n\n" ++
      "theorem accepts_iff_parse_bounded (word : List Nat) :\n" ++
      "    grammar.Accepts word ↔ ∃ tree, LALR.parse grammar tables (fuel word) word = .ok tree := by\n" ++
      "  rw [fuel_eq]\n" ++
      "  exact LALR.Progress.accepts_iff_parse items_checked budget_checked safety_checked progress_checked word\n\n" ++
      "theorem parse_terminates (word : List Nat) :\n" ++
      "    (∃ tree, LALR.parse grammar tables (fuel word) word = .ok tree) ∨\n" ++
      "      LALR.parse grammar tables (fuel word) word = .error .rejected := by\n" ++
      "  rw [fuel_eq]\n" ++
      "  exact LALR.Progress.parse_terminates budget_checked safety_checked progress_checked word\n\n" ++
      "def parse (input : List Nat) : Except LALR.Failure LALR.Tree :=\n" ++
      "  LALR.parse grammar tables (fuel input) input\n\n" ++
      "theorem parse_correct (word : List Nat) :\n" ++
      "    (grammar.Accepts word ↔ ∃ tree, parse word = .ok tree) ∧\n" ++
      "    ((∃ tree, parse word = .ok tree) ∨ parse word = .error .rejected) :=\n" ++
      "  ⟨accepts_iff_parse_bounded word, parse_terminates word⟩\n\n" ++
      "theorem parsed_tree (word : List Nat) (tree : LALR.Tree) (parsed : parse word = .ok tree) :\n" ++
      "    LALR.checkTree grammar word tree = true :=\n" ++
      "  LALR.RuntimeProofs.run_checked (LALR.RuntimeProofs.initial grammar word)\n" ++
      "    (by simpa only [parse, LALR.parse_eq_run] using parsed)\n\n" }

private structure SafetyPieces where
  /-- Shared reduction premises for the data module (public across reductions). -/
  shared : String
  /-- One body per reduction module, each about `fileSize` reduction certificates. -/
  reductionFiles : Array String
  /-- The reduction join, row chunks and `safety_checked` for the safety module. -/
  join : String

/-- Check each reduction summary separately, then substitute the proved
equalities into the unchanged validator. The reduction certificates are spread
across several modules so no single process retains every masked-pop decision
term; the row-safety chunks and the join stay in the safety module. -/
private def safetyCertificates (g : Grammar) (tables : Tables) (edges : List Edge)
    (fileSize : Nat := 20) : SafetyPieces := Id.run do
  let rows := Safety.reductionStates g tables edges
  -- Shared premises, established once and reused by every reduction certificate.
  -- The masked pop equivalence needs the edge-source bound and the goto-table
  -- shape; the literal state count keeps the kernel from re-measuring the table.
  let shared := options ++
    "theorem edge_source_bound : ∀ e ∈ edges, e.source < tables.actions.size := by decide +kernel\n\n" ++
    "theorem gotos_size_eq : tables.gotos.size = tables.actions.size := rfl\n\n" ++
    s!"theorem state_count : tables.actions.size = {tables.actions.size} := rfl\n\n"
  -- Emit each reduction certificate's declaration text, then group them into
  -- files. Every reduction constant is public so the safety module's join can
  -- reference the equalities proved in the reduction modules.
  let mut certs : Array String := #[]
  let mut names : Array String := #[]
  let mut cases := ""
  for i in [:rows.size] do
    let name := s!"reduction_{i}"
    let prod := s!"(grammar.productions[{i}]?.getD (⟨0, []⟩ : LALR.Production))"
    let expression := s!"LALR.Safety.popStates tables.actions.size edges {prod}.output.reverse " ++
      s!"(LALR.Safety.gotoStates tables {prod}.input)"
    -- Rewrite the array pop into the masked pop, replace the goto vector's mask
    -- with the single-pass goto fold, and pin the state count before the kernel
    -- reduces the machine-word bit operations.
    certs := certs.push (s!"noncomputable def {name} : Array Bool := {repr rows[i]!}\n\n" ++
      options ++ s!"theorem {name}_checked : {expression} = {name} := by\n" ++
      "  rw [LALR.Safety.popStates_eq edge_source_bound (by rw [LALR.Safety.gotoStates, Array.size_ofFn]),\n" ++
      "    LALR.Safety.gotoMask_eq rfl gotos_size_eq, state_count]\n" ++
      "  decide +kernel\n\n")
    names := names.push name
    cases := cases ++ s!"    | {i} => exact {name}_checked\n"
  let mut reductionFiles : Array String := #[]
  let mut base := 0
  while base < certs.size do
    let stop := min (base + fileSize) certs.size
    let mut body := ""
    for j in [base:stop] do
      body := body ++ certs[j]!
    reductionFiles := reductionFiles.push body
    base := base + fileSize
  -- One structural-safety certificate per state, reading only that state's action
  -- and goto rows. Joined by the engine lemma `safety_of_rows`, so no single
  -- kernel term covers the whole table; the transient is bounded by one row.
  let count := tables.actions.size
  -- Group the per-state obligations into fixed-size chunks. One certificate per
  -- chunk keeps only a handful of kernel decision terms resident at once, which
  -- caps the module's cumulative peak, while each chunk's transient stays small.
  let chunkSize := 10
  let mut rowCases := ""
  let mut rbase := 0
  while rbase < count do
    let c := min chunkSize (count - rbase)
    rowCases := rowCases ++ options ++
      s!"private theorem chunk_{rbase}_checked :\n" ++
      s!"    ∀ i : Fin {c}, LALR.Safety.rowValid grammar tables edges reductions acceptance ({rbase} + i.val) := by decide +kernel\n\n"
    rbase := rbase + chunkSize
  let mut rowDispatch := ""
  for q in [:count] do
    let b := (q / chunkSize) * chunkSize
    rowDispatch := rowDispatch ++ s!"    | {q} => exact chunk_{b}_checked ⟨{q - b}, by decide⟩\n"
  let join := "private noncomputable def reductions : Array (Array Bool) := " ++ array names ++ "\n\n" ++
    options ++ "private theorem reductions_checked :\n" ++
    "    LALR.Safety.reductionStates grammar tables edges = reductions := by\n" ++
    "  apply Array.ext\n" ++
    "  · simp only [LALR.Safety.reductionStates, Array.size_map]\n    rfl\n" ++
    "  · intro i hi _\n" ++
    s!"    have bound : i < {rows.size} := by\n" ++
    "      simpa only [LALR.Safety.reductionStates, Array.size_map] using hi\n" ++
    "    simp only [LALR.Safety.reductionStates, Array.getElem_map]\n" ++
    "    match i with\n" ++ cases ++ s!"    | n+{rows.size} => omega\n" ++
    "\nprivate noncomputable def acceptance : Array Bool := " ++ reprStr (Safety.acceptStates g tables edges) ++ "\n\n" ++
    options ++ "private theorem acceptance_checked :\n" ++
    "    LALR.Safety.acceptStates grammar tables edges = acceptance := by decide +kernel\n\n" ++
    rowCases ++
    options ++ "theorem safety_checked : LALR.Safety.validate grammar tables edges = true := by\n" ++
    "  apply LALR.Safety.validate_iff.mpr\n" ++
    "  unfold LALR.Safety.Conditions\n" ++
    "  rw [reductions_checked, acceptance_checked]\n" ++
    "  apply LALR.Safety.safety_of_rows\n" ++
    "  · decide +kernel\n" ++
    "  · decide +kernel\n" ++
    "  · exact gotos_size_eq\n" ++
    "  · decide +kernel\n" ++
    "  · intro q\n" ++
    "    rcases q with ⟨q, bound⟩\n" ++
    s!"    change q < {count} at bound\n" ++
    "    match q with\n" ++ rowDispatch ++ s!"    | n+{count} => omega\n\n"
  return { shared, reductionFiles, join }

/-- The relative file name and content for one emitted module. `name` is the
module-name suffix under the grammar's `Generated` prefix; the umbrella module
uses the empty suffix. -/
structure EmittedModule where
  name : String
  text : String

/-- All modules emitted for one grammar: the umbrella plus its submodules. -/
structure Emission where
  umbrella : String
  submodules : Array EmittedModule

/-- The generated module namespace must be a dotted path of Lean identifiers.
Both emission modes reject anything else. -/
private def validNamespace (moduleNamespace : String) : Bool :=
  (moduleNamespace.splitOn ".").all (fun part =>
    !part.isEmpty && part.toList.all (fun c => Parser.identRest c) &&
      (part.toList.head?).any Parser.identStart)

/-- The certificate bodies for one grammar, before any module wrapping. Every
field is plain declaration text under the shared namespace and carries no
imports, so the split emitter wraps each into its own module while the
single-file emitter concatenates them under one namespace. -/
private structure GeneratedParts where
  tablesBody : String
  sourceBody : String
  itemsBody : String
  reductionFiles : Array String
  safetyBody : String
  progressBody : String
  umbrellaBody : String
  canonicalStates : Nat
  lalrStates : Nat

/-- Validate the grammar and emit every certificate group's declaration text.
Shared by both emission modes so the split and single-file outputs never drift:
each field here is exactly the body one split module carries. -/
private def generatedParts (source : String) : Except String GeneratedParts := do
  let sourceTokens ← Parser.EBNF.lex source
  let sourceGrammar ← Parser.EBNF.parseTokens sourceTokens
  let lowering ← Frontend.lowerWithWitness sourceGrammar
  let p := lowering.prepared
  let c ← generate p.grammar
  let g := p.grammar
  let facts ← firstSets g
  if !FirstCheck.validate g facts then
    throw "candidate failed nullable/FIRST validation"
  if !Safety.validate g c.tables c.collection.edges.toList then
    throw "candidate failed structural safety validation"
  if !ItemCheck.validate g c.tables facts c.collection.states then
    throw "candidate failed LR item coverage validation"
  let resources ← Resources.generate g c.tables c.collection.edges.toList
  let budget := resources.budget
  if !Fuel.validate g budget then throw "candidate failed linear fuel validation"
  if !Progress.validate c.tables c.collection.edges.toList budget resources.credits then
    throw "candidate failed total parsing progress validation"
  let ebnf ← ebnfCertificates source sourceTokens sourceGrammar lowering
  let items := itemCertificates c.collection.states
  let safety := safetyCertificates g c.tables c.collection.edges.toList
  let budgetPieces := budgetCertificates budget resources.credits
  -- The data group: table literals, source, and the shared reduction premises.
  let tablesBody :=
    Parser.EBNF.Emission.sourceCertificate source ++
    s!"def alphabet : Array Parser.Symbol := {repr p.alphabet}\n\n" ++
    s!"def grammar : LALR.Grammar := ⟨{g.terminals}, {g.nonterminals}, {g.start}, " ++
      array (g.productions.map production) ++ "⟩\n\n" ++
    ebnf.data ++
    "def tables : LALR.Tables := ⟨" ++ array (c.tables.actions.map fun row => array (row.map action)) ++
      ", " ++ array (c.tables.gotos.map fun row => array (row.map fun n =>
        n.map (fun n => s!"some {n}") |>.getD "none")) ++ "⟩\n\n" ++
    "def edges : List LALR.Edge := [" ++
      String.intercalate ", " (c.collection.edges.toList.map edge) ++ "]\n\n" ++
    "def firstFacts : Array LALR.First := " ++ array (facts.map firstFact) ++ "\n\n" ++
    items.data ++
    safety.shared ++
    budgetPieces.data
  -- The source/EBNF certificate module.
  let sourceBody := ebnf.proofs ++ ruleCertificates sourceGrammar
  -- The item-coverage certificate module.
  let itemsBody :=
    "-- Proof-producing normalization; all resulting terms are kernel checked.\n" ++
    "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
    "set_option cbv.warning false in\n" ++
    "theorem first_checked : LALR.FirstCheck.validate grammar firstFacts = true := by cbv\n\n" ++
    items.proofs
  -- The progress/budget certificate group.
  let progressBody := budgetPieces.progress
  -- The safety group joins the reduction certificates.
  let safetyBody := safety.join
  -- The cross-group runtime contracts.
  let umbrellaBody :=
    "theorem accepts_iff_parse (word : List Nat) :\n" ++
    "    grammar.Accepts word ↔ ∃ fuel tree, LALR.parse grammar tables fuel word = .ok tree :=\n" ++
    "  LALR.Completeness.accepts_iff_parse items_checked\n\n" ++
    "theorem nullable_coverage (symbols : List LALR.Atom)\n" ++
    "    (h : grammar.semantics.Derives symbols []) :\n" ++
    "    (LALR.firstSequence firstFacts symbols).nullable = true :=\n" ++
    "  LALR.FirstProofs.nullable_complete first_checked h\n\n" ++
    "theorem lookahead_coverage (symbols : List LALR.Atom) (word : List Nat) (following : Nat)\n" ++
    "    (h : grammar.semantics.Derives symbols (word.map _root_.Symbol.terminal)) :\n" ++
    "    word.headD following ∈ LALR.lookaheads firstFacts symbols following :=\n" ++
    "  LALR.FirstProofs.lookahead_complete first_checked h\n\n" ++
    budgetPieces.rest ++
    sourceParserContract ++
    "theorem execution_safe (fuel : Nat) (input : List Nat) (error : LALR.Failure)\n" ++
    "    (h : LALR.parse grammar tables fuel input = .error error) :\n" ++
    "    error = .exhausted ∨ error = .rejected :=\n" ++
    "  LALR.Safety.validated_parse_safe safety_checked h\n\n" ++
    locatedParserContract
  return {
    tablesBody := tablesBody, sourceBody := sourceBody, itemsBody := itemsBody,
    reductionFiles := safety.reductionFiles, safetyBody := safetyBody,
    progressBody := progressBody, umbrellaBody := umbrellaBody,
    canonicalStates := c.canonicalStates, lalrStates := c.collection.states.size }

/-- Emit the split module set: an umbrella that imports a per-group module
directory. Each group's body is wrapped with its imports under the shared
namespace; the umbrella states the final theorems. -/
def emit (source : String) (moduleNamespace : String := "Parser.LALRGenerated")
    (modulePrefix : String := "Parser.LALRGenerated") : Except String Emission := do
  if !validNamespace moduleNamespace then throw "invalid generated namespace"
  let parts ← generatedParts source
  let noEdit := "-- Generated by the in-tree Lean lalrgen; do not edit.\n"
  -- Reduction certificate modules and their import names.
  let reductionNames := (Array.range parts.reductionFiles.size).map fun k => s!"Reductions{k}"
  let reductionImports := reductionNames.toList.map fun n => s!"{modulePrefix}.{n}"
  -- Assemble the modules.
  let dataImport := s!"{modulePrefix}.Tables"
  let mut submodules : Array EmittedModule := #[]
  submodules := submodules.push
    ⟨"Tables", moduleText moduleNamespace noEdit parserImports parts.tablesBody⟩
  submodules := submodules.push
    ⟨"Source", moduleText moduleNamespace noEdit [dataImport] parts.sourceBody⟩
  submodules := submodules.push
    ⟨"Items", moduleText moduleNamespace noEdit [dataImport] parts.itemsBody⟩
  for name in reductionNames, body in parts.reductionFiles do
    submodules := submodules.push
      ⟨name, moduleText moduleNamespace noEdit [dataImport] body⟩
  submodules := submodules.push
    ⟨"Safety", moduleText moduleNamespace noEdit (dataImport :: reductionImports) parts.safetyBody⟩
  submodules := submodules.push
    ⟨"Progress", moduleText moduleNamespace noEdit [dataImport] parts.progressBody⟩
  let umbrellaImports :=
    [dataImport, s!"{modulePrefix}.Source", s!"{modulePrefix}.Items"] ++
      reductionImports ++ [s!"{modulePrefix}.Safety", s!"{modulePrefix}.Progress"]
  let umbrellaComment :=
    "-- LALR(1) tables with checked token-language and execution contracts.\n" ++
    "-- Generated by the in-tree Lean lalrgen; do not edit.\n" ++
    s!"-- {parts.canonicalStates} canonical states; {parts.lalrStates} LALR states.\n" ++
    "-- Certificates are split across the Generated/ directory; this umbrella\n" ++
    "-- imports them and states the final theorems.\n"
  let umbrella := moduleText moduleNamespace umbrellaComment umbrellaImports parts.umbrellaBody
  return { umbrella, submodules }

/-- Emit the whole certificate set as one self-contained module. It reuses the
same per-group bodies as the split emitter, concatenated under one namespace with
no imports between groups, so the theorem names, statements and mutation-sensitive
definitions (`edges`, `firstFacts`, `itemStates`, `fuel`, `loweringWitness`,
`source`, the table constants) match exactly. Standalone tools can then check the
result with `lake env lean` directly. -/
def emitSingle (source : String)
    (moduleNamespace : String := "Parser.LALRGenerated") : Except String String := do
  if !validNamespace moduleNamespace then throw "invalid generated namespace"
  let parts ← generatedParts source
  let comment :=
    "-- LALR(1) tables with checked token-language and execution contracts.\n" ++
    "-- Generated by the in-tree Lean lalrgen --single; do not edit.\n" ++
    s!"-- {parts.canonicalStates} canonical states; {parts.lalrStates} LALR states.\n" ++
    "-- Single-file mode: every certificate group in one module, each body identical\n" ++
    "-- to the split module's, for standalone `lake env lean` checks.\n"
  let body :=
    parts.tablesBody ++ parts.sourceBody ++ parts.itemsBody ++
      String.join parts.reductionFiles.toList ++ parts.safetyBody ++
      parts.progressBody ++ parts.umbrellaBody
  return moduleText moduleNamespace comment parserImports body

end LALRGenerator

def main (args : List String) : IO UInt32 := do
  -- Single-file mode emits every certificate group into one module so standalone
  -- tooling can check it with `lake env lean` without the split import graph.
  let (single, args) := match args with
    | "--single" :: rest => (true, rest)
    | _ => (false, args)
  let (moduleNamespace, args) := match args with
    | "--namespace" :: ns :: rest => (ns, rest)
    | _ => ("Parser.LALRGenerated", args)
  let (modulePrefix, args) := match args with
    | "--module" :: mp :: rest => (mp, rest)
    | _ => (moduleNamespace, args)
  match args with
  | [input, output] =>
    try
      let source ← IO.FS.readFile input
      let outputPath : System.FilePath := output
      if single then
        match LALRGenerator.emitSingle source moduleNamespace with
        | .error error => IO.eprintln error; return (1 : UInt32)
        | .ok text =>
          IO.FS.writeFile outputPath text
          -- Leave only the single file: drop any split directory left by an
          -- earlier run so single mode never mixes with loose submodules.
          let directory := outputPath.withExtension ""
          if ← directory.pathExists then IO.FS.removeDirAll directory
          return (0 : UInt32)
      else
        match LALRGenerator.emit source moduleNamespace modulePrefix with
        | .error error => IO.eprintln error; return (1 : UInt32)
        | .ok emission =>
          IO.FS.writeFile outputPath emission.umbrella
          -- Submodules live in the directory named by the umbrella without its
          -- extension; recreate it so removed modules never linger.
          let directory := outputPath.withExtension ""
          if ← directory.pathExists then IO.FS.removeDirAll directory
          IO.FS.createDirAll directory
          for m in emission.submodules do
            IO.FS.writeFile (directory / (m.name ++ ".lean")) m.text
          return (0 : UInt32)
    catch e => IO.eprintln (toString e); return (1 : UInt32)
  | _ =>
    IO.eprintln "usage: lalrgen [--single] [--namespace Name] [--module Prefix] grammar.ebnf Output.lean"
    return (2 : UInt32)
