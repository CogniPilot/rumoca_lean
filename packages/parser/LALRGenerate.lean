import Parser.LALR.Generator
import Parser.LALR.EBNF
import Parser.EBNF.SourceText
import Parser.LALR.Safety
import Parser.LALR.ItemCheck
import Parser.LALR.Resources

/-! Grammar-parametric table emitter. All implementation is Lean and lives in the
parser package. It does not publish the complete source `CertifiedParser`:
Frontend actions still need their own contracts. The generated token parser
has checked EBNF preservation, safety, completeness and resource bounds. -/
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

/-- Bind the actual grammar text and generated CFG through a finite structural
witness. These constants are proof-only; the runtime retains its token alphabet
and the ordinary LR tables. -/
private def ebnfCertificates (tokens : List Parser.EBNF.Lexeme)
    (sourceGrammar : Parser.EBNF.Grammar)
    (certificate : Frontend.Certified sourceGrammar) : String :=
  let options := "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n"
  "noncomputable def sourceGrammar : Parser.EBNF.Grammar := " ++ reprStr sourceGrammar ++ "\n\n" ++
  "private noncomputable def prepared : LALR.Frontend.Prepared := ⟨alphabet, " ++
    reprStr certificate.prepared.names ++ ", grammar⟩\n\n" ++
  "private noncomputable def loweringWitness : LALR.Frontend.Witness := ⟨" ++
    reprStr certificate.witness.meanings ++ ",\n" ++
    reprStr certificate.witness.roots ++ ",\n" ++
    reprStr certificate.witness.rules ++ "⟩\n\n" ++
  "private noncomputable def sourceTokens : List Parser.EBNF.Lexeme := " ++ reprStr tokens ++ "\n\n" ++
  options ++ "private theorem lexing_checked : Parser.EBNF.lex source = .ok sourceTokens := by\n" ++
    "  unfold Parser.EBNF.lex\n  rw [source_toList]\n  decide +kernel\n\n" ++
  options ++ "private theorem parsing_checked : Parser.EBNF.parseTokens sourceTokens = .ok sourceGrammar :=\n" ++
    "  by decide +kernel\n\n" ++
  "theorem source_read_checked : Parser.EBNF.parse source = .ok sourceGrammar :=\n" ++
    "  (Parser.EBNF.parse_of_lex lexing_checked).trans parsing_checked\n\n" ++
  options ++ "theorem lowering_checked : loweringWitness.validate sourceGrammar prepared = true :=\n" ++
    "  by decide +kernel\n\n" ++
  "def encode (symbol : Parser.Symbol) : Nat :=\n" ++
    "  (alphabet.findIdx? (· == symbol)).getD (alphabet.size + 1)\n\n" ++
  "theorem ebnf_correct (word : List Parser.Symbol) :\n" ++
    "    Parser.EBNF.Accepts sourceGrammar word ↔ grammar.Accepts (word.map encode) :=\n" ++
    "  loweringWitness.accepts_iff (LALR.Frontend.Witness.validate_iff.mp lowering_checked)\n" ++
    "    (by decide +kernel) word\n\n"

private def sourceParserContract : String :=
  "def parseSymbols (word : List Parser.Symbol) : Except LALR.Failure LALR.Tree :=\n" ++
    "  parse (word.map encode)\n\n" ++
  "theorem source_parse_correct (word : List Parser.Symbol) :\n" ++
    "    Parser.EBNF.parse source = .ok sourceGrammar ∧\n" ++
    "    (Parser.EBNF.Accepts sourceGrammar word ↔ ∃ tree, parseSymbols word = .ok tree) ∧\n" ++
    "    ((∃ tree, parseSymbols word = .ok tree) ∨ parseSymbols word = .error .rejected) :=\n" ++
    "  ⟨source_read_checked, (ebnf_correct word).trans (parse_correct (word.map encode)).1,\n" ++
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
  "    Parser.EBNF.parse source = .ok sourceGrammar ∧\n" ++
  "    (Parser.EBNF.Accepts sourceGrammar (tokens.map (fun token => token.value.symbol)) ↔\n" ++
  "      ∃ result, parseLocated text tokens = .ok result) ∧\n" ++
  "    ((∃ result, parseLocated text tokens = .ok result) ∨\n" ++
  "      parseLocated text tokens = .error .rejected) := by\n" ++
  "  have checked := LALR.parseLocated_correct items_checked budget_checked safety_checked\n" ++
  "    progress_checked (encodeLocatedTokens tokens)\n" ++
  "  rw [← located_fuel tokens] at checked\n" ++
  "  refine ⟨source_read_checked, ?_, checked.2⟩\n" ++
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


/-- Each state gets a small kernel obligation; the final theorem composes all
rows against the unchanged grammar-parametric item validator. -/
private def itemCertificates (states : Array ItemSet) : String := Id.run do
  let options := "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n"
  let mut text := "noncomputable def itemStates : Array LALR.ItemSet := " ++
    array (states.map fun state => "[" ++ String.intercalate ", " (state.map item) ++ "]") ++ "\n\n"
  let mut cases := ""
  for q in [:states.size] do
    let row := s!"(LALR.ItemCheck.items itemStates {q})"
    text := text ++ options ++ s!"private theorem items_{q}_checked :\n" ++
      s!"    ∀ i ∈ {row}, LALR.ItemCheck.Valid grammar i ∧\n" ++
      s!"      LALR.ItemCheck.Closed grammar firstFacts {row} i ∧\n" ++
      s!"      LALR.ItemCheck.Advances grammar tables itemStates {q} i := by decide +kernel\n\n"
    cases := cases ++ s!"    | {q} => exact items_{q}_checked\n"
  return text ++ options ++ "theorem items_checked :\n" ++
    "    LALR.ItemCheck.validate grammar tables firstFacts itemStates = true := by\n" ++
    "  apply LALR.ItemCheck.validate_iff.mpr\n" ++
    "  refine ⟨by decide +kernel, by decide +kernel, first_checked, by decide +kernel, ?_⟩\n" ++
    "  intro q\n" ++
    "  rcases q with ⟨q, bound⟩\n" ++
    s!"  change q < {states.size} at bound\n" ++
    "  match q with\n" ++ cases ++ s!"    | n+{states.size} => omega\n\n"

/-- Only the two scalar budget coefficients are used by runtime parsing.
The complete per-production credit witness remains proof-only metadata. -/
private def budgetCertificates (budget : Fuel.Budget) (credits : Progress.Credits) : String :=
  "noncomputable def fuelBudget : LALR.Fuel.Budget := ⟨" ++
    toString budget.perToken ++ ", " ++ reprStr budget.nonterminals ++ "⟩\n\n" ++
  "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
  "theorem budget_checked : LALR.Fuel.validate grammar fuelBudget = true := by decide +kernel\n\n" ++
  "noncomputable def progressCredits : LALR.Progress.Credits := ⟨" ++
    reprStr credits.states ++ ", " ++ toString credits.ceiling ++ "⟩\n\n" ++
  "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
  "theorem progress_checked : LALR.Progress.validate tables edges fuelBudget progressCredits = true :=\n" ++
  "  by decide +kernel\n\n" ++
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
  "    (by simpa only [parse, LALR.parse_eq_run] using parsed)\n\n"

/-- Check each reduction summary separately, then substitute the proved
equalities into the unchanged validator. Separate declarations avoid one
monolithic normalization of all the reduction computations. -/
private def safetyCertificates (g : Grammar) (tables : Tables) (edges : List Edge) : String := Id.run do
  let rows := Safety.reductionStates g tables edges
  let options := "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n"
  let mut declarations := ""
  let mut names : Array String := #[]
  let mut cases := ""
  for i in [:rows.size] do
    let name := s!"reduction_{i}"
    let prod := s!"(grammar.productions[{i}]?.getD (⟨0, []⟩ : LALR.Production))"
    let expression := s!"LALR.Safety.popStates tables.actions.size edges {prod}.output.reverse " ++
      s!"(LALR.Safety.gotoStates tables {prod}.input)"
    declarations := declarations ++ s!"private noncomputable def {name} : Array Bool := {repr rows[i]!}\n\n" ++
      options ++ s!"private theorem {name}_checked : {expression} = {name} := by decide +kernel\n\n"
    names := names.push name
    cases := cases ++ s!"    | {i} => exact {name}_checked\n"
  return declarations ++ "private noncomputable def reductions : Array (Array Bool) := " ++ array names ++ "\n\n" ++
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
    options ++ "theorem safety_checked : LALR.Safety.validate grammar tables edges = true := by\n" ++
    "  unfold LALR.Safety.validate\n  rw [reductions_checked, acceptance_checked]\n  decide +kernel\n\n"

def emit (source : String) (moduleNamespace : String := "Parser.LALRGenerated") : Except String String := do
  if !(moduleNamespace.splitOn ".").all (fun part =>
      !part.isEmpty && part.toList.all (fun c => Parser.identRest c) &&
        (part.toList.head?).any Parser.identStart) then
    throw "invalid generated namespace"
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
  return "-- LALR(1) tables with checked token-language and execution contracts.\n" ++
    "-- Generated by the in-tree Lean lalrgen; do not edit.\n" ++
    s!"-- {c.canonicalStates} canonical states; {c.collection.states.size} LALR states.\n" ++
    "import Parser.LALR.SafetyProofs\nimport Parser.LALR.FirstProofs\nimport Parser.LALR.Progress\n" ++
    "import Parser.Token\nimport Parser.LALR.LocatedCompleteness\nimport Parser.LALR.EBNFEncoding\n" ++
    "import Parser.EBNF.Rules\nimport Parser.LALR.Actions\n\nopen Parser\n\n" ++
    s!"namespace {moduleNamespace}\n\n" ++
    "set_option maxRecDepth 10000\nset_option maxHeartbeats 8000000\n\n" ++
    Parser.EBNF.Emission.sourceCertificate source ++
    s!"def alphabet : Array Parser.Symbol := {repr p.alphabet}\n\n" ++
    s!"def grammar : LALR.Grammar := ⟨{g.terminals}, {g.nonterminals}, {g.start}, " ++
    array (g.productions.map production) ++ "⟩\n\n" ++
    ebnfCertificates sourceTokens sourceGrammar lowering ++
    ruleCertificates sourceGrammar ++
    "def tables : LALR.Tables := ⟨" ++ array (c.tables.actions.map fun row => array (row.map action)) ++
    ", " ++ array (c.tables.gotos.map fun row => array (row.map fun n =>
      n.map (fun n => s!"some {n}") |>.getD "none")) ++ "⟩\n\n" ++
    "def edges : List LALR.Edge := [" ++
      String.intercalate ", " (c.collection.edges.toList.map edge) ++ "]\n\n" ++
    "def firstFacts : Array LALR.First := " ++ array (facts.map firstFact) ++ "\n\n" ++
    "-- Proof-producing normalization; all resulting terms are kernel checked.\n" ++
    "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 8000000 in\n" ++
    "set_option cbv.warning false in\n" ++
    "theorem first_checked : LALR.FirstCheck.validate grammar firstFacts = true := by cbv\n\n" ++
    itemCertificates c.collection.states ++
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
    "-- Typed frontend actions remain a separate obligation.\n" ++
    safetyCertificates g c.tables c.collection.edges.toList ++
    budgetCertificates budget resources.credits ++
    sourceParserContract ++
    "theorem execution_safe (fuel : Nat) (input : List Nat) (error : LALR.Failure)\n" ++
    "    (h : LALR.parse grammar tables fuel input = .error error) :\n" ++
    "    error = .exhausted ∨ error = .rejected :=\n" ++
    "  LALR.Safety.validated_parse_safe safety_checked h\n\n" ++
    locatedParserContract ++
    s!"end {moduleNamespace}\n"

end LALRGenerator

def main (args : List String) : IO UInt32 := do
  let (moduleNamespace, args) := match args with
    | "--namespace" :: ns :: rest => (ns, rest)
    | _ => ("Parser.LALRGenerated", args)
  match args with
  | [input, output] =>
    try
      let source ← IO.FS.readFile input
      match LALRGenerator.emit source moduleNamespace with
      | .error error => IO.eprintln error; return (1 : UInt32)
      | .ok text => IO.FS.writeFile output text; return (0 : UInt32)
    catch e => IO.eprintln (toString e); return (1 : UInt32)
  | _ =>
    IO.eprintln "usage: lalrgen [--namespace Name] grammar.ebnf Candidate.lean"
    return (2 : UInt32)
