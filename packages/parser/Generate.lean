import Parser.EBNF

open Parser

namespace Generator

def atoms : RE Symbol → List Symbol
  | .char a => [a]
  | .plus a b | .comp a b => atoms a ++ atoms b
  | .star a => atoms a
  | _ => []

def unique (xs : List Symbol) : Array Symbol :=
  xs.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]

def symbolCode : Symbol → String
  | .ident => ".ident"
  | .literal s => s!"(.literal {repr s})"

def regexCode (atom : α → String) : RE α → String
  | .zero => ".zero"
  | .epsilon => ".epsilon"
  | .char a => s!"(.char {atom a})"
  | .plus a b => s!"(.plus {regexCode atom a} {regexCode atom b})"
  | .comp a b => s!"(.comp {regexCode atom a} {regexCode atom b})"
  | .star a => s!"(.star {regexCode atom a})"

structure Tables where
  states : Array (RE Nat)
  rows : Array (Array Nat)

/-- Derivative closure with a hard resource limit. Equality-based interning is
deliberately confined to preprocessing, never runtime parsing. -/
def close (width : Nat) : Nat → Nat → Tables → Except String Tables
  | 0, _, _ => .error "DFA exceeds 4096 states; simplify the grammar"
  | fuel + 1, cursor, tables => do
    if cursor ≥ tables.states.size then return tables
    let r := tables.states[cursor]?.getD .zero
    let mut states := tables.states
    let mut row := #[]
    for c in [:width] do
      let d := r.step c
      let index := states.findIdx? (· == d)
      match index with
      | some i => row := row.push i
      | none =>
        row := row.push states.size
        states := states.push d
    close width fuel (cursor + 1) ⟨states, tables.rows.push row⟩

def arrayCode (xs : Array String) : String := "#[" ++ String.intercalate ", " xs.toList ++ "]"

def ebnfExprCode : EBNF.Expr → String
  | .terminal s => s!"(.terminal {symbolCode s})"
  | .ref name => s!"(.ref {repr name})"
  | .seq a b => s!"(.seq {ebnfExprCode a} {ebnfExprCode b})"
  | .alt a b => s!"(.alt {ebnfExprCode a} {ebnfExprCode b})"
  | .optional a => s!"(.optional {ebnfExprCode a})"
  | .many a => s!"(.many {ebnfExprCode a})"

def lexemeCode : EBNF.Lexeme → String
  | .name s => s!"(.name {repr s})"
  | .text s => s!"(.text {repr s})"
  | .punct c => s!"(.punct {repr c})"

/-- Keep an exact source literal and certify its character view. Chunking
keeps generated terms shallow. Prevent tactics in this generated namespace
from unfolding UTF-8 encoding unnecessarily; kernel reduction is unaffected. -/
def sourceCertificate (source : String) : String := Id.run do
  let chars := source.toList.toArray
  let chunks := (List.range ((chars.size + 63) / 64)).map fun i =>
    (chars.extract (64 * i) (64 * (i + 1))).toList
  let mut text := s!"def source : String := {repr source}\n\n"
  for (chunk, i) in chunks.zipIdx do
    text := text ++ s!"def sourceChars{i} : List Char := {repr chunk}\n\n"
  let indices := List.range chunks.length
  let charParts := String.intercalate " ++ " (indices.map fun i => s!"sourceChars{i}")
  text := text ++ s!"def sourceChars : List Char := {if chunks.isEmpty then "[]" else charParts}\n\n" ++
    "-- Guide elaboration only: all equalities are still kernel-checked.\n" ++
    "attribute [local irreducible] String.ofList\n\n" ++
    "theorem source_ofList : source = String.ofList sourceChars := by rfl\n\n" ++
    "theorem source_toList : source.toList = sourceChars := by\n" ++
    "  rw [source_ofList, String.toList_ofList]\n\n" ++
    s!"theorem source_length : source.toList.length = {chars.size} :=\n" ++
    "  (congrArg List.length source_toList).trans (by decide +kernel)\n\n"
  return text

def generate (source : String) (runtimeOnly : Bool := false)
    (moduleNamespace : String := "Parser.Generated") : Except String String := do
  unless (moduleNamespace.splitOn ".").all (fun part =>
      !part.isEmpty && part.toList.all identRest &&
        (part.toList.head?).any identStart) do
    throw "invalid Lean namespace"
  let tokens ← EBNF.lex source
  let parsed ← EBNF.parseTokens tokens
  let raw ← EBNF.compile source
  let alphabet := unique (atoms raw)
  let width := alphabet.size + 1 -- zero is the unknown-token class
  let encode := fun s => (alphabet.findIdx? (· == s)).map (· + 1) |>.getD 0
  let grammar := raw.map encode
  let tables ← close width 4096 0 ⟨#[grammar.simplify], #[]⟩
  let count := tables.states.size
  let symbols := arrayCode (alphabet.map symbolCode)
  let langs := arrayCode (tables.states.map (regexCode (fun n => s!"({n} : Fin {width})")))
  let rows := arrayCode (tables.rows.map (fun row =>
    arrayCode (row.map (fun n => s!"({n} : Fin {count})"))))
  let finals := arrayCode (tables.states.map (fun r => if r.nullable then "true" else "false"))
  if runtimeOnly then
    return "-- Generated runtime tables. The language frontend owns their proof-table equivalence.\n" ++
      s!"import Parser.Token\nimport Parser.AutomatonRuntime\n\nopen Parser\n\nnamespace {moduleNamespace}\n\n" ++
      s!"def alphabet : Array Symbol := {symbols}\n\n" ++
      s!"abbrev Letter := Fin {width}\nabbrev State := Fin {count}\n\n" ++
      "def encode (s : Symbol) : Letter :=\n" ++
      s!"  ⟨((alphabet.findIdx? (· == s)).map (· + 1) |>.getD 0) % {width}, Nat.mod_lt _ (by decide +kernel)⟩\n\n" ++
      s!"def transitions : Array (Array State) := {rows}\n\n" ++
      s!"def accepting : Array Bool := {finals}\n\n" ++
      "def next (s : State) (c : Letter) : State :=\n" ++
      "  let row := transitions[s.val]?.getD #[]\n  row[c.val]?.getD 0\n\n" ++
      "def finalState (s : State) : Bool := accepting[s.val]?.getD false\n\n" ++
      "def recognize (xs : List Letter) : Bool := runDFA next finalState 0 xs\n\n" ++
      s!"end {moduleNamespace}\n"
  return "-- Generated by the Lean EBNF compiler. Do not edit.\n" ++
    "import Parser.EBNF\nimport Parser.Automaton\nimport Parser.Alphabet\n\n" ++
    "set_option maxRecDepth 10000\nset_option maxHeartbeats 8000000\n\n" ++
    s!"open Parser\n\nnamespace {moduleNamespace}\n\n" ++
    sourceCertificate source ++
    s!"def sourceTokens : List EBNF.Lexeme := [{String.intercalate ", " (tokens.map lexemeCode)}]\n\n" ++
    "theorem lexing_checked : EBNF.lex source = .ok sourceTokens := by\n" ++
    "  unfold EBNF.lex\n  rw [source_toList]\n  decide +kernel\n\n" ++
    s!"def parsedGrammar : EBNF.Grammar := [{String.intercalate ", " (parsed.map fun (name, body) => s!"({repr name}, {ebnfExprCode body})")} ]\n\n" ++
    "theorem parsing_checked : EBNF.parseTokens sourceTokens = .ok parsedGrammar := by decide +kernel\n\n" ++
    s!"def expansionFuel : Nat := {EBNF.expansionFuel source parsed}\n\n" ++
    s!"theorem rules_length : parsedGrammar.length = {parsed.length} := by decide +kernel\n\n" ++
    "theorem fuel_checked : EBNF.expansionFuel source parsedGrammar = expansionFuel :=\n" ++
    "  (EBNF.expansionFuel_of_lengths source_length rules_length).trans (by decide +kernel)\n\n" ++
    s!"def rawGrammar : RE Symbol := {regexCode symbolCode raw}\n\n" ++
    "theorem expansion_checked : EBNF.expandGrammar expansionFuel parsedGrammar = .ok rawGrammar := by decide +kernel\n\n" ++
    "theorem source_checked : EBNF.compile source = .ok rawGrammar := by\n" ++
    "  have hp : EBNF.parse source = .ok parsedGrammar := (EBNF.parse_of_lex lexing_checked).trans parsing_checked\n" ++
    "  exact (EBNF.compile_of_parse hp).trans\n" ++
    "    ((congrArg (fun fuel => EBNF.expandGrammar fuel parsedGrammar) fuel_checked).trans expansion_checked)\n\n" ++
    s!"def alphabet : Array Symbol := {symbols}\n\n" ++
    s!"abbrev Letter := Fin {width}\nabbrev State := Fin {count}\n\n" ++
    "def encode (s : Symbol) : Letter :=\n" ++
    s!"  ⟨((alphabet.findIdx? (· == s)).map (· + 1) |>.getD 0) % {width}, Nat.mod_lt _ (by decide +kernel)⟩\n\n" ++
    s!"def grammar : RE Letter := {regexCode (fun n => s!"({n} : Letter)") grammar}\n\n" ++
    "theorem encoding_checked : rawGrammar.map encode = grammar := by decide +kernel\n\n" ++
    "theorem alphabet_checked : ∀ a ∈ Alphabet.atoms rawGrammar, a ∈ alphabet := by\n" ++
    "  simp [rawGrammar, Alphabet.atoms, alphabet]\n\n" ++
    s!"def languages : Array (RE Letter) := {langs}\n\n" ++
    s!"def transitions : Array (Array State) := {rows}\n\n" ++
    s!"def accepting : Array Bool := {finals}\n\n" ++
    "def language (s : State) : RE Letter := languages[s.val]?.getD .zero\n\n" ++
    "def next (s : State) (c : Letter) : State :=\n" ++
    "  let row := transitions[s.val]?.getD #[]\n" ++
    "  row[c.val]?.getD 0\n\n" ++
    "def finalState (s : State) : Bool := accepting[s.val]?.getD false\n\n" ++
    "theorem transitions_checked : ∀ s c, (language s).step c = language (next s c) := by decide +kernel\n\n" ++
    "theorem accepting_checked : ∀ s, finalState s = (language s).nullable := by decide +kernel\n\n" ++
    "theorem start_checked : language 0 = grammar.simplify := by decide +kernel\n\n" ++
    "def parser : CertifiedDFA Letter where\n" ++
    "  State := State\n  start := 0\n  next := next\n  final := finalState\n  language := language\n" ++
    "  next_correct := transitions_checked\n  final_correct := accepting_checked\n\n" ++
    "def recognize (xs : List Letter) : Bool := parser.run parser.start xs\n\n" ++
    "theorem recognize_correct (xs : List Letter) :\n" ++
    "    recognize xs = true ↔ grammar.Accepts xs := by\n" ++
    "  rw [recognize, parser.run_correct]\n" ++
    "  change (language 0).Accepts xs ↔ _\n" ++
    "  rw [start_checked]\n  exact RegularExpression.simplify_correct _ _\n\n" ++
    "theorem recognize_symbols_correct (xs : List Symbol) :\n" ++
    "    recognize (xs.map encode) = true ↔ rawGrammar.Accepts xs := by\n" ++
    "  rw [recognize_correct, ← encoding_checked]\n" ++
    "  exact Alphabet.encode_reflects alphabet rawGrammar alphabet_checked xs\n\n" ++
    s!"end {moduleNamespace}\n"

end Generator

def runGenerator (check runtimeOnly : Bool) (moduleNamespace input output : String) : IO UInt32 := do
  try
    let source ← IO.FS.readFile input
    match Generator.generate source runtimeOnly moduleNamespace with
    | .error e => IO.eprintln e; return (1 : UInt32)
    | .ok code =>
      if check then
        if (← IO.FS.readFile output) != code then
          IO.eprintln s!"{output} is stale; regenerate it"
          return (1 : UInt32)
      else
        IO.FS.writeFile output code
      return (0 : UInt32)
  catch e => IO.eprintln (toString e); return (1 : UInt32)

def main (args : List String) : IO UInt32 := do
  let (moduleNamespace, args) := match args with
    | "--namespace" :: name :: rest => (name, rest)
    | _ => ("Parser.Generated", args)
  match args with
  | [input, output] => runGenerator false false moduleNamespace input output
  | ["--check", input, output] => runGenerator true false moduleNamespace input output
  | ["--runtime", input, output] => runGenerator false true moduleNamespace input output
  | ["--check-runtime", input, output] => runGenerator true true moduleNamespace input output
  | _ =>
    IO.eprintln "usage: ebnfgen [--namespace Name] [--check|--runtime|--check-runtime] grammar.ebnf Generated.lean"
    return 2
